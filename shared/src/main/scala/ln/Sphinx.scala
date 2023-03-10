package scoin.ln

import scala.annotation.tailrec
import scala.util.{Failure, Success, Try}
import scodec.Attempt
import scodec.bits.ByteVector

import scoin._
import scoin.ln._

object Sphinx {

  /** Supported packet version. Note that since this value is outside of the
    * onion encrypted payload, intermediate nodes may or may not use this value
    * when forwarding the packet to the next node.
    */
  val Version = 0

  // We use HMAC-SHA256 which returns 32-bytes message authentication codes.
  val MacLength = 32

  def mac(key: ByteVector, message: ByteVector): ByteVector32 =
    Crypto.hmac256(key, message)

  def generateStream(key: ByteVector, length: Int): ByteVector =
    Crypto
      .chacha20(
        ByteVector.fill(length)(0),
        key,
        ByteVector.fill(12)(0)
      )

  def generateKey(keyType: ByteVector, secret: ByteVector32): ByteVector32 =
    Crypto.hmac256(keyType, secret)

  def generateKey(keyType: String, secret: ByteVector32): ByteVector32 =
    generateKey(ByteVector.view(keyType.getBytes("UTF-8")), secret)

  def computeSharedSecret(pub: PublicKey, secret: PrivateKey): ByteVector32 =
    Crypto.sha256(pub.multiply(secret).value)

  def computeBlindingFactor(pub: PublicKey, secret: ByteVector): ByteVector32 =
    Crypto.sha256(pub.value ++ secret)

  def blind(pub: PublicKey, blindingFactor: ByteVector32): PublicKey =
    pub.multiply(PrivateKey(blindingFactor))

  def blind(pub: PublicKey, blindingFactors: Seq[ByteVector32]): PublicKey =
    blindingFactors.foldLeft(pub)(blind)

  /** Compute the ephemeral public keys and shared secrets for all nodes on the
    * route.
    *
    * @param sessionKey
    *   this node's session key.
    * @param publicKeys
    *   public keys of each node on the route.
    * @return
    *   a tuple (ephemeral public keys, shared secrets).
    */
  def computeEphemeralPublicKeysAndSharedSecrets(
      sessionKey: PrivateKey,
      publicKeys: Seq[PublicKey]
  ): (Seq[PublicKey], Seq[ByteVector32]) = {
    val ephemeralPublicKey0 =
      blind(Crypto.G, sessionKey.value)
    val secret0 = computeSharedSecret(publicKeys.head, sessionKey)
    val blindingFactor0 = computeBlindingFactor(ephemeralPublicKey0, secret0)
    computeEphemeralPublicKeysAndSharedSecrets(
      sessionKey,
      publicKeys.tail,
      Seq(ephemeralPublicKey0),
      Seq(blindingFactor0),
      Seq(secret0)
    )
  }

  @tailrec
  private def computeEphemeralPublicKeysAndSharedSecrets(
      sessionKey: PrivateKey,
      publicKeys: Seq[PublicKey],
      ephemeralPublicKeys: Seq[PublicKey],
      blindingFactors: Seq[ByteVector32],
      sharedSecrets: Seq[ByteVector32]
  ): (Seq[PublicKey], Seq[ByteVector32]) = {
    if (publicKeys.isEmpty) (ephemeralPublicKeys, sharedSecrets)
    else {
      val ephemeralPublicKey =
        blind(ephemeralPublicKeys.last, blindingFactors.last)
      val secret =
        computeSharedSecret(blind(publicKeys.head, blindingFactors), sessionKey)
      val blindingFactor = computeBlindingFactor(ephemeralPublicKey, secret)
      computeEphemeralPublicKeysAndSharedSecrets(
        sessionKey,
        publicKeys.tail,
        ephemeralPublicKeys :+ ephemeralPublicKey,
        blindingFactors :+ blindingFactor,
        sharedSecrets :+ secret
      )
    }
  }

  /** Peek at the first bytes of the per-hop payload to extract its length.
    */
  def peekPayloadLength(payload: ByteVector): Int = {
    require(payload.head != 0, "legacy onion format is not supported anymore")
    MacLength + PaymentOnionCodecs.payloadLengthDecoder
      .decode(payload.bits)
      .require
      .value
      .toInt
  }

  /** Decrypting an onion packet yields a payload for the current node and the
    * encrypted packet for the next node.
    *
    * @param payload
    *   decrypted payload for this node.
    * @param nextPacket
    *   packet for the next node.
    * @param sharedSecret
    *   shared secret for the sending node, which we will need to return failure
    *   messages.
    */
  case class DecryptedPacket(
      payload: ByteVector,
      nextPacket: OnionRoutingPacket,
      sharedSecret: ByteVector32
  ) {
    val isLastPacket: Boolean = nextPacket.hmac == ByteVector32.Zeroes
  }

  /** A encrypted onion packet with all the associated shared secrets.
    *
    * @param packet
    *   encrypted onion packet.
    * @param sharedSecrets
    *   shared secrets (one per node in the route). Known (and needed) only if
    *   you're creating the packet. Empty if you're just forwarding the packet
    *   to the next node.
    */
  case class PacketAndSecrets(
      packet: OnionRoutingPacket,
      sharedSecrets: Seq[(ByteVector32, PublicKey)]
  )

  /** Generate a deterministic filler to prevent intermediate nodes from knowing
    * their position in the route. See
    * https://github.com/lightningnetwork/lightning-rfc/blob/master/04-onion-routing.md#filler-generation
    *
    * @param keyType
    *   type of key used (depends on the onion we're building).
    * @param packetPayloadLength
    *   length of the packet's encrypted onion payload (e.g. 1300 for standard
    *   payment onions).
    * @param sharedSecrets
    *   shared secrets for all the hops.
    * @param payloads
    *   payloads for all the hops.
    * @return
    *   filler bytes.
    */
  def generateFiller(
      keyType: String,
      packetPayloadLength: Int,
      sharedSecrets: Seq[ByteVector32],
      payloads: Seq[ByteVector]
  ): ByteVector = {
    require(
      sharedSecrets.length == payloads.length,
      "the number of secrets should equal the number of payloads"
    )

    (sharedSecrets zip payloads).foldLeft(ByteVector.empty)(
      (padding, secretAndPayload) => {
        val (secret, perHopPayload) = secretAndPayload
        val perHopPayloadLength = peekPayloadLength(perHopPayload)
        require(
          perHopPayloadLength == perHopPayload.length + MacLength,
          s"invalid payload: length isn't correctly encoded: $perHopPayload"
        )
        val key = generateKey(keyType, secret)
        val padding1 = padding ++ ByteVector.fill(perHopPayloadLength)(0)
        val stream =
          generateStream(key, packetPayloadLength + perHopPayloadLength)
            .takeRight(padding1.length)
        padding1.xor(stream)
      }
    )
  }

  /** Decrypt the incoming packet, extract the per-hop payload and build the
    * packet for the next node.
    *
    * @param privateKey
    *   this node's private key.
    * @param associatedData
    *   associated data.
    * @param packet
    *   packet received by this node.
    * @return
    *   a DecryptedPacket(payload, packet, shared secret) object where:
    *   - payload is the per-hop payload for this node.
    *   - packet is the next packet, to be forwarded using the info that is
    *     given in the payload.
    *   - shared secret is the secret we share with the node that sent the
    *     packet. We need it to propagate failure messages upstream. or a
    *     BadOnion error containing the hash of the invalid onion.
    */
  def peel(
      privateKey: PrivateKey,
      associatedData: Option[ByteVector32],
      packet: OnionRoutingPacket
  ): Either[BadOnion, DecryptedPacket] = packet.version match {
    case 0 =>
      Try(PublicKey(packet.publicKey, checkValid = true)) match {
        case Success(packetEphKey) =>
          val sharedSecret = computeSharedSecret(packetEphKey, privateKey)
          val mu = generateKey("mu", sharedSecret)
          val check = mac(
            mu,
            associatedData.map(packet.payload ++ _).getOrElse(packet.payload)
          )
          if (check == packet.hmac) {
            val rho = generateKey("rho", sharedSecret)
            // Since we don't know the length of the per-hop payload (we will learn it once we decode the first bytes),
            // we have to pessimistically generate a long cipher stream.
            val stream = generateStream(rho, 2 * packet.payload.length.toInt)
            val bin = (packet.payload ++ ByteVector.fill(packet.payload.length)(
              0
            )) xor stream

            Try(peekPayloadLength(bin)) match {
              case Success(perHopPayloadLength) => {
                val perHopPayload = bin.take(perHopPayloadLength - MacLength)
                val hmac = ByteVector32(
                  bin.slice(
                    perHopPayloadLength - MacLength,
                    perHopPayloadLength
                  )
                )
                val nextOnionPayload =
                  bin.drop(perHopPayloadLength).take(packet.payload.length)
                val nextPubKey = blind(
                  packetEphKey,
                  computeBlindingFactor(packetEphKey, sharedSecret)
                )

                Right(
                  DecryptedPacket(
                    perHopPayload,
                    OnionRoutingPacket(
                      Version,
                      nextPubKey.value,
                      nextOnionPayload,
                      hmac
                    ),
                    sharedSecret
                  )
                )
              }
              case Failure(_) => Left(InvalidOnionVersion(hash(packet)))
            }
          } else {
            Left(InvalidOnionHmac(hash(packet)))
          }
        case Failure(_) => Left(InvalidOnionKey(hash(packet)))
      }
    case _ => Left(InvalidOnionVersion(hash(packet)))
  }

  /** Wrap the given packet in an additional layer of onion encryption, adding
    * an encrypted payload for a specific node.
    *
    * Packets are constructed in reverse order:
    *   - you first create the packet for the final recipient
    *   - then you call wrap(...) until you've built the final onion packet that
    *     will be sent to the first node in the route
    *
    * @param payload
    *   per-hop payload for the target node.
    * @param associatedData
    *   associated data.
    * @param ephemeralPublicKey
    *   ephemeral key shared with the target node.
    * @param sharedSecret
    *   shared secret with this hop.
    * @param packet
    *   current packet or random bytes if the packet hasn't been initialized.
    * @param onionPayloadFiller
    *   optional onion payload filler, needed only when you're constructing the
    *   last packet.
    * @return
    *   the next packet.
    */
  def wrap(
      payload: ByteVector,
      associatedData: Option[ByteVector32],
      ephemeralPublicKey: PublicKey,
      sharedSecret: ByteVector32,
      packet: Either[ByteVector, OnionRoutingPacket],
      onionPayloadFiller: ByteVector = ByteVector.empty
  ): OnionRoutingPacket = {
    val packetPayloadLength = packet match {
      case Left(startingBytes) => startingBytes.length.toInt
      case Right(p)            => p.payload.length.toInt
    }
    require(
      payload.length <= packetPayloadLength - MacLength,
      s"packet per-hop payload cannot exceed ${packetPayloadLength - MacLength} bytes"
    )

    val (currentMac, currentPayload): (ByteVector32, ByteVector) =
      packet match {
        // Packet construction starts with an empty mac and random payload.
        case Left(startingBytes) => (ByteVector32.Zeroes, startingBytes)
        case Right(p)            => (p.hmac, p.payload)
      }
    val nextOnionPayload = {
      val onionPayload1 = payload ++ currentMac ++ currentPayload.dropRight(
        payload.length + MacLength
      )
      val onionPayload2 = onionPayload1 xor generateStream(
        generateKey("rho", sharedSecret),
        packetPayloadLength
      )
      onionPayload2.dropRight(onionPayloadFiller.length) ++ onionPayloadFiller
    }

    val nextHmac = mac(
      generateKey("mu", sharedSecret),
      associatedData.map(nextOnionPayload ++ _).getOrElse(nextOnionPayload)
    )
    val nextPacket = OnionRoutingPacket(
      Version,
      ephemeralPublicKey.value,
      nextOnionPayload,
      nextHmac
    )
    nextPacket
  }

  /** Create an encrypted onion packet that contains payloads for all nodes in
    * the list.
    *
    * @param sessionKey
    *   session key.
    * @param packetPayloadLength
    *   length of the packet's encrypted onion payload (e.g. 1300 for standard
    *   payment onions).
    * @param publicKeys
    *   node public keys (one per node).
    * @param payloads
    *   payloads (one per node).
    * @param associatedData
    *   associated data.
    * @return
    *   An onion packet with all shared secrets. The onion packet can be sent to
    *   the first node in the list, and the shared secrets (one per node) can be
    *   used to parse returned failure messages if needed.
    */
  def create(
      sessionKey: PrivateKey,
      packetPayloadLength: Int,
      publicKeys: Seq[PublicKey],
      payloads: Seq[ByteVector],
      associatedData: Option[ByteVector32]
  ): Try[PacketAndSecrets] = Try {
    require(
      payloads.map(_.length + MacLength).sum <= packetPayloadLength,
      s"packet per-hop payloads cannot exceed $packetPayloadLength bytes"
    )
    val (ephemeralPublicKeys, sharedsecrets) =
      computeEphemeralPublicKeysAndSharedSecrets(sessionKey, publicKeys)
    val filler = generateFiller(
      "rho",
      packetPayloadLength,
      sharedsecrets.dropRight(1),
      payloads.dropRight(1)
    )

    // We deterministically-derive the initial payload bytes: see https://github.com/lightningnetwork/lightning-rfc/pull/697
    val startingBytes =
      generateStream(generateKey("pad", sessionKey.value), packetPayloadLength)
    val lastPacket = wrap(
      payloads.last,
      associatedData,
      ephemeralPublicKeys.last,
      sharedsecrets.last,
      Left(startingBytes),
      filler
    )

    @tailrec
    def loop(
        hopPayloads: Seq[ByteVector],
        ephKeys: Seq[PublicKey],
        sharedSecrets: Seq[ByteVector32],
        packet: OnionRoutingPacket
    ): OnionRoutingPacket = {
      if (hopPayloads.isEmpty) packet
      else {
        val nextPacket = wrap(
          hopPayloads.last,
          associatedData,
          ephKeys.last,
          sharedSecrets.last,
          Right(packet)
        )
        loop(
          hopPayloads.dropRight(1),
          ephKeys.dropRight(1),
          sharedSecrets.dropRight(1),
          nextPacket
        )
      }
    }

    val packet = loop(
      payloads.dropRight(1),
      ephemeralPublicKeys.dropRight(1),
      sharedsecrets.dropRight(1),
      lastPacket
    )
    PacketAndSecrets(packet, sharedsecrets.zip(publicKeys))
  }

  /** When an invalid onion is received, its hash should be included in the
    * failure message.
    */
  def hash(onion: OnionRoutingPacket): ByteVector32 =
    Crypto.sha256(
      OnionRoutingCodecs
        .onionRoutingPacketCodec(onion.payload.length.toInt)
        .encode(onion)
        .require
        .toByteVector
    )

  /** A properly decrypted failure from a node in the route.
    *
    * @param originNode
    *   public key of the node that generated the failure.
    * @param failureMessage
    *   friendly failure message.
    */
  case class DecryptedFailurePacket(
      originNode: PublicKey,
      failureMessage: FailureMessage
  )

  object FailurePacket {
    val MaxPayloadLength = 256
    val PacketLength = MacLength + MaxPayloadLength + 2 + 2

    /** Create a failure packet that will be returned to the sender. Each
      * intermediate hop will add a layer of encryption and forward to the
      * previous hop. Note that malicious intermediate hops may drop the packet
      * or alter it (which breaks the mac).
      *
      * @param sharedSecret
      *   destination node's shared secret that was computed when the original
      *   onion for the HTLC was created or forwarded: see OnionPacket.create()
      *   and OnionPacket.wrap().
      * @param failure
      *   failure message.
      * @return
      *   a failure packet that can be sent to the destination node.
      */
    def create(
        sharedSecret: ByteVector32,
        failure: FailureMessage
    ): ByteVector = {
      val um = generateKey("um", sharedSecret)
      val packet = FailureMessageCodecs
        .failureOnionCodec(um)
        .encode(failure)
        .require
        .toByteVector
      wrap(packet, sharedSecret)
    }

    /** Wrap the given packet in an additional layer of onion encryption for the
      * previous hop.
      *
      * @param packet
      *   failure packet.
      * @param sharedSecret
      *   destination node's shared secret.
      * @return
      *   an encrypted failure packet that can be sent to the destination node.
      */
    def wrap(packet: ByteVector, sharedSecret: ByteVector32): ByteVector = {
      if (packet.length != PacketLength) {
        // logger.warn(
        //   s"invalid error packet length ${packet.length}, must be $PacketLength (malicious or buggy downstream node)"
        // )
      }
      val key = generateKey("ammag", sharedSecret)
      val stream = generateStream(key, PacketLength)
      // If we received a packet with an invalid length, we trim and pad to forward a packet with a normal length upstream.
      // This is a poor man's attempt at increasing the likelihood of the sender receiving the error.
      packet.take(PacketLength).padLeft(PacketLength) xor stream
    }

    /** Decrypt a failure packet. Node shared secrets are applied until the
      * packet's MAC becomes valid, which means that it was sent by the
      * corresponding node. Note that malicious nodes in the route may have
      * altered the packet, triggering a decryption failure.
      *
      * @param packet
      *   failure packet.
      * @param sharedSecrets
      *   nodes shared secrets.
      * @return
      *   Success(secret, failure message) if the origin of the packet could be
      *   identified and the packet decrypted, Failure otherwise.
      */
    def decrypt(
        packet: ByteVector,
        sharedSecrets: Seq[(ByteVector32, PublicKey)]
    ): Try[DecryptedFailurePacket] = Try {
      require(
        packet.length == PacketLength,
        s"invalid error packet length ${packet.length}, must be $PacketLength"
      )

      @tailrec
      def loop(
          packet: ByteVector,
          secrets: Seq[(ByteVector32, PublicKey)]
      ): DecryptedFailurePacket = secrets match {
        case Nil =>
          throw new RuntimeException(
            s"couldn't parse error packet=$packet with sharedSecrets=$sharedSecrets"
          )
        case (secret, pubkey) :: tail =>
          val packet1 = wrap(packet, secret)
          val um = generateKey("um", secret)
          FailureMessageCodecs
            .failureOnionCodec(um)
            .decode(packet1.toBitVector) match {
            case Attempt.Successful(value) =>
              DecryptedFailurePacket(pubkey, value.value)
            case _ => loop(packet1, tail)
          }
      }

      loop(packet, sharedSecrets)
    }
  }

  /** Route blinding is a lightweight technique to provide recipient anonymity
    * by blinding an arbitrary amount of hops at the end of an onion path. It
    * can be used for payments or onion messages.
    */
  object RouteBlinding {

    /** @param publicKey
      *   introduction node's public key (which cannot be blinded since the
      *   sender need to find a route to it).
      * @param blindedPublicKey
      *   blinded public key, which hides the real public key.
      * @param blindingEphemeralKey
      *   blinding tweak that can be used by the receiving node to derive the
      *   private key that matches the blinded public key.
      * @param encryptedPayload
      *   encrypted payload that can be decrypted with the introduction node's
      *   private key and the blinding ephemeral key.
      */
    case class IntroductionNode(
        publicKey: PublicKey,
        blindedPublicKey: PublicKey,
        blindingEphemeralKey: PublicKey,
        encryptedPayload: ByteVector
    )

    /** @param blindedPublicKey
      *   blinded public key, which hides the real public key.
      * @param encryptedPayload
      *   encrypted payload that can be decrypted with the receiving node's
      *   private key and the blinding ephemeral key.
      */
    case class BlindedNode(
        blindedPublicKey: PublicKey,
        encryptedPayload: ByteVector
    )

    /** @param introductionNodeId
      *   the first node, not blinded so that the sender can locate it.
      * @param blindingKey
      *   blinding tweak that can be used by the introduction node to derive the
      *   private key that matches the blinded public key.
      * @param blindedNodes
      *   blinded nodes (including the introduction node).
      */
    case class BlindedRoute(
        introductionNodeId: PublicKey,
        blindingKey: PublicKey,
        blindedNodes: Seq[BlindedNode]
    ) {
      require(blindedNodes.nonEmpty, "blinded route must not be empty")
      val introductionNode: IntroductionNode = IntroductionNode(
        introductionNodeId,
        blindedNodes.head.blindedPublicKey,
        blindingKey,
        blindedNodes.head.encryptedPayload
      )
      val subsequentNodes: Seq[BlindedNode] = blindedNodes.tail
      val blindedNodeIds: Seq[PublicKey] = blindedNodes.map(_.blindedPublicKey)
      val encryptedPayloads: Seq[ByteVector] =
        blindedNodes.map(_.encryptedPayload)
    }

    /** Blind the provided route and encrypt intermediate nodes' payloads.
      *
      * @param sessionKey
      *   this node's session key.
      * @param publicKeys
      *   public keys of each node on the route, starting from the introduction
      *   point.
      * @param payloads
      *   payloads that should be encrypted for each node on the route.
      * @return
      *   a blinded route.
      */
    def create(
        sessionKey: PrivateKey,
        publicKeys: Seq[PublicKey],
        payloads: Seq[ByteVector]
    ): BlindedRoute = {
      require(
        publicKeys.length == payloads.length,
        "a payload must be provided for each node in the blinded path"
      )
      var e = sessionKey
      val (blindedHops, blindingKeys) = publicKeys
        .zip(payloads)
        .map { case (publicKey, payload) =>
          val blindingKey = e.publicKey
          val sharedSecret = computeSharedSecret(publicKey, e)
          val blindedPublicKey =
            blind(publicKey, generateKey("blinded_node_id", sharedSecret))
          val rho = generateKey("rho", sharedSecret)
          val encrypted =
            Crypto.ChaCha20Poly1305
              .encrypt(
                payload,
                rho,
                ByteVector.fill(12)(0),
                ByteVector.empty
              )
          e = e.multiply(
            PrivateKey(Crypto.sha256(blindingKey.value ++ sharedSecret.bytes))
          )
          (BlindedNode(blindedPublicKey, encrypted), blindingKey)
        }
        .unzip
      BlindedRoute(publicKeys.head, blindingKeys.head, blindedHops)
    }

    /** Compute the blinded private key that must be used to decrypt an incoming
      * blinded onion.
      *
      * @param privateKey
      *   this node's private key.
      * @param blindingEphemeralKey
      *   unblinding ephemeral key.
      * @return
      *   this node's blinded private key.
      */
    def derivePrivateKey(
        privateKey: PrivateKey,
        blindingEphemeralKey: PublicKey
    ): PrivateKey = {
      val sharedSecret = computeSharedSecret(blindingEphemeralKey, privateKey)
      privateKey.multiply(
        PrivateKey(generateKey("blinded_node_id", sharedSecret))
      )
    }

    /** Decrypt the encrypted payload (usually found in the onion) that contains
      * instructions to locate the next node.
      *
      * @param privateKey
      *   this node's private key.
      * @param blindingEphemeralKey
      *   unblinding ephemeral key.
      * @param encryptedPayload
      *   encrypted payload for this node.
      * @return
      *   a tuple (decrypted payload, unblinding ephemeral key for the next
      *   node)
      */
    def decryptPayload(
        privateKey: PrivateKey,
        blindingEphemeralKey: PublicKey,
        encryptedPayload: ByteVector
    ): Try[(ByteVector, PublicKey)] = Try {
      val sharedSecret = computeSharedSecret(blindingEphemeralKey, privateKey)
      val rho = generateKey("rho", sharedSecret)
      val decrypted = Crypto.ChaCha20Poly1305
        .decrypt(
          encryptedPayload,
          rho,
          ByteVector.fill(12)(0),
          ByteVector.empty
        )
      val nextBlindingEphemeralKey = blind(
        blindingEphemeralKey,
        computeBlindingFactor(blindingEphemeralKey, sharedSecret)
      )
      (decrypted, nextBlindingEphemeralKey)
    }
  }
}
