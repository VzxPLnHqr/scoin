package scoin.reckless

import scoin._
import scoin.Crypto._
import scodec.bits._

// Here we encapsulate some of the per-person functionality we sometimes
// need for testing purposes.
// We can use some scala modifiers like `private[this] def` to emulate 
// that only the "person" itself can access its own private values.
final case class Person(name: String) {

  // naive, insecure, demo purposes only
  private[this] def seed: ByteVector32 = sha256(ByteVector(name.getBytes))

  def priv: PrivateKey = PrivateKey(sha256(seed))

  def pub: PublicKey = priv.publicKey

  /**
    * calculate the i'th per commitment secret
    */
  private[this] def perCommitSecret(i: Int): PrivateKey =
    ln.Generators.perCommitSecret(seed,i)

  /** calculate the i'th per commitment point
   * */
  def perCommitPoint(i: Int): PublicKey =
    ln.Generators.perCommitPoint(seed,i)

  /** a blinded public key */
  def revocationPubKey(remoteNodePerCommitPoint: PublicKey): PublicKey =
    ln.Generators.revocationPubKey(this.pub,remoteNodePerCommitPoint)


  /** Calculate the i'th "publishing" secret
   *  The publisher of a commitment transaction is forced to reveal
   *  this secret thereby allowing the other party to punish (if necessary)
   * */
  def publishingSecret(i: Int): PrivateKey = 
    ln.Generators.perCommitSecret(
      //naive re-use of ln stuff here
      sha256(ByteVector("publishing secret".getBytes) ++ seed),
      index = i
    )

  /**
   * The i'th "publishing" public key. This is the point which the remote
   * party tweaks their real signature with, to get `adapterSig`. If the
   * real signature `sig` is ever broadcast, the local party can calculate the
   * publishing secret (it is just `sig - adapterSig`). */
  def publishingPubKey(i: Int): PublicKey = publishingSecret(i).publicKey

  /**
    * Generate musig2 nonce
    *
    * @param aggregateXOnlyPublicKey
    * @param message
    * @param nextRand32
    * @return (97-byte secNonce, 66-byte pubNonce)
    */
  def musig2NonceGen(
          aggregateXOnlyPublicKey: XOnlyPublicKey, 
          message: ByteVector,
          nextRand32: => ByteVector32 ) = Musig2.nonceGen(
          secretSigningKey = Some(priv.value),
          pubKey = pub,
          aggregateXOnlyPublicKey = Some(aggregateXOnlyPublicKey),
          message = Some(message),
          extraIn = None,
          nextRand32 = nextRand32
  )
} // end of Person class

