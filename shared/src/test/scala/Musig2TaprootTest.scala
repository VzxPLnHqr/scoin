package scoin

import utest._
import scoin._
import Crypto._
import scodec.bits._

object Musig2TaprootTest extends TestSuite {
  val tests = Tests {
    test("musig2 with taproot - create and spend via keypath") {
      // GOAL: create a pay2tr output which is 2of2 (musig2)
      //       - fund the output
      //       - spend the output via keypath spend
      val alice_priv = PrivateKey(BigInt(21)) // super great secret choice, Alice.
      val alice_pub = alice_priv.publicKey

      val bob_priv = PrivateKey(BigInt(52)) // also really secure. Way to go Bob!
      val bob_pub = bob_priv.publicKey

      // create an aggregate public key (pointQ) in a KeyAggCtx
      // keyaggctx.pointQ is the aggregate public key
      val keyaggctx = Musig2.keyAgg(List(alice_pub,bob_pub))
      val pointQ = keyaggctx.pointQ

      // construct the output public key for the taproot output
      val outputXOnlyPubKey = pointQ.xonly

      // fund a pay2tr output locked to
      val fundingTx = Transaction(
        version = 2,
        txIn = List(
          TxIn.coinbase(OP_1 :: OP_1 :: Nil) // bogus coinbase
        ),
        txOut = List(
          TxOut(
            amount = Satoshi(1_000_000L),
            publicKeyScript = Script.pay2tr(outputXOnlyPubKey)
          )
        ),
        lockTime = 0L
      )

      // Alice and Bob agree to send the funds solely to Bob
      // Normally Bob would provide a fresh public key, but here
      // we just reuse his existing one.
      // 
      // Bob creates an unsigned spending transaction.
      val unsignedSpendingTx = Transaction(
        version = 2,
        txIn = List(
          TxIn(
            outPoint = OutPoint(fundingTx,0),
            signatureScript = ByteVector.empty,
            sequence = TxIn.SEQUENCE_FINAL,
            witness = ScriptWitness.empty
          )
        ),
        txOut = List(
          TxOut(
            amount = fundingTx.txOut(0).amount - Satoshi(5000), // 5000 sat fee
            publicKeyScript = Script.pay2tr(bob_pub.xonly.outputKey(merkleRoot = None)) // to Bob only
          )
        ),
        lockTime = 0L
      )

      // now we need to construct the message to be signed
      // sometimes people use `z` to represent the message which is constructed
      // by hashing the spending transaction in a special way
      val z = Transaction.hashForSigningSchnorr(
        tx = unsignedSpendingTx,
        inputIndex = 0,
        inputs = List(fundingTx.txOut(0)),
        sighashType = SIGHASH_DEFAULT, // (0x00),
        sigVersion = SigVersion.SIGVERSION_TAPROOT,
        codeSeparatorPos = 0xffffffffL
      )

      // Now Alice and Bob need to share their public nonce points.
      // It is IMPORTANT they each use fresh randomness for their nonce points.
      // Here we use terrible randomness for demonstration purposes.
      // Alice and Bob each run the `Musig2.nonceGen` algorithm and then exchange
      // their public nonces.
      val (alice_secnonce, alice_pubnonce) = Musig2.nonceGen(
        secretSigningKey = Some(alice_priv.value),
        pubKey = alice_pub,
        aggregateXOnlyPublicKey = Some(outputXOnlyPubKey),
        message = Some(z),
        extraIn = None,
        nextRand32 = ByteVector32.fromValidHex("01"*32) // not secure
      )

      // Note: other than the public key and fresh randomnesss,
      // the other fields are optional for nonce generation. Supplying them
      // just provides some "added protection" in case the available randomness
      // is not the best (think constrained hardware device).
      val (bob_secnonce, bob_pubnonce) = Musig2.nonceGen(
        secretSigningKey = Some(bob_priv.value),
        pubKey = bob_pub,
        aggregateXOnlyPublicKey = Some(outputXOnlyPubKey),
        message = Some(z.bytes),
        extraIn = None,
        nextRand32 = ByteVector32.fromValidHex("02"*32) // not secure
      )

      // combine their respective pubnonces
      val aggnonce = Musig2.nonceAgg(List(alice_pubnonce, bob_pubnonce))

      // Create a signing session context
      // The context can be re-created by either of Alice or Bob
      val ctx = Musig2.SessionCtx(
          aggNonce = aggnonce,
          numPubKeys = 2,
          pubKeys = List(alice_pub.value, bob_pub.value),
          numTweaks = 0, // default: no tweaks
          tweaks = List(), // default: no tweaks
          isXonlyTweak = List(), // default: no tweaks
          message = z // the (hash of) the spending transaction
      )

      // Alice and Bob each independently sign using the Musig2 signing algorithm.
      // The resulting partial signatures are 32-bytes each.
      val alice_psig = Musig2.sign(alice_secnonce,alice_priv,ctx)
      val bob_psig = Musig2.sign(bob_secnonce,bob_priv,ctx)

      // Combine the partial signatures into a complete, valid BIP340 signature.
      val sig = Musig2.partialSigAgg(List(alice_psig,bob_psig),ctx)

      // verify that our signature is valid
      assert(verifySignatureSchnorr(sig,z,pointQ.xonly))

      // Update our transaction to include the signature in the witness.
      val signedTx = unsignedSpendingTx.updateWitness(0,ScriptWitness(List(sig)))

      // Verify that our spending transaction is valid. The below would throw
      // an exception if not.
      Transaction.correctlySpends(signedTx,List(fundingTx),ScriptFlags.STANDARD_SCRIPT_VERIFY_FLAGS)
    }

    // Here we encapsulate some of the per-person functionality we need.
    // We use some scala modifiers like `private[this] def` to emulate that only
    // the "person" itself can access its own private values.
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

    test("musig2 with taproot - adaptor sigs") {
      /** Goal: Alice and Bob each end up with a musig2 adaptor signature.
       *        Each can repair and publish their signature, but by doing 
       *        so it reveals the publisher's "publishing secret" which is
       *        which is the discrete logarithm for the publisher's
       *        "publishing point." 
       * 
       * See: https://github.com/t-bast/lightning-docs/blob/master/schnorr.md#musig2-adaptor-signatures
      */
      val alice = Person("alice11")
      val bob = Person("bob")

      // create an aggregate public key (pointQ) in a KeyAggCtx
      // keyaggctx.pointQ is the aggregate public key
      val keyaggctx = Musig2.keyAgg(Musig2.keySort(List(alice.pub,bob.pub)))
      val pointQ = keyaggctx.pointQ
        
      // the message we will musig2 sign and then build adaptor signatures for
      val msg = ByteVector32.fromValidHex("07"*32)

      // generate and exchange pubnonces
      val (alice_secnonce, alice_pnonce) = alice.musig2NonceGen(
        aggregateXOnlyPublicKey = pointQ.xonly,
        message = msg,
        nextRand32 = ByteVector32.fromValidHex("A0"*32)
      )

      val (bob_secnonce, bob_pnonce) = bob.musig2NonceGen(
        aggregateXOnlyPublicKey = pointQ.xonly,
        message = msg,
        nextRand32 = ByteVector32.fromValidHex("B0"*32)
      )

      // aggregate the public nonces
      val aggnonce = Musig2.nonceAgg(List(alice_pnonce,bob_pnonce))

      // create a signing context (Alice and Bob can each do independently)
      val ctx = Musig2.SessionCtx(
        aggNonce = aggnonce,
        numPubKeys = 2,
        pubKeys = Musig2.keySort(List(alice.pub,bob.pub)).map(_.value),
        numTweaks = 0,
        tweaks = List.empty,
        isXonlyTweak = List.empty,
        message = msg
      )

      // Now Alice generates a partial signature which is tweaked by
      // Bob's "publishing point" T
      // She does this by tweaking the aggnonce with the secret before signing.
      // The aggnonce is represented by two points (R1,R2), so we create a new
      // aggnonce (R1+T, R2)
      /*val tweakedAggNonce = aggnonce.splitAt(33) match {
        case (bytesR1,bytesR2) => 
          (PublicKey(bytesR1) + bob.publishingPubKey(0)).value ++ bytesR2
      }

      val tweakedCtx = ctx.copy(aggNonce = tweakedAggNonce)

      println(ctx.sessionValues.b.toString(16))
      println(tweakedCtx.sessionValues.b.toString(16))*/
      val (alice_psig,b_alice,e_alice,pointR_alice) = Musig2.signWithAdaptorPoint(
        secnonce = alice_secnonce,
        privateKey = alice.priv,
        ctx = ctx,
        adaptorPoint = bob.publishingPubKey(0)
      )

      // Bob creates the adapter signature
      val (bob_psig,b_bob,e_bob,pointR_bob) = Musig2.signWithAdaptorPoint(
        secnonce = bob_secnonce,
        privateKey = bob.priv,
        ctx = ctx,
        adaptorPoint = bob.publishingPubKey(0)
      )
      assert(b_alice == b_bob)
      assert(e_alice == e_bob)
      assert(pointR_alice == pointR_bob)
      // Alice can/should verify Bob's adapter signature before sending her
      // partial signature:
      val e = Musig2.intModN(
        Crypto.calculateBip340challenge(
          data = ctx.message,
          noncePointR = (bob.publishingPubKey(0) + pointR_alice).xonly,
          publicKey = pointQ.xonly
        )
      )
      assert(e == e_alice)
      
      val g = if(pointQ.isEven) BigInt(1) else BigInt(-1).mod(N)
      val tacc = keyaggctx.accumulatedTweak
      val s = (Musig2.int(alice_psig)+Musig2.int(bob_psig) + (e*g*tacc).mod(N)).mod(N)
      assert(
        (G*PrivateKey(s))
        ==
        (pointR_alice + pointQ*PrivateKey(e))
      )
    }
    
    test("musig2 with taproot - offchain non-interactive utxo cycles") {
      // 
      // GOAL: Non-interactive transfer of entire utxo from Alice to Bob and back to Alice
      //       1. Alice and Bob fund a 2-of-2 musig pay2tr keypath-only output
      //       2. the utxo is initially owned by Alice ... time passes ...
      //       3. Alice transfers utxo to Bob ... time passes ...
      //       4. Bob tansfers back to Alice, thereby completing a "cycle."
      //       5. Complete N cycles.
      // 
      // We require that while Bob is the owner of the utxo, that if Alice tries
      // to withdraw it, he will be able (has time) to punish her and withdraw it
      // to himself.
      // 
      // We require that after initial setup, no further coordination need to be
      // done by Alice and Bob.
      //
      // How?
      // Make a lightning-like non-interactive unified channel!
      // See "unified" channels - https://suredbits.com/generalized-bitcoin-channels/
      //      also known as "generalized" channels - https://eprint.iacr.org/2020/476.pdf
      // See also "Pathcoin" - https://gist.github.com/AdamISZ/b462838cbc8cc06aae0c15610502e4da

      // Create our people (see definition of `Person` class above)
      val alice = Person("alice")
      val bob = Person("bob")

      // Calculate the aggregate public key (pointQ) in a KeyAggCtx
      // keyaggctx.pointQ is the aggregate public key
      val keyaggctx = Musig2.keyAgg(List(alice.pub, bob.pub))
      val pointQ = keyaggctx.pointQ

      // Construct the output public key for the taproot output
      val outputXOnlyPubKey = pointQ.xonly.outputKey(merkleRoot = None)

      // Fund a pay2tr output locked to the aggregated output key
      val fundingTx = Transaction(
        version = 2,
        txIn = List(
          TxIn.coinbase(OP_1 :: OP_1 :: Nil) // bogus coinbase
        ),
        txOut = List(
          TxOut(
            amount = Satoshi(1_000_000L),
            publicKeyScript = Script.pay2tr(outputXOnlyPubKey)
          )
        ),
        lockTime = 0L
      )
      // Make a note of the output index and amount for the funding transaction.
      val fundingVout = 0
      val fundingAmount = fundingTx.txOut(fundingVout).amount

      // Remember the OutPoint (needed by commitment transactions)
      val fundingOutPoint = OutPoint(fundingTx,fundingVout)

      /** Calculate the i'th commitment transaction. 
       * 
       * Generally, each commitment transaction revokes the prior commitment 
       * transaction and spends the funding output into a third transaction,
       * the "state" transaction. The state transaction splits the balance
       * accordingly.
       * 
       * However, in our specialized case of entire-utxo-transfer, there is no
       * need to further split the balance. Or, in other words, from a given
       * commitment transaction we can easily calculate the state. This property
       * is what allows our scheme to be non-interactive.
       * 
       * What we need the signed/broadcasted commitment transaction to do is
       * include information as to who broadcast it so that the non-broadcasting
       * partner can punish, if necessary.
       * 
       * Our commitment transaction has a single output, and a script with three
       * branches. Of course all of these branches could be encoded in a single
       * script, but here we are also trying to demonstrate taproot/tapscript, so
       * we instead encode the script branches as tapleafs, construct the merkle
       * root, and the pay2tr output (optionally, with keypath spending disabled). 
       * 
       * Technically, keypath spending neednot be disabled since even after 
       * the commitment transaction has been broadcast, the two parties could 
       * still choose to cooperate to close the channel without revealing the 
       * tapscripts.
       * */
      def unsignedCommitTx(
            i: Int // the i'th commitment transaction to calculate
        ): Transaction = {
          // specify the script branches:
          //
          // Alice can punish (spend immediately) if she know's both:
          //  `r_i`, the revocation secret corresponding to Alice's i'th
          //         blinded revocation pubkey which further corresponds with
          //         Bob's i'th per-commitment Point.
          //  `y_i`, the publishing secret corresponding to Bob's i'th 
          //         publishing public key
          //  `d_a`, her own private key.
          //
          // Here we only need to know the points and construct a script branch
          // representing a spending condition requiring a musig2 signature for
          // the aggregate key of all three of the above points.
          val Musig2.KeyAggCtx(aliceAggPubKey,_,_) = Musig2.keyAgg(
            List(
              alice.pub, 
              alice.revocationPubKey(bob.perCommitPoint(i)),
              bob.publishingPubKey(i)
            )
          )
          val alicePunishes = OP_PUSHDATA(aliceAggPubKey.xonly) :: OP_CHECKSIG :: Nil
          
          // Repeat, but for Bob.
          val Musig2.KeyAggCtx(bobAggPubKey,_,_) = Musig2.keyAgg(
            List(
              bob.pub, 
              bob.revocationPubKey(alice.perCommitPoint(i)),
              alice.publishingPubKey(i)
            )
          )
          val bobPunishes = OP_PUSHDATA(bobAggPubKey.xonly) :: OP_CHECKSIG :: Nil

          // The third branch of the commitTx is is the one which is spendable
          // by the "state transaction." The state transaction is what allocates
          // the sats to whatever set of outputs was agreed upon by the parties
          // (the state of the channel). We call this branch the "delayThenPay"
          // branch. Here we choose a delay of approximately 3 months (in blocks).
          val timeoutNumBlocks = 144*30*3.toLong
          val delayThenPay = OP_PUSHDATA(Script.encodeNumber(timeoutNumBlocks))
                            :: OP_CHECKSEQUENCEVERIFY :: OP_DROP
                            // now push the Alice & Bob aggregate pubkey (pointQ)
                            :: OP_PUSHDATA(pointQ.xonly) :: OP_CHECKSIG :: Nil

          val scripts = List(alicePunishes, bobPunishes, delayThenPay)
          val leaves = scripts.zipWithIndex.map { case (script, idx) =>
              ScriptLeaf(idx, Script.write(script), Script.TAPROOT_LEAF_TAPSCRIPT)
          }
          val scriptTree = ScriptTree.naiveFromList(leaves)
          val merkleRoot = scriptTree.hash
          val outputScript = Script.pay2tr(pointQ.xonly.outputKey(merkleRoot = Some(merkleRoot)))

          Transaction(
            version = 2,
            txIn = List(
                TxIn(
                  outPoint = fundingOutPoint, 
                  signatureScript = ByteVector.empty, 
                  sequence = TxIn.SEQUENCE_FINAL, 
                  witness = ScriptWitness.empty
                )
            ),
            txOut = List(TxOut(fundingAmount,outputScript)),
            lockTime = 0L
          )
      }

      // Now we need to create our "state transactions," which spend the commitment
      // transactions. A state transaction spends the "delayThenPay" path of a
      // commitment transaction and then allocates the sats accordingly. 
      
      // In our case the allocation made by the state transaction is trivial:
      // State 0: all goes to Alice
      // State 1: all goes to Bob
      // State 2: all goes to Alice
      // State i if i is even: all goes to Alice
      // State i if i is odd: all goes to Bob
      def unsignedStateTx(i: Int, commitTxVout: Int = 0): Transaction = {
        val commitTxOutPoint = OutPoint(unsignedCommitTx(i),commitTxVout)
        val payeePubKey = if(i % 2 == 0) alice.pub else bob.pub
        Transaction(
          version = 2,
          txIn = Seq(TxIn(
            outPoint = commitTxOutPoint,
            signatureScript = ByteVector.empty,
            sequence = (144*30*3).toLong, // approximately 3 months (in blocks)
            witness = ScriptWitness.empty
            )),
          txOut = Seq(TxOut(
            amount = fundingAmount,
            publicKeyScript = Script.pay2tr(payeePubKey.xonly.outputKey(merkleRoot = None))
          )),
          lockTime = 0L
        )
      }

      // With the above functions in place, we can calculate N commitment 
      // transactions and corresponding state transactions.
      // for N = 10
      val unsignedTxs = (0 until 10).map(i => (unsignedCommitTx(i) -> unsignedStateTx(i)))
      //unsignedTxs.foreach(println(_))

      // Because our state transactions are pre-determined and simply alternate,
      // we can sign and exchange all of them during setup.

      // Next we need to calculate the adapter signaatures for the commitment
      // transactions. For Alice to transfer the utxo to Bob non-interactively, 
      // at step `i`, she will need to furnish Bob with:
      //    - an an adapter signature for the commitment transaction,
      //    - and her per-commitment secret
      //
      // Both of these items can be computed at setup.

      // The adapter signature is approximately 96 bytes, and the per-commitment
      // secret is 32-bytes. So the total per-transfer overhead is around 128 bytes.

      // If she ever broadcasts a commitment transaction for which she has previously
      // furnished Bob with a (valid) adapter signature, Bob will have time to
      // punish her and transfer the funds.
    }
  }
}