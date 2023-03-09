package scoin.reckless

import scoin._
import scoin.Crypto._
import scodec.bits._

import utest._

object NonInteractiveCycleChannelsTest extends TestSuite {
  val tests = Tests {
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
    val outputXOnlyPubKey = pointQ.xonly

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
        val (outputKey, parity) = pointQ.xonly.tapTweak(merkleRoot = Some(merkleRoot))
        val outputScript = Script.pay2tr(outputKey)

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
          publicKeyScript = Script.pay2tr(payeePubKey.xonly)
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
