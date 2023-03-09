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

    // Create our people (see definition of `reckless.Person` -- it just provides
    // some convenient "wallet-like" methods for us for testing purposes)
    val alice = Person("alice")
    val bob = Person("bob")

    // Calculate the aggregate public key (pointQ) in a KeyAggCtx
    // keyaggctx.pointQ is the aggregate public key
    val keyaggctx = Musig2.keyAgg(List(alice.pub, bob.pub))
    val pointQ = keyaggctx.pointQ

    // Construct the output public key for the funding taproot output
    // This output will be spent via key-spend only (using musig2!), so there 
    // is no need to tweak it with a merkle root.
    val outputXOnlyPubKey = pointQ.xonly

    // Fund a pay2tr output locked to the aggregated output key
    val fundingTx = Transaction(
      version = 2,
      txIn = List.empty, // bogus coinbase
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

    // The below constant is used by the delay branch of all commitment transactions
    val timeoutNumBlocks = 144*30*3.toLong

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
     * partner can punish, if necessary. This information transmission is
     * accomplished with adaptor signatures, musig2 style.
     * 
     * Our commitment transaction has a single output, and a script with three
     * branches. Of course all of these branches could be encoded in a single
     * script, but here we are also trying to demonstrate taproot/tapscript, so
     * we instead encode the script branches as tapleafs, construct the merkle
     * root, and the pay2tr output (optionally, with keypath spending disabled). 
     * 
     * Technically, keypath spending need not be disabled because even after 
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
        //         blinded revocation pubkey. When Bob gives alice his
        //         i'th per-commitment secret, only Alice will be able to calculate
        //         the revocation secret `r_i`, as the calculation depends on her
        //         private key.
        // 
        //  `y_i`, the publishing secret corresponding to Bob's i'th 
        //         publishing public key
        //
        // Here we only need to know the points and construct a script branch
        // representing a spending condition requiring a musig2 signature for
        // the aggregate key of the above points.
        val Musig2.KeyAggCtx(aliceAggPubKey,_,_) = Musig2.keyAgg(
          List(
            alice.revocationPubKey(bob.perCommitPoint(i)),
            bob.publishingPubKey(i)
          )
        )
        val alicePunishes = OP_PUSHDATA(aliceAggPubKey.xonly) :: OP_CHECKSIG :: Nil

        // Repeat, but for Bob.
        val Musig2.KeyAggCtx(bobAggPubKey,_,_) = Musig2.keyAgg(
          List( 
            bob.revocationPubKey(alice.perCommitPoint(i)),
            alice.publishingPubKey(i)
          )
        )
        val bobPunishes = OP_PUSHDATA(bobAggPubKey.xonly) :: OP_CHECKSIG :: Nil

        // The third branch of the commitTx is is the one which is spendable
        // by the "state transaction." The state transaction is what allocates
        // the sats to whatever set of outputs was agreed upon by the parties
        // (the state of the channel). We call this branch the "delayThenPay"
        // branch.
        // 
        // Notice how this branch is locked to the same Alice+Bob aggregate
        // public key (pointQ).
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

    // Next we need to calculate the adapter signatures for the commitment
    // transactions. While the commitment transaction held by each party
    // is the same, for each commitment transaction, each party will 
    // have an adaptor signature where the addaptor point is chosen to be 
    // the other party's publishing point.
    //
    // Therefore, the party who publishes the commitment transaction is also
    // revealing its corresponding publishing secret.
    // 
    // The adaptor signatures can be exchanged and verified at setup time.
    // 
    // At setup time, each party will also calculate their per-commitment
    // secrets, and corresponding per-commitment points. They exchange the
    // per-commitment points, but keep the per-commitment secrets to themselves.
    // 
    // For Alice to transfer the utxo to Bob non-interactively, at step `i`, 
    // she will simply need to furnish Bob with her `i`th per-commitment secret.
    // This can be done via email, text message, file drop, or a plain old hand
    // written note.
    // 
    // Each per-commitment secret is just a 256-bit number, similar to a private
    // key. As such, encoding it as a BIP39 sequence of 12 or 24 words is an
    // interesting idea.
    //
    // While the transfer of the UTXO here is non-interactive, there is still a
    // requirement for the receiver:
    //         - to verify the per-commitment secret (can be done offline)
    //         - monitor the blockchain for broadcast of the old (now revoked)
    //           commitment transaction.
    // 
    // The adaptor signatures exchanged and verified at setup time ensure that
    // we know *who* published a given commitment transaction, and also furnishes
    // the non-publishing party with half of the information necessary to spend
    // the utxo immediately. The other half is provided by per-commitment secret.
    //
    // For example, say we are just starting out (state i = 0). The setup is 
    // complete, and the signed state transaction assigns the funds to Alice by
    // spendng the delay path of the 0th commitment transaction.
    // 
    // Alice can simply broadcast the commitment transaction, wait, then broadcast
    // the state transaction. She will the the ultimate beneficiary.
    //
    // Alternatively, Alice can provide Bob with her 0th per-commitment secret,
    // thereby assigning the utxo to Bob. Now, if she ever broadcasts the 0th
    // commitment transaction, Bob will learn her 0th publishing secret, and now
    // has all the information necessary to claim the utxo.

    // We are now in state i = 1. Bob owns the utxo. He can transfer it back to
    // Alice by providing her his per-commitment secret, thereby transitioning
    // to state i = 2.

    // The pattern continues until i = N, at which point the parties will need to
    // continue their setup process and generate more commitment and state transactions.
    
  }
}
