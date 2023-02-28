package scoin

import scala.scalajs.js
import scala.scalajs.js.annotation._
import scodec.bits._
import scala.scalajs.js.typedarray.Uint8Array

object ScoinJS {
  @JSExportTopLevel("Transaction")
  object TransactionJS {
    @JSExport
    def read(hex: String) = TransactionJS(Transaction.read(hex))
  }

  @JSExportAll
  class TransactionJS(tx: Transaction) {
    def version = tx.version.toInt
  }

  @JSExportTopLevel("Script")
  object ScriptJS {
    /**
      * 
      *
      * @param xOnlyPublicKey (as hex string)
      * @return a scriptPubKey for taproot (as hex string)
      */
    @JSExport
    def pay2tr(xOnlyPublicKey: String): String =
      Script.write(Script.pay2tr(Crypto.XOnlyPublicKey(ByteVector32.fromValidHex(xOnlyPublicKey)))).toHex
  }
}
