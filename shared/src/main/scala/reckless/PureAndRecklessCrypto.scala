package scoin.reckless

import scoin._

/**
  * Herein is a reckless-but-pure platform-independent implementation
  * of the crypto APIs we need
  */
trait PureAndRecklessCrypto extends Crypto {

    def somethingReckless: Boolean = true

}
