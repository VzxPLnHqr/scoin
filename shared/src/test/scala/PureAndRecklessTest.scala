package scoin

import utest._

object PureAndRecklessTest extends TestSuite {
    val tests = Tests {
        test("platform-independent Crypto") {
            import Crypto.{reckless => Crypto}
            require(Crypto.somethingReckless)
        }
    }
}