import Test.HUnit
import AlgebraicTest
import TermTest
import HornTest

main = runTestTT $ TestList [algTest, tTest, hTest1, hTest2]