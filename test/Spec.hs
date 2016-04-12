import Test.HUnit
import AlgebraicTest
import TermTest

main = runTestTT $ TestList [algTest, tTest]