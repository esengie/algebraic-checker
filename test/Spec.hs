import Test.HUnit
import AlgebraicTest
import TermTest
import HornTest
import qualified NaturalCategory as NatCat
import qualified NaturalHorn as H

import Test.HUnit

catTest1 :: Test
catTest1 = TestCase $ assertBool "Leib" $ not.isLeft $ H.proof NatCat.one

catTest2 :: Test
catTest2 = TestCase $ assertBool "Strict" $ not.isLeft $ H.proof NatCat.two

catTest3 :: Test
catTest3 = TestCase $ assertBool "SubstAx" $ not.isLeft $ H.proof NatCat.three

main = runTestTT $ TestList [algTest, tTest, hTest1, hTest2, catTest1, catTest2, catTest3]