import Test.HUnit
--import AlgebraicTest
import TermTest
--import HornTest hiding (isLeft)
import NaturalCategory as N
import NaturalHorn as N

import Test.HUnit

isLeft (Left _) = True
isLeft (Right _) = False

catTest1 :: Test
catTest1 = TestCase $ assertBool "Leib" $ not.isLeft $ N.proof N.one

catTest2 :: Test
catTest2 = TestCase $ assertBool "Strict" $ not.isLeft $ N.proof N.two

catTest3 :: Test
catTest3 = TestCase $ assertBool "SubstAx" $ not.isLeft $ N.proof N.three

catTest4 :: Test
catTest4 = TestCase $ assertBool "Theorem id in cat theory" $ N.proof N.st2 == N.theorem2 "x"

main = runTestTT $ TestList [{-algTest,-} tTest, {-hTest1, hTest2,-} catTest1, catTest2, catTest3, catTest4]