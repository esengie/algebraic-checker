{-# LANGUAGE MultiParamTypeClasses #-}

module HornTest where

import Test.HUnit

import Horn
import Term

data Sort = L | Dr
    deriving (Show, Eq)
    
data Fun = And | Or
    deriving (Show, Eq)

instance Signature Sort Fun where
    dom And = [L, L]
    dom Or = [L, L]

    cod _ = L

data Axioms s f = AndComm | OrComm | AndAssoc | OrAssoc | AndAbsorb | OrAbsorb
    deriving (Show)

var x = Var x L
x *. y = FunApp And [x,y]
x +. y = FunApp Or [x,y]

instance Theory Axioms Sort Fun where
    axiom AndAssoc = createSeq [] [(var "x" *. var "y") *. var "z" :== var "x" *. (var "y" *. var "z")]
    axiom OrAssoc = createSeq [] [(var "x" +. var "y") +. var "z" :== var "x" +. (var "y" +. var "z")]
    axiom AndComm = createSeq [] [var "x" *. var "y" :== var "y" *. var "x"]
    axiom OrComm = createSeq [] [var "x" +. var "y" :== var "y" +. var "x"]
    axiom AndAbsorb = createSeq [] [var "x" *. (var "x" +. var "y") :== var "x"]
    axiom OrAbsorb = createSeq [] [var "x" +. (var "x" *. var "y") :== var "x"]

zero = Refl $ fromListVNS [("x", L)]


-- x +. (x *. (x +. x)) = x
one = EAndL [var "x" *. (var "x" +. var "y") :== var "x", var "x" +. (var "x" *. var "y") :== var "x"]
one' = Subst one "y" (var "x" +. var "x")

two = IAnd (Axiom AndAbsorb) (Axiom OrAbsorb)
--two' = 

three = Comp two one'
-- var "x" +. var "x" == var "x" +. (var "x" *. (var "x" +. var "x"))
--two
four = Congr [var "x":== Var "y" Dr, var "x" *. var "z" :== var "x" *. var "z"]

four' = Congr [var "x" *. var "y" :== Var "y" Dr, var "x" *. var "z" :== var "x" *. var "z"]

isLeft (Left _) = True
isLeft (Right _) = False

hTest1 = TestCase $ assertBool "H first" $ isLeft $ proof four
hTest2 = TestCase $ assertBool "H first" $ isLeft $ proof four'
