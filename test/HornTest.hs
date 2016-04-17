{-# LANGUAGE MultiParamTypeClasses #-}

module HornTest where

--import Test.HUnit

import Horn
import Term

data Sort = L
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

instance HTheory Axioms Sort Fun where
    axiom AndAssoc = createSeq [] [(var "x" *. var "y") *. var "z" :== var "x" *. (var "y" *. var "z")]
    axiom OrAssoc = createSeq [] [(var "x" +. var "y") +. var "z" :== var "x" +. (var "y" +. var "z")]
    axiom AndComm = createSeq [] [var "x" *. var "y" :== var "y" *. var "x"]
    axiom OrComm = createSeq [] [var "x" +. var "y" :== var "y" +. var "x"]
    axiom AndAbsorb = createSeq [] [var "x" *. (var "x" +. var "y") :== var "x"]
    axiom OrAbsorb = createSeq [] [var "x" +. (var "x" *. var "y") :== var "x"]

zero = HRefl $ fromListVNS [("x", L)]


-- x +. (x *. (x +. x)) = x
one = EAndL [var "x" *. (var "x" +. var "y") :== var "x", var "x" +. (var "x" *. var "y") :== var "x"]
one' = Subst one "y" (var "x" +. var "x")

two = IAnd (Axiom AndAbsorb) (Axiom OrAbsorb)
--two' = 

three = Comp two one'
-- var "x" +. var "x" == var "x" +. (var "x" *. (var "x" +. var "x"))
--two


-- Я не понимаю смысла польз аксиом



data Sort2 = D | F | G
    deriving (Show, Eq)
    
data Fun2 = M | P | One | Zero | INV 
    deriving (Show, Eq)

instance Signature Sort2 Fun2 where
    dom M = [D, D]
    dom P = [D, D]
    dom One = []
    dom Zero = []
    dom INV = [D]

    cod _ = D

vs = fromListVNS [("x", D), ("y", D)]

fmla2 = [Var "x" D :== Var "y" D, Var "x" F :== Var "y" D]
fmla1 = [Var "x" D :== Var "y" D, Var "x" D :== Var "y" D]
