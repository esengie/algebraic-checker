{-# LANGUAGE MultiParamTypeClasses #-}

module TermTest where

import Control.Exception (ErrorCall(ErrorCall), evaluate)
import Test.HUnit
import Test.HUnit.Tools (assertRaises)

import Term

data Sort = D | F | G
    deriving (Show, Eq)
    
data Fun = M | P | One | Zero | INV 
    deriving (Show, Eq)

instance Signature Sort Fun where
    dom M = [D, D]
    dom P = [D, D]
    dom One = []
    dom Zero = []
    dom INV = [D]

    cod _ = D

x *. y = FunApp M [x,y]
x +. y = FunApp P [x,y]

msg = "Discrepancy \"x\":=\"D and F\"\n"

erroneous = (Var "x" D) *. (Var "x" F) *. (Var "x" G)

tTest :: Test
tTest = TestCase $ assertEqual "Wrong sorts" (Left msg) (varsCheck erroneous)
