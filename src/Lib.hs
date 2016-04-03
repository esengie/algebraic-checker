module Lib
    where

import Data.List(intercalate, find, lookup)

data Sort = G | F
    deriving (Show, Eq)
data Fun = M | I 
    deriving (Show, Eq)

dom :: Fun -> [Sort]
dom M = [G, G]
dom I = []

cod::Fun -> Sort
cod _ = G

----------------------------------------------------
data Term = Var String Sort | FunApp Fun [Term] 
    deriving (Eq)

infix 4 :==
data Formula = Term :== Term
    deriving (Show, Eq)

instance Show Term where
    show (Var v _) = v
    show (FunApp f ts) = show f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

----------------------------------------------------

data Axiom = Assoc | El | Er

axiom :: Axiom -> Formula
axiom Assoc = FunApp M [FunApp M [Var "x" G, Var "y" G], Var "z" G] :==
     FunApp M [Var "x" G, FunApp M [Var "y" G, Var "z" G]]
axiom El = FunApp M [FunApp I [], Var "x" G] :== Var "x" G
axiom Er = FunApp M [Var "x" G, FunApp I []] :== Var "x" G

--------------------------------------------------

typeOf :: Term -> Sort 
typeOf (Var _ s) = s
typeOf (FunApp f _) = cod f


-- rewrite using Either for placement of errors
typeCheck :: Term -> Bool
typeCheck (Var _ s) = True
typeCheck (FunApp f lst) = (foldl (&&) True (map typeCheck lst)) && dom f == map typeOf lst

typeFormula :: Formula -> Bool
typeFormula (a :== b)    = typeCheck a && typeCheck b && typeOf a == typeOf b


----------------------------------
-- data Principles = Axiom Formula | Refl Term | Sym Principles | Trans Principles Principles 
--                | Congr Function [Principles] | App Principles String Term


someFunc :: IO ()
someFunc = putStrLn "someFunc"
