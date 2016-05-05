
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE InstanceSigs #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# LANGUAGE FunctionalDependencies #-}
-- {-# LANGUAGE KindSignatures #-}

module Nn where

import NaturalHorn hiding (Rule(..), proof)
import Control.Monad(foldM)
import Data.List(tail, init, intersperse)

import qualified Data.Map as Map
import qualified Data.Set as Set

import LaCarte
import Term

data family Rules r a s f ala

data Rule a s f ala
        = Axiom (a s f) -- not used
        ----------------------------------------------------
        | Refl [Formula s f] (VarNames s)   --                    |- x = x
        | Sym ala              --            a :== b |- b :== a
        | Select Int [Formula s f]          --        phi and psi |- phi
        | Leib (Formula s f) Name ala ala  -- x = y and phi[x/z] |- phi[y/z]
        | Strict Int ala          --    F(t_1) = F(t_1) |- t_1 = t_1
        -- Due to definition give variables in sorted order
        | SubstAx (a s f) [ala] [Term s f] --   axiom plus subst

data Trans a s f ala = Trans ala ala

instance (Theory a s f) => Functor (Rule a s f) where
    fmap f (Axiom a) = Axiom a
    fmap f (Refl flas vm) = Refl flas vm
    fmap f (Sym a) = Sym (f a)
    fmap f (Select m lst) = Select m lst
    fmap f (Leib fs n x y) = Leib fs n (f x) (f y)
    fmap f (Strict m x) = Strict m (f x)
    fmap f (SubstAx ax lst tlst) = SubstAx ax (map f lst) tlst

instance (Theory a s f) => Functor (Trans a s f) where
    fmap f (Trans x y) = Trans (f x) (f y)

class (Functor f2) => Proof f2 where
    type S f2
    type F f2
    proofA:: f2 (ErrSec (S f2) (F f2)) -> ErrSec (S f2) (F f2)

instance Theory a s f => Proof (Rule a s f) where
    type S(Rule a s f) = s
    type F(Rule a s f) = f
    proofA (Axiom s) = do
        a <- axiom s
        typeCheckSeq a
        varsCheckS a
        return a

    proofA (Sym rl) = do
        (Seq vs x (a :== b)) <- rl
        return $ Seq vs x (b :== a)

    proofA (Select n flas) = do
        checkListLength n flas
        createSeq flas (flas !! (n-1))

    proofA (Refl left vm) 
        | vm == emptyVNS = Left "Can't apply Refl to empty set of vars"
        | otherwise = 
          let (nel, sel) = Map.elemAt 0 vm
              v = Var nel sel in
                  createSeq left $ v :== v
    proofA (Strict n pr) = do
        (Seq vs cont1 (t1 :== t2)) <- pr
        (FunApp f ts) <- check t1 t2
        checkListLength n ts
        let term = ts !! (n-1)
        createSeq cont1 (term :== term)
            where check f1@(FunApp _ _) f2@(FunApp _ _) | f1 == f2 = Right f1
                        | otherwise = Left $ "Not a fundef in Strict"
                  check _ _ = Left $ "Not a fundef in Strict"

instance Theory a s f => Proof (Trans a s f) where
    type S (Trans a s f) = s
    type F (Trans a s f) = f
    proofA (Trans rl rr) = do
        (Seq vs1 x1 (a :== c1)) <- rl
        (Seq vs2 x2 (c2 :== b)) <- rr
        check x1 x2
        if c1 == c2 then createSeq x1 (a :== b)
            else Left $ "Trans doesn't apply " ++ show c1 ++ " and " ++ show c2
                where check x1 x2 | x1 == x2 = Right ()
                                  | otherwise = Left $ "Contexts in trans must be the same: " ++ show x1 ++ " and " ++ show x2


instance (Proof f2, Proof g, S f2 ~ S g, F f2 ~ F g) => Proof (f2 :+: g) where
    type S (f2 :+: g) = S f2
    type F (f2 :+: g) = F f2
    proofA (Inl f) = proofA f
    proofA (Inr g) = proofA g

proof :: (Proof f) => Expr f -> ErrSec (S f) (F f)
proof expr = foldExpr proofA expr

--axim :: ((Rule a s f) :<: e) => Expr e -> Expr e -> Expr e
--axim ax = In $ inj $ N.Axiom ax
