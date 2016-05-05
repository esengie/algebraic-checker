
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
 {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE InstanceSigs #-}
 {-# LANGUAGE FlexibleInstances #-}
 {-# LANGUAGE FlexibleContexts #-}
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

--data family Rules r a s f ala

data Rule a s f ala = Axiom (a s f) -- not used
        ----------------------------------------------------
         | Refl [Formula s f] (VarNames s)   --                    |- x = x
         | Sym ala              --            a :== b |- b :== a
         | Select Int [Formula s f]          --        phi and psi |- phi
         | Leib (Formula s f) Name ala ala  -- x = y and phi[x/z] |- phi[y/z]
         | Strict Int ala          --    F(t_1) = F(t_1) |- t_1 = t_1
        -- Due to definition give variables in sorted order
         | SubstAx (a s f) [ala] [Term s f] --   axiom plus subst

data Trans a s f ala = Trans ala ala

data Struct a s f where 
    Ax :: a -> s -> f -> Struct a a a
    Srt :: a -> s -> f -> Struct s s s
    Fun :: a -> s -> f -> Struct f f f

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

class (Theory a s f, Functor (f2 a s f)) => Proof f2 a s f where
    proofA:: f2 a s f (ErrSec s f) -> ErrSec s f

instance (Theory a s f) => Proof Rule a s f where
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

instance Theory a s f => Proof Trans a s f where
    proofA (Trans rl rr) = do
        (Seq vs1 x1 (a :== c1)) <- rl
        (Seq vs2 x2 (c2 :== b)) <- rr
        check x1 x2
        if c1 == c2 then createSeq x1 (a :== b)
            else Left $ "Trans doesn't apply " ++ show c1 ++ " and " ++ show c2
                where check x1 x2 | x1 == x2 = Right ()
                                  | otherwise = Left $ "Contexts in trans must be the same: " ++ show x1 ++ " and " ++ show x2


instance (Proof f2 a s f, Proof g a s f) => Proof (f2 :+: g) a s f where
    proofA (Inl f) = proofA f
    proofA (Inr g) = proofA g

proof :: (Proof f2 a s f) => Expr (f2 a s f) -> ErrSec s f
proof expr = foldExpr proofA expr

axim :: (Rule :<: e) a s f => a s f -> Expr (e a s f)
axim ax = In $ inj $ Axiom ax

refl :: (Rule :<: e) a s f => [Formula s f] -> VarNames s -> Expr (e a s f)
refl flas vs = In $ inj $ Refl flas vs

sym :: (Rule :<: e) a s f => Expr (e a s f) -> Expr (e a s f)
sym x = In $ inj $ Sym x

select :: (Rule :<: e) a s f => Int -> [Formula s f] -> Expr (e a s f)
select n flas = In $ inj $ Select n flas

strict :: (Rule :<: e) a s f => Int -> Expr (e a s f) -> Expr (e a s f)
strict n x = In $ inj $ Strict n x

trans :: (Trans :<: e) a s f => Expr (e a s f) -> Expr (e a s f) -> Expr (e a s f)
trans a b = In $ inj $ Trans a b


        -- | Leib (Formula s f) Name ala ala  -- x = y and phi[x/z] |- phi[y/z]
