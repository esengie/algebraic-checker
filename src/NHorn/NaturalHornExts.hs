{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module NHorn.NaturalHornExts (
    AxiomRule,
    Trans,
    axim,
    trans
    ) where

import Text.PrettyPrint.Leijen

import NHorn.LaCarte
import NHorn.Sequent
import NHorn.NaturalHorn
import NHorn.NaturalHornPretty
import Term

data Trans a s f ala = Trans ala ala

data AxiomRule a s f ala = AxiomRule (a s f)

instance (Theory a s f) => Functor (Trans a s f) where
    fmap f (Trans x y) = Trans (f x) (f y)

instance (Theory a s f) => Functor (AxiomRule a s f) where
    fmap f (AxiomRule a) = AxiomRule a

instance Theory a s f => Proof Trans a s f where
    proofA (Trans rl rr) = do
        (Seq vs1 x1 (a :== c1)) <- rl
        (Seq vs2 x2 (c2 :== b)) <- rr
        check x1 x2
        if c1 == c2 then createSeq x1 (a :== b)
            else Left $ "Trans doesn't apply " ++ show c1 ++ " and " ++ show c2
                where check x1 x2 | x1 == x2 = Right ()
                                  | otherwise = Left $ "Contexts in trans must be the same: " ++ show x1 ++ " and " ++ show x2

instance (Theory a s f) => Proof AxiomRule a s f where
    proofA (AxiomRule s) = do
        a <- axiom s
        typeCheckSeq a
        varsCheckS a
        return a

axim :: (AxiomRule :<: e) a s f => a s f -> Expr (e a s f)
axim ax = In $ inj $ AxiomRule ax

trans :: (Trans :<: e) a s f =>  Expr (e a s f) -> Expr (e a s f) -> Expr (e a s f)
trans a b = In $ inj $ Trans a b


instance Theory a s f => Prettier Trans a s f where
    pretty' (Trans l r) = text "trans" <> parens (pretty l <> comma <+> pretty r)

instance Theory a s f => Prettier AxiomRule a s f where
    pretty' (AxiomRule ax) = text $ name ax