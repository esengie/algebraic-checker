{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module NHorn.NaturalHorn (
    Rule(..),
    Proof(..),
    proof,
    refl,
    sym,
    select,
    strict,
    leib,
    proofAx,
    ) where

import Control.Monad(foldM)

import qualified Data.Map as Map
import qualified Data.Set as Set

import NHorn.Sequent
import NHorn.LaCarte
import Term

data Rule a s f ala
         = Refl [Formula s f] (VarNames s)   --                    |- x = x
         | Sym ala              --            a :== b |- b :== a
         | Select Int [Formula s f]          --        phi and psi |- phi
         | Leib (Formula s f) Name ala ala  -- x = y and phi[x/z] |- phi[y/z]
         | Strict Int ala          --    F(t_1) = F(t_1) |- t_1 = t_1
        -- Due to definition give variables in sorted order
         | ProofAx (a s f) [ala] [Term s f] --   axiom plus subst

instance (Theory a s f) => Functor (Rule a s f) where
    fmap f (Refl flas vm) = Refl flas vm
    fmap f (Sym a) = Sym (f a)
    fmap f (Select m lst) = Select m lst
    fmap f (Leib fs n x y) = Leib fs n (f x) (f y)
    fmap f (Strict m x) = Strict m (f x)
    fmap f (ProofAx ax lst tlst) = ProofAx ax (map f lst) tlst

-----------------------------------------------------------------------------

class (Theory a s f, Functor (f2 a s f)) => Proof f2 a s f where
    proofA :: f2 a s f (ErrSec s f) -> ErrSec s f

instance (Proof f2 a s f, Proof g a s f) => Proof (f2 :+: g) a s f where
    proofA (Inl f) = proofA f
    proofA (Inr g) = proofA g

proof :: (Proof f2 a s f) => Expr (f2 a s f) -> ErrSec s f
proof = foldExpr proofA

instance (Theory a s f) => Proof Rule a s f where
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

    proofA (Leib (tL :== tR) v pIn pProof) = do
        (Seq vs cont1 (t1 :== t2)) <- pIn
        check <- pProof
        let s1 = typeOf t1
        let s2 = typeOf t2
        substL <- subst tL v s1 t1
        substR <- subst tR v s1 t1
        check2 <- createSeq cont1 (substL :== substR)

        retL <- subst tL v s2 t2
        retR <- subst tR v s2 t2
        if check == check2
            then createSeq cont1 (retL :== retR)
            else Left $ "Incorrect substitution for Left side, need " ++ show check ++ " but have " ++ show check2

    proofA (ProofAx ax proofs terms) = do
        ax' <- axiom ax
        typeCheckSeq ax'
        varsCheckS ax'

        axiP@(Seq vsSeq leftAx rightAx) <- (Right ax')
        -- Get all proofs
        proofLst <- sequence proofs

        -- typeCheck terms
        sortTerms <- mapM typeCheckTerm terms

        -- rename all the stuff in axioms to impose independency of substitution
        let mangled_l = Set.fromList $ map fst $ Map.toList vsSeq
        let leftAx' = map (mangleFla mangled_l) leftAx
        let vsSeq' = mangleVars mangled_l vsSeq

        -- subst into axiom and check equality
        let namesAndtermsAndTypes = zip3 (map fst $ Map.toList vsSeq') sortTerms terms
        leftSide <- mapM (\x -> foldM (substHelper vsSeq') x namesAndtermsAndTypes) leftAx'
        leftCheck leftSide (map rightS proofLst)

        -- check contexts equality
        ctx <- contCheck $ map leftS proofLst

        -- subst into vars to the left of |- in an axiom
        -- this if is a semihack to use createSeq
        if null leftAx then createSeq ctx rightAx
            else do
                (Seq llVars _ _) <- createSeq leftAx $ head leftAx
                -------------- Clutter
                let mangled_r = Set.fromList $ map fst $ Map.toList llVars
                let m_llVars = mangleVars mangled_r llVars
                let vsSeq'' = mangleVars mangled_r vsSeq
                ------------------------
                let namesAndtermsAndTypes2 = filter (\(n,s,t) -> Map.member n m_llVars) namesAndtermsAndTypes
                res <- foldM (substHelper vsSeq'') (mangleFla mangled_r rightAx) namesAndtermsAndTypes2
                createSeq ctx res

        where
            leftCheck lsAx lsSeq = if lsAx == lsSeq then return () else Left $ "Precondition doesn't match subst into axiom: \n"
                ++ show lsAx ++ "\n" ++ show lsSeq
            contCheck [] = return []
            contCheck ctxs = foldM (\a b -> if a == b then return b else Left $ "Contexts differ") (head ctxs) ctxs


checkListLength n lst
    | n < 1 = Left $ "Index is less than 1"
    | length lst >= n = Right ()
    | otherwise = Left $ "Index is bigger than a list"

substHelper :: Signature s f => VarNames s -> Formula s f -> (Name, s, Term s f) -> Either Err (Formula s f)
substHelper vsSeq fla (nam, sortTerm, term) =  do
    let vsT = varsTerm term
    allVs <- combine vsT (Right vsSeq) -- to check compatibility
    substIntoF nam sortTerm term fla

------------------------------------------------------------------------------


-- Constructors
refl :: (Rule :<: e) a s f => [Formula s f] -> VarNames s -> Expr (e a s f)
refl flas vs = In $ inj $ Refl flas vs

sym :: (Rule :<: e) a s f => Expr (e a s f) -> Expr (e a s f)
sym x = In $ inj $ Sym x

select :: (Rule :<: e) a s f => Int -> [Formula s f] -> Expr (e a s f)
select n flas = In $ inj $ Select n flas

strict :: (Rule :<: e) a s f => Int -> Expr (e a s f) -> Expr (e a s f)
strict n x = In $ inj $ Strict n x

leib :: (Rule :<: e) a s f => Formula s f -> Name -> Expr (e a s f) -> Expr (e a s f) -> Expr (e a s f)
leib fla nam a b = In $ inj $ Leib fla nam a b

proofAx :: (Rule :<: e) a s f => a s f -> [Expr (e a s f)] -> [Term s f] -> Expr (e a s f)
proofAx ax proofs terms = In $ inj $ ProofAx ax proofs terms
