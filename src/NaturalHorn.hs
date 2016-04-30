{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators, GADTs #-}


module NaturalHorn (
    Rule(..),
    Theory(..),
    Sequent,
    leftS,
    rightS,
    defFun,
    createSeq,
    proof,
    )
    where

import Control.Monad(foldM)
import Data.List(tail, init)
import LaCarte
import qualified Data.Map as Map
import qualified Data.Set as Set

import Term

data Sequent s f = Seq { varNs :: VarNames s,
            leftS :: [Formula s f],
            rightS :: Formula s f}
    deriving (Eq)

type ErrSec s f = Either Err (Sequent s f)

defFun :: Signature s f => Term s f -> Formula s f
defFun b = b :== b

instance (Signature s f) => Show (Sequent s f) where
    show seq = show (leftS seq) ++ " |- " ++ show (varNs seq) ++ " -- " ++ show (rightS seq)

createSeq :: Signature s f => [Formula s f] -> Formula s f -> ErrSec s f
createSeq left right = do
    let lst1 = map varsCheckF left
    let lst2 = varsCheckF right
    let memp = Map.empty
    checked <- foldM combine memp (lst2:lst1)
    let seqt = Seq checked left right
    typeCheckSeq seqt
    return seqt


varsSequent :: Signature s f => Sequent s f -> VarNames s
varsSequent seq = Map.union (thing (leftS seq)) $ thing $ [rightS seq]
    where thing st = foldl (\a b -> Map.union a (varsFormula b)) Map.empty st

-- Checks that the vars are of the same sort everywhere they are mentioned
varsCheckS :: Signature s f => Sequent s f -> Either Err (VarNames s)
varsCheckS seqt = do
    let lst1 = map varsCheckF $ leftS seqt
    let lst2 = varsCheckF $ rightS seqt
    let memp = Map.empty
    checked <- foldM combine memp (lst2:lst1)
    if (Map.difference checked $ varNs seqt) == emptyVNS
        then return checked
        else Left "Not enough variables in context"

typeCheckSeq :: Signature s f => Sequent s f -> Either Err ()
typeCheckSeq seqt = do
    let lst1 = map typeCheckFormula $ leftS seqt
    let lst2 = map typeCheckFormula $ [rightS seqt]
    sequence_ (lst1 ++ lst2)
                 

class (Show (a s f), Signature s f) => Theory a s f | a -> s f, s f -> a where 
    axiom :: a s f -> ErrSec s f


data Rule a s f ala
        = Axiom (a s f)
        ----------------------------------------------------
        | User (Expr ala)
        ----------------------------------------------------
        | Refl [Formula s f] (VarNames s)   --                    |- x = x
        | Sym (Rule a s f ala)              --            a :== b |- b :== a
        | Select Int [Formula s f]          --        phi and psi |- phi
        | Leib (Formula s f) Name (Rule a s f ala) (Rule a s f ala)  -- x = y and phi[x/z] |- phi[y/z]
        | Strict Int (Rule a s f ala)          --    F(t_1) = F(t_1) |- t_1 = t_1
        -- Due to definition give variables in sorted order
        | SubstAx (a s f) [Rule a s f ala] [Term s f] --   axiom plus subst
-----------------------------------------------------------------

data Empty r
type IniRules a s f = Rule a s f Empty

-----------------------------------------------------------------

checkListLength n lst 
    | n < 1 = Left $ "Index is less than 1"
    | length lst >= n = Right ()
    | otherwise = Left $ "Index is bigger than a list"

proof :: (Theory a s f{-, UserRules t s f-}) => IniRules a s f -> ErrSec s f
-- This is user defined so checks the correctness of that
proof (Axiom s) = do
    a <- axiom s
    typeCheckSeq a
    varsCheckS a
    return a

--proof (User t) = do 
--    a <- fmap def t
--    typeCheckSeq a
--    varsCheckS a
--    return a    
-------------------------------------------------

proof (Sym rl) = do
    (Seq vs x (a :== b)) <- proof rl
    return $ Seq vs x (b :== a)

proof (Select n flas) = do
    checkListLength n flas
    createSeq flas (flas !! (n-1))

----------------------------------------------------------------------

proof (Refl left vm) 
  | vm == emptyVNS = Left "Can't apply Refl to empty set of vars"
  | otherwise = 
    let (nel, sel) = Map.elemAt 0 vm
        v = Var nel sel in
            createSeq left $ v :== v

proof (Leib (tL :== tR) v pIn pProof) = do
    (Seq vs cont1 (t1 :== t2)) <- proof pIn
    check <- proof pProof
    let s1 = typeOf t1
    let s2 = typeOf t2
    substL <- subst tL v s1 t1
    substR <- subst tR v s1 t1    
    check2 <- createSeq cont1 (substL :== substR)

    retL <- subst tL v s2 t2
    retR <- subst tR v s2 t2
    if check == check2
        then createSeq cont1 (retL :== retR)
        else Left "Incorrect substitution for Left side"

proof (Strict n pr) = do
    (Seq vs cont1 (t1 :== t2)) <- proof pr
    (FunApp f ts) <- check t1 t2
    checkListLength n ts
    let term = ts !! (n-1)
    createSeq cont1 (term :== term)
        where check f1@(FunApp _ _) f2@(FunApp _ _) | f1 == f2 = Right f1
                    | otherwise = Left $ "Not a fundef in Strict"
              check _ _ = Left $ "Not a fundef in Strict"

proof (SubstAx ax proofs terms) = do
    axiP@(Seq vsSeq leftAx rightAx) <- proof (Axiom ax)
    -- Get all proofs
    proofLst <- mapM proof proofs

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
    if leftAx == [] then createSeq ctx rightAx
        else do 
            (Seq llVars _ _) <- createSeq leftAx $ leftAx!!0
            -------------- Clutter 
            let mangled_r = Set.fromList $ map fst $ Map.toList llVars
            let m_llVars = mangleVars mangled_r llVars
            let vsSeq'' = mangleVars mangled_r vsSeq
            ------------------------
            let namesAndtermsAndTypes2 = filter (\(n,s,t) -> Map.member n m_llVars) namesAndtermsAndTypes
            res <- foldM (substHelper vsSeq'') (mangleFla mangled_r rightAx) namesAndtermsAndTypes2
            createSeq ctx res

    where
        leftCheck lsAx lsSeq  = if lsAx == lsSeq then return () else Left $ "Precondition doesn't match subst into axiom: \n"
            ++ show lsAx ++ "\n" ++ show lsSeq
        contCheck [] = return []
        contCheck ctxs = foldM (\a b -> if a == b then return b else Left $ "Contexts differ") (ctxs !! 0) ctxs

    
mangle :: Set.Set Name -> Name -> Name
mangle st v | Set.member v st = "'''" ++ v ++ "'''"
         | otherwise = v

mangleFla :: Signature s f => Set.Set Name -> Formula s f -> Formula s f
mangleFla st (a :== b) = mangleTerm st a :== mangleTerm st b

mangleTerm :: Signature s f => Set.Set Name -> Term s f -> Term s f
mangleTerm st v@(Var n s) = Var (mangle st n) s
mangleTerm st (FunApp f lst) = FunApp f $ map (mangleTerm st) lst

mangleVars :: Signature s f => Set.Set Name -> VarNames s -> VarNames s
mangleVars st vsSeq = Map.fromList $ map (\(a,b) -> (mangle st a, b)) (Map.toList vsSeq)

substHelper :: Signature s f => VarNames s -> Formula s f -> (Name, s, Term s f) -> Either Err (Formula s f)
substHelper vsSeq fla (nam, sortTerm, term) =  do
    let vsT = varsTerm term
    allVs <- combine vsT (Right vsSeq) -- to check compatibility
    substIntoF nam sortTerm term fla
    
    
                    