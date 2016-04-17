{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}

module Horn (
    HRule(..),
    HTheory(..),
    Sequent,
    createSeq,
    proof,
    --varsSequent,
    )
    where

import Control.Monad(foldM)
import Data.List(tail, init)
import LaCarte
import qualified Data.Map as Map

import Term

data Sequent s f = Seq { varNs :: VarNames s,
            leftS :: [Formula s f],
            rightS :: [Formula s f]}
    deriving (Show, Eq)

createSeq :: Signature s f => [Formula s f] -> [Formula s f] -> Either Err (Sequent s f)
createSeq left right = do
    let lst1 = map varsCheckF left
    let lst2 = map varsCheckF right
    let memp = Map.empty
    checked <- foldM combine memp (lst1 ++ lst2)
    let seqt = Seq checked left right
    typeCheckSeq seqt
    return seqt


varsSequent :: Signature s f => Sequent s f -> VarNames s
varsSequent seq = Map.union (thing (leftS seq)) $ thing $ rightS seq
    where thing st = foldl (\a b -> Map.union a (varsFormula b)) Map.empty st

-- Checks that the vars are of the same sort everywhere they are mentioned
varsCheckS :: Signature s f => Sequent s f -> Either Err (VarNames s)
varsCheckS seqt = do
    let lst1 = map varsCheckF $ leftS seqt
    let lst2 = map varsCheckF $ rightS seqt
    let memp = Map.empty
    checked <- foldM combine memp (lst1 ++ lst2)
    if (Map.difference checked $ varNs seqt) == emptyVNS
        then return checked
        else Left "Not enough variables in context"

typeCheckSeq :: Signature s f => Sequent s f -> Either Err ()
typeCheckSeq seqt = do
    let lst1 = map typeCheckFormula $ leftS seqt
    let lst2 = map typeCheckFormula $ rightS seqt
    sequence_ (lst1 ++ lst2)
                 
substIntoF :: Signature s f => Name -> s -> Term s f -> Formula s f -> Either Err (Formula s f)
substIntoF name sort t (a :== b) = do 
    l <- (subst a name sort t)
    r <- (subst b name sort t)
    return $ l :== r

class (Show (a s f), Signature s f) => HTheory a s f | a -> s f, s f -> a where 
    axiom :: a s f -> Either Err (Sequent s f)

data HRule a s f
        = Axiom (a s f)
        -- | User (ala (HRule a s f ala))
        | Id [Formula s f]     --           phi |- phi
        | Top [Formula s f]    --           phi |- Top
        | EAndL [Formula s f]  --   phi and psi |- phi
        | EAndR [Formula s f]  --   phi and psi |- psi
        | HRefl (VarNames s)   --               |- x = x
        | HLeib [Formula s f]  -- x = y and phi |- phi[y/x]
        | Comp (HRule a s f) (HRule a s f)
        | IAnd (HRule a s f) (HRule a s f)
        | Subst (HRule a s f) Name (Term s f)
    deriving (Show)
-----------------------------------------------------------------

--data Empty r
--type IniRules a s f = HRule a s f Empty

--data Sym r = Sym r
--data Trans r = Trans r r
--data Congr r = Congr r r r

--type ExtRules a s f = HRule a s f (Sym :+: Trans :+: Congr)

--class UserRules ala where
--    def :: ala (HRule a s f t) -> HRule a s f ala

-----------------------------------------------------------------

proof :: (HTheory a s f {-, UserRules t -}) => HRule a s f -> Either Err (Sequent s f)
-- This is user defined so checks the correctness of that
proof (Axiom s) = do
    a <- axiom s
    typeCheckSeq a
    varsCheckS a
    return a
-------------------------------------------------

proof (Id f) = createSeq f f

proof (Top f) = createSeq f []

proof (EAndL []) = Left "EAndL must have at least one formula to the left"
proof (EAndL f) = createSeq f $ tail f

proof (EAndR []) = Left "EAndR must have at least one formula to the left"
proof (EAndR f) = createSeq f $ init f

proof (HRefl vm) 
  | vm == emptyVNS = Left "Can't apply HRefl to empty set of vars"
  | otherwise = 
    let (nel, sel) = Map.elemAt 0 vm
        v = Var nel sel in
            createSeq [] $ [v :== v]

proof (HLeib []) = Left "Leib must have at least one formula to the left"
proof (HLeib f@(x:xs)) = case isVarEqualityFormula x of
    Left _ -> Left "Leib must have at least one Vars equality to the left"
    Right (n, sr) -> do
        a <- sequence $ map (substIntoF n sr $ rightT x) xs
        createSeq f a

    where isVarEqualityFormula ((Var n sr) :== (Var _ _)) = Right (n,sr)
          isVarEqualityFormula _ = Left "Not Vars on the sides of formula"

proof (Comp a b) = do
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    vmap <- combine v1 (Right v2)
    if lr == rl then return $ Seq vmap ll rr -- may add unneeded vars into context
        else Left $ "Composition doesn't work " ++ show lr ++ " isn't the same as " ++ show rl

proof (IAnd a b) = do 
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    vmap <- combine v1 (Right v2)
    if ll == rl then return $ Seq vmap ll (lr ++ rr)
        else Left $ "IAnd doesn't work " ++ show ll ++ " isn't the same as " ++ show rl    

proof (Subst seq' nam term) = do
    sq@(Seq vsSeq l r) <- proof seq'
    -- Just to check
    (Seq llVars _ _) <- createSeq l []
    check nam llVars sq
    -------------------
    sortTerm <- typeCheckTerm term
    let vsT = varsTerm term
    allVs <- combine vsT (Right vsSeq) -- to check compatibility
    l' <- sequence $ map (substIntoF nam sortTerm term) l
    r' <- sequence $ map (substIntoF nam sortTerm term) r
    return $ Seq allVs l' r'
        where check nam mp sq = if Map.member nam mp
                then Right ()
                else Left $ "Subst " ++ nam ++ " is not a free var on the left side of " 
                    ++ show sq












-- res = (Seq {varNs = fromList [("x",D),("y",D)], left = [x = y,x = y], right = [y = y]})