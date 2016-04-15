{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Horn where

import Data.List(tail, init)
import qualified Data.Map as Map

import Term

data Sequent s f = Seq { varNs :: VarNames s,
            leftS :: [Formula s f],
            rightS :: [Formula s f]}
    deriving (Show, Eq)

data HAxiom s f = Id (VarNames s) [Formula s f]
    | Top (VarNames s) [Formula s f]
    | EAndL (VarNames s) [Formula s f]
    | EAndR (VarNames s) [Formula s f]
    | HRefl (VarNames s) [Formula s f]
    | HLeib (VarNames s) [Formula s f]
    deriving (Show, Eq)

data HRule a s f = UAxiom (a s f)
        | RAxiom (HAxiom s f)
        | Comp (HRule a s f) (HRule a s f) 
        | IAnd (HRule a s f) (HRule a s f)
        | Subst (HRule a s f) Name (Term s f)
    deriving (Show)

hAxiom :: Signature s f => HAxiom s f -> Either Err (Sequent s f)
hAxiom (Id vs f) = Right $ Seq vs f f
hAxiom (Top vs f) = Right $ Seq vs f []

hAxiom (EAndL vs []) = Left "EAndL must have at least one formula to the left"
hAxiom (EAndL vs f) = Right $ Seq vs f $ tail f

hAxiom (EAndR vs []) = Left "EAndR must have at least one formula to the left"
hAxiom (EAndR vs f) = Right $ Seq vs f $ init f

hAxiom (HRefl vm f) 
  | vm == emptyVNS = Left "Can't apply HRefl to empty set of vars"
  | otherwise = 
    let (nel, sel) = Map.elemAt 0 vm
        v = Var nel sel in
            return $ Seq (Map.singleton nel sel) [] $ [v :== v]

hAxiom (HLeib vm []) = Left "Leib must have at least one formula to the left"
hAxiom (HLeib vm f@(x:xs)) = case isVarTypeFormula x of
    Left _ -> Left "Leib must have at least one formula to the left"
    Right (n, sr) -> do 
        a <- sequence $ map (substMapper n sr $ rightT x) xs
        return $ Seq vm f a
                 
substMapper :: Signature s f => Name -> s -> Term s f -> Formula s f -> Either Err (Formula s f)
substMapper name sort t (a :== b) = do 
    l <- (subst a name sort t)
    r <- (subst b name sort t)
    return $ l :== r

isVarTypeFormula :: Signature s f => Formula s f -> Either Err (Name, s)
isVarTypeFormula ((Var n sr) :== (Var _ _)) = Right (n,sr)
isVarTypeFormula _ = Left "Not Vars on the sides of formula"


class (Show (a s f), Signature s f) => HTheory a s f where 
    uAxiom :: a s f -> Either Err (Sequent s f)

proof :: HTheory a s f => HRule a s f -> Either Err (Sequent s f)
proof (UAxiom s) = uAxiom s
proof (RAxiom s) = hAxiom s

--- add varchecking
proof (Comp a b) = do
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    if lr == rl then return $ Seq (Map.union v1 v2) ll rr
        else Left $ "Congruence does't work " ++ show lr ++ " isn't the same as " ++ show rl

proof (IAnd a b) = do 
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    if ll == rl then return $ Seq (Map.union v1 v2) ll (lr ++ rr)
        else Left $ "IAnd does't work " ++ show ll ++ " isn't the same as " ++ show rl    

proof (Subst seq' nam term) = do
    (Seq vsSeq l r) <- proof seq'
    sortTerm <- typeCheck term
    let vsT = vars term
    let allVs = Map.union vsT vsSeq
    l' <- sequence $ map (substMapper nam sortTerm term) l
    r' <- sequence $ map (substMapper nam sortTerm term) r
    return $ Seq allVs l r



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

vs = fromListVNS [("x", D), ("y", D)]

fmla2 = [Var "x" D :== Var "y" D, Var "x" F :== Var "y" D]
fmla1 = [Var "x" D :== Var "y" D, Var "x" D :== Var "y" D]

-- res = (Seq {varNs = fromList [("x",D),("y",D)], left = [x = y,x = y], right = [y = y]})