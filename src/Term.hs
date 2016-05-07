{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Term (
    Err,
    Formula(..),
    Name,
    Signature(..),
    Term(..),
    VarNames,
    combine,
    emptyVNS,
    fromListVNS,
    mangle,
    mangleFla,
    mangleTerm,
    mangleVars,
    subst,
    substIntoF,
    typeCheckTerm,
    typeCheckFormula,
    typeOf,
    varsCheckF,
    varsCheckT,
    varNotIn,
    varsFormula,
    varsTerm,
    )
    where

import           Control.Monad (foldM)
import           Data.List     (intercalate)
import qualified Data.Map      as Map
import qualified Data.Set      as Set

class (Eq s, Show s, Eq f, Show f) => Signature s f | f -> s, s -> f where
    dom :: f -> [s]
    cod :: f -> s

type Name = String

type VarNames s = Map.Map Name s

emptyVNS :: VarNames s
emptyVNS = Map.empty

fromListVNS :: [(Name, s)] -> VarNames s
fromListVNS = Map.fromList

data Term s f = Var Name s | FunApp f [Term s f]
    deriving (Eq)

instance (Show s, Show f) => Show (Term s f) where
    show (Var v _) = v
    show (FunApp f ts) = show f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

infix 4 :==
data Formula s f = (:==) { leftT  :: Term s f,
                           rightT :: Term s f}
    deriving (Eq)

instance (Show s, Show f) => Show (Formula s f) where
    show (t :== t') = show t ++ " = " ++ show t'

err :: Signature s f => Term s f -> Term s f -> Either Err s
err (Var n1 a) (Var _ b) | a == b = Right a
        | otherwise = Left $ "Same name, different sorts: " ++ show n1
            ++ " : " ++ show a ++ " and " ++ show b

varsCheckT :: Signature s f => Term s f -> Either Err (VarNames s)
varsCheckT t = vars' t Map.empty
    where
        vars' v@(Var k s) m = let mv = Map.lookup k m in
          case mv of
            Nothing -> Right $ Map.insert k s m
            Just v2 -> do
                _ <- err v (Var k v2)
                return m
        vars' (FunApp _ l) _ =  do
            let lst = map varsCheckT l
            let memp = Map.empty
            foldM combine memp lst

varsCheckF :: Signature s f => Formula s f -> Either Err (VarNames s)
varsCheckF (a :== b) = do
    l <- varsCheckT a
    combine l $ varsCheckT b


-- Combines two var sets, error if vars have one name but different sort
combine :: Signature s f => VarNames s -> Either Err (VarNames s) -> Either Err (VarNames s)
combine m1 b = do
    m2 <- b
    let left = Map.intersection m1 m2
    let right = Map.intersection m2 m1
    if left == right then return $ Map.union m1 m2
        else Left $ "Discrepancy " ++ Map.showTree
          (Map.intersectionWith (\a b-> show a ++ " and " ++ show b) left right)

varsTerm :: Signature s f => Term s f -> VarNames s
varsTerm t = vars' t Map.empty
    where
        vars' (Var k s) m = Map.insert k s m
        vars' (FunApp _ l) _ = foldl Map.union Map.empty $ map varsTerm l

varsFormula :: Signature s f => Formula s f -> VarNames s
varsFormula (a :== b) = Map.union (varsTerm a) (varsTerm b)

varNotIn :: Signature s f => Term s f -> Name
varNotIn t = let names = varsTerm t in
    getName "vvvvvv" names where
        getName s names | Map.member s names = getName ('v':s) names
                        | otherwise = s

typeOf :: Signature s f => Term s f -> s
typeOf (Var _ s) = s
typeOf (FunApp f _) = cod f

type Err = String

typeCheckTerm :: Signature s f => Term s f -> Either Err s
typeCheckTerm (Var _ s) = Right s
typeCheckTerm x@(FunApp f lst) = do
    mapM_ typeCheckTerm lst
    let types = map typeOf lst
    if dom f == types
        then Right $ typeOf x
        else Left $ "Domain of " ++ show f ++ " is not " ++ show types ++ " in " ++ show lst

typeCheckFormula :: Signature s f => Formula s f -> Either Err s
typeCheckFormula (a :== b) = do
    x <- typeCheckTerm a
    typeCheckTerm b
    if typeOf a == typeOf b
        then return x
        else Left $ "Type mismatch: " ++ show a ++ " and " ++ show b

subst :: Signature s f => Term s f -> Name -> s -> Term s f -> Either Err (Term s f)
subst v@(Var n s) vn vs t'
    | n == vn && s == vs = Right t'
    | n == vn && s /= vs = Left $ "Types of vars are different, can't substitute "
        ++ vn ++ ":" ++ show vs ++ " for " ++ n ++ ":" ++ show s
    | otherwise = Right v
subst (FunApp n ts) vn vs t' = do
    nts <- changeList ts vn vs t'
    Right (FunApp n nts)
        where
            changeList [] _ _ _ = Right []
            changeList (t : ts) vn vs t' = do
                nt <- subst t vn vs t'
                nts <- changeList ts vn vs t'
                Right (nt : nts)

substIntoF :: Signature s f => Name -> s -> Term s f -> Formula s f -> Either Err (Formula s f)
substIntoF name sort t (a :== b) = do
    l <- subst a name sort t
    r <- subst b name sort t
    return $ l :== r


mangle :: Set.Set Name -> Name -> Name
mangle st v | Set.member v st = "'''" ++ v ++ "'''"
         | otherwise = v

mangleFla :: Signature s f => Set.Set Name -> Formula s f -> Formula s f
mangleFla st (a :== b) = mangleTerm st a :== mangleTerm st b

mangleTerm :: Signature s f => Set.Set Name -> Term s f -> Term s f
mangleTerm st (Var n s) = Var (mangle st n) s
mangleTerm st (FunApp f lst) = FunApp f $ map (mangleTerm st) lst

mangleVars :: Signature s f => Set.Set Name -> VarNames s -> VarNames s
mangleVars st vsSeq = Map.fromList $ map (\(a,b) -> (mangle st a, b)) (Map.toList vsSeq)
