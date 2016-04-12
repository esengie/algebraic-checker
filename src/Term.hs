{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Term (
    Err,
    Formula(..),
    Name,
    Signature(..),
    Term(..),
    subst,
    typeOf,
    typeCheck,
    typeFormula,
    vars,
    varNotIn,
    varsCheck
    )
    where

import Control.Monad(foldM)
import Data.List(intercalate)
import qualified Data.Map as Map

class (Eq s, Show s, Eq f, Show f) => Signature s f | f -> s, s -> f where
    dom :: f -> [s]
    cod :: f -> s

type Name = String 

data Term s f = Var Name s | FunApp f [Term s f] 
    deriving (Eq)

instance (Show s, Show f) => Show (Term s f) where
    show (Var v _) = v
    show (FunApp f ts) = show f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

infix 4 :==
data Formula s f = Term s f :== Term s f
    deriving (Eq)

instance (Show s, Show f) => Show (Formula s f) where
    show (t :== t') = show t ++ " = " ++ show t'

err :: Signature s f => Term s f -> Term s f -> Either Err s
err (Var n1 a) (Var n2 b) | a == b = Right a
        | otherwise = Left $ "Same name, different sorts: " ++ show n1 
            ++ " : " ++ show a ++ " and " ++ show b

varsCheck :: Signature s f => Term s f -> Either Err (Map.Map Name s)
varsCheck t = vars' t Map.empty
    where 
        vars' v@(Var k s) m = let mv = Map.lookup k m in 
          case mv of 
            Nothing -> Right $ Map.insert k s m
            Just v2 -> do 
                _ <- err v (Var k v2)
                return m
        vars' (FunApp f l) s =  do
            let lst = map varsCheck l
            let memp = Map.empty
            foldM combine memp lst

combine :: Signature s f => (Map.Map Name s) -> Either Err (Map.Map Name s) -> Either Err (Map.Map Name s)
combine m1 b = do 
    m2 <- b
    let left = Map.intersection m1 m2
    let right = Map.intersection m2 m1
    if left == right then return $ Map.union m1 m2
        else Left $ "Discrepancy " ++ Map.showTree 
          (Map.intersectionWith (\a b-> show a ++ " and " ++ show b) left right)

vars :: Signature s f => Term s f -> Map.Map Name s
vars t = vars' t Map.empty
    where 
        vars' (Var k s) m = Map.insert k s m
        vars' (FunApp f l) s = foldl Map.union Map.empty $ map vars l

varNotIn :: Signature s f => Term s f -> Name
varNotIn t = let names = vars t in
    getName "vvvvvv" names where
        getName s names | Map.member s names = getName ('v':s) names
                        | otherwise = s    

typeOf :: Signature s f => Term s f -> s
typeOf (Var _ s) = s
typeOf (FunApp f _) = cod f

type Err = String

typeCheck :: Signature s f => Term s f -> Either Err s
typeCheck (Var _ s) = Right s
typeCheck x@(FunApp f lst) = do
    sequence (map typeCheck lst)
    let types = map typeOf lst
    if dom f == types
        then Right $ typeOf x
        else Left $ "Domain of " ++ show f ++ " is not " ++ show types ++ " in " ++ show lst

typeFormula :: Signature s f => Formula s f -> Either Err s
typeFormula (a :== b) = do 
    x <- typeCheck a
    y <- typeCheck b
    if typeOf a == typeOf b
        then Right x
        else Left $ "Type mismatch: " ++ show a ++ " and " ++ show b

subst :: Signature s f => Term s f -> Name -> s -> Term s f -> Either Err (Term s f)
subst v@(Var n s) vn vs t'
    | n == vn && s == vs = Right t'
    | n == vn && s /= vs = Left "Types of vars are different"
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


