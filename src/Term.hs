{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Term (
    Err,
    Formula(..),
    Name,
    Signature(..),
    Term(..),
    typeOf,
    typeCheck,
    typeFormula,
    vars,
    varNotIn
    )
    where

import Data.List(intercalate)
import qualified Data.Set as Set

class (Eq s, Show s, Eq f, Show f) => Signature s f | f -> s where
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

vars :: (Signature s f) => Term s f -> Set.Set Name
vars t = vars' t Set.empty
    where 
        vars' (Var k _) s = Set.insert k s
        vars' (FunApp f l) s = foldl Set.union Set.empty $ map vars l

varNotIn :: (Signature s f) => Term s f -> Name
varNotIn t = let names = vars t in
    getName "vvvvvv" names where
        getName s names | Set.member s names = getName ('v':s) names
            | otherwise = s    

typeOf :: (Signature s f) => Term s f -> s
typeOf (Var _ s) = s
typeOf (FunApp f _) = cod f

type Err = String

typeCheck :: (Signature s f) => Term s f -> Either Err s
typeCheck (Var _ s) = Right s
typeCheck x@(FunApp f lst) = do
    sequence (map typeCheck lst)
    let types = map typeOf lst
    if dom f == types
        then Right $ typeOf x
        else Left $ "Domain of " ++ show f ++ " is not " ++ show types ++ " in " ++ show lst

typeFormula :: (Signature s f) => Formula s f -> Either Err s
typeFormula (a :== b) = do 
    x <- typeCheck a
    y <- typeCheck b
    if typeOf a == typeOf b
        then Right x
        else Left $ "Type mismatch: " ++ show a ++ " and " ++ show b

