{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib
    where

import Data.List(intercalate)
import Control.Monad(sequence, mapM)

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


data Rules a s f = Axiom a | Refl (Term s f) | Sym (Rules a s f) 
            | Trans (Rules a s f) (Rules a s f)
            | Cong f [Rules a s f] | App (Rules a s f) Name (Term s f)

trans :: [Rules a s f] -> Rules a s f
trans [p] = p
trans (p:ps) = Trans p (trans ps)

class (Signature s f) => Proof a s f | a -> s f where 
    axiom :: a -> Formula s f
    proof :: Rules a s f -> Either Err (Formula s f)
    proof (Axiom f) = Right $ axiom f

    proof (Refl term) = do
        _ <- typeCheck term  
        Right $ term :== term

    proof (Sym pr) = do 
        (t1 :== t2) <- proof pr
        Right $ t2 :== t1

    proof (Trans p1 p2) = do
        (t1 :== t2) <- proof p1
        (t2' :== t3) <- proof p2
        if t2 == t2'
            then Right $ t1 :== t3
            else Left ""

    proof (Cong f ps) = do
        (ts1, ts2) <- buildFunction ps
        let t1 = FunApp f ts1
        let t2 = FunApp f ts2
        _ <- typeCheck t1
        _ <- typeCheck t2
        Right $ t1 :== t2
            where
                buildFunction [] = Right ([], [])
                buildFunction  (p : ps) = do
                    (t1 :== t2) <- proof p
                    (ts1, ts2) <- buildFunction ps
                    Right (t1 : ts1, t2 : ts2)
    
    proof (App p v t) = do
        s <- typeCheck t
        (t1 :== t2) <- proof p
        nt1 <- changeTerm t1 v s t
        nt2 <- changeTerm t2 v s t
        Right $ nt1 :== nt2
            where
                changeTerm v@(Var n s) vn vs t'
                    | n == vn && s == vs = Right t'
                    | n == vn && s /= vs = Left ""
                    | otherwise = Right v
                changeTerm (FunApp n ts) vn vs t' = do
                    nts <- changeList ts vn vs t'
                    Right (FunApp n nts)

                changeList [] _ _ _ = Right []
                changeList (t : ts) vn vs t' = do
                    nt <- changeTerm t vn vs t'
                    nts <- changeList ts vn vs t'
                    Right (nt : nts)
