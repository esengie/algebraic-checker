{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Algebraic (
    Rules(..),
    Theory(..),
    proof,
    trans,
    sym,
    )
    where

import Text.PrettyPrint

import Term

data Rules a s f = Axiom a | Refl (Term s f) | Sym (Rules a s f) 
            | Trans (Rules a s f) (Rules a s f)
            | Leib (Formula s f) Name (Rules a s f) (Rules a s f)
            | Cong f [Rules a s f] | App (Rules a s f) Name (Term s f)
    deriving (Show)

trans :: (Theory a s f) => [Rules a s f] -> Rules a s f
trans [p] = p
trans (p:ps) = Trans p (trans ps)

sym :: (Theory a s f) => Rules a s f -> Rules a s f
sym r = case proof r of  
    Right (a :== b) -> 
        let k = typeOf a
            s = varNotIn a in 
            (Leib ((Var s k) :== a) s r (Refl a))
    Left x -> r -- it will propagate


class (Show a, Signature s f) => Theory a s f | a -> s f where 
    axiom :: a -> Formula s f

proof :: (Theory a s f) => Rules a s f -> Either Err (Formula s f)
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

proof (Leib (tL :== tR) v pIn pProof) = do
    (t1 :== t2) <- proof pIn
    check <- proof pProof
    let s1 = typeOf t1
    let s2 = typeOf t2
    substL <- changeTerm tL v s1 t1
    substR <- changeTerm tR v s1 t1    

    retL <- changeTerm tL v s2 t2
    retR <- changeTerm tR v s2 t2
    if (check == (substL :== substR))
        then Right $ (retL :== retR)
        else Left "Incorrect substitution for Left side"
    
proof (App p v t) = do
    s <- typeCheck t
    (t1 :== t2) <- proof p
    nt1 <- changeTerm t1 v s t
    nt2 <- changeTerm t2 v s t
    Right $ nt1 :== nt2

changeTerm :: (Signature s f) => Term s f -> Name -> s -> Term s f -> Either Err (Term s f)
changeTerm v@(Var n s) vn vs t'
    | n == vn && s == vs = Right t'
    | n == vn && s /= vs = Left "Types of vars are different"
    | otherwise = Right v
changeTerm (FunApp n ts) vn vs t' = do
    nts <- changeList ts vn vs t'
    Right (FunApp n nts)
        where 
            changeList [] _ _ _ = Right []
            changeList (t : ts) vn vs t' = do
                nt <- changeTerm t vn vs t'
                nts <- changeList ts vn vs t'
                Right (nt : nts)
