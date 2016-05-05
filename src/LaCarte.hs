{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fglasgow-exts #-}

module LaCarte (
    Expr(..),
    (:+:)(..),
    (:<:)(..),
    foldExpr,
    inj,
    prj,
    )
    where

newtype Expr f = In (f (Expr f))

instance Show (f (Expr f)) => Show (Expr f) where
    showsPrec _ (In x) = showParen True (showString "In " . showsPrec 11 x)

out :: Expr f -> f (Expr f)
out (In x) = x

data (f :+: g) e = Inl (f e) | Inr (g e) deriving Show

instance (Functor f, Functor g) => Functor (f :+: g) where
   fmap h (Inl f) = Inl (fmap h f)
   fmap h (Inr g) = Inr (fmap h g)

--class (Functor sub, Functor sup) => (:<:) sub sup where
--   inj :: sub a -> sup a

--instance TypTree sub sup => (:<:) sub sup where inj = treeInj

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)


data Val e = Val Int deriving Show
data Add e = Add e e deriving Show
data Mul e = Mul e e deriving Show

instance Functor Val where
    fmap f (Val x) = Val x
instance Functor Add where
    fmap f (Add l r) = Add (f l) (f r)
instance Functor Mul where
    fmap f (Mul l r) = Mul (f l) (f r)

class Functor f => Eval f where
    evalA :: f Int -> Int

instance Eval Val where
    evalA (Val x) = x
instance Eval Add where
    evalA (Add x y) = x + y
instance Eval Mul where
    evalA (Mul x y) = x * y

instance (Eval f, Eval g) => Eval (f :+: g) where
    evalA (Inl f) = evalA f
    evalA (Inr g) = evalA g

eval :: Eval f => Expr f -> Int
eval expr = foldExpr evalA expr

val :: (Val :<: e) => Int -> Expr e
val x = In $ inj $ Val x

add :: (Add :<: e) => Expr e -> Expr e -> Expr e
add x y = In $ inj $ Add x y

mul :: (Mul :<: e) => Expr e -> Expr e -> Expr e
mul x y = In $ inj $ Mul x y

test :: Expr (Val :+: Add)
test = In (Inr (Add (val 118) (val 1219)))

test2 :: Expr (Add :+: Val)
test2 = val 1

test3 :: Expr ((Add :+: Val) :+: Mul)
test3 = add (mul (val 1) (val 2)) (val 3)

test4 :: Expr (Add :+: (Val :+: Mul))
test4 = add (mul (val 1) (val 2)) (val 3)

-- our typtree selection prefers left injection
--test5 :: Expr ((Val :+: Val) :+: (Val :+: Val))
--test5 = val 1

data Pos = Here | Le Pos | Ri Pos
data Res = Found Pos | NotFound | Ambiguous

type family Elem (e :: * -> *) (p :: * -> *) :: Res where
    Elem e e = Found Here
    Elem e (l :+: r ) = Choose (Elem e l ) (Elem e r )
    Elem e p = NotFound

type family Choose (l :: Res) (r :: Res) :: Res where
    Choose (Found x ) (Found y) = Ambiguous
    Choose Ambiguous y = Ambiguous
    Choose x Ambiguous = Ambiguous
    Choose (Found x) y = Found (Le x )
    Choose x (Found y)= Found (Ri y)
    Choose x y = NotFound

data Proxy a = P
class Subsume (res :: Res) f g where
    inj' :: Proxy res -> f a -> g a
    prj' :: Proxy res -> g a -> Maybe (f a)

instance Subsume (Found Here) f f where
    inj' _ = id
    prj' _ = Just
instance Subsume (Found p) f l => Subsume (Found (Le p)) f (l :+: r ) where
    inj' _ = Inl . inj' (P :: Proxy (Found p))
    prj' _ (Inl x ) = prj' (P :: Proxy (Found p)) x
    prj' _ (Inr _) = Nothing
instance Subsume (Found p) f r => Subsume (Found (Ri p)) f (l :+: r ) where
    inj' _ = Inr . inj' (P :: Proxy (Found p))
    prj' _ (Inr x ) = prj' (P :: Proxy (Found p)) x
    prj' _ (Inl _) = Nothing

type f :<: g = Subsume (Elem f g) f g

inj :: forall f g a. (f :<: g) => f a -> g a
inj = inj' (P :: Proxy (Elem f g))
prj :: forall f g a. (f :<: g) => g a -> Maybe (f a)
prj = prj' (P :: Proxy (Elem f g))
