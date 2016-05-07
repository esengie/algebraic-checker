{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolymorphicComponents #-}

module NHorn.LaCarte (
    Expr(..),
    (:+:)(..),
    (:<:),
    foldExpr,
    inj,
    prj,
    )
    where

newtype Expr f = In (f (Expr f))

data (f2 :+: g) a s f e = Inl (f2 a s f e) | Inr (g a s f e)

instance (Functor (f2 a s f), Functor (g a s f)) => Functor ((f2 :+: g) a s f) where
   fmap h (Inl f) = Inl (fmap h f)
   fmap h (Inr g) = Inr (fmap h g)

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

--------------------- Quite a bit harder part of code

data Pos = Here | Le Pos | Ri Pos
data Res = Found Pos | NotFound | Ambiguous

type family Elem (e :: (* -> * -> *) -> * -> * -> * -> *) (p :: (* -> * -> *) -> * -> * -> * -> * ) :: Res where
    Elem e e = Found Here
    Elem e (l :+: r) = Choose (Elem e l ) (Elem e r )
    Elem e p = NotFound

type family Choose (l :: Res) (r :: Res) :: Res where
    Choose (Found x ) (Found y) = Ambiguous
    Choose Ambiguous y = Ambiguous
    Choose x Ambiguous = Ambiguous
    Choose (Found x) y = Found (Le x )
    Choose x (Found y)= Found (Ri y)
    Choose x y = NotFound

data Proxy a = P
class Subsume (res :: Res) f2 g a s f where
    inj' :: Proxy res -> f2 a s f a' -> g a s f a'
    prj' :: Proxy res -> g a s f a' -> Maybe (f2 a s f a')

instance Subsume (Found Here) f2 f2 a s f where
    inj' _ = id
    prj' _ = Just
instance Subsume (Found p) f2 l a s f => Subsume (Found (Le p)) f2 (l :+: r ) a s f where
    inj' _ = Inl . inj' (P :: Proxy (Found p))
    prj' _ (Inl x ) = prj' (P :: Proxy (Found p)) x
    prj' _ (Inr _) = Nothing
instance Subsume (Found p) f2 r a s f => Subsume (Found (Ri p)) f2 (l :+: r ) a s f where
    inj' _ = Inr . inj' (P :: Proxy (Found p))
    prj' _ (Inr x ) = prj' (P :: Proxy (Found p)) x
    prj' _ (Inl _) = Nothing

type (f2 :<: g) a s f = Subsume (Elem f2 g) f2 g a s f

inj :: forall f2 g a s f e. (f2 :<: g) a s f => f2 a s f e -> g a s f e
inj = inj' (P :: Proxy (Elem f2 g))
prj :: forall f2 g a s f e. (f2 :<: g) a s f => g a s f e -> Maybe (f2 a s f e)
prj = prj' (P :: Proxy (Elem f2 g))
