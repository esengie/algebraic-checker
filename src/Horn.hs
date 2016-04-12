{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Horn where

import Data.List(tail, init)
import qualified Data.Map as Map

import Term

type VarNames s = Map.Map Name s

emptyVNS :: VarNames s
emptyVNS = Map.empty

fromListVNS :: [(Name, s)] -> VarNames s
fromListVNS lst = Map.fromList lst

data Sequent s f = Seq { varNs :: VarNames s,
            left :: [Formula s f],
            right :: [Formula s f]}
    deriving (Show, Eq)

data HAxiom s f = Id (VarNames s) [Formula s f]
    | Top (VarNames s) [Formula s f]
    | EAndL (VarNames s) [Formula s f]
    | EAndR (VarNames s) [Formula s f]
    | Refl (VarNames s) [Formula s f]
    | Leib (VarNames s) [Formula s f]
    deriving (Show, Eq)

data HRule a s f = Axiom a 
        | HAxiom s f
        | Comp (HRule a s f) (HRule a s f) 
        | IAnd (HRule a s f) (HRule a s f)
        | Subst (HRule a s f) (Term s f)

    deriving (Show)

hAxiom :: HAxiom s f -> Sequent s f
hAxiom (Id vs f) = Seq vs f f
hAxiom (Top vs f) = Seq vs f []
hAxiom (EAndL vs []) = error "EAndL must have at least one formula to the left"
hAxiom (EAndL vs f) = Seq vs f $ tail f
hAxiom (EAndR vs []) = error "EAndR must have at least one formula to the left"
hAxiom (EAndR vs f) = Seq vs f $ init f
hAxiom (Refl emptyVNS _) = error "Can't apply Refl to empty set of vars"
hAxiom (Refl vm f) = 
    let (nel, sel) = Map.elemAt 0 vm
        v = Var nel sel in
            Seq (Map.singleton nel sel) [] $ [v :== v]

class (Show a, Signature s f) => Theory a s f | a -> s f where 
    axiom :: a -> Sequent s f
