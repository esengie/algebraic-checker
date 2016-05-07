{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators, GADTs #-}


module NHorn.Sequent 
    where

import Control.Monad(foldM)
import Data.List(tail, init, intersperse)

import qualified Data.Map as Map
import qualified Data.Set as Set

import NHorn.LaCarte
import Term

data Sequent s f = Seq { varNs :: VarNames s,
            leftS :: [Formula s f],
            rightS :: Formula s f}
    deriving (Eq)

type ErrSec s f = Either Err (Sequent s f)

defFun :: Signature s f => Term s f -> Formula s f
defFun b = b :== b

instance (Signature s f) => Show (Sequent s f) where
    show seq = show (leftS seq) ++ " |- " ++ show (varNs seq) ++ " -- " ++ show (rightS seq)

createSeq :: Signature s f => [Formula s f] -> Formula s f -> ErrSec s f
createSeq left right = do
    let lst1 = map varsCheckF left
    let lst2 = varsCheckF right
    let memp = Map.empty
    checked <- foldM combine memp (lst2:lst1)
    let seqt = Seq checked left right
    typeCheckSeq seqt
    return seqt


varsSequent :: Signature s f => Sequent s f -> VarNames s
varsSequent seq = Map.union (thing (leftS seq)) $ thing $ [rightS seq]
    where thing st = foldl (\a b -> Map.union a (varsFormula b)) Map.empty st

-- Checks that the vars are of the same sort everywhere they are mentioned
varsCheckS :: Signature s f => Sequent s f -> Either Err (VarNames s)
varsCheckS seqt = do
    let lst1 = map varsCheckF $ leftS seqt
    let lst2 = varsCheckF $ rightS seqt
    let memp = Map.empty
    checked <- foldM combine memp (lst2:lst1)
    if (Map.difference checked $ varNs seqt) == emptyVNS
        then return checked
        else Left "Not enough variables in context"

typeCheckSeq :: Signature s f => Sequent s f -> Either Err ()
typeCheckSeq seqt = do
    let lst1 = map typeCheckFormula $ leftS seqt
    let lst2 = map typeCheckFormula $ [rightS seqt]
    sequence_ (lst1 ++ lst2)
                 

class (Show (a s f), Signature s f) => Theory a s f | a -> s f, s f -> a where 
    axiom :: a s f -> ErrSec s f
    name :: a s f -> Name
