{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}


module NHorn.NaturalHornPretty(
    Prettier(..)
    )
    where


import Text.PrettyPrint.Leijen

import qualified Data.Map as Map

import NHorn.LaCarte
import NHorn.Sequent
import NHorn.NaturalHorn
import Term

class (Theory a s f, Proof f2 a s f) => Prettier f2 a s f where
    pretty' :: (Prettier g a s f) => f2 a s f (Expr (g a s f)) -> Doc

instance (Prettier g a s f) => Pretty (Expr (g a s f)) where
    pretty (In t) = pretty' t

instance (Prettier g a s f) => Show (Expr (g a s f)) where
    show a = show (pretty a)

instance (Prettier f2 a s f, Prettier g a s f) => Prettier (f2 :+: g) a s f where
    pretty' (Inl f) = pretty' f
    pretty' (Inr g) = pretty' g

instance Theory a s f => Prettier Rule a s f where
    pretty' (Refl ctx vm) = let (a, b) = Map.elemAt 0 vm
        in text "refl" <> parens (text a)
    pretty' (Sym r) = text "sym" <> parens (pretty r)
    pretty' (Select n lst) = text "select" <> parens (int n)  --hcat (map (string.show) lst) </> string " |-- " </> string (show $ lst!!(n-1))
    pretty' (Leib phi x p q) = text "leib" <> braces (indent 0 $ cip id [text ("\\" ++ x), (text.show) phi, pretty p, pretty q])
    pretty' (Strict n p) = text "sf_" <> cip (text.show) [(unright $ getFunName p), show n] <> parens (pretty p)
        where getFunName p = do 
                (Seq _ _ ((FunApp f _) :== _)) <- proof p
                return $ show f
    pretty' (ProofAx ax ups terms) = text (name ax) <> brackets (indent 0 (cip (text.show) terms <> semi </> cip pretty ups))

cip :: (a -> Doc) -> [a] -> Doc
cip f lst = cat (punctuate (comma <> space) (map f lst))

unright (Right s) = s 
unright (Left s) = error "@@@You should proofcheck before showing/prettyprinting@@@"
