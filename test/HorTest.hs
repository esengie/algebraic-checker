{-# LANGUAGE MultiParamTypeClasses #-}

module HorTest where

import qualified Horn as H
import Term

data Sort = O | H
    deriving (Show, Eq)
    
data Fun = Id | Dot | Dom | Cod | Excl | PaOb | PaHom | Proj1 | Proj2 | Top
    deriving (Show, Eq)

instance Signature Sort Fun where
    dom Id = [O]
    dom Dot = [H, H]
    dom Dom = [H]
    dom Cod = [H]
    dom Excl = [O]
    dom PaOb = [O, O]
    dom PaHom = [H, H]
    dom Proj1 = [O, O]
    dom Proj2 = [O, O]   
    dom Top = []

    cod Id = H
    cod Dot = H
    cod Dom = O
    cod Cod = O
    cod Excl = H
    cod PaOb = O
    cod PaHom = H
    cod Proj1 = H
    cod Proj2 = H     
    cod Top = O


data Axioms s f = DotUse Name Name | LeftId Name | RightId Name 
    | DotAssoc Name Name Name | DomId Name | CodId Name
    | DomDot Name Name | CodDot Name Name
    | DomExcl Name | CodExcl Name
    | TopEq Name Name | DomProj1 Name Name | DomProj2 Name Name
    | CodProj1 Name Name | CodProj2 Name Name
    | DefPaHom Name Name | Proj1Comp Name Name | Proj2Comp Name Name
    | H1H2 Name Name Name Name
    deriving (Show)

obj x = Var x O
hom f = Var f H

id' x = FunApp Id [x]
f *. g = FunApp Dot [f, g]

dom' f = FunApp Dom [f]
cod' f = FunApp Cod [f]

proj1 x y = FunApp Proj1 [x, y]
proj2 x y = FunApp Proj2 [x, y]

excl x = FunApp Excl [x]

pair (x, y) = FunApp PaOb [x, y]
pairF [f, g] = FunApp PaHom [f, g]

top = FunApp Top []

instance H.Theory Axioms Sort Fun where
    axiom (DotUse f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        [hom g *. hom f :== hom g *. hom f]
    axiom (LeftId f) = H.createSeq [] [id' (cod' $ hom f) *. hom f :== hom f]
    axiom (RightId f) = H.createSeq [] [hom f *. id' (cod' $ hom f):== hom f]
    axiom (DotAssoc f g h) = H.createSeq [cod' (hom f) :== dom' (hom g), cod' (hom g) :== dom' (hom h)] 
        [hom h *. (hom g *. hom f) :== (hom h *. hom g) *. hom f]
    axiom (DomId x) = H.createSeq [] [dom' (id' $ obj x):== obj x]
    axiom (CodId x) = H.createSeq [] [cod' (id' $ obj x):== obj x]

    axiom (DomDot f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        [dom'(hom g *. hom f) :== dom'( hom f)]
    axiom (CodDot f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        [cod'(hom g *. hom f) :== cod'(hom g)]
    --axiom (DomExcl x) =
    --axiom (CodExcl x) =
    --axiom (TopEq f g) = 
    --axiom (DomProj1 x y) = 
    --axiom (DomProj2 x y) =
    --axiom (CodProj1 x y) = 
    --axiom (CodProj2 x y) =
    --axiom (DefPaHom f g) =
    --axiom (Proj1Comp f g) =
    --axiom (Proj2Comp f g) =
    --axiom (H1H2 f g h1 h2) =

--zero = HRefl $ fromListVNS [("x", L)]


---- x +. (x *. (x +. x)) = x
--one = EAndL [var "x" *. (var "x" +. var "y") :== var "x", var "x" +. (var "x" *. var "y") :== var "x"]
--one' = Subst one "y" (var "x" +. var "x")

--two = IAnd (Axiom AndAbsorb) (Axiom OrAbsorb)
----two' = 

--three = Comp two one'
---- var "x" +. var "x" == var "x" +. (var "x" *. (var "x" +. var "x"))
----two
--four = Congr [var "x":== Var "y" Dr, var "x" *. var "z" :== var "x" *. var "z"]

--four' = Congr [var "x" *. var "y" :== Var "y" Dr, var "x" *. var "z" :== var "x" *. var "z"]

--isLeft (Left _) = True
--isLeft (Right _) = False

