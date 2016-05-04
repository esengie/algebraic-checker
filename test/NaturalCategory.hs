{-# LANGUAGE MultiParamTypeClasses #-}

module NaturalCategory where

import qualified NaturalHorn as H
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
    | DefPaHomTo Name Name | DefPaHomFrom Name Name 
    | Proj1Comp Name Name | Proj2Comp Name Name
    | H1H2 Name Name Name Name
    | Idd (H.Sequent s f)
    deriving (Show)

obj :: Name -> Term Sort Fun
obj x = Var x O
hom :: Name -> Term Sort Fun
hom f = Var f H

id' :: Term Sort Fun -> Term Sort Fun
id' x = FunApp Id [x]

(*.) :: Term Sort Fun -> Term Sort Fun -> Term Sort Fun
f *. g = FunApp Dot [f, g]

dom' :: Term Sort Fun -> Term Sort Fun
dom' f = FunApp Dom [f]
cod' :: Term Sort Fun -> Term Sort Fun
cod' f = FunApp Cod [f]

proj1 :: (Term Sort Fun, Term Sort Fun) -> Term Sort Fun
proj1 (x,y) = FunApp Proj1 [x, y]
proj2 :: (Term Sort Fun, Term Sort Fun) -> Term Sort Fun
proj2 (x,y) = FunApp Proj2 [x, y]

excl :: Term Sort Fun -> Term Sort Fun
excl x = FunApp Excl [x]

pair :: (Term Sort Fun, Term Sort Fun) -> Term Sort Fun
pair (x, y) = FunApp PaOb [x, y]
pairF :: [Term Sort Fun] -> Term Sort Fun
pairF [f, g] = FunApp PaHom [f, g]

top :: Term Sort Fun
top = FunApp Top [] 

instance H.Theory Axioms Sort Fun where
    axiom (DotUse f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        $ hom g *. hom f :== hom g *. hom f
    axiom (LeftId f) = H.createSeq [] $ id' (cod' $ hom f) *. hom f :== hom f
    axiom (RightId f) = H.createSeq [] $ hom f *. id' (cod' $ hom f):== hom f
    axiom (DotAssoc f g h) = H.createSeq [cod' (hom f) :== dom' (hom g), cod' (hom g) :== dom' (hom h)] 
        $ hom h *. (hom g *. hom f) :== (hom h *. hom g) *. hom f
    axiom (DomId x) = H.createSeq [] $ dom' (id' $ obj x):== obj x
    axiom (CodId x) = H.createSeq [] $ cod' (id' $ obj x):== obj x

    axiom (DomDot f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        $ dom'(hom g *. hom f) :== dom'( hom f)
    axiom (CodDot f g) = H.createSeq [cod' (hom f) :== dom' (hom g)] 
        $ cod'(hom g *. hom f) :== cod'(hom g)
    axiom (DomExcl x) = H.createSeq [] $ dom'(excl $ obj x) :== obj x
    axiom (CodExcl x) = H.createSeq [] $ cod'(excl $ obj x) :== top
    axiom (TopEq f g) = H.createSeq [dom' (hom f) :== dom' (hom g),
        cod' (hom f) :== top, cod' (hom g) :== top] $ hom f :== hom g
    axiom (DomProj1 x y) = H.createSeq [] $ dom'(proj1 (obj x, obj y)) :== pair (obj x, obj y)
    axiom (DomProj2 x y) = H.createSeq [] $ dom'(proj2 (obj x, obj y)) :== pair (obj x, obj y)
    axiom (CodProj1 x y) = H.createSeq [] $ cod'(proj1 (obj x, obj y)) :== obj x
    axiom (CodProj2 x y) = H.createSeq [] $ cod'(proj2 (obj x, obj y)) :== obj y
    axiom (DefPaHomTo f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] $ pairF [hom f, hom g] :== pairF [hom f, hom g]
    axiom (DefPaHomFrom f g) = H.createSeq [pairF [hom f, hom g] :== pairF [hom f, hom g]] $ dom' (hom f) :== dom' (hom g)
    axiom (Proj1Comp f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] 
        $ proj1  (cod'(hom f), cod'(hom g)) *. pairF [hom f, hom g] :== hom f
    axiom (Proj2Comp f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] 
        $ proj2  (cod'(hom f), cod'(hom g)) *. pairF [hom f, hom g] :== hom g
    axiom (H1H2 f g h1 h2) = H.createSeq [ff proj1 f g *. hom h1 :== hom f, ff proj1 f g *. hom h2 :== hom f,
        ff proj2 f g *. hom h1 :== hom g, ff proj2 f g *. hom h2 :== hom g] $ hom h1 :== hom h2
            where ff p f g = p (cod'(hom f), cod'(hom g))

    axiom (Idd g) = Right g

    name (DotUse f g) = "DotUse_" ++ f ++ "_" ++ g
    name (LeftId f) = "LeftId_" ++ f
    name (RightId f) = "RightId_" ++ f
    name (DotAssoc f g h) = "DotAssoc_" ++ f ++ "_" ++ g ++ "_" ++ h
    name (DomId x) = "DomId_" ++ x
    name (CodId x) = "CodId_" ++ x
    name (DomDot f g) = "DomDot_" ++ f ++ "_" ++ g
    name (CodDot f g) = "CodDot_" ++ f ++ "_" ++ g
    name (DomExcl x) = "DomExcl_" ++ x
    name (CodExcl x) = "CodExcl_" ++ x
    name (TopEq f g) = "TopEq_" ++ f ++ "_" ++ g
    name (DomProj1 x y) = "DomProj1_" ++ x ++ "_" ++ y
    name (DomProj2 x y) = "DomProj2_" ++ x ++ "_" ++ y
    name (CodProj1 x y) = "CodProj1_" ++ x ++ "_" ++ y
    name (CodProj2 x y) = "CodProj2_" ++ x ++ "_" ++ y
    name (DefPaHomTo f g) = "DefPaHomTo_" ++ f ++ "_" ++ g
    name (DefPaHomFrom f g) = "DefPaHomFrom_" ++ f ++ "_" ++ g
    name (Proj1Comp f g) = "Proj1Comp_" ++ f ++ "_" ++ g
    name (Proj2Comp f g) = "Proj2Comp_" ++ f ++ "_" ++ g
    name (H1H2 f g h1 h2) = "H1H2_" ++ f ++ "_" ++ g ++ "_" ++ h1 ++ "_" ++ h2

    name (Idd g) = "Error"

unright (Right g) = g


----- stupid example of working Leib with the help of all powerful Idd axiom
on = H.Axiom $ Idd $ unright $ H.createSeq [dom'(hom "f") :== dom'(hom "g")] $ hom "f" :== hom "g"
on' = H.Axiom $ Proj1Comp "f" "g"
one = H.Leib (proj1  (cod'(hom "f"), cod'(hom "g")) *. pairF [hom "f", hom "g"] :== hom "f") "f" on on'

----- stupid example of working Strict with the help of all powerful Idd axiom
tw = H.Axiom $ Idd $ unright $ H.createSeq [dom'(hom "f") :== dom'(hom "g")] $ (hom "f") *. (hom "g") :== (hom "f") *. (hom "g")
two = H.Strict 1 tw

----- stupid example of working SubstAx with the help of all powerful Idd axiom
three = H.SubstAx (TopEq "f" "g") [ff(dom' (hom "g") :== dom' (hom "f")),
    ff(cod' (hom "g") :== top), ff(cod' (hom "f") :== top)] [hom "g", hom "f"]
three' = H.Axiom (TopEq "f" "g")

ff s = H.Axiom $ Idd $ unright $ H.createSeq [] s

------------------------------------------------------------------------------------------

theorem1 x = H.createSeq [] $ pairF [excl(obj x), id'(obj x)] *. proj2 (top, obj x) :== id'(pair(top, obj x))
theorem2 x = H.createSeq [] $ proj2 (top, obj x) *. pairF [excl(obj x), id'(obj x)] :== id'(obj x)

-- So we have this, let's subst: g := id x, f:= !x
start' :: H.IniRules Axioms Sort Fun
start' = H.Axiom $ Proj2Comp "f" "g" 

-- dom (id x) == dom (!x)
domId :: H.IniRules Axioms Sort Fun
domId = H.Axiom $ DomId "x"
domE :: H.IniRules Axioms Sort Fun
domE = H.Sym $ H.Axiom $ DomExcl "x"
prIdExcl :: H.IniRules Axioms Sort Fun
prIdExcl = H.Sym $ H.Trans domId domE

-- P2(cod(id x), cod(!x)) *. [id x, !x] = !x
start :: H.IniRules Axioms Sort Fun
start = H.SubstAx (Proj2Comp "f" "g") [prIdExcl] [excl (obj "x"), id' (obj "x")]

-- cod(!x) = Top and cod(id x) = x
codE :: H.IniRules Axioms Sort Fun
codE = H.Axiom $ CodExcl "x"
codId :: H.IniRules Axioms Sort Fun
codId = H.Axiom $ CodId "x"

-- So let's leibnitz it in
l_fla1 = proj2  (obj "l", cod' (id' (obj "x"))) *. pairF [excl (obj "x"), id' (obj "x")] :== id' (obj "x")
l_fla2 = proj2  (top , obj "l") *. pairF [excl (obj "x"), id' (obj "x")] :== id' (obj "x")

-- We do that in two steps
st1 :: H.IniRules Axioms Sort Fun
st1 = H.Leib l_fla1 "l" codE start 
st2 :: H.IniRules Axioms Sort Fun
st2 = H.Leib l_fla2 "l" codId st1 

-- H.proof st2 == theorem2 "x"