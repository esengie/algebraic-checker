{-# LANGUAGE MultiParamTypeClasses #-}

module Category where

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
    | DefPaHomTo Name Name | DefPaHomFrom Name Name 
    | Proj1Comp Name Name | Proj2Comp Name Name
    | H1H2 Name Name Name Name
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
    axiom (DomExcl x) = H.createSeq [] [dom'(excl $ obj x) :== obj x]
    axiom (CodExcl x) = H.createSeq [] [cod'(excl $ obj x) :== top]
    axiom (TopEq f g) = H.createSeq [dom' (hom f) :== dom' (hom g),
        cod' (hom f) :== top, cod' (hom g) :== top] [hom f :== hom g]
    axiom (DomProj1 x y) = H.createSeq [] [dom'(proj1 (obj x, obj y)) :== pair (obj x, obj y)]
    axiom (DomProj2 x y) = H.createSeq [] [dom'(proj2 (obj x, obj y)) :== pair (obj x, obj y)]
    axiom (CodProj1 x y) = H.createSeq [] [cod'(proj1 (obj x, obj y)) :== obj x]
    axiom (CodProj2 x y) = H.createSeq [] [cod'(proj2 (obj x, obj y)) :== obj y]
    axiom (DefPaHomTo f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] [pairF [hom f, hom g] :== pairF [hom f, hom g]]
    axiom (DefPaHomFrom f g) = H.createSeq [pairF [hom f, hom g] :== pairF [hom f, hom g]] [dom' (hom f) :== dom' (hom g)]
    axiom (Proj1Comp f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] 
        [proj1  (cod'(hom f), cod'(hom g)) *. pairF [hom f, hom g] :== hom f]
    axiom (Proj2Comp f g) = H.createSeq [dom' (hom f) :== dom' (hom g)] 
        [proj2  (cod'(hom f), cod'(hom g)) *. pairF [hom f, hom g] :== hom g]
    axiom (H1H2 f g h1 h2) = H.createSeq [ff proj1 f g *. hom h1 :== hom f, ff proj1 f g *. hom h2 :== hom f,
        ff proj2 f g *. hom h1 :== hom g, ff proj2 f g *. hom h2 :== hom g] [hom h1 :== hom h2]
            where ff p f g = p (cod'(hom f), cod'(hom g))



unright (Right g) = g

sym seqt = (H.Comp seqt (sym' obj seqt))
symF seqt = (H.Comp seqt (sym' hom seqt))
sym' obj seqt = let rtOne = head (H.rightS $ unright $ H.proof seqt)
    in H.Subst (H.Subst (H.Sym [obj "x'''" :== obj "y'''"]) 
        "x'''" (leftT rtOne)) "y'''" (rightT rtOne)

trans seqt = H.Comp seqt $ trans' obj seqt
transF seqt = H.Comp seqt $ trans' hom seqt
trans' obj seqt = let rights = (H.rightS $ unright $ H.proof seqt)
                      fst = head rights
                      snd = head $ tail rights
    in H.Subst (H.Subst (H.Subst (H.Trans [obj "x'''" :== obj "y'''", obj "y'''" :== obj "z'''"]) 
        "x'''" (leftT fst)) "y'''" (rightT fst)) "z'''" (rightT snd)


theorem1 x = H.createSeq [] [pairF [excl(obj x), id'(obj x)] *. proj2 (top, obj x) :== id'(pair(top, obj x))]
theorem2 x = H.createSeq [] [proj2 (top, obj x) *. pairF [excl(obj x), id'(obj x)] :== id'(obj x)]

--- theorem2
step1 = H.Subst (H.Subst (H.Axiom $ Proj2Comp "f" "g") "f" (excl $ obj "x")) "g" (id' $ obj "x")

ref1_1 = H.Axiom (DomExcl "x")
ref1_2 = H.Axiom (DomId "x")
ref1 = trans $ H.IAnd ref1_1 (sym ref1_2)

step2 = H.Comp ref1 step1

ref3_1 = H.Axiom (CodExcl "x")
ref3_2 = H.Axiom (CodId "x")

------------- Так можно?
step3_1 = H.Congr [obj "z" :== obj "y", obj "z'" :== obj "y'",
    H.defFun (proj2(obj "z", obj "z'") *. pairF[excl(obj "x"), id'(obj "x")])]

step3_2 = H.Subst (H.Subst step3_1 "z" $ cod'(excl(obj"x"))) "y" top
step3_3 = H.Subst (H.Subst step3_2 "z'" $ cod'(id'(obj "x"))) "y'" $ obj "x"

----ref3 = ...
ref3' = H.IAnd ref3_1 ref3_2
easier_than_to_type = H.Strict $ H.rightS $ unright $ H.proof step2
subst_easier = H.EAndR $ H.rightS $ unright $ H.proof easier_than_to_type
ref3'' = H.Comp step2 $ H.Comp easier_than_to_type subst_easier

ref3 = H.IAnd ref3' ref3''

step4 = symF $ H.Comp ref3 step3_3
step5 = transF $ H.IAnd step4 step2

---------- step5 == theorem2 "x"
