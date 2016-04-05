{-# LANGUAGE MultiParamTypeClasses #-}

import Lib
import Test.HUnit

data Sort = D
    deriving (Show, Eq)
    
data Fun = M | P | One | Zero | INV 
    deriving (Show, Eq)

instance Signature Sort Fun where
    dom M = [D, D]
    dom P = [D, D]
    dom One = []
    dom Zero = []
    dom INV = [D]

    cod _ = D

data Axioms = Assoc | El | Er | PInv_L | Passoc | PEl | PEr
            | PSym | PInv | Dist_R | Dist_L | Strange


var x = Var x D
x *. y = FunApp M [x,y]
x +. y = FunApp P [x,y]
inv x = FunApp INV [x]
one = FunApp One []
zero = FunApp Zero []

instance Proof Axioms Sort Fun where
    axiom Assoc = (var "x" *. var "y") *. var "z" :== var "x" *. (var "y" *. var "z")
    axiom El = one *. var "x" :== var "x"
    axiom Er = var "x" *. one :== var "x"
    axiom PInv_L = inv (var "x") +. var "x" :== zero
    axiom Passoc = (var "x" +. var "y") +. var "z" :== var "x" +. (var "y" +. var "z")
    axiom PEl = zero +. var "x" :== var "x" 
    axiom PEr = var "x" +. zero :== var "x"
    axiom PSym = var "x" +. var "y" :== var "y" +. var "x"
    axiom PInv = var "x" +. (inv $ var "x") :== zero
    axiom Dist_R = var "x" *. (var "y" +. var "z") :== (var "x" *. var "y") +. (var "x" *. var "z")
    axiom Dist_L = (var "y" +. var "z") *. var "x" :== (var "y" *. var "x") +. (var "z" *. var "x")
    axiom Strange = var "x" *. var "x" :== var "x"
    

xx :: Term Sort Fun
xx = (var "x" +. var "x")

trans :: [Rules Axioms Sort Fun] -> Rules Axioms Sort Fun
trans [p] = p
trans (p:ps) = Trans p (trans ps)

-- x + x = (x + x) + (x + x)
proof1 :: Rules Axioms Sort Fun
proof1 = trans
    [ App (Sym $ Axiom Strange) "x" xx
    , App (App (App (Axiom Dist_R) "x" xx) "y" (var "x")) "z" (var "x") 
    , Cong P $ replicate 2 (App (App (Axiom Dist_L) "y" (var "x")) "z" (var "x"))
    , Cong P $ replicate 2 $ Cong P $ replicate 2 (Axiom Strange)
    ]

-- -(x + x) + ((x + x) + (x + x)) = x + x
proof2 :: Rules Axioms Sort Fun
proof2 = trans
    [ App (App (App (Sym $ Axiom Passoc) "x" (inv xx)) "y" xx) "z" xx
    , Cong P [App (Axiom PInv_L) "x" xx, Refl xx]
    , App (Axiom PEl) "x" xx
    ]

-- (x + x) = 0
proof3 :: Rules Axioms Sort Fun
proof3 = trans
    [ Sym proof2
    , Cong P [Refl $ inv xx, Sym proof1]
    , App (Axiom PInv_L) "x" xx
    ]

snippet :: Bool
snippet = case proof proof3 of 
            Right x -> True 
            Left x -> False

test1 :: Test
test1 = TestCase (assertBool "first" snippet)

main = runTestTT $ TestList [test1]