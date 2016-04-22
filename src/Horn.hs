{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}

module Horn (
    Rule(..),
    Theory(..),
    Sequent,
    leftS,
    rightS,
    defFun,
    createSeq,
    proof,
    )
    where

import Control.Monad(foldM)
import Data.List(tail, init)
import LaCarte
import qualified Data.Map as Map

import Term

data Sequent s f = Seq { varNs :: VarNames s,
            leftS :: [Formula s f],
            rightS :: [Formula s f]}
    deriving (Eq)

defFun :: Signature s f => Term s f -> Formula s f
defFun b = b :== b

instance (Signature s f) => Show (Sequent s f) where
    show seq = show (leftS seq) ++ " |- " ++ show (varNs seq) ++ " -- " ++ show (rightS seq)

createSeq :: Signature s f => [Formula s f] -> [Formula s f] -> Either Err (Sequent s f)
createSeq left right = do
    let lst1 = map varsCheckF left
    let lst2 = map varsCheckF right
    let memp = Map.empty
    checked <- foldM combine memp (lst1 ++ lst2)
    let seqt = Seq checked left right
    typeCheckSeq seqt
    return seqt


varsSequent :: Signature s f => Sequent s f -> VarNames s
varsSequent seq = Map.union (thing (leftS seq)) $ thing $ rightS seq
    where thing st = foldl (\a b -> Map.union a (varsFormula b)) Map.empty st

-- Checks that the vars are of the same sort everywhere they are mentioned
varsCheckS :: Signature s f => Sequent s f -> Either Err (VarNames s)
varsCheckS seqt = do
    let lst1 = map varsCheckF $ leftS seqt
    let lst2 = map varsCheckF $ rightS seqt
    let memp = Map.empty
    checked <- foldM combine memp (lst1 ++ lst2)
    if (Map.difference checked $ varNs seqt) == emptyVNS
        then return checked
        else Left "Not enough variables in context"

typeCheckSeq :: Signature s f => Sequent s f -> Either Err ()
typeCheckSeq seqt = do
    let lst1 = map typeCheckFormula $ leftS seqt
    let lst2 = map typeCheckFormula $ rightS seqt
    sequence_ (lst1 ++ lst2)
                 

class (Show (a s f), Signature s f) => Theory a s f | a -> s f, s f -> a where 
    axiom :: a s f -> Either Err (Sequent s f)


data Rule a s f ala
        = Axiom (a s f)
        ----------------------------------------------------
        | User (ala (Rule a s f ala))
        | Sym [Formula s f]    --                a :== b |- b :== a
        | Trans [Formula s f]  --    a :== b and b :== c |- a :== c
        | Congr [Formula s f]  -- x_i :== y_i and f(x_i) |- f(y_i)
        | Strict [Formula s f] --              t_1 = t_2 |- t_1 = t_1 and t_2 = t_2
        ----------------------------------------------------
        | Id [Formula s f]     --           phi |- phi
        | Top [Formula s f]    --           phi |- Top
        | EAndL [Formula s f]  --   phi and psi |- phi
        | EAndR [Formula s f]  --   phi and psi |- psi
        | Refl (VarNames s)   --               |- x = x
        | Leib [Formula s f]  -- x = y and phi |- phi[y/x]
        | Comp (Rule a s f ala) (Rule a s f ala)
        | IAnd (Rule a s f ala) (Rule a s f ala)
        | Subst (Rule a s f ala) Name (Term s f)
    
    --deriving (Show)


-----------------------------------------------------------------

data Empty r
type IniRules a s f = Rule a s f Empty

--data Sym r = Sym r
--data Trans r = Trans r r
--data Congr r = Congr r r

--type ExtRules a s f = Rule a s f (Sym :+: Trans :+: Congr)

class UserRules ala where
    def :: ala (Rule a s f t) -> Rule a s f ala

-----------------------------------------------------------------

proof :: (Theory a s f {-, UserRules t -}) => IniRules a s f -> Either Err (Sequent s f)
-- This is user defined so checks the correctness of that
proof (Axiom s) = do
    a <- axiom s
    typeCheckSeq a
    varsCheckS a
    return a
-------------------------------------------------

proof (Sym []) = Left "Refl must have one formula not ZERO"
proof (Sym [(a :== b)]) = createSeq [(a :== b)] [(b :== a)]
proof (Sym _) = Left "Refl must have one formula not MANY"

proof (Trans []) = Left "Refl must have two formulas not ZERO"
proof (Trans [x]) = Left "Refl must have two formulas not ONE"
proof (Trans l@([(a :== b), (b1 :== c)])) = if b == b1
    then createSeq l [a :== c]
    else Left $ "Trans doesn't work"
proof (Trans _) = Left "Refl must have two formulas not MANY"

proof (Congr []) = Left "Congruence needs at least a function"
proof (Congr lst) = do 
    let a@(fnl :== fnr) = last lst
    _ <- checkVars $ init lst
    if fnl /= fnr then Left "Func must be defined"
        else do
            let lefts = map leftT (init lst)
            let rights = map rightT (init lst)
            sfnr <- foldM subsst fnr (zip lefts rights)
            createSeq lst [(fnl :== sfnr)]
                where subsst t ((Var name srt), y) = subst t name srt y
                      checkVars [] = Right ()
                      checkVars (((Var _ _) :== (Var _ _)):xs) = checkVars xs
                      checkVars (x:xs) = Left $ show x ++ " is not a var formula! Congr needs a list of vars before a function"

proof (Strict []) = Left "Strict needs one equality"
proof (Strict f@[a:==b]) = createSeq f [a:==a, b:==b]
proof (Strict _) = Left "Strict needs one equality"

----------------------------------------------------------------------
proof (Id f) = createSeq f f

proof (Top f) = createSeq f []

proof (EAndL []) = Left "EAndL must have at least one formula to the left"
proof (EAndL f) = createSeq f $ tail f

proof (EAndR []) = Left "EAndR must have at least one formula to the left"
proof (EAndR f) = createSeq f $ init f

proof (Refl vm) 
  | vm == emptyVNS = Left "Can't apply Refl to empty set of vars"
  | otherwise = 
    let (nel, sel) = Map.elemAt 0 vm
        v = Var nel sel in
            createSeq [] $ [v :== v]

proof (Leib []) = Left "Leib must have at least one formula to the left"
proof (Leib f@(x:xs)) = case isVarEqualityFormula x of
    Left _ -> Left "Leib must have at least one Vars equality to the left"
    Right (n, sr) -> do
        a <- sequence $ map (substIntoF n sr $ rightT x) xs
        createSeq f a

    where isVarEqualityFormula ((Var n sr) :== (Var _ _)) = Right (n,sr)
          isVarEqualityFormula _ = Left "Not Vars on the sides of formula"

proof (Comp a b) = do
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    vmap <- combine v1 (Right v2)
    if lr == rl then {-return $ Seq vmap-} createSeq ll rr -- may add unneeded vars into context
        else Left $ "Composition doesn't work " ++ show lr ++ " isn't the same as " ++ show rl

proof (IAnd a b) = do 
    (Seq v1 ll lr) <- proof a
    (Seq v2 rl rr) <- proof b
    vmap <- combine v1 (Right v2)
    if ll == rl then return $ Seq vmap ll (lr ++ rr)
        else Left $ "IAnd doesn't work " ++ show ll ++ " isn't the same as " ++ show rl    

proof (Subst seq' nam term) = do
    sq@(Seq vsSeq l r) <- proof seq'
    -- Just to check
    (Seq llVars _ _) <- createSeq l []
    check nam llVars sq
    -------------------
    sortTerm <- typeCheckTerm term
    let vsT = varsTerm term
    allVs <- combine vsT (Right vsSeq) -- to check compatibility
    l' <- sequence $ map (substIntoF nam sortTerm term) l
    r' <- sequence $ map (substIntoF nam sortTerm term) r
    return $ Seq allVs l' r'
        where check nam mp sq = if Map.member nam mp
                then Right ()
                else Left $ "Subst " ++ nam ++ " is not a free var on the left side of " 
                    ++ show sq



                    