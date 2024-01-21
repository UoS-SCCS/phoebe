{-# LANGUAGE StandaloneDeriving, GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Terms where
import Data.Map (Map, (!), fromList, keys, elems)
import qualified Data.Set as S
import Data.List as L
import HelperFunctions
import Debug.Trace
-- import ShowFunctions

deriving instance Eq (Terms a)

type Var = String

data Terms a where
    -- Atomic Concrete Terms
    Const    :: Const -> Terms a
    Name     :: Name  -> Terms Grd
    Nonce    :: Int   -> Terms Grd
    Key      :: Key   -> Terms Grd
    -- Atomic Abstract Terms
    AbsName  :: RoleName  -> Terms Abs
    AbsNonce :: NonceName -> Terms Abs 
    AbsKey   :: KeyName   -> Terms Abs 
    AbsList  :: Terms Abs -> Terms Abs
    -- Atomic Logic Terms
    VarAg    :: Var -> Terms Logic 
    VarName  :: Var -> Terms Logic
    VarKey   :: Var -> Terms Logic
    Abs      :: Terms Abs -> Terms Logic
    Grd      :: Terms Grd -> Terms Logic
    -- Additional Abstract Terms
    Self     :: Terms Abs        
    Role     :: RoleName  -> Terms Abs
    -- Constructors
    Tuple    :: [Terms Grd] -> Terms Grd           -- for whitelists
    PubKey   :: Terms a -> Terms a
    PrivKey  :: Terms a -> Terms a
    Pair     :: Terms a -> Terms a -> Terms a
    Triple   :: Terms a -> Terms a -> Terms a -> Terms a
    Crypt    :: Terms a -> Terms a -> Terms a
    SCrypt   :: Terms a -> Terms a -> Terms a
    Hash     :: Terms a -> Terms a
    -- Undeciph Destructors 
    -- (owner is not necessary as we modelled public key encryption with Crypt a m not Crypt (pub(a)) m) 
    Proj1    :: Terms Grd -> Terms Grd
    Proj2    :: Terms Grd -> Terms Grd
    Proj3    :: Terms Grd -> Terms Grd
    DCrypt   :: Terms Grd -> Terms Grd
    DSCrypt  :: Terms Grd -> Terms Grd
    DHash    :: Terms Grd -> Terms Grd


-- | we could have used these atoms directly in Terms a, by defining 
-- CTerm :: Grd -> Terms Grd
-- ATerm :: Abs -> Term Abs
-- but CTerm and ATerm become cumbersome
--
type Term = Terms Grd -- ^ \[ \mathcal{T}(F, T_0) \]
type AbsTerm = Terms Abs -- ^ \[ \mathcal{T}(F, \mathcal{V}) \]
type LogicTerm = Terms Logic -- ^ \[ \mathcal{T}(F, \mathcal{X}) \]

type Nonce = Int

data Name = Alice | Bob | Charlie | Tag Int | Reader Int |  Spy  
    deriving (Eq, Ord)

data Key = LKey Int | SsKey Int
    deriving (Eq, Ord)

data RoleName = A | B | C | T | R | DY -- ^$\mathcal{R}$
    deriving (Eq, Show, Ord)

data NonceName = NA | NB | NC | N | NT | NR | ND -- ^$\mathcal{N}$
    deriving (Eq, Show, Ord)

data KeyName = KK | KT  -- ^$\mathcal{K}$
    deriving (Eq, Show, Ord)


data Grd = CName Name | CNonce Int | CKey Key                -- dummy data type
data Abs = AName RoleName | ANonce NonceName | AbKey KeyName -- dummy data type
data Logic = Logic 

type Const = Int
    




deriving instance Ord (Terms a)


type Mapping = (AbsTerm, Term)


-- | δ(f(t)) = f(δ(t))
tLiftDelta :: Map LogicTerm LogicTerm -> LogicTerm -> LogicTerm 
tLiftDelta frm (VarKey k)                  = frm!(VarKey k)
tLiftDelta frm (VarName a)                  = frm!(VarName a)
tLiftDelta frm (VarAg x)                  = frm!(VarAg x)
tLiftDelta frm (Grd a)                     = Grd a
tLiftDelta frm (PubKey k)                  = PubKey (tLiftDelta frm k)
tLiftDelta frm (Pair t1 t2)                =  Pair ( tLiftDelta frm t1) (tLiftDelta frm t2)
tLiftDelta frm (Triple t1 t2 t3)           = Triple (tLiftDelta frm t1) (tLiftDelta frm t2) (tLiftDelta frm t3)
tLiftDelta frm (Crypt a m)           =  Crypt (tLiftDelta frm a) (tLiftDelta frm m)
tLiftDelta frm (SCrypt k m)           =  SCrypt (tLiftDelta frm k) (tLiftDelta frm m)
tLiftDelta frm (Hash m)           =   Hash (tLiftDelta frm m) 


-- | σ(f(t)) = f(σ(t)) in logics
tLiftSigma :: Map LogicTerm LogicTerm -> LogicTerm -> LogicTerm 
tLiftSigma frm (Abs a)                     = frm!(Abs a)
tLiftSigma frm (VarKey k)                  = (VarKey k)
tLiftSigma frm (VarName a)                  = (VarName a)
tLiftSigma frm (VarAg x)                  = (VarAg x)
tLiftSigma frm (Grd a)                     = Grd a
tLiftSigma frm (PubKey k)                  = PubKey (tLiftSigma frm k)
tLiftSigma frm (Pair t1 t2)                = Pair (tLiftSigma frm t1) (tLiftSigma frm t2)
tLiftSigma frm (Triple t1 t2 t3)           = Triple (tLiftSigma frm t1) (tLiftSigma frm t2) (tLiftSigma frm t3)
tLiftSigma frm (Crypt a m)           =  Crypt (tLiftSigma frm a) (tLiftSigma frm m)
tLiftSigma frm (SCrypt k m)           =  SCrypt (tLiftSigma frm k) (tLiftSigma frm m)
tLiftSigma frm (Hash m)           =  Hash (tLiftSigma frm m) 

-- | σ(f(t)) = f(σ(t)) in protocol semantics
tLift :: Map (Terms a) Term -> Terms a -> Term 
tLift frm (Const n)                      = Const n
tLift frm (AbsNonce n)                   = frm!(AbsNonce n)
tLift frm (AbsName a)                    = frm!(AbsName a)
tLift frm (AbsKey k)                     = frm!(AbsKey k) 
tLift frm (Nonce n)                   = (Nonce n)
tLift frm (Name a)                    = (Name a)
tLift frm (Key k)                     = (Key k) 
tLift frm (PubKey k)                     = PubKey (tLift frm k)
tLift frm (Pair pt1 pt2) 
   | (Pair pt1 pt2) `elem` (keys frm)       = frm!(Pair pt1 pt2)
   | otherwise                              = Pair (tLift frm pt1) (tLift frm pt2)
tLift frm (Triple pt1 pt2 pt3) 
   | (Triple pt1 pt2 pt3) `elem` (keys frm) = frm!(Triple pt1 pt2 pt3)
   | otherwise                              = Triple (tLift frm pt1) (tLift frm pt2) (tLift frm pt3)
tLift frm (SCrypt k m)   
   | (SCrypt k m) `elem` (keys frm)         = frm!(SCrypt k m)
   | otherwise                              = SCrypt (frm!k) (tLift frm m)
tLift frm (Crypt a m)
   | (Crypt a m) `elem` (keys frm)          = frm!(Crypt a m)
   | otherwise                              = Crypt (frm!a) (tLift frm m)
tLift frm (Hash m)
   | (Hash m) `elem` (keys frm)             = frm!(Hash m)
   | otherwise                              = Hash (tLift frm m)

subterms :: Terms a -> [Terms a]
subterms (Const n)         = [Const n]
subterms (Name a)          = [Name a]
subterms (Nonce n)         = [Nonce n]
subterms (Key k)           = [Key k]
subterms (AbsName a)       = [AbsName a]
subterms (AbsNonce n)      = [AbsNonce n]
subterms (AbsKey k)        = [AbsKey k]
subterms (PubKey a)        = [a, PubKey a]
subterms (Tuple ls)        = ls ++ concatMap subterms ls
subterms (Pair t1 t2)      = subterms t1 `L.union` subterms t2 `L.union` [Pair t1 t2]
subterms (Triple t1 t2 t3) = subterms t1 `L.union` subterms t2 `L.union` subterms t3 `L.union` [Triple t1 t2 t3]
subterms (Crypt a n)       = a:(subterms n) `L.union` [Crypt a n]
subterms (SCrypt k n)      = k:(subterms n) `L.union` [SCrypt k n]
subterms (Hash t)          = subterms t 

atomSubs :: Terms a -> [Terms a]
atomSubs trm = filter isAtomic (subterms trm)

isAtomic (Const n) = True
isAtomic (Name a) = True
isAtomic (Nonce n) = True
isAtomic (Key k) = True
isAtomic (AbsName a) = True
isAtomic (PubKey a) = True 
isAtomic (AbsNonce n) = True
isAtomic (AbsKey k) = True
isAtomic (Pair t1 t2) = False
isAtomic (Triple t1 t2 t3) = False
isAtomic (Crypt a n) = False
isAtomic (SCrypt k n) = False
isAtomic (Hash t) = False

isSubtermOf :: Term -> Term -> Bool
isSubtermOf t m = t `elem` subterms m

synthable ::  Term ->[Term] -> Bool 
synthable (Const n)         trms = (Const n) `elem` trms
synthable (Name a)          trms = (Name a) `elem` trms
synthable (Nonce n)         trms = (Nonce n) `elem` trms
synthable (Key k)           trms = (Key k) `elem` trms
synthable (Pair t1 t2)      trms = (Pair t1 t2) `elem` trms || (synthable t1 trms && synthable t2 trms)
synthable (Triple t1 t2 t3) trms = (Triple t1 t2 t3)`elem` trms || (synthable t1 trms && synthable t2 trms && synthable t3 trms)
synthable (Crypt a m)       trms = (Crypt a m)`elem` trms || (synthable a trms &&  synthable m trms)
synthable (SCrypt k m)      trms = (SCrypt k m)`elem` trms || (synthable k trms &&  synthable m trms)
synthable (Hash m)          trms = (Hash m)`elem` trms ||(synthable m trms)

-- e.g. recipe spyTerms ({A,n_A}_B, {alice, n0}_bob) = [({A,n_A}_B, {alice, n0}_bob)] if {alice,n0}_bob ∈ spyTerms and n0\not∈
recipe :: [Term] -> Mapping  -> [Mapping]   
recipe trms (ac, Const c)         = [(ac, Const c) | Const c `elem` trms] 
recipe trms (aa, Name a)          = [(aa, Name a) |Name a`elem` trms]
recipe trms (an, Nonce n)         = [(an, Nonce n) |Nonce n`elem` trms]
recipe trms (ak, Key k)           = [(ak, Key k) |Key k`elem` trms]
recipe trms (Pair a1 a2, Pair t1 t2) 
    | recipe trms (a1,t1) /= []  && recipe trms (a2,t2) /= [] = recipe trms (a1,t1) ++ recipe trms (a2,t2) 
    | otherwise = [] 
recipe trms (Triple a1 a2 a3, Triple t1 t2 t3) 
    | recipe trms (a1,t1) /= [] &&  recipe trms (a2,t2) /= [] && recipe trms (a3,t3) /= [] =  recipe trms (a1,t1) ++ recipe trms (a2,t2)++ recipe trms (a3,t3)
    | otherwise = [] 
recipe trms (Crypt aa am, Crypt a m)   
    | recipe trms (aa, a) /= [] &&  recipe trms (am, m) /= [] =  recipe trms (am, m) ++ recipe trms (aa, a)
    | Crypt a m `elem` trms = [(Crypt aa am, Crypt a m)] 
    | otherwise = [] 
recipe trms (SCrypt ak am, SCrypt k m)   
    | recipe trms (ak, k) /= [] &&  recipe trms (am, m) /= [] = recipe trms (ak, k) ++ recipe trms (am, m)  
    | SCrypt k m `elem` trms = [(SCrypt ak am, SCrypt k m)] 
    | otherwise = [] 
recipe trms (Hash am, Hash m)   
    | Hash m `elem` trms = [(Hash am, Hash m)] 
    | otherwise = recipe trms (am, m)

-- extract everything that can be extracted from Message wrt an agent
analz :: Name -> [Term] -> [Term]
analz   a hs =
    let inj xs = xs
        fst xs = [x | Pair x y <-xs]
              ++ [x | Triple x y z <-xs]
        snd xs = [y | Pair x y <-xs]
              ++ [y | Triple x y z <-xs]
        thd xs = [z | Triple x y z <-xs]
        dec xs = [x | Crypt a' x <- xs, a' == Name a]
        sdec xs = [x | SCrypt k x <- xs, k<-xs]
    in closure (inj `orf` fst `orf` snd `orf` thd `orf` dec  `orf` sdec) hs 


-- create the messages that can be constructed from what is known
-- synth :: [Term] -> [Term]
-- synth hs =
--     let inj xs = xs
--         crypt     :: [Term] -> [Term]
--         crypt xs   = [Crypt (Name a) x | x<-xs, PubKey (Name a)<-xs]
--         scrypt    :: [Term] -> [Term]
--         scrypt xs  = [SCrypt (Key (LKey i))  n | (Key (LKey i)) <-xs, n<-xs]
--         pair      :: [Term] -> [Term]
--         pair xs    = [Pair x y | x<-xs , y<-xs ]
--         triple    :: [Term] -> [Term]
--         triple xs  = [Triple x y z| x<-xs , y<-xs, z<-xs]
--     in (inj `orf` crypt `orf` scrypt `orf` pair `orf` triple) hs



match :: Map AbsTerm Term -> Map AbsTerm Term -> Bool  
match map1 map2 = and [(map1!k)==(map2!k) | k<-commonKeys] 
  where
    commonKeys = L.intersect (keys map1) (keys map2)  

frameDom :: [Mapping] -> [AbsTerm]  
frameDom frm = fst (unzip frm) 



