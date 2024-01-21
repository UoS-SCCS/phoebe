{-# LANGUAGE StandaloneDeriving, GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module LogicSyntax where
import Data.Tree               -- Use trees from Data.Tree module
import Data.Map (Map, (!), fromList, keys, elems, union, findWithDefault, empty, toList)
import qualified Data.Set as S
import qualified Data.List as L
import Debug.Trace
import Data.Maybe
import HelperFunctions
--
deriving instance Eq (Terms a)
type Var = String

data Terms a where
    -- Atomic Concrete Terms
    Const    :: Const -> Terms a
    Name     :: Name  -> Terms Grd
    Nonce    :: Int   -> Terms Grd
    Key      :: Key   -> Terms Grd
    Datum    :: Name  -> Terms Grd
    -- Atomic Abstract Terms
    AbsName  :: RoleName  -> Terms Abs
    AbsNonce :: NonceName -> Terms Abs 
    AbsKey   :: KeyName   -> Terms Abs 
    AbsDatum :: DatumName   -> Terms Abs 
    AbsList  :: Terms Abs -> Terms Abs
    -- Atomic Logic Terms
    VarAg    :: Var -> Terms Logic 
    VarName  :: Var -> Terms Logic
    VarKey   :: Var -> Terms Logic
    VarNonce :: Var -> Terms Logic
    Abs      :: Terms Abs -> Terms Logic
    Grd      :: Terms Grd -> Terms Logic
    -- Additional Abstract Terms
    Self     :: Terms Abs        
    Role     :: RoleName  -> Terms Abs
    Session  :: Terms Abs
    -- Constructors
    Tuple    :: [Terms Grd] -> Terms Grd           -- for whitelists
    PubKey   :: Terms a -> Terms a
    PrivKey  :: Terms a -> Terms a
    Pair     :: Terms a -> Terms a -> Terms a
    Triple   :: Terms a -> Terms a -> Terms a -> Terms a
    Crypt    :: Terms a -> Terms a -> Terms a
    SCrypt   :: Terms a -> Terms a -> Terms a
    Hash     :: Terms a -> Terms a
    Mac      :: Terms a -> Terms a -> Terms a
    -- Undeciph Destructors 
    -- (owner is not necessary as we modelled public key encryption with Crypt a m not Crypt (pub(a)) m) 
    Proj1    :: Terms Grd -> Terms Grd
    Proj2    :: Terms Grd -> Terms Grd
    Proj3    :: Terms Grd -> Terms Grd
    DCrypt   :: Terms Grd -> Terms Grd
    DSCrypt  :: Terms Grd -> Terms Grd
    DHash    :: Terms Grd -> Terms Grd

-- one may find a better way to do this
unGrd :: LogicTerm -> Term
unGrd (Grd a) = a 
unGrd (Const a) = Const a 
unGrd (PubKey a) = PubKey (unGrd a) 
unGrd (Pair t1 t2) = Pair (unGrd t1) (unGrd t2)
unGrd (Triple t1 t2 t3) = Triple (unGrd t1) (unGrd t2) (unGrd t3)
unGrd (Crypt a m) = Crypt (unGrd a) (unGrd m)
unGrd (SCrypt k m) = SCrypt (unGrd k) (unGrd m)
unGrd (Hash m) = Hash (unGrd m)
unGrd (Mac k m) = Mac (unGrd k) (unGrd m) 

-- | we could have used these atoms directly in Terms a, by defining 
-- CTerm :: Grd -> Terms Grd
-- ATerm :: Abs -> Term Abs
-- but CTerm and ATerm become cumbersome
--
type Term = Terms Grd -- ^ \[ \mathcal{T}(F, T_0) \]
type AbsTerm = Terms Abs -- ^ \[ \mathcal{T}(F, \mathcal{V}) \]
type LogicTerm = Terms Logic -- ^ \[ \mathcal{T}(F, \mathcal{X}) \]

type Nonce = Int

data Name = Alice | Bob | Charlie | Tag Int | Reader Int | Device Int | Server Int | Spy  
    deriving (Eq, Ord)

data DatumName = JoinEUI | DevEUI 
    deriving (Eq, Ord, Show)

data Key = LKey Int | SsKey Int | LShared Name Name
    deriving (Eq, Ord)

data RoleName = A | B | C | T | R | DY | D | S-- ^$\mathcal{R}$
    deriving (Eq, Show, Ord)

data NonceName = NA | NB | NC | N | NT | NR | ND | DevNonce | JoinNonce-- ^$\mathcal{N}$
    deriving (Eq, Show, Ord)

data KeyName = KK | KT | NwkKey | DevAddr | DData-- ^$\mathcal{K}$
    deriving (Eq, Show, Ord)

data Grd = CName Name | CNonce Int | CKey Key                -- dummy data type
data Abs = AName RoleName | ANonce NonceName | AbKey KeyName -- dummy data type
data Logic = Logic 
type Const = Int
deriving instance Ord (Terms a)

type Mapping = (AbsTerm, Term)

-- | δ(f(t)) = f(δ(t)) in logic terms
tLiftDelta :: Map LogicTerm LogicTerm -> LogicTerm -> LogicTerm 
tLiftDelta frm (VarKey k)        = (frm!(VarKey k))
tLiftDelta frm (VarNonce k)      = (frm!(VarNonce k))
tLiftDelta frm (VarName a)       = (frm!(VarName a))
tLiftDelta frm (VarAg x)         = (frm!(VarAg x))
tLiftDelta frm (Grd a)           = Grd a
tLiftDelta frm (PubKey k)        = PubKey (tLiftDelta frm k)
tLiftDelta frm (Pair t1 t2)      = Pair (tLiftDelta frm t1) (tLiftDelta frm t2)
tLiftDelta frm (Triple t1 t2 t3) = Triple (tLiftDelta frm t1) (tLiftDelta frm t2) (tLiftDelta frm t3)
tLiftDelta frm (Crypt a m)       = Crypt (tLiftDelta frm a) (tLiftDelta frm m)
tLiftDelta frm (SCrypt k m)      = SCrypt (tLiftDelta frm k) (tLiftDelta frm m)
tLiftDelta frm (Mac k m)         = Mac (tLiftDelta frm k) (tLiftDelta frm m)
tLiftDelta frm (Hash m)          = Hash (tLiftDelta frm m)

-- | σ(f(t)) = f(σ(t)) in logics
tLiftSigma :: Map LogicTerm LogicTerm -> LogicTerm -> LogicTerm 
tLiftSigma frm (Abs a)           = frm!(Abs a)
tLiftSigma frm (VarKey k)        = (VarKey k)
tLiftSigma frm (VarNonce k)      = (VarNonce k)
tLiftSigma frm (VarName a)       = (VarName a)
tLiftSigma frm (VarAg x)         = (VarAg x)
tLiftSigma frm (Grd a)           = Grd a
tLiftSigma frm (PubKey k)        = PubKey (tLiftSigma frm k)
tLiftSigma frm (Pair t1 t2)      = Pair (tLiftSigma frm t1) (tLiftSigma frm t2)
tLiftSigma frm (Triple t1 t2 t3) = Triple (tLiftSigma frm t1) (tLiftSigma frm t2) (tLiftSigma frm t3)
tLiftSigma frm (Crypt a m)       = Crypt (tLiftSigma frm a) (tLiftSigma frm m)
tLiftSigma frm (SCrypt k m)      = SCrypt (tLiftSigma frm k) (tLiftSigma frm m)
tLiftSigma frm (Hash m)          = Hash (tLiftSigma frm m)
tLiftSigma frm (Mac k m)          = Mac (tLiftSigma frm k) (tLiftSigma frm m)

-- | σ(f(t)) = f(σ(t)) in protocol semantics
tLift :: Map (Terms a) Term -> Terms a -> Term 
tLift frm (Const n)                         = Const n
tLift frm (AbsNonce n)                    = frm!(AbsNonce n)
tLift frm (AbsName a)                     = frm!(AbsName a)
tLift frm (AbsKey k)                      = frm!(AbsKey k)
tLift frm (AbsDatum d)                    = frm!(AbsDatum d)
tLift frm (Nonce n)                         = (Nonce n)
tLift frm (Datum d)                         = (Datum d)
tLift frm (Name a)                          = (Name a)
tLift frm (Key k)                           = (Key k)
tLift frm (PubKey k)                        = PubKey (tLift frm k)
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
tLift frm (Mac k m)
   | (Mac k m) `elem` (keys frm)            = frm!(Mac k m)
   | otherwise                              = Mac (frm!k) (tLift frm m)

subterms :: Terms a -> [Terms a]
subterms (Const n)         = [Const n]
subterms (Datum a)         = [Datum a]
subterms (Name a)          = [Name a]
subterms (Nonce n)         = [Nonce n]
subterms (Key k)           = [Key k]
subterms (AbsName a)       = [AbsName a]
subterms (AbsNonce n)      = [AbsNonce n]
subterms (AbsKey k)        = [AbsKey k]
subterms (AbsDatum d)        = [AbsDatum d]
subterms (PubKey a)        = [a, PubKey a]
subterms (Tuple ls)        = ls ++ concatMap subterms ls
subterms (Pair t1 t2)      = subterms t1 `L.union` subterms t2 `L.union` [Pair t1 t2]
subterms (Triple t1 t2 t3) = subterms t1 `L.union` subterms t2 `L.union` subterms t3 `L.union` [Triple t1 t2 t3]
subterms (Crypt a n)       = a:(subterms n) `L.union` [Crypt a n]
subterms (SCrypt k n)      = k:(subterms n) `L.union` [SCrypt k n]
subterms (Hash t)          = subterms t 
subterms (Mac k t)          = k:(subterms t) 

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
isAtomic (AbsDatum d) = True
isAtomic (Pair t1 t2) = False
isAtomic (Triple t1 t2 t3) = False
isAtomic (Crypt a n) = False
isAtomic (SCrypt k n) = False
isAtomic (Hash t) = False
isAtomic (Mac k t) = False

isSubtermOf :: Term -> Term -> Bool
isSubtermOf t m = t `elem` subterms m

synthable ::  Term ->[Term] -> Bool 
synthable (Const n)         trms = (Const n) `elem` trms
synthable (Name a)          trms = (Name a) `elem` trms
synthable (Datum d)         trms = (Datum d) `elem` trms
synthable (Nonce n)         trms = (Nonce n) `elem` trms
synthable (Key k)           trms = (Key k) `elem` trms
synthable (Pair t1 t2)      trms = (Pair t1 t2) `elem` trms || (synthable t1 trms && synthable t2 trms)
synthable (Triple t1 t2 t3) trms = (Triple t1 t2 t3)`elem` trms || (synthable t1 trms && synthable t2 trms && synthable t3 trms)
synthable (Crypt a m)       trms = (Crypt a m)`elem` trms || (synthable a trms &&  synthable m trms)
synthable (SCrypt k m)      trms = (SCrypt k m) `elem` trms || (synthable k trms &&  synthable m trms)
synthable (Mac k m)         trms = (Mac k m) `elem` trms || (synthable k trms &&  synthable m trms)
synthable (Hash m)          trms = (Hash m) `elem` trms ||(synthable m trms)

-- e.g. recipe spyTerms ({A,n_A}_B, {alice, n0}_bob) = [({A,n_A}_B, {alice, n0}_bob)] if {alice,n0}_bob ∈ spyTerms and n0\not∈
recipe :: [Term] -> Mapping  -> [Mapping]   
recipe trms (ac, Const c)         = [(ac, Const c) | Const c `elem` trms] 
recipe trms (aa, Name a)          = [(aa, Name a) |Name a`elem` trms]
recipe trms (ad, Datum d)         = [(ad, Datum d) |Datum d`elem` trms]
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
recipe trms (Mac ak am, Mac k m)   
    | recipe trms (ak, k) /= [] &&  recipe trms (am, m) /= [] = recipe trms (ak, k) ++ recipe trms (am, m)  
    | Mac k m `elem` trms = [(Mac ak am, Mac k m)] 
    | otherwise = [] 

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


match :: Map AbsTerm Term -> Map AbsTerm Term -> Bool  
match map1 map2 = and [(map1!k)==(map2!k) | k<-commonKeys] 
  where
    commonKeys = L.intersect (keys map1) (keys map2)  

frameDom :: [Mapping] -> [AbsTerm]  
frameDom frm = fst (unzip frm) 
--
-- =========================== PROTOCOL SYNTAX =============================
--
data Agent = Agent    
    { _name  :: Name
    , _sess  :: Maybe Int
    , _role  :: Maybe RoleName
    , _id    :: Int
    , _iniTerms :: [Term]  
    , _iniFrame :: [Mapping] 
    , _indistActions :: [[Action]] 
    }
    deriving (Eq, Ord) 

data ProtocolSpec = ProtocolSpec 
    { _spy::Agent
    , _honestAgents::[Agent]
    , _actions::[Action]
    , _roles::[RoleName]
    , _protName::String
    }

data Action 
    = Send Int RoleName Stmt        [AbsTerm] AbsTerm
    | Rec  Int RoleName (Stmt,Stmt)           AbsTerm
    deriving (Eq, Ord) 

-- =========================== LOGIC SYNTAX =============================
--

data IndexTerm = UAg Agent |  UVarAg Var | UVarName Var | UName Name | UAbsName RoleName
    deriving (Eq, Ord) 
  

data Stmt 
    = BConst Bool
    | GEq LogicTerm LogicTerm -- greater or equal to for nonces
    | Has IndexTerm LogicTerm
    | Listed IndexTerm LogicTerm
    | EqI IndexTerm IndexTerm -- equality of index terms
    | Link IndexTerm (AbsTerm, LogicTerm) 
    | Conj [Stmt] 
    | Disj [Stmt] 
    | Imp Stmt Stmt
    | Neg Stmt
    | K IndexTerm Stmt
    | F Stmt
    | P Stmt
    | EndHas IndexTerm LogicTerm
    | EndLink IndexTerm (AbsTerm, LogicTerm) 
    | ExistsAg LogicTerm Stmt
    | ForAllAg LogicTerm Stmt
    | ExistsHonestAg LogicTerm Stmt
    | ForAllHonestAg LogicTerm Stmt
    | ExistsKey LogicTerm Stmt
    | ForAllKey LogicTerm Stmt
    | ExistsName LogicTerm Stmt
    | ForAllName LogicTerm Stmt
    | ExistsNonce LogicTerm Stmt
    | ForAllNonce LogicTerm Stmt
    deriving (Eq, Ord) 

nEqI :: IndexTerm -> IndexTerm -> Stmt
nEqI a b = Neg (EqI a b) 

geq :: LogicTerm -> LogicTerm -> Stmt 
geq t t' = GEq t t'
infixl 4 ≥
(≥) = geq 

conj :: Stmt -> Stmt -> Stmt
conj f g = Conj [f,g]
infixl 5 ∧
(∧) = conj

inl :: LogicTerm -> IndexTerm -> Stmt
inl t u = Listed u t
(∈) = inl

disj :: Stmt -> Stmt -> Stmt
disj f g = Disj [f,g]
infixl 6 ∨
(∨) = disj

imp :: Stmt -> Stmt -> Stmt
imp f g = Imp f g
(⇒) = imp


forAllHonest :: [LogicTerm] -> Stmt -> Stmt 
forAllHonest [v] f = ForAllHonestAg v f
forAllHonest (v:vs) f = ForAllHonestAg v (forAllHonest vs f) 

forAllAg :: [LogicTerm] -> Stmt -> Stmt 
forAllAg [v] f = ForAllAg v f
forAllAg (v:vs) f = ForAllAg v (forAllAg vs f) 

forAllName :: [LogicTerm] -> Stmt -> Stmt 
forAllName [v] f = ExistsName v f
forAllName (v:vs) f = ExistsName v (forAllName vs f) 

existsHonest :: [LogicTerm] -> Stmt -> Stmt 
existsHonest [v] f = ExistsHonestAg v f
existsHonest (v:vs) f = ExistsHonestAg v (existsHonest vs f) 

existsName :: [LogicTerm] -> Stmt -> Stmt 
existsName [v] f = ExistsName v f
existsName (v:vs) f = ExistsName v (existsName vs f) 

existsKey :: [LogicTerm] -> Stmt -> Stmt 
existsKey [v] f = ExistsKey v f
existsKey (v:vs) f = ExistsKey v (existsKey vs f) 

existsNonce :: [LogicTerm] -> Stmt -> Stmt 
existsNonce [v] f = ExistsNonce v f
existsNonce (v:vs) f = ExistsNonce v (existsNonce vs f) 

existsAg :: [LogicTerm] -> Stmt -> Stmt 
existsAg [v] f = ExistsAg v f
existsAg (v:vs) f = ExistsAg v (existsAg vs f) 

true = BConst True
false = BConst False
trues = (true,true) 

-- ======  Useful formulas for expressing privacy properties ================
-- agent ag plays role r or some agent named a plays role of r

plays :: IndexTerm -> RoleName -> Stmt 
plays (UAg ag) r  = (Link (UAg ag) (Role r, Grd (Name (_name ag))))
plays (UName a) r = (Link (UName a) (Role r, Grd (Name a))) 
plays (UVarAg x) r = (Link (UVarAg x) (Role r, VarAg x))
plays (UVarName x) r = (Link (UVarName x) (Role r, (VarName x)))

-- the agent x | the r-agent is named a
named :: IndexTerm -> LogicTerm -> Stmt
named u (Grd (Name a)) = Link u (Self, Grd (Name a)) 
named u (VarAg x) = Link u (Self, VarAg x) 
named u (VarName a) = Link u (Self, VarName a) 

-- | a house keeping function to convert a term into a uterm
-- not that every uterm is mapped to an agent, not to a name
-- the agent in question is supplied as argument, it is the agent
-- that is going to do the send or receive
uName :: LogicTerm -> IndexTerm
uName (Grd (Name a)) = UName a 

sigmaLift :: (Map LogicTerm LogicTerm, Map IndexTerm Agent) -> Stmt -> Stmt 
sigmaLift subs@(sigma,sigmaAg) (BConst b)                    = BConst b
sigmaLift subs@(sigma,sigmaAg) (GEq (Abs (AbsNonce n)) n')         = sigmaLift subs (GEq (sigma!Abs (AbsNonce n)) n')
sigmaLift subs@(sigma,sigmaAg) (GEq n' (Abs (AbsNonce n)))         = sigmaLift subs (GEq n' (sigma!Abs (AbsNonce n)))
sigmaLift subs@(sigma,sigmaAg) (GEq n n')                          = GEq n n'
sigmaLift subs@(sigma,sigmaAg) (EqI (UVarAg a) (UVarAg b))         = sigmaLift subs (EqI (UAg (sigmaAg!UVarAg a)) (UAg (sigmaAg!UVarAg b)))
sigmaLift subs@(sigma,sigmaAg) (EqI (UAg a) (UAg b))         = EqI (UAg a) (UAg b)
sigmaLift subs@(sigma,sigmaAg) (Has (UAbsName a) t)          = Has (uName (sigma!Abs (AbsName a))) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (Link (UAbsName a) (at,t))    = Link (UAg (sigmaAg!(UAbsName a))) (at, (tLiftSigma sigma t))
sigmaLift subs@(sigma,sigmaAg) (Listed (UAbsName a) t)       = Listed (UAg (sigmaAg!UAbsName a)) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndHas (UAbsName a) t)       = EndHas (uName (sigma!Abs (AbsName a))) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndLink (UAbsName a) (at,t)) = EndLink (UAg (sigmaAg!(UAbsName a))) (at, tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (K (UVarAg x) f)              = (K (UVarAg x) f)              
sigmaLift subs@(sigma,sigmaAg) (Has (UVarAg x) t)            = (Has (UVarAg x) t)            
sigmaLift subs@(sigma,sigmaAg) (Link (UVarAg x) (at,t))      = (Link (UVarAg x) (at,t))      
sigmaLift subs@(sigma,sigmaAg) (Listed (UVarAg x) t)         = (Listed (UVarAg x) t)         
sigmaLift subs@(sigma,sigmaAg) (EndHas (UVarAg x) t)         = (EndHas (UVarAg x) t)         
sigmaLift subs@(sigma,sigmaAg) (EndLink (UVarAg x) (at,t))   = (EndLink (UVarAg x) (at,t))   
sigmaLift subs@(sigma,sigmaAg) (K (UVarName x) f)            = (K (UVarName x) f)            
sigmaLift subs@(sigma,sigmaAg) (Has (UVarName x) t)          = (Has (UVarName x) t)          
sigmaLift subs@(sigma,sigmaAg) (Link (UVarName x) (at,t))    = (Link (UVarName x) (at,t))    
sigmaLift subs@(sigma,sigmaAg) (EndHas (UVarName x) t)       = (EndHas (UVarName x) t)       
sigmaLift subs@(sigma,sigmaAg) (EndLink (UVarName x) (at,t)) = (EndLink (UVarName x) (at,t)) 
sigmaLift subs@(sigma,sigmaAg) (Listed (UVarName x) t)       = (Listed (UVarName x) t)       
sigmaLift subs@(sigma,sigmaAg) (Conj fs)                     = Conj (map (sigmaLift subs) fs)
sigmaLift subs@(sigma,sigmaAg) (Disj fs)                     = Disj (map (sigmaLift subs) fs)
sigmaLift subs@(sigma,sigmaAg) (Imp f g)                     = Imp (sigmaLift subs f) (sigmaLift subs g)
sigmaLift subs@(sigma,sigmaAg) (Neg f)                       = Neg (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (Has (UName a) t)             = Has (UName a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (Link (UName a) (at,t))       = Link (UName a) (at, tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndHas (UName a) t)          = EndHas (UName a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndLink (UName a) (at,t))    = EndLink (UName a) (at, tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (Listed (UName a) t)          = Listed (UName a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (K (UName a) t)               = K (UName a) (sigmaLift subs t)
sigmaLift subs@(sigma,sigmaAg) (Has (UAg a) t)               = Has (UAg a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (Link (UAg a) (at,t))         = Link (UAg a) (at, tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndHas (UAg a) t)            = EndHas (UAg a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (EndLink (UAg a) (at,t))      = EndLink (UAg a) (at, tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (Listed (UAg a) t)            = Listed (UAg a) (tLiftSigma sigma t)
sigmaLift subs@(sigma,sigmaAg) (K (UAg a) f)                 = K (UAg a) (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (P f)                         = P (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (F f)                         = F (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ExistsKey x f)               = ExistsKey x (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ForAllKey x f)               = ForAllKey x (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ExistsNonce x f)               = ExistsNonce x (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ForAllNonce x f)               = ForAllNonce x (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ExistsName x f)              = ExistsName x (sigmaLift subs f)
sigmaLift subs@(sigma,sigmaAg) (ForAllName x f)              = ForAllName x (sigmaLift subs f)


deltaLift :: (Map LogicTerm LogicTerm, Map IndexTerm Agent) -> Stmt -> Stmt 
deltaLift subs@(delta,deltaAg) (BConst b)                    = BConst b
deltaLift subs@(delta,deltaAg) (GEq (VarNonce n) n')          = deltaLift subs (GEq (delta!VarNonce n) n')
deltaLift subs@(delta,deltaAg) (GEq n' (VarNonce n))    = deltaLift subs (GEq n' (delta!VarNonce n))
deltaLift subs@(delta,deltaAg) (GEq n n')                          = GEq n n'
deltaLift subs@(delta,deltaAg) (EqI (UVarAg a) (UVarAg b))         = deltaLift subs (EqI (UAg (deltaAg!UVarAg a)) (UAg (deltaAg!UVarAg b)))
deltaLift subs@(delta,deltaAg) (EqI (UAg a) (UAg b))         = EqI (UAg a) (UAg b)
deltaLift subs@(delta,deltaAg) (K (UVarAg x) f)              = K (UAg (deltaAg!UVarAg x)) (deltaLift subs f)
deltaLift subs@(delta,deltaAg) (Has (UVarAg x) t)            = Has (UAg (deltaAg!UVarAg x)) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Link (UVarAg x) (at,t))      = Link (UAg (deltaAg!UVarAg x) ) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Listed (UVarAg x) t)         = Listed (UAg (deltaAg!UVarAg x) ) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndHas (UVarAg x) t)         = EndHas (UAg (deltaAg!UVarAg x)) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndLink (UVarAg x) (at,t))   = EndLink (UAg (deltaAg!UVarAg x) ) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (K (UVarName x) f)            = K (uName (delta!VarName x)) (deltaLift subs f)
deltaLift subs@(delta,deltaAg) (Has (UVarName x) t)          = Has (uName (delta!VarName x)) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Link (UVarName x) (at,t))    = Link (uName (delta!VarName x) ) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndHas (UVarName x) t)       = EndHas (uName (delta!VarName x)) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndLink (UVarName x) (at,t)) = EndLink (uName (delta!VarName x) ) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Listed (UVarName x) t)       = Listed (uName (delta!VarName x) ) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Conj fs)                     = Conj (map (deltaLift subs) fs)
deltaLift subs@(delta,deltaAg) (Disj fs)                     = Disj (map (deltaLift subs) fs)
deltaLift subs@(delta,deltaAg) (Imp f g)                     = Imp (deltaLift subs f) (deltaLift subs g)
deltaLift subs@(delta,deltaAg) (Neg f)                       = Neg (deltaLift subs f)
deltaLift subs@(delta,deltaAg) (Has (UName a) t)             = Has (UName a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Link (UName a) (at,t))       = Link (UName a) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndHas (UName a) t)          = EndHas (UName a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndLink (UName a) (at,t))    = EndLink (UName a) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Listed (UName a) t)          = Listed (UName a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (K (UName a) t)               = K (UName a) (deltaLift subs t)
deltaLift subs@(delta,deltaAg) (Has (UAg a) t)               = Has (UAg a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Link (UAg a) (at,t))         = Link (UAg a) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndHas (UAg a) t)            = EndHas (UAg a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (EndLink (UAg a) (at,t))      = EndLink (UAg a) (at, tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (Listed (UAg a) t)            = Listed (UAg a) (tLiftDelta delta t)
deltaLift subs@(delta,deltaAg) (K (UAg a) f)                 = K (UAg a) (deltaLift subs f)
deltaLift subs@(delta,deltaAg) (P f)                         = P (deltaLift subs f)
deltaLift subs@(delta,deltaAg) (F f)                         = F (deltaLift subs f)

deriving instance Show Stmt
deriving instance Show IndexTerm

instance Show Agent 
  where
    show ag 
      | _name ag == Spy = show (_name ag) 
      | otherwise = "(" ++ show (_name ag) ++ "," ++ show (fromJust $ _role ag) ++ "," ++ show (fromJust $ _sess ag) ++"," ++show (_iniTerms ag) ++ ")"

wlist :: Agent -> Term
wlist ag =  findWithDefault (Tuple [])  (AbsList Self) (fromList (_iniFrame ag)) 

instance Show (Terms a)
  where
    show (Grd a) = "Grd" ++ show a
    show (Session) = "Sess" 
    show (Abs a) = "Abs" ++show a
    show (Const a) = show a
    show (Datum a) = show a
    show (Name a) = show a
    show (Nonce n) = "n"++show n
    show (VarAg x) = show x
    show (VarKey x) = show x
    show (VarNonce x) = show x
    show (VarName x) = show x
    show (Key (SsKey k)) = "kk"++show k
    show (Key (LKey k)) = "k"++show k
    show (Key (LShared a b)) = "k_"++show a++show b++ ""
    show (AbsName a) = show a
    show (AbsNonce n) = show n
    show (AbsKey k) = show k
    show (AbsDatum d) = show d
    show (AbsList a) = "S"++show a
    show (Role a) = "η"++show a
    show (Self) = "Self"
    show (Tuple ts) = "{"++showListC ts++"}"
    show (PubKey a) = "k"++show a
    show (PrivKey a) = "k*"++show a
    show (Pair m m') = "⟨"++show m++","++show m'++"⟩"
    show (Triple m n p) = "⟨"++show m++","++show n++","++show p++"⟩"
    show (Crypt a m) = "{"++show m++"}_"++show a
    show (SCrypt k m) = "⦃"++show m++"⦄_"++show k
    show (Hash m) = "hash("++show m++")" 
    show (Mac k m) = "mac("++show m++";" ++ show k ++ ")" 
    show (DCrypt m) = "DCrypt("++show m++")"
    show (DSCrypt m) = "DSCrypt("++show m++")"
    show (DHash m) = "DHash("++show m++")" 
    show (Proj1 m) = "Proj1("++show m++")" 
    show (Proj2 m) = "Proj2("++show m++")" 
    show (Proj3 m) = "Proj3("++show m++")" 
    
instance Show Name 
  where
    show Alice = "a"
    show Bob = "b"
    show Charlie = "c"
    show Spy = "i"
    show (Tag i) = "t"++show i
    show (Reader i) = "r"++show i
    show (Server i) = "s"++show i
    show (Device i) = "d"++show i

instance Show Key 
  where
    show (LKey i) = show i
    show (SsKey i) = show i
