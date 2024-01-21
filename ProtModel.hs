{-# LANGUAGE StandaloneDeriving, GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module ProtModel where
import Data.Tree               -- Use trees from Data.Tree module
import Data.Map (Map, (!), fromList, keys, elems, union, findWithDefault, empty, toList, filterWithKey)
import qualified Data.Set as S
import qualified Data.List as L
import Debug.Trace
import Data.Maybe
import HelperFunctions
-- import Terms
import LogicSyntax

data Event 
    = ESend Int (RoleName, Agent) [Mapping] Mapping 
    | ERec  Int (RoleName, Agent) [Mapping] Mapping
    deriving (Eq, Ord) 

type Trace = [Event] 


countSessions :: RoleName -> Trace -> Int
countSessions r tr = length [ESend 1 (ag,r) ms m | ESend 1 (ag,r) ms m <- tr] `max` length [ERec 1 (ag,r) ms m | ERec 1 (ag,r) ms m <- tr]

enabledEvents :: ProtocolSpec -> Action -> Trace -> [Event] 
enabledEvents prot (Send i r phi pts pt) tr = 
    concat [ (enabledESend ag (Send i r phi pts pt) tr) 
           | ag <- _honestAgents prot    
           , filterTrace prot tr ag -- constant whitelist, bounding sessions, reducing by symmetries 
           , _role ag == Just r
           , step (Just r) ag tr == (i-1)
           -- , let sigma = fromList (links ag tr)
           , let sigma = fromList (frame ag tr)
           , let maxSessR = maximum (0:[fromJust (_sess ag') | (ESend 1 (r, ag') maps map) <- tr , r == fromJust (_role ag)]) 
           , if i==1 then ((maxSessR + 1) == fromJust (_sess ag)) else True
           , truth0Abs (prot,tr) (abs2logic sigma,map1 (UAbsName r) ag) phi
           ]
        
enabledEvents prot (Rec i r phis pt) tr = 
    concat [  enabledERec prot (ag,_spy prot) (Rec i r phis pt) tr 
           | ag <- _honestAgents prot
           , filterTrace prot tr ag 
           , let maxSessR = maximum (0:[fromJust (_sess ag') | (ERec 1 (r, ag') maps map) <- tr , r == fromJust (_role ag)]) 
           , if i==1 then ((maxSessR + 1) == fromJust (_sess ag)) else True
           , _role ag == Just r
           , step (Just r) ag tr == (i-1)
           ]

-- =============== ESend Update =====================
enabledESend :: Agent -> Action -> Trace -> [Event]
enabledESend ag (Send i r phi pts pt) tr =
    -- [ ESend i (r, ag) freshmaps (pt, msg) | atomSubs pt `isSublistOf` frameDom (freshmaps `L.union` links ag tr)]
    [ ESend i (r, ag) freshmaps (pt, msg) | atomSubs pt `isSublistOf` frameDom (freshmaps `L.union` frame ag tr)]
      where
        -- Prelude.map applies a function to a list argument, returns a list of image
        freshmaps = Prelude.map (makeFreshMap ag tr) pts  
        -- msg = tLift (fromList (freshmaps `L.union` links ag tr)) pt
        msg = tLift (fromList (freshmaps `L.union` frame ag tr)) pt

-- possSigmaImages take atomic subterms of the prot term 
-- and all atomic subterms of subs(trms) not necessary in analz(trms) 
-- WELL TYPED SIGMAS
possSigmaImages :: AbsTerm -> [Term] -> [Term]  
possSigmaImages (AbsName r) trms  = L.nub [Name a | Name a <- concatMap subterms trms]
possSigmaImages (AbsNonce r) trms = L.nub [Nonce n | Nonce n <- concatMap subterms trms]
possSigmaImages (AbsKey pk) trms  = L.nub [Key k | Key k <- concatMap subterms trms]
possSigmaImages (AbsDatum pk) trms  = L.nub [Name d | Name d <- concatMap subterms trms]

makeFreshMap :: Agent -> Trace -> AbsTerm -> Mapping 
makeFreshMap ag tr (AbsNonce n) = (AbsNonce n, Nonce (maxNonceTrace tr + 1))
makeFreshMap ag tr (AbsKey sk)  = (AbsKey sk, Key (SsKey (maxSsKeyTrace tr + 1)))
----------------------------------------------------


-- =============== EReceive Update =====================
enabledERec :: ProtocolSpec -> (Agent,Agent) -> Action -> Trace -> [Event]
enabledERec prot (ag,spy) (Rec i r (pre,post) pt) tr = 
    [
    ERec i (r, ag) (filter (\x -> isAtomic (fst x) && not (x `elem` spyFrame)) (recipe spyTerms (pt,msg))) (pt, msg) -- know if the spy prepared it
    | let freshSpy = [Nonce (maxNonceTrace tr + 1), Key (SsKey (maxSsKeyTrace tr + 1))] 
    -- , let spyTerms = sees spy tr ++ freshSpy
    -- , let spyFrame = links spy tr
    , let spyTerms = terms spy tr ++ freshSpy
    , let spyFrame = frame spy tr
    , injectList  <- buildSigmas (atomSubs pt) spyTerms
    , let msg      = tLift (fromList injectList) pt
    -- , let frameAg  = fromList (links ag tr)
    , let frameAg  = fromList (frame ag tr)
    , let inSigma  = fromList injectList
    , let sigma    = (inSigma `union` frameAg)  -- union prefer the left when the two overlaps, so we put inSigma fresh terms on the left
    , match inSigma frameAg
    , suitable prot inSigma
    , synthable msg spyTerms                            -- taking advantage of well-typed sigmas
    , (truth0Abs (prot, tr) (abs2logic sigma, map1 (UAbsName r) ag) pre)
    , (truth0Abs (prot, tr++[ERec i (r,ag) [] (pt, msg)] ) (abs2logic sigma, map1 (UAbsName r) ag) post)
    -- , msg `elem` synth(synth ... (synth spyTerms))    -- computing synth closure is costly
    ] 

-- convert the types in mappings, (AbsTerm, Term) 
abs2logic :: Map AbsTerm Term -> Map LogicTerm LogicTerm
abs2logic map = 
  let lmap = toList map
      in fromList ([(Abs at, Grd t) | (at,t) <- lmap]) 
  

-- | this ensures distinct names are mapped to distinct names (only role names)  
-- note that B in PrivAuth is a name but not a role name, one can have σ(B)=σ(C) 
-- distinct nonce to distinct nonces
-- distinct keys to distinctkeys 
suitable :: ProtocolSpec -> Map AbsTerm Term -> Bool
suitable prot mp 
     = True
    && length (filterWithKey (\k _ -> k `elem` nameTerms) mp)  == length nameTerms 
    && length (filterWithKey (\k _ -> k `elem` nonceTerms) mp)  == length nonceTerms 
    && length (filterWithKey (\k _ -> k `elem` keyTerms) mp)  == length keyTerms 
    -- && length (L.nub [mp!t | t <- nonceTerms]) == length nonceTerms
    -- && length (L.nub [mp!t | t <- nameTerms])  == length nameTerms 
    -- && length (L.nub [mp!t | t <- keyTerms])   == length keyTerms 
    -- && length (L.nub [mp!t | t <- dataTerms])   == length dataTerms 
      where
        nonceTerms = [AbsNonce n |AbsNonce n <- keys mp] 
        -- dataTerms = [AbsDatum n |AbsDatum n <- keys mp] 
        nameTerms  = [AbsName a |AbsName a <- keys mp , a `elem` _roles prot] 
        keyTerms   = [AbsKey k |AbsKey k <- keys mp] 

buildSigmas :: [AbsTerm] -> [Term] -> [[(AbsTerm,Term)]]
buildSigmas subs spyTerms = L.nub [(zip subs sigmaImage) | sigmaImage <- sigmaImages]
  where
    sigmaImages = combinations [possSigmaImages pt spyTerms | pt <- subs]  
----------------------------------------------------


maxNonceTrace :: Trace -> Int
maxNonceTrace s = 
    max (maximum (0:[maxNonceTrace' m | ESend n a ms (pm, m) <- s])) 
        (maximum (0:[maxNonceTrace' m | ERec  n a st (pm, m) <- s]))
  where
    maxNonceTrace' :: Term -> Int
    maxNonceTrace' (Nonce n)         = n
    maxNonceTrace' (Name a)          = 0
    maxNonceTrace' (Datum d)         = 0
    maxNonceTrace' (Key k)           = 0
    maxNonceTrace' (PubKey a)        = 0
    maxNonceTrace' (Pair m m')       = max (maxNonceTrace' m) (maxNonceTrace' m')
    maxNonceTrace' (Triple m m' m'') = maximum [maxNonceTrace' m, maxNonceTrace' m', maxNonceTrace' m'']
    maxNonceTrace' (Crypt a m)       = maxNonceTrace' m
    maxNonceTrace' (SCrypt k m)      = max (maxNonceTrace' k) (maxNonceTrace' m)
    maxNonceTrace' (Hash m)          = maxNonceTrace' m
    maxNonceTrace' (Mac k m)         = max (maxNonceTrace' k) (maxNonceTrace' m)

maxSsKeyTrace :: Trace -> Int
maxSsKeyTrace s = maximum (0:[maxSsKeyTrace' m | ESend n a ms (pm, m) <- s]) 
  where
    maxSsKeyTrace' :: Term -> Int
    maxSsKeyTrace' (Key (SsKey n))   = n
    maxSsKeyTrace' (Key _)           = 0
    maxSsKeyTrace' (Nonce n)         = 0
    maxSsKeyTrace' (Datum d)         = 0
    maxSsKeyTrace' (PubKey a)        = 0
    maxSsKeyTrace' (Name a)          = 0
    maxSsKeyTrace' (Pair m m')       = max (maxSsKeyTrace' m) (maxSsKeyTrace' m')
    maxSsKeyTrace' (Triple m m' m'') = maximum [maxSsKeyTrace' m, maxSsKeyTrace' m', maxSsKeyTrace' m'']
    maxSsKeyTrace' (Crypt a m)       = maxSsKeyTrace' m
    maxSsKeyTrace' (SCrypt k m)      = max (maxSsKeyTrace' k) (maxSsKeyTrace' m)
    maxSsKeyTrace' (Hash m)          = maxSsKeyTrace' m
    maxSsKeyTrace' (Mac k m)         = max (maxSsKeyTrace' k) (maxSsKeyTrace' m)

filterTrace :: ProtocolSpec -> Trace ->  Agent -> Bool
filterTrace prot tr ag = (constantWhitelist)
  where
    symmetrySess = fromJust (_sess ag) <= (maxSessA + 1)
    constantWhitelist = null whiteListA || wlist ag `elem` whiteListA
    maxSessA = maximum (0:map (\z -> fromJust (_sess z)) (aliveNamed prot tr (_name ag)))  
    whiteListA = map wlist (aliveNamed prot tr (_name ag))
    namesHonestAlive = L.nub (map _name (aliveHonestAg tr) ++ [_name ag]) 


frame :: Agent -> Trace -> [Mapping]
frame ag tr = analzP ag (terms ag tr) (links ag tr)  


links :: Agent -> Trace -> [Mapping]
-- foldr applies the function (\e->e) to each event of tr, accumulating the result in list frm (frm is initially [] ) 
--
-- links ag tr 
--          | _name ag == Spy =  analzU ag (sees ag tr) (analzP ag (sees ag tr) updatedFrame) 
--          | otherwise =  analzP ag (sees ag tr) updatedFrame
--
-- links ag tr =analzP ag (sees ag tr) (updatedFrame ag)


links ag tr = _iniFrame ag `L.union` foldr (\e frm -> update e `L.union` frm) [] tr
  where 
    -- updatedFrame ag = (_iniFrame ag `L.union` foldr (\e frm -> update e `L.union` frm) [] tr)
    update :: Event -> [Mapping] 
    update (ESend n (r, ag') maps map@(at,t)) 
      | ag == ag'        = map:maps
      | _name ag == Spy = [(at',t) | acts <- _indistActions ag, Send n' r' phi ats at' <- acts,  n==n', r==r']
      | otherwise      =  [] 
    update (ERec n (r, ag')  st  map)
      | ag == ag'        = [map]
      | _name ag == Spy = st
      | otherwise      = [] 

terms :: Agent -> Trace -> [Term] 
terms ag tr | _name ag == Spy = analz Spy (sees ag tr)
terms ag tr | otherwise = analz (_name ag) (concat [sees ag' tr| ag' <- aliveHonestAg tr , _name ag == _name ag'])

-- foldr applies the function (\e->e) to each event of tr, accumulating the result in list trm (trm is initially [] ) 
sees :: Agent -> Trace  -> [Term]
-- sees ag s =  analz (_name ag) (_iniTerms ag `L.union` foldr (\e trm -> update e `L.union` trm) [] (s)) 
sees ag s = (_iniTerms ag `L.union` foldr (\e trm -> update e `L.union` trm) [] (s)) 
  where 
    update (ESend n (r, ag') ms (pm, m)) 
      | ag == ag'         = m:[m'| (pm',m') <- ms] 
      | _name ag == Spy   = [m] 
      | otherwise         = [] 
    update (ERec  n (r, ag') st (pm, m)) 
      | ag == ag'         = [m] 
      | otherwise         = []

seesName :: Name -> Trace -> [Term] 
seesName a s = analz a (concat [sees ag s| ag <- aliveHonestAg s , _name ag == a]) 


analzP :: Agent -> [Term] -> [Mapping] -> [Mapping]
analzP ag trms frm = closure (inj `orf` fst `orf` snd `orf` thrd `orf` dec `orf` sdec `orf` unhash `orf` unmac) frm 
    where 
      inj xs   = xs
      fst xs   = [(px, x) | (Pair px py, Pair x y) <-xs]
              ++ [(px, x) | (Triple px py pz, Triple x y z) <-xs]
      snd xs   = [(py, y) | (Pair px py, Pair x y) <-xs]
              ++ [(py, y) | (Triple px py pz, Triple x y z) <-xs]
      thrd xs  = [(pz, z) | (Triple px py pz, Triple x y z) <-xs]
      dec xs   = [(px, x) | (Crypt pag px, Crypt (Name a) x) <- xs, _name ag == a]
              ++ [(pag, Name a) | (Crypt pag px, Crypt (Name a) x) <- xs, _name ag == a]
      sdec xs  = [(px, x) | (SCrypt pk px, SCrypt k x) <- xs, k `elem` trms]
              ++ [(pk, k) | (SCrypt pk px, SCrypt k x) <- xs, k `elem` trms]
      unmac xs = [(px, x) | (Mac pk px, Mac k x) <- xs, k `elem` trms]
              ++ [(pk, k) | (Mac pk px, Mac k x) <- xs, k `elem` trms]
      unhash xs = [(pm, m)  | (Hash pm, Hash m) <- xs, (m `elem` trms) ] 
     
undeciph' :: Agent -> [Terms Grd] -> Terms Grd -> Bool 
undeciph' ag trms (Proj1 _) = True 
undeciph' ag trms (Proj2 _) = True 
undeciph' ag trms (Proj3 _) = True 
undeciph' ag trms (DCrypt _) = True 
undeciph' ag trms (DSCrypt _) = True 
undeciph' ag trms (DHash _) = True 
undeciph' ag trms (Pair x y) = undeciph' ag trms x || undeciph' ag trms y
undeciph' ag trms (Triple x y z) = undeciph' ag trms x || undeciph' ag trms y || undeciph' ag trms z
undeciph' ag trms (Crypt (Name a) m) | _name ag /= a = True 
undeciph' ag trms (SCrypt k m) | not (k `elem` trms) = True  
undeciph' ag trms (Hash m) | not (m `elem` trms) = True
undeciph' ag trms (Nonce n) = True 
undeciph' ag trms (Key n)  = True 
undeciph' ag trms _  = False 


-- define steps for a role
step :: Maybe RoleName -> Agent -> Trace -> Int
step (Just r) ag s 
  | null s  = 0
  | otherwise   = (maximum (0:[n | (ESend n (r,ag') ms m) <- s, ag' == ag])) 
            `max` (maximum (0:[n | (ERec  n (r,ag') st m) <- s, ag' == ag]))
step Nothing ag s = -1


-- =================== INDISTINGUISHABILITY relation ==========================
equiv :: Agent -> Trace  -> Trace  -> Bool
equiv ag tr tr' = frameEquiv ag tr tr'  
                && filter (\t -> not (undeciph' ag (terms ag tr) t)) (terms ag tr) 
                == filter (\t -> not (undeciph' ag (terms ag tr') t)) (terms ag tr') 
                -- && filter (\t -> not (undeciph' ag (sees ag tr) t)) (sees ag tr) 
                -- == filter (\t -> not (undeciph' ag (sees ag tr') t)) (sees ag tr') 
                && step (_role ag) ag tr' == step (_role ag) ag tr

frameEquiv :: Agent -> Trace -> Trace -> Bool  
frameEquiv ag tr tr'
  = dom == dom'                                                                 -- same domain
  && and [length (image pt frm) == length (image pt frm') | pt <- S.toList dom] -- same size image
  && and [(pt,t) `elem` frm'  | (pt,t)    <- frm , not (undeciph' ag trm t) ]
  && and [(pt',t') `elem` frm | (pt',t')  <- frm', not (undeciph' ag trm' t')] 
  where 
    dom = S.fromList (fst (unzip frm)) ; 
    dom' = S.fromList (fst (unzip frm'))
    image pt frm = [t' | (pt',t') <- frm, pt' == pt ] 
    frm = frame ag tr ; frm' = frame ag tr';
    trm = terms ag tr ; trm' = terms ag tr'
    -- frm = links ag tr ; frm' = links ag tr';
    -- trm = sees ag tr ; trm' = sees ag tr'

-- =========================================================================





truth0 :: (ProtocolSpec, Trace) -> Stmt -> Bool
truth0 (prot,tr) (BConst b)                = b
truth0 (prot,[])  f                         = False
truth0 (prot,tr) (Has (UAg ag) m)          =   unGrd m `elem` terms ag tr
truth0 (prot,tr) (Has (UName a) m)         =  unGrd m `elem` seesName a tr 
truth0 (prot,tr) (EndHas (UAg ag) m)       =  unGrd m `elem` terms ag tr && step (_role ag) ag tr == maxStep (prot, _role ag)
truth0 (prot,tr) (Link (UAg ag) (pt,t))    =  (pt, unGrd t) `elem` frame ag tr
truth0 (prot,tr) (EndLink (UAg ag) (pt,t)) =  ((pt, unGrd t) `elem` frame ag tr)&&  step (_role ag) ag tr == maxStep (prot, _role ag)
truth0 (prot,tr) (Listed (UAg ag) t)       =  (unGrd t `isSubtermOf` wlist ag)
-- truth0 (prot,tr) (Has (UAg ag) m)          = (unGrd m `elem` sees ag tr)
-- truth0 (prot,tr) (Has (UName a) m)         = (unGrd m `elem` seesName a tr) 
-- truth0 (prot,tr) (EndHas (UAg ag) m)       = unGrd m `elem` sees ag tr && step (_role ag) ag tr == maxStep (prot, _role ag)
-- truth0 (prot,tr) (Link (UAg ag) (pt,t))    = ((pt, unGrd t) `elem` links ag tr)
-- truth0 (prot,tr) (EndLink (UAg ag) (pt,t)) = ((pt, unGrd t) `elem` links ag tr)&&  step (_role ag) ag tr == maxStep (prot, _role ag)
-- truth0 (prot,tr) (Listed (UAg ag) t)       = (unGrd t `isSubtermOf` wlist ag)
truth0 (prot,tr) (Conj fs)                 = and [truth0 (prot,tr) f | f <- fs]
truth0 (prot,tr) (Disj fs)                 = or [truth0 (prot,tr) f | f <- fs]
truth0 (prot,tr) (Imp f g)                 = truth0 (prot,tr) g || not (truth0 (prot,tr) f)
truth0 (prot,tr) (Neg f)                   = (not (truth0 (prot,tr) f))
truth0 (prot,tr) (GEq (Grd (Nonce n)) (Grd (Nonce n')))   =  (n >= n')
truth0 (prot,tr) (EqI (UAg a) (UAg b))   =  (a == b)

truth0Abs :: (ProtocolSpec, Trace )-> (Map LogicTerm LogicTerm, Map IndexTerm Agent) -> Stmt -> Bool
-- truth0Abs (prot, tr) (sigma, sigmaAg) f =   (truth (prot, [tr],  tr) ( sigmaLift (sigma,sigmaAg) f))
truth0Abs (prot, tr) (sigma, sigmaAg) f =  truth (prot, [tr],  tr) ( sigmaLift (sigma,sigmaAg) f)

maxStep :: (ProtocolSpec, Maybe RoleName) -> Int
maxStep (prot, r) = maximum [i | Send i r' ph fr msg <- _actions prot, r == Just r'] 
                    `max` maximum [i | Rec i r' ph msg <- _actions prot, r ==  Just r']

-- | The truth is defined at (prot,M,tr) rather than just (M,tr) 
-- to get the alive agents, we need the spy from prot in addition to alive agents from tr
-- (alternatively we could have added Spy in the signature of events) 
truth :: (ProtocolSpec,[Trace],Trace) -> Stmt -> Bool
truth (prot,mdl,tr) f =  truth' (prot,mdl,tr) (empty,empty) f
  where
    truth' :: (ProtocolSpec,[Trace],Trace) -> (Map LogicTerm LogicTerm, Map IndexTerm Agent) -> Stmt -> Bool 
    truth' (prot,mdl,tr) sigmas (BConst b)                 = b
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (GEq t t')         =  truth0 (prot,tr) (GEq (tLiftDelta sigma t) (tLiftDelta sigma t'))
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (EqI (UAg a)  (UAg b) )         =  truth0 (prot,tr) (EqI (UAg a) (UAg b))
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (EqI (UVarAg a)  (UVarAg b) )         =  truth0 (prot,tr) (EqI (UAg (sigmaAg!UVarAg a)) (UAg (sigmaAg!UVarAg b)))
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (Has (UAg ag) t)           =  truth0 (prot,tr) (Has (UAg ag) (tLiftDelta sigma t))&&  ag `elem` (aliveAg prot tr)
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (EndHas (UAg ag) t)           = truth0 (prot,tr) (EndHas (UAg ag) (tLiftDelta sigma t))&&  ag `elem` (aliveAg prot tr)
    truth' (prot,mdl,tr) (sigma, sigmaAg)  (Link (UAg ag) (pt,t))     =  truth0 (prot,tr) (Link (UAg ag) (pt,(tLiftDelta sigma t) )) &&  ag `elem` (aliveAg prot tr)
    truth' (prot,mdl,tr) (sigma, sigmaAg)  (EndLink (UAg ag) (pt,t))     = truth0 (prot,tr) (EndLink (UAg ag) (pt,(tLiftDelta sigma t) )) &&  ag `elem` (aliveAg prot tr)
    -- truth' (prot,mdl,tr) sigmas (Listed (UAg ag) t)        = truth0 (prot,tr) (deltaLift sigmas (Listed (UAg ag) t)) &&  ag `elem` (aliveAg prot tr)
    truth' (prot,mdl,tr) (sigma,sigmaAg) (Listed (UAg ag) t)        = truth0 (prot,tr) (Listed (UAg ag) (tLiftDelta sigma t)) &&  ag `elem` (aliveAg prot tr)
    truth' (prot,mdl,tr) sigmas (Link (UVarAg x) (pt,t))     = truth' (prot,mdl,tr) sigmas (deltaLift sigmas (Link (UVarAg x) (pt,t)))
    truth' (prot,mdl,tr) sigmas (EndLink (UVarAg x) (pt,t))  = truth' (prot,mdl,tr) sigmas (deltaLift sigmas (EndLink (UVarAg x) (pt,t)))
    truth' (prot,mdl,tr) sigmas (Listed (UVarAg x) t)        = truth' (prot,mdl,tr) sigmas (deltaLift sigmas (Listed (UVarAg x) t))
    truth' (prot,mdl,tr) sigmas (Has (UVarAg x) m)           = truth' (prot,mdl,tr) sigmas (deltaLift sigmas (Has (UVarAg x) m))
    truth' (prot,mdl,tr) sigmas (EndHas (UVarAg x) m)        = truth' (prot,mdl,tr) sigmas (deltaLift sigmas (EndHas (UVarAg x) m))
    truth' ctxt sigmas (Conj fs)                           = and [truth' ctxt sigmas f | f <- fs]
    truth' ctxt sigmas (Disj fs)                           = or [truth' ctxt sigmas f | f <- fs]
    truth' ctxt sigmas (Imp f g)                           = truth' ctxt sigmas g || not (truth' ctxt sigmas f)
    truth' ctxt sigmas (Neg f)                             = not (truth' ctxt sigmas f)
    truth' ctxt sigmas (K (UVarAg x) f)                      =  truth' ctxt sigmas (deltaLift sigmas (K (UVarAg x) f))
    truth' (prot,mdl,tr) (sigma,sigmaAg)  (Link (UName a) (pt,t))    = or [truth0 (prot,tr) (Link (UAg ag) (pt,(tLiftDelta sigma t) ) ) | ag <- (aliveAg prot tr), _name ag == a]
    truth' (prot,mdl,tr) (sigma,sigmaAg) (EndLink (UName a) (pt,t)) = or [truth0 (prot,tr) (EndLink (UAg ag) (pt,(tLiftDelta sigma t)) ) | ag <- (aliveAg prot tr), _name ag == a, step (_role ag) ag tr == maxStep (prot, _role ag) ]
    truth' (prot,mdl,tr) (sigma,sigmaAg) (Listed (UName a) t)       = or [truth0 (prot,tr) (Listed (UAg ag) (tLiftDelta sigma t)) | ag <- (aliveAg prot tr), _name ag == a]
    truth' (prot,mdl,tr) (sigma,sigmaAg) (Has (UName a) m)          =  or [ truth0 (prot,tr) (Has (UAg ag) (tLiftDelta sigma m)) | ag <- (aliveAg prot tr), _name ag == a]
    truth' (prot,mdl,tr) (sigma,sigmaAg) (EndHas (UName a) m)       = or [truth0 (prot,tr) (EndHas (UAg ag) (tLiftDelta sigma m)) | ag <- (aliveAg prot tr), _name ag == a, step (_role ag) ag tr == maxStep (prot, _role ag)]
    truth' (prot,mdl,tr) sigmas (K (UName a) f)            = or [truth' (prot,mdl,tr) sigmas (K (UAg ag) f) | ag <- (aliveAg prot tr), _name ag == a]
    truth' (prot,mdl,tr) sigmas (K (UAg ag) f)             = and [truth' (prot,mdl,tr') sigmas f | tr' <- mdl, equiv ag tr tr']
    truth' ctxt@(prot,mdl,tr) sigmas (P f)                 = or [truth' (prot,mdl,tr') sigmas f | tr' <- mdl, tr' `L.isPrefixOf` tr]
    truth' ctxt@(prot,mdl,tr) sigmas (F f)                 = or [truth' (prot,mdl,tr') sigmas f | tr' <- mdl, tr `L.isPrefixOf` tr']
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllAg (VarAg x) f) = and [truth' ctxt (sigma `union` map1 (VarAg x) (Grd (Name (_name ag))),sigmaAg `union` (map1 (UVarAg x) ag)) f | ag <- (aliveAg prot tr)]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsAg (VarAg x) f) = or  [truth' ctxt (sigma `union` map1 (VarAg x) (Grd (Name (_name ag))),sigmaAg `union` (map1 (UVarAg x) ag)) f | ag <- (aliveAg prot tr)]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllHonestAg (VarAg x) f) = and [truth' ctxt (sigma `union` map1 (VarAg x) (Grd (Name (_name ag))),sigmaAg `union` (map1 (UVarAg x) ag)) f | ag <- (aliveHonestAg tr)]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsHonestAg (VarAg x) f) = or  [truth' ctxt (sigma `union` map1 (VarAg x) (Grd (Name (_name ag))),sigmaAg `union` (map1 (UVarAg x) ag)) f | ag <- (aliveHonestAg tr)]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllKey v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Key k) | Key k <- (terms ag tr)] | ag <- aliveAg prot tr] )]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsKey v f) = or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- ( concat [[Grd (Key k) | Key k <- (terms ag tr)] | ag <- aliveAg prot tr] )]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllName v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Name a) | Name a <- (terms ag tr)] | ag <- aliveAg prot tr] )]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsName v f) = or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Name a) | Name a <- (terms ag tr)] | ag <- aliveAg prot tr] )]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllNonce v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Nonce a) | Nonce a <- (terms ag tr)] | ag <- aliveAg prot tr] )]
    truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsNonce v f) = (or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Nonce a) | Nonce a <- (terms ag tr)] | ag <- aliveAg prot tr] )])
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllKey v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Key k) | Key k <- (sees ag tr)] | ag <- aliveAg prot tr] )]
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsKey v f) = or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- ( concat [[Grd (Key k) | Key k <- (sees ag tr)] | ag <- aliveAg prot tr] )]
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllName v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Name a) | Name a <- (sees ag tr)] | ag <- aliveAg prot tr] )]
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsName v f) = or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Name a) | Name a <- (sees ag tr)] | ag <- aliveAg prot tr] )]
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ForAllNonce v f) = and [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Nonce a) | Nonce a <- (sees ag tr)] | ag <- aliveAg prot tr] )]
    -- truth' ctxt@(prot,mdl,tr) sigmas@(sigma,sigmaAg) (ExistsNonce v f) = or [truth' ctxt (sigma `union` map1 v t,sigmaAg) f | t <- (concat [[Grd (Nonce a) | Nonce a <- (sees ag tr)] | ag <- aliveAg prot tr] )]


aliveAg :: ProtocolSpec -> Trace  -> [Agent] 
aliveAg prot tr = [_spy prot] ++ L.nub [ag | ESend i (r,ag) ms m <- tr] `L.union` [ag | ERec i (r,ag) st m <- tr]

aliveNamed :: ProtocolSpec -> Trace -> Name -> [Agent]
aliveNamed prot tr a = filter (\z -> _name z == a) (aliveAg prot tr)

aliveWithRole :: RoleName -> Trace -> [Agent]
aliveWithRole r tr = filter (\z -> _role z == Just r) (aliveHonestAg tr)

aliveHonestAg :: Trace  -> [Agent] 
aliveHonestAg tr = L.nub [ag | ESend i (r,ag) ms m <- tr] `L.union` [ag | ERec i (r,ag) st m <- tr]
        

sat :: ProtocolSpec -> Stmt -> Maybe Trace
sat prot frml = let model = build prot 
                    in justHead [tr | tr <- model, truth (prot, model,tr) frml, not (null tr)] -- 

allSat :: ProtocolSpec -> Stmt -> [Trace]
allSat prot frml = let model = build prot 
                       in [tr | tr <- model, truth (prot, model,tr) frml]

satK :: Agent -> (ProtocolSpec, [Trace]) -> Stmt -> Maybe Trace 
satK ag (prot, model) f = justHead [head ec | ec <- equivClasses (equiv ag) model,  truthK (ag, ec) (prot,model) f]

allSatK :: Agent -> (ProtocolSpec, [Trace]) -> Stmt -> [Trace]
allSatK ag (prot, model) f = concat [ec | ec <- equivClasses (equiv ag) model,  truthK (ag, ec) (prot,model) f]
      
-- | the truth of a formula at an equivalence class of an agent
truthK :: (Agent, [Trace]) -> (ProtocolSpec,[Trace]) -> Stmt -> Bool
truthK (ag, []) (prot,mdl) f                                 = False   
truthK (ag, ec) (prot,mdl) (K (UAg ag') f)       | ag == ag' = truthK (ag, ec) (prot,mdl)  f
truthK (ag, ec) (prot,mdl) (Neg (K (UAg ag') f)) | ag == ag' = or [not $ truth (prot,mdl,tr) f | tr <- ec] 
truthK (ag, ec) (prot,mdl) f                                 = and [truth (prot,mdl,tr) f | tr <- ec ] 

-- | MODEL BUILDING
build :: ProtocolSpec -> [Trace] 
build prot = L.nub (flatten (buildTree (ext prot) []))

buildT :: ProtocolSpec -> Tree Trace 
buildT prot = buildTree (ext prot) []

--
buildTree :: (Trace ->[Trace])-> Trace -> Tree Trace 
buildTree extension init = Node init (map (buildTree extension) (extension init))

-- | This takes trace and generates all possible new traces,
-- eg say we have tr=[t1,t2,...,tn] and the set of possible new events is [ev1,ev2,...,evM]
-- then this will return [[t1,t2,...,tn,ev1],[t1,...,tn,ev2],...,[t1,...,tn,evM]]
-- note we use a union to combine tr and evX thus [t1,...,tn,evX]=[t1,...,tn]
-- "filter constantWList" guarantees that the whitelist of Alice (or Bob or ...) is constant in one exec 
ext :: ProtocolSpec -> Trace -> [Trace]
ext prot t = L.nub (map (\x -> t `L.union` [x]) extension)
  where 
    extension= anyf (Prelude.map (enabledEvents prot) (_actions prot)) t -- see HelperFunctions for anyf


instance Show Event 
  where
    show (ESend i (r,ag) ms m) = 
      show i ++"."++show ag  ++ "!: ("++ showListC (snd (unzip ms))  ++ ")" ++"" ++ show (snd m) ++ "\n"
    show (ERec  i (r,ag) st m) = 
      show i ++"."++show ag   ++ "?: ("++ showListC (snd (unzip st)) ++ ")" ++"" ++ show (snd m) ++ "\n"


tree prot = drawTree (fmap show (buildT prot))
writeTree prot = writeFile (_protName prot ++ "_tree.txt") (tree prot) -- show the tree
writeAgents prot = writeFile (_protName prot ++ "_agents.txt") (show (_honestAgents prot)) -- show the tree
writeLeaves prot = writeFile (_protName prot ++ "_leaves.txt") (unlines [show s| s<- build prot]) -- show the leaves line by line
writeSat prot frml = writeFile (_protName prot ++ "_sat.txt") (satHead prot frml ++ show (sat prot frml))  
writeAllSat prot frml = writeFile (_protName prot ++ "_allSat.txt") (allSatHead prot frml ++ unlines [show f| f<-allSat prot frml])  

satHead prot frml = "sat(" ++ show (_protName prot) ++ ", " ++ show frml ++ ")\n"
allSatHead prot frml = "allSat(" ++ show (_protName prot) ++ ", " ++ show frml ++ ")\n"
writeEquivClass prot = writeFile (_protName prot ++ "_equivClasses.txt") (unlines ["\n\n" ++ show ag ++ unlines (["{\n" ++ unlines [(show s ) ++"  \n terms of "++ show ag  ++ show (terms ag s)  ++ "  \n frame of " ++ show ag  ++ ": " ++ showFrame (links ag s)| s <- ss]++"}\n" | ss <- (equivClasses (equiv ag) (build prot))]) | ag <- (_spy prot):_honestAgents prot, _name ag == Server 1, _sess ag == Just 1])
