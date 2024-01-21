{-# LANGUAGE StandaloneDeriving, GADTs #-}
module BasicHash (satNegStrongLinkabilityBH,satNegWeakUnlinkabilityBH) where
import ProtModel
import Data.Tree               -- Use trees from Data.Tree module
import Data.Maybe
import qualified Data.List as L
import qualified Data.Set as S
import HelperFunctions
import Debug.Trace
-- import Terms
import LogicSyntax
-- import ShowFunctions


-- ---------- Basic Hash (Reader has whitelist of shared keys) ----------
maxSessions = 4
numTags = 3
keys = [Key (LKey i) | i <- [1..numTags]] 
tagNames    = [Tag i | i <- [1..numTags]] 
readerNames = [Reader 1]
names = (Spy:tagNames ++ readerNames) 
roles = [T, R] 
agents = trace ("tag agents" ++ show (length tagAgents) ++ "reader agents" ++ show (length readerAgents) ) tagAgents ++ readerAgents
spy = Agent 
      { _name = Spy , _sess = Nothing, _role = Nothing
      , _iniTerms=[Key (LKey 0)]
      , _iniFrame=[] 
      , _id = 0
      , _indistActions = [[a]|a<-actions] 
      } 

actions =    
    [ Send 1 T true       [AbsNonce NT] (Pair (AbsNonce NT) (Hash (Pair (AbsNonce NT) (AbsKey KT))))
    , Rec  1 R (true,phi)               (Pair (AbsNonce NT) (Hash (Pair (AbsNonce NT) (AbsKey KT))))
    ]
    where
      phi = ExistsKey (VarKey "x") ((VarKey "x" ∈ UAbsName R) ∧ (Link (UAbsName R) (Hash (Pair (AbsNonce NT) (AbsKey KT)), Hash (Pair (Abs (AbsNonce NT)) (VarKey "x")))))  

basicHash :: ProtocolSpec
basicHash = ProtocolSpec 
  { _spy = spy
  , _roles = roles 
  , _honestAgents = agents
  , _actions = actions
  , _protName = "BasicHash"
  }

tagAgents :: [Agent] 
tagAgents = 
    [ Agent 
      { _name=nm
      , _sess=Just sess
      , _role=Just T
      , _id=id
      , _iniTerms=[k, Name nm] 
      , _iniFrame=[(Role T, Name nm), (Self, Name nm), (AbsName T, Name nm), (AbsKey KT, k)] 
      , _indistActions=[] 
      }
    | ((sess, nm, k), id) <- zip possibleTags [1 ..]   
    ] 
    where
      possibleTags = 
          [ (sess, Tag n, Key (LKey m)) 
          | sess <- [1..maxSessions]
          , Tag n <- tagNames 
          , Key (LKey m) <- keys
          , n == m
          ] 

readerAgents :: [Agent] 
readerAgents = 
    [ Agent 
      { _name=nm
      , _sess=Just sess
      , _role=Just R
      , _id=id
      , _iniTerms=keys ++ [Name nm] 
      , _iniFrame=[(Role R, Name nm), (Self, Name nm), (AbsName R, Name nm), (AbsList Self, Tuple list), (AbsList (AbsName R), Tuple list)] 
      , _indistActions=[] 
      }
    | ((sess, nm, list), id) <- zip possibleReaders [1]  -- just one reader 
    ] 
    where
      possibleReaders = 
          [ (sess, nm, lst) 
          | sess <- [1..maxSessions]
          , nm <- readerNames
          , lst <- lPowerSet keys -- we allow the reader to have all honest keys in its whitelist
          ] 

negWeakUnlinkability :: Stmt
negWeakUnlinkability = existsHonest [VarAg "x", VarAg "y"]  (UVarAg "x" `plays` T ∧ UVarAg "y" `plays` T ∧ K (UAg spy) (ExistsName (VarName "t") (UVarAg "x" `named` VarName "t" ∧ UVarAg "y" `named` VarName "t" ∧ nEqI (UVarAg "x") (UVarAg "x")  )))

-- negWeakUnlinkability =   (K (UAg spy) (ExistsName (VarName "y") (forAllHonest [VarAg "x"] (Link (UVarAg "x") (Role T, VarAg "x") `imp` (Link (UVarAg "x") (Self, VarName "y") )) ) ))

-- here is the strong linkability when n_sess=3
-- it is feasible to mechanise this formula for any n_sess 
negStrongUnlinkability :: Stmt
negStrongUnlinkability =  (K (UAg spy) (existsName varnames (forAllHonest [VarAg "x"] (Link (UVarAg "x") (Role T, VarAg "x") `imp` Disj [Link (UVarAg "x") (Self, varname) | varname <-varnames]) ) ))
  where
    varnames = [VarName ("y"++show i) | i <- [1..(maxSessions-1)]]

satNegWeakUnlinkabilityBH = show (justHead [tr | tr <- build basicHash, truth (basicHash, build basicHash,tr) (negWeakUnlinkability),  countSessions T tr == maxSessions])
satNegStrongLinkabilityBH = show (justHead [tr | tr <- build basicHash, truth (basicHash, build basicHash,tr) (negStrongUnlinkability),  countSessions T tr == maxSessions])
allSatNegStrongLinkabilityBH = show ([tr | tr <- build basicHash, truth (basicHash, build basicHash,tr) (negStrongUnlinkability),  countSessions T tr == maxSessions])

-- with the following settings
-- maxSessions = 3
-- keys = [Key (LKey 1), Key (LKey 2)] 
-- tagNames    = [Tag 1, Tag 2] 
-- readerNames = [Reader 1]
-- >>> satNegStrongUnlinkability 
-- Just [1.(t1,T,1,{})!: (n1)⟨n1,hash(⟨n1,k1⟩)⟩
-- ,1.(t1,T,2,{})!: (n2)⟨n2,hash(⟨n2,k1⟩)⟩
-- ,1.(t1,T,3,{})!: (n3)⟨n3,hash(⟨n3,k1⟩)⟩
-- ]
