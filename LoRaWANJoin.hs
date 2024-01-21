module LoRaWANJoin where
import ProtModel
import Data.Tree               -- Use trees from Data.Tree module
import Data.Maybe
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as S
import HelperFunctions
import LogicSyntax

maxSessions = 1
deviceNames = [Device 1, Device 2]
serverNames = [Server 1]
names = (Spy:deviceNames ++ serverNames) 
roles = [D, S] --  Device (End Device) and Server (Network Server) 
agents = trace ("device agents" ++ show (length deviceAgents) ++ "server agents" ++ show (length serverAgents)) deviceAgents ++ serverAgents

loRaWANJoin :: ProtocolSpec
loRaWANJoin = ProtocolSpec 
  { _spy = spy
  , _roles = roles 
  , _honestAgents = agents
  , _actions = actions
  , _protName = "LoRaWANJoin"
  }

actions = 
  [ Send 1 D true                [AbsNonce DevNonce] (Pair mes1 (Mac (AbsKey NwkKey) mes1))  
  , Rec  1 S (nonceCond, macAuth)                  (Pair mes1 (Mac (AbsKey NwkKey) mes1))  
  , Send 2 S true                [AbsNonce JoinNonce, AbsKey DevAddr] (SCrypt (AbsKey NwkKey) mes2)
  , Rec  2 D (nonceCond', true)             (SCrypt (AbsKey NwkKey) mes2)      
  , Send 3 D true                [AbsKey DData] (Pair (AbsKey DevAddr) (SCrypt (AbsKey NwkKey) (AbsKey DData)))  
  , Rec  3 S trues                              (Pair (AbsKey DevAddr) (SCrypt (AbsKey NwkKey) (AbsKey DData)))  
  ]
  where
    mes1 = Triple (AbsDatum JoinEUI) (AbsDatum DevEUI) (AbsNonce DevNonce)
    mes2 = Pair (AbsNonce JoinNonce) (AbsKey DevAddr)  
    macAuth = ExistsKey (VarKey "x") ((VarKey "x" ∈ UAbsName S) ∧ Link (UAbsName S) (Mac (AbsKey NwkKey) (mes1), Mac (VarKey "x") (mes1')))
    nonceCond = Neg (ExistsNonce (VarNonce "n") (Has (UAbsName S) (VarNonce "n") 
                                                ∧ (VarNonce "n" ≥ Abs (AbsNonce DevNonce)))) 
    mes1' = Triple (Abs (AbsDatum JoinEUI)) (Abs (AbsDatum DevEUI)) (Abs (AbsNonce DevNonce))
    nonceCond' = Neg (ExistsNonce (VarNonce "n") (Has (UAbsName D) (VarNonce "n") 
                                                ∧ (VarNonce "n" ≥ Abs (AbsNonce JoinNonce))))

deviceAgents :: [Agent] 
deviceAgents = 
    [ Agent 
      { _name=nm
      , _sess=Just sess
      , _role=Just D
      , _id=id
      , _iniTerms=[Name nm, Name srvr, Key (LShared nm srvr)] 
      , _iniFrame=[ (Role D, Name nm) 
                  , (Self, Name nm)
                  , (AbsName D, Name nm)
                  , (AbsDatum DevEUI, Name nm)
                  , (AbsDatum JoinEUI, Name srvr)
                  , (AbsKey NwkKey, Key (LShared nm srvr))
                  ] 
      , _indistActions=[] 
      }
    | ((sess, nm, srvr), id) <- zip possibleDevices [1 ..]   
    ] 
    where
      possibleDevices = 
          [ (sess, nm, srvr) 
          | sess <- [1 .. maxSessions]
          , nm <- deviceNames 
          , srvr <- serverNames
          ] 

serverAgents :: [Agent] 
serverAgents = 
    [ Agent 
      { _name=srvrNm
      , _sess=Just sess
      , _role=Just S
      , _id=id
      , _iniTerms=[Name srvrNm] ++ [Key (LShared dvc srvrNm) | dvc <- deviceNames]  
      , _iniFrame=[ (Role S, Name srvrNm) 
                  , (Self, Name srvrNm)
                  , (AbsName S, Name srvrNm)
                  , (AbsList Self, Tuple [Key (LShared dvc srvrNm) | dvc <- deviceNames])
                  , (AbsList (AbsName S), Tuple [Key (LShared dvc srvrNm) | dvc <- deviceNames])
                  , (AbsDatum JoinEUI, Name srvrNm)
                  ] 
      , _indistActions=[] 
      }
    | ((sess, srvrNm), id) <- zip possibleServers [1 ..]   
    ] 
    where
      possibleServers = 
          [ (sess, srvrNm) 
          | sess <- [1..maxSessions]
          , srvrNm <- serverNames 
          ] 

spy = Agent 
      { _name = Spy , _sess = Nothing, _role = Nothing
      , _iniTerms= [] 
                -- ++ [Key (LKey 0)] -- the intruder is given some key
                ++ [Datum nm | nm <- deviceNames]
                ++ [Name nm | nm <- deviceNames] 
                ++ [Name srvr | srvr <- serverNames]
      , _iniFrame=[] 
      , _id = 0
      , _indistActions = [[a]|a<-actions] 
      } 

trackDev :: Stmt
trackDev = K (UAg spy) (ExistsName (VarName "y") (ExistsKey (VarKey "z") (existsHonest [VarAg "x"] (Link (UVarAg "x") (AbsDatum DevEUI, VarName "y") ∧  Link (UVarAg "x") (AbsKey DevAddr, VarKey "z") ∧ (UVarAg "x") `plays` D )))) 
