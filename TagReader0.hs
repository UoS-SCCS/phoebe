module TagReader0 (satKeyLinkTR0,satNameLinkTR0,satKeyWeakLinkTR0,satNameWeakLinkTR0)  where
import ProtModel
import Data.Tree               
import Data.Maybe
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as S
import HelperFunctions
-- import Terms
import LogicSyntax
-- import ShowFunctions
{-|
Module      : TagReader0
Description : A linkable Tag Reader Protocol 
Example17 in "A method for unbounded verification of privacy-type properties"  
by Hirschi et al

* Run all tests with
```
doctest TagReader0.hs

```
* To change the parameters for the model, see
```
numTags = 2
numReaders = 1
maxSessions = 2
keys = [Key (LKey 1), Key (LKey 2)] -- long-term keys are not bound to names,
so there can be two tags sharing the same key with a reader
```
-}


-- ----------  Tag & Reader (Reader has whitelist of shared keys) ----------
maxSessions = 2
numTags = 2
keys = [Key (LKey i) | i <- [1,2] ] -- 2 keys, 2 groups
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

set l = S.fromList l

actions =    
    [ Send 1 T true           [AbsNonce NT] (SCrypt (AbsKey KT) (AbsNonce NT))
    , Rec  1 R trues                        (SCrypt (AbsKey KT) (AbsNonce NT))
    , Send 2 R true           [AbsNonce NR] (SCrypt (AbsKey KT) (AbsNonce NR))  
    , Rec  2 T (fresh,true)                 (SCrypt (AbsKey KT) (AbsNonce NR))
    , Send 3 T true           []            (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
    , Rec  3 R (true,match)                 (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
    , Rec  3 R trues                 (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
    ]
  where
    fresh = Neg (Has (UAbsName T) (Abs (AbsNonce NR))) 
    match = existsNonce [VarNonce "nr", VarNonce "nt"] ( existsKey [VarKey "kt"]  $
            Conj [ Link (UAbsName R) (AbsKey KT, VarKey "kt")
                 , Link (UAbsName R) (AbsNonce NR, VarNonce "nr")
                 , Link (UAbsName R) (AbsNonce NT, VarNonce "nt")
                 , Link (UAbsName R) (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)),
                                      SCrypt (VarKey "kt") (Pair (VarNonce "nr") (VarNonce "nt")))
                 ] )

tagReader :: ProtocolSpec
tagReader = ProtocolSpec 
  { _spy = spy
  , _roles = roles 
  , _honestAgents = agents
  , _actions = actions
  , _protName = "TagReader0"
  }

tagAgents :: [Agent] 
tagAgents = 
    [ Agent 
      { _name=nm
      , _sess=Just sess
      , _role=Just T
      , _id=id
      , _iniTerms=[k] 
      , _iniFrame=[(AbsName T, Name nm), (AbsKey KT, k)] 
      , _indistActions=[] 
      }
    | ((sess, nm, k), id) <- zip possibleTags [1 ..]   
    ] 
    where
      possibleTags = 
          [ (sess, nm, ky) 
          | sess <- [1..maxSessions]
          , nm <- tagNames 
          , ky <- keys
          ] 

readerAgents :: [Agent] 
readerAgents = 
    [ Agent 
      { _name=nm
      , _sess=Just sess
      , _role=Just R
      , _id=id
      , _iniTerms=keys
      , _iniFrame=[(AbsName R, Name nm), (AbsList Self, Tuple list), (AbsList (AbsName R), Tuple list)] 
      , _indistActions=[] 
      }
    | ((sess, nm, list), id) <- zip possibleReaders [1]   
    ] 
    where
      possibleReaders = 
          [ (sess, nm, lst) 
          | sess <- [1..maxSessions]
          , nm <- readerNames
          , lst <- [keys] 
          ] 


keyLink =  K (UAg spy) (ExistsKey (VarKey "y") (forAllHonest [VarAg "x"] (Link (UVarAg "x") (AbsKey KT, VarKey "y"))))

nameLink =  K (UAg spy) (ExistsName (VarName "y") (forAllHonest [VarAg "x"] (Link (UVarAg "x") (AbsName T, VarName "y"))))

nameWeakLink = existsHonest [VarAg "x", VarAg "y"]  (UVarAg "x" `plays` T ∧ UVarAg "y" `plays` T ∧ K (UAg spy) (ExistsName (VarName "t") (UVarAg "x" `named` VarName "t" ∧ UVarAg "y" `named` VarName "t" ∧ nEqI (UVarAg "x") (UVarAg "x")  ))) 

keyWeakLink = existsHonest [VarAg "x", VarAg "y"]  (UVarAg "x" `plays` T ∧ UVarAg "y" `plays` T ∧ K (UAg spy) (ExistsKey (VarKey "k") (Link (UVarAg "x") (AbsKey KT, VarKey "k") ∧ Link (UVarAg "y") (AbsKey KT, VarKey "k") ∧ nEqI (UVarAg "x") (UVarAg "x")))) 
-- -------------- test ----------------
-- >>> satKeyLink 
-- Just [1.(t1,T,1,{})!: (n1)⦃n1⦄_k1
-- ,1.(t2,T,2,{})!: (n2)⦃n2⦄_k1
-- ,1.(r1,R,1,{k1,k2})?: ()⦃n1⦄_k1
-- ,2.(r1,R,1,{k1,k2})!: (n3)⦃n3⦄_k1
-- ,2.(t1,T,1,{})?: ()⦃n2⦄_k1
-- ,2.(t2,T,2,{})?: ()⦃n1⦄_k1
-- ,3.(t1,T,1,{})!: ()⦃⟨n2,n1⟩⦄_k1
-- ,3.(t2,T,2,{})!: ()⦃⟨n1,n2⟩⦄_k1
-- ]

satKeyLinkTR0 = show (justHead [tr | tr <- build tagReader, truth (tagReader, build tagReader,tr) keyLink, length (aliveWithRole T tr) == maxSessions , map (\x -> (step (_role x) x tr)) (aliveWithRole T tr) ==[3,3]])

satNameLinkTR0 = show (justHead [tr | tr <- build tagReader, truth (tagReader, build tagReader,tr) nameLink, length (aliveWithRole T tr) == maxSessions, map (\x -> (step (_role x) x tr)) (aliveWithRole T tr) ==[3,3]])

satKeyWeakLinkTR0 = show (justHead [tr | tr <- build tagReader, truth (tagReader, build tagReader,tr) keyWeakLink, length (aliveWithRole T tr) == maxSessions , map (\x -> (step (_role x) x tr)) (aliveWithRole T tr) ==[3,3]])

satNameWeakLinkTR0 = show (justHead [tr | tr <- build tagReader, truth (tagReader, build tagReader,tr) nameWeakLink, length (aliveWithRole T tr) == maxSessions, map (\x -> (step (_role x) x tr)) (aliveWithRole T tr) ==[3,3]])
-- we restrict to states where tags have finished their actions (3 is the number of steps in the protocol for each role) 
