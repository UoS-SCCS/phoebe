{-# LANGUAGE GADTs #-}
module PrivAuth (privAuthGoal2A,privAuthXGoal2A,privAuthGoal2C,privAuthXGoal2C,
                privAuthGoal2A',privAuthXGoal2A',privAuthGoal2C',privAuthXGoal2C',
                privAuthGoal3,privAuthGoal3',privAuthXGoal3,privAuthXGoal3') where



import ProtModel
import Data.Tree               -- Use trees from Data.Tree module
import Data.Maybe
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as S
import HelperFunctions
-- import Terms
import LogicSyntax
-- import ShowFunctions
{-|
Module      : PrivAuth
Description : Private Authentication Protocol [Abadi] 

* This file provide the original protocol PrivAuth and the broken version PrivAuthX
* Abstractions
  * first msg sent modelled as {A,NA}_B
  * 2nd non-decoy msg  sent modelled as {B,NA,NB}_A  

* After any modification, run all tests with
```
doctest PrivAuth.hs

```
* To change the parameters for the model see
```
names = [Alice, Bob]
maxSessions = 1
```
-}

-- ========================== PARAMETERS ======================================

honestAgents = trace ("number of agents A" ++ show (length agentsA) ++ "... number of agents C" ++ show (length agentsC)) agentsA ++ agentsC
agents = spy:honestAgents
names = [Alice, Bob]
maxSessions = 1
roles = [A,C] 
actions =
    [ Send 1 A true      [AbsNonce NA]           (Crypt (AbsName B) (Pair (AbsName A) (AbsNonce NA)))
    , Rec  1 C trues                              (Crypt (AbsName B) (Pair (AbsName A) (AbsNonce NA)))
    , Send 2 C phi       [AbsNonce NC]           (Crypt (AbsName A) (Triple (AbsName C) (AbsNonce NA) (AbsNonce NC)))  
    , Send 2 C (Neg phi) [AbsNonce N, AbsKey KK] (SCrypt (AbsKey KK) (AbsNonce N))  
    , Rec  2 A trues                             (Crypt (AbsName A) (Triple (AbsName C) (AbsNonce NA) (AbsNonce NC)))  
    , Rec  2 A trues                              (SCrypt (AbsKey KK) (AbsNonce N))  
    ]
actionsX = [actions!!0,actions!!1,actions!!2,actions!!4] 

phi :: Stmt
phi = Conj
  [ Link (UAbsName C) (AbsName B, Abs (AbsName C))  -- (Link_ag (B, _name ag)) ^ happens if C decrypts the first message
  , Listed (UAbsName C) (PubKey (Abs (AbsName A)))  -- K_A ∈ S_C
  ]

privAuth :: ProtocolSpec
privAuth = ProtocolSpec 
  { _spy = spy
  , _roles = roles -- //
  , _honestAgents = honestAgents
  , _actions = actions
  , _protName = "PrivAuth"
  }

privAuthX :: ProtocolSpec
privAuthX = ProtocolSpec 
  { _spy = spy
  , _roles = roles 
  , _honestAgents = honestAgents
  , _actions = actionsX
  , _protName = "PrivAuth"
  }

agentsA ::  [Agent]
agentsA =
  [ Agent
    { _name=a, _sess=Just sess, _role=Just A
    , _iniTerms = [Name a | a <- names]
                ++[PubKey (Name a) | a<-names]
                ++[PrivKey (Name a)] 
    , _iniFrame = 
      if isJust nameB  
        then [(Self,Name a) ,
              (AbsName A,Name a) ,
              (Role A,Name a),
              (AbsName B, Name (fromJust nameB)),
              (AbsList Self, Tuple list),
              (AbsList (AbsName A), Tuple list)
             ]  
        else [(Self,Name a),
              (AbsName A,Name a),
              (Role A,Name a),
              (AbsList Self, Tuple list),
              (AbsList (AbsName A), Tuple list)
             ]
    , _id=id
    , _indistActions=[] 
    }
  | a <- names , ((sess, list, nameB), id) <- zip (possibleAgents a) [1 ..]
  ] 
    where
      possibleAgents a =
        [ (sess, list, Just nameB) 
        | sess <- [1..maxSessions] 
        , list <- lPowerSet [PubKey (Name a') | a' <- (L.delete a names)]
        , length list <= 1
        , nameB <- names
        , PubKey (Name nameB) `elem` list
        ]
        ++
        [ (sess, [], Nothing ) 
        | sess <- [1..maxSessions] 
        ]

agentsC :: [Agent]
agentsC =
    [ Agent
      { _name=a, _sess=Just sess, _role=Just C 
      , _iniTerms= [ Name a | a <- names]
                 ++[PubKey (Name a) | a<-names]++[PrivKey (Name a)]
      , _iniFrame=[ (AbsName C, Name a) 
                  , (Self, Name a) 
                  , (Role C, Name a)
                  , (AbsList Self, Tuple list)
                  , (AbsList (AbsName C), Tuple list)
                  ]
      , _id=id
      , _indistActions=[] 
      }
    | a <- names , ((sess, list), id) <- zip (possibleAgents a ) [1 ..]
    ] 
    where
      possibleAgents a =
          [ (sess, list) 
          | sess <- [1..maxSessions] 
          , list <- lPowerSet [PubKey (Name a') | a' <- (L.delete a names)]
          , length list <= 1
          ]
spy = Agent 
      { _name = Spy , _sess = Nothing, _role = Nothing
      , _iniTerms=[Name a | a <- names]++[PubKey (Name a) | a<-names]
      , _iniFrame=[(Self, Name Spy), (AbsList Self, Tuple [PubKey (Name a) | a<-names])] -- spy is quantified in e.g. exists vara in goal3
      , _id = 0
      , _indistActions = [[actions!!0],[actions!!1],[actions!!2,actions!!3],[actions!!4,actions!!5]]
      } 

spyX = Agent 
      { _name = Spy , _sess = Nothing, _role = Nothing
      , _iniTerms=[Name a | a <- names]++[PubKey (Name a) | a<-names]
      , _iniFrame=[(Self, Name Spy), (AbsList Self, Tuple [PubKey (Name a) | a<-names])] -- spy is quantified in e.g. exists vara in goal3
      , _id = 0
      , _indistActions = [[actions!!0],[actions!!1],[actions!!2],[actions!!3]]
      } 

allAgents = spy:agents
privAuthGoal2C = show (sat privAuth (Neg goal2responder))
privAuthXGoal2C = show (sat privAuthX (Neg goal2responder))
privAuthGoal2A = show (sat privAuth (Neg goal2initiator))
privAuthXGoal2A = show (sat privAuthX (Neg goal2initiator))
privAuthGoal2C' = show (sat privAuth (Neg goal2responderVsSpy'))
privAuthXGoal2C' = show (sat privAuthX (Neg goal2responderVsSpy'))
privAuthGoal2A' = show (sat privAuth (Neg goal2initiatorVsSpy'))
privAuthXGoal2A' = show (sat privAuthX (Neg goal2initiatorVsSpy'))
privAuthGoal3 = show (sat privAuth (Neg goal3Spy))
privAuthGoal3' = show (sat privAuth (Neg goal3Spy'))
privAuthXGoal3 = show (sat privAuthX (Neg goal3Spy))
privAuthXGoal3' = show (sat privAuthX (Neg goal3Spy'))
--------------------- simple tests ----------------
-- >>> aliceExists =  Neg (existsAg [VarAg "x"] (Link (UVarAg "x") (Self, Grd (Name Alice))))
-- >>> sat privAuthX (Neg aliceExists)
-- Just [1.(b,A,1,[Ka]):--|N1|->{(b,N1)}_a
-- ]
-- >>> sat privAuthX (aliceExists)
-- Just [1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
-- ]
--
-- >>> initiatorExists =  (existsAg [VarAg "x"] (Link (UVarAg "x") (Role A, VarAg "x")))
-- >>> responderExists =  (existsAg [VarAg "x"] (Link (UVarAg "x") (Role C, VarAg "x")))
-- >>> sat privAuthX (initiatorExists)
-- Just [1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
-- ]
-- >>> (sat privAuthX (Neg initiatorExists))
-- Just [1.(a,C,1,[]):<-|a,N1,a|--{(a,N1)}_a
-- ]
-- >>> (sat privAuthX (responderExists))
-- Just [1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
-- ,1.(a,C,1,[Kb]):<-|a,N2,a|--{(a,N2)}_a
-- ]
-- >>> (sat privAuthX (Neg responderExists))
-- Just [1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
-- ]
--
-- >>> bobPlaysInitiator = (existsAg [VarAg "x"] (Conj [Link (UVarAg "x") (Self, Grd (Name Bob)), Link (UVarAg "x") (Role A, VarAg "x")]))
-- Just [1.(b,A,1,[Ka]):--|N1|->{(b,N1)}_a
-- ]
-- >>> (sat privAuthX (Neg bobPlaysInitiator))
-- Just [1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
-- ]

-- ========================== EXAMPLES finding attacks ========================
--
-- -------------------------- -------------------------- --------------------------
-- | GOAL II Minimal Anonymity of Responder - 
-- An agent x should know the name b of the responder y if pubkey(name(x)) ∈ S_y 
-- ∀x ∀b K_x(plays(b,C)) ⇒ named(x,b) ∨ pub(x)∈S_b  
-- ------------ test 1 -----------------
-- >>>sat privAuth (Neg goal2responder)
-- Nothing
-- >>> sat privAuthX (Neg goal2responder)
-- Just [1.(a,A,1,{kb})!: (n1){⟨a,n1⟩}_b
-- ,1.(a,C,1,{kb})?: (b,n2,a){⟨b,n2⟩}_a
-- ,2.(a,C,1,{kb})!: (n3){⟨a,n2,n3⟩}_b
-- ]
goal2responder :: Stmt -- TODO use conjunction instead of forAllHonest
goal2responder =  
    forAllAg [VarAg "x"] (forAllHonest [VarAg "y"] (
      (   (Neg (UVarAg "x" `named` VarAg "y") ∧ (Neg (PubKey (VarAg "x") ∈ UVarAg "y")))
       ⇒  (Neg (K (UVarAg "x")  (UVarAg "y" `plays` C)) )
      )))

-------------------------------------------------------------------------------------
      
---- GOAL II' Total Anonymity of Responder - An agent x should know the name b of the responder y if (pubkey(name(x)) ∈ S_y) 
---- ∀x ∀b K_x(¬plays(b,C)) ⇒ named(x,b) ∨ pub(x)∈S_b  
-- goal2responder' :: Stmt 
-- goal2responder' = 
--     forAllAg [VarAg "x"] (forAllHonest [VarAg "y"] (
--       (   (Neg (UVarAg "x" `named` VarAg "y") ∧ (Neg (PubKey (VarAg "x") ∈ UVarAg "y")))
--        ⇒  (Neg (K (UVarAg "x")  (Neg (UVarAg "y" `plays` C))) )
--       )))

goal2responder' :: Stmt 
goal2responder' = 
    Conj [forAllAg [VarAg "x"] (
      (   (Neg (UVarAg "x" `named` VarName "a") ∧ (Neg (PubKey (VarAg "x") ∈ UVarName "a")))
       ⇒  (Neg (K (UVarAg "x")  (Neg (UVarName "a" `plays` C))) )
      )) | a <- names]

----
goal2responderVsSpy' :: Stmt -- same as above but vs Spy only
goal2responderVsSpy' =
    (Neg (existsHonest [VarAg "y"] (UVarAg "y" `plays` C)))  
    ∨
    ((forAllHonest [VarAg "a"]       
     (  (Neg (UVarAg "a" `plays` C))
      ⇒ (Neg (K (UName Spy) (Neg (UVarAg "a" `plays` C))))
     )
    )) 


---- GOAL II Minimal Anonymity of Initiator - An agent x can know the name of the initiator y only if (pubkey(name(x)) ∈ S_y) 
---- ∀a ∀x K_x(plays(a,A)) ⇒ pub(x)∈S_a ∨ named(x,a)   
---- ------------ test 1 -----------------
---- >>> sat privAuth (Neg goal2initiator)
---- Nothing
---- >>> sat privAuthX (Neg goal2initiator)
---- Nothing
---- -------------------------------------

-- ∀x ∀b K_x(¬plays(b,A)) ⇒ named(x,b) ∨ pub(x)∈S_b  
goal2initiator :: Stmt 
goal2initiator = 
    -- forAll [(UVar varx), (UVar vara)]       
    --   (     (plays (UVar vara) A)
    --    ⇒ ( Neg (K (UVar varx) (plays (UVar vara) A)) ∨ ((named (UVar varx) (Var vara) ∨ (PubKey (Var varx) ∈ (UVar vara)))))
    --   ) 
    -- easier equivalent formula
    forAllAg [VarAg "x"] (forAllHonest [VarAg "a"] (
      (   (Neg (UVarAg "x" `named` VarAg "a"))
       ⇒ (Neg (K (UVarAg "x")  (UVarAg "a" `plays`  A)) ∨ ((PubKey (VarAg "x" )) ∈ (UVarAg "a")))
      )))
            
---- GOAL II' Total Anonymity of Initiator - An agent x does not know that some name is not playing as initiator y only if (pubkey(name(x)) ∈ S_y) 
---- ∀a ∀x  (¬named(x,a))∧ ¬(named(a,Spy))  ⇒ pub(x)∈S_a ∨ ¬K_x(¬plays(a,A))   -- spy does not play any role so it's a bad counterex
goal2initiator' :: Stmt 
goal2initiator' = 
    forAllAg [VarAg "x"] (forAllHonest [VarAg "a"]
      (     (Neg (plays (UVarAg "a") A) ∧ Neg (named (UVarAg "x") (VarAg "a"))
       ⇒ ( Neg (K (UVarAg "x") (Neg (plays (UVarAg "a") A))) ∨ (PubKey (VarAg "x") ∈ (UVarAg "a"))))
      )) 
---- this gives spurious attacks (and only spurious attacks), e.g. [1.(a,C,1,[]):<-|b,N1,a|--{(b,N1)}_a]
---- spy knows that the agent it injected the first message is not an A-Agent, the receive event is allowed only if the receiver is a C agent
---- so there is no attack where there actually exists initiator action
---- a better formula would say: there is no initiator or agent x does not know who is not the initiator
---- 
---- for the version vs Anobody, needs 2 or more sessions for this, otherwise the A-agent implicitly knows everybody else is not playing A
---- for the version vs Spy, 1 session is enough
--goal2initiator'' :: Stmt 
--goal2initiator'' = 
--    (Neg (existsHonest [UVar vary] (UVar vary `plays` A)))   
--    ∨
--    (forAll [UVar varx] (forAllHonest [UVar vara]
--     (  (Neg (UVar vara `plays` A) ∧ Neg (UVar varx `named` Var vara))
--      ⇒ ((Neg (K (UVar varx) (Neg (UVar vara `plays` A))) ∨ (PubKey (Var varx) ∈ (UVar vara))))
--     ))
--    ) 

goal2initiatorVsSpy' :: Stmt -- same as above but vs Spy only
goal2initiatorVsSpy' =
    (Neg (existsHonest [VarAg "y"] (UVarAg "y" `plays` A)))   
    ∨
    ((forAllHonest [(VarAg "a")]       
     (  (Neg (UVarAg "a" `plays` A))
      ⇒ (Neg (K (UName Spy) (Neg (UVarAg "a" `plays` A))))
     )
    )) 


---- GOAL III Privacy of whitelist - who's in
---- -- ∀c:Names ∀a:UAg (¬named(a,c) ∧ ¬named(a,Spy)) ⇒ ¬ K_spy (K_c∈Sa)  
goal3Spy :: Stmt
goal3Spy =
   Conj [ ForAllAg (VarAg "a") $ (Neg  (UVarAg "a" `named` Grd (Name c) ) ∧ Neg  (UVarAg "a" `named` Grd (Name Spy))) ⇒ Neg (K (UAg spy) (Grd (PubKey (Name c)) ∈ (UVarAg "a")))| c <-names]

---- GOAL III Privacy of whitelist - who's not in
---- -- ∀c:Names ∀a:Unames (¬named(a,c) ∧ ¬named(a,Spy)) ⇒ ¬K_spy (¬(K_b∈Sag_a) )  
goal3Spy' :: Stmt
goal3Spy' =
    Conj [ ForAllAg (VarAg "a") $ (Neg (UVarAg "a" `named`  Grd (Name c)) ∧ Neg (UVarAg "a" `named` Grd (Name Spy))) ⇒ Neg (K (UAg spy)  (Neg (Grd (PubKey (Name c)) ∈ UVarAg "a")))| c <-names]

---- GOAL III Privacy of whitelist - who's in
---- the two goal3Spy can be generalised to account for other agents
----  ∀c:names ∀b:Unames ∃a:Unames (¬named(a,c) ∧ ¬named(a,b) ∧ ¬named(a,Spy)) ⇒ ¬K_b (K_c∈S_a)  
---- in addition a has to be ≠ Spy, everybody knows the whitelist of Spy contains everybody (we assumed that) 
goal3 :: Stmt
goal3 =
    Neg (Disj [ ExistsAg (VarAg "x") $ ExistsAg (VarAg "a") $ (Conj [Neg  (named (UVarAg "x") (Grd (Name c)) ),Neg  (named (UVarAg "a") (Grd (Name c)) ), Neg (named (UVarAg "x") (VarAg "a")), Neg (named (UVarAg "a") (Grd (Name Spy)))]) ∧ (K (UVarAg "x")  (Grd (PubKey (Name c)) ∈ (UVarAg "a")))| c <-names])

---- GOAL III Privacy of whitelist - who's not in
----  ∀c:names ∀b:Unames ∃a:Unames (¬named(a,c) ∧ ¬named(a,b)) ⇒ ¬K_b (¬K_c∈S_a)  
goal3' :: Stmt
goal3' =
    Neg (Disj [ ExistsAg (VarAg "x") $ ExistsAg (VarAg "a") $ (Conj [Neg  (named (UVarAg "x") (Grd (Name c)) ),Neg (named (UVarAg "a") (Grd (Name c)) ),  Neg (named (UVarAg "x") (VarAg "a"))]) ∧ (K (UVarAg "x")  (Neg (Grd (PubKey (Name c)) ∈ (UVarAg "a"))))| c <-names])



---- -- ∀a,b ⋅ (link_b (C,b) ∧ link_b (A,a)  → P link_a (C,b))
---- ------------ test -----------------
---- >>> sat privAuth (Neg weakAgreementCauthA)
---- Just [ 1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
---- ,1.(a,C,1,[Kb]):<-|b,N2,a|--{(b,N2)}_a
---- ,2.(a,C,1,[Kb]):--|N3|->{(a,N2,N3)}_b
---- ]
--weakAgreementCauthA :: Stmt 
--weakAgreementCauthA = 
--  Conj [      (EndLink (UName b) (AbsName C, Name b) ∧ EndLink (UName b) (AbsName A, Name a)) 
--        ⇒ (P (EndLink (UName a) (AbsName C, Name b))) 
--        | a <- names, b <- names, a/=b
--       ]

---- -- ∀a,b ⋅ (link_a (A,a) ∧ link_a (C,b)  → P link_b (A,a))
---- ------------ test -----------------
---- >>> sat privAuth (Neg weakAgreementAauthC)
---- Nothing
--weakAgreementAauthC :: Stmt
--weakAgreementAauthC = 
--  Conj [      (EndLink (UName a) (AbsName A, Name a) ∧ EndLink (UName a) (AbsName C, Name b)) 
--        ⇒ (P (EndLink (UName b) (AbsName A, Name a))) 
--        | a <- names, b <- names, a/=b
--       ]

---- -- ∀a,b ⋅ (link_b (A,a) ∧ link_b (C,b))  → P (link_a (Self,a)))
---- ------------ test -----------------
---- >>> sat privAuth (Neg alivenessCauthA)
---- Just [ 1.(a,A,1,[Kb]):--|N1|->{(a,N1)}_b
---- ,1.(a,C,1,[Kb]):<-|b,N2,a|--{(b,N2)}_a
---- ,2.(a,C,1,[Kb]):--|N3|->{(a,N2,N3)}_b
---- ]
--alivenessCauthA :: Stmt
--alivenessCauthA = 
--  Conj [      (EndLink (UName b) (AbsName C, Name b) ∧ EndLink (UName b) (AbsName A, Name a)) 
--        ⇒ (P (Link (UName a) (Self, Name a))) 
--        | a <- names, b <- names, a/=b
--       ]

---- -- ∀a,b ⋅ (link_a (A,a) ∧ link_a (C,b)  → P (link_b (A,b) ∨ link_b (B,b)))
---- ------------ test  -----------------
---- >>> sat privAuth (Neg alivenessAauthC)
---- Nothing
--alivenessAauthC ::  Stmt
--alivenessAauthC = 
--  Conj [  (EndLink (UName a)  (AbsName A, Name a) ∧ EndLink (UName a)  (AbsName C, Name b)) 
--        ⇒ (P (Link (UName b) (Self, Name b))) 
--        | a <- names, b <- names, a/=b
--       ]
