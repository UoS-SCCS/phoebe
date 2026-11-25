{-|
Module      : Schnorr
Description : A Schnorr-style identification scheme with a symbolic proof of knowledge.

    V -> P : nV
    P -> V : < h(k) , zk_DL( k , r ; h(k) , nV ) >

The prover holds a long-term secret k; h(k) plays the part of the public key
g^k.  The statement DL says: "I know w such that the public value equals h(w)".
The proof is bound to the verifier's challenge nV and carries fresh
randomness r among its hidden components.

Models
  * honest   : one prover name whose secret ranges over two candidates, one
               honest verifier, verification on;
  * noverify : as above, but the verifier does not run ver (negative control);
  * reveal   : identification by showing the secret (negative control);
  * link     : three provers, two prover sessions, the intruder as verifier;
  * reveal-anon : `reveal` with two prover names sharing the candidate secrets;
  * bound    : `honest` with a single candidate secret, i.e. a public binding
               between the prover's name and its secret.
-}
module Schnorr where
import ProtModel
import LogicSyntax
import HelperFunctions
import Checks
import Data.Maybe
import qualified Data.List as L

-- ---------------------------------------------------------------------------
-- statement and message patterns
-- ---------------------------------------------------------------------------

-- | DL :  beta_0 = h(alpha_0)
dl :: ZkStmt
dl = ZkStmt "DL" [(ZP 0, ZHash (ZW 0))]

-- | the proof as the prover builds it
proofP :: AbsTerm
proofP = Zk dl [AbsKey KF, AbsNonce NRn] [Hash (AbsKey KF), AbsNonce NV]

-- | the proof as the verifier parses it: the hidden part is unconstrained
proofV :: AbsTerm
proofV = Zk dl [AbsKey KF2, AbsNonce NRn] [Hash (AbsKey KF1), AbsNonce NV]

data Variant = Variant
  { vName    :: String
  , vVerify  :: Bool             -- ^ the verifier runs ver on the proof
  , vReveal  :: Bool             -- ^ the prover shows its secret instead of proving
  , vHonestV :: Bool             -- ^ honest verifier agents exist (otherwise the intruder verifies)
  , vSess    :: Int              -- ^ sessions per role
  , vProvers :: [(Name, [Key])]  -- ^ prover names with the candidate values of their secret
  }

verifierName :: Name
verifierName = Verifier 1

actionsOf :: Variant -> [Action]
actionsOf v =
     [ Send 1 Vr true [AbsNonce NV] (AbsNonce NV) | vHonestV v ]
  ++ [ Rec  1 Pr trues (AbsNonce NV)
     , Send 2 Pr true [AbsNonce NRn] msgP ]
  ++ [ Rec  2 Vr (true, post) msgV | vHonestV v ]
  where
    msgP | vReveal v = Pair (Hash (AbsKey KF)) (AbsKey KF)
         | otherwise = Pair (Hash (AbsKey KF)) proofP
    msgV | vReveal v = Pair (Hash (AbsKey KF1)) (AbsKey KF1)
         | otherwise = Pair (Hash (AbsKey KF1)) proofV
    post | vVerify v && not (vReveal v) = Verifies (UAbsName Vr) proofV
         | otherwise                    = true

-- | the intruder: its own secret k0, and the directory of public values
spyOf :: Variant -> Agent
spyOf v = Agent
  { _name = Spy, _sess = Nothing, _role = Nothing, _id = 0
  , _iniTerms = [Key (LKey 0)] ++ L.nub [Hash (Key k) | (_, ks) <- vProvers v, k <- ks]
  , _iniFrame = []
  , _indistActions = [[a] | a <- actionsOf v]
  }

-- | A prover agent.  The entry for `AbsList Self` makes the secret constant per
-- name within one execution (the tool keeps that entry constant per name).
proverAgents :: Variant -> [Agent]
proverAgents v =
  [ Agent { _name = nm, _sess = Just s, _role = Just Pr, _id = i
          , _iniTerms = [Key k, Name nm]
          , _iniFrame = [ (Role Pr, Name nm), (Self, Name nm), (AbsName Pr, Name nm)
                        , (AbsKey KF, Key k), (AbsList Self, Tuple [Key k]) ]
          , _indistActions = [] }
  | ((s, nm, k), i) <- zip [ (s, nm, k) | s <- [1 .. vSess v], (nm, ks) <- vProvers v, k <- ks ] [1 ..] ]

verifierAgents :: Variant -> [Agent]
verifierAgents v =
  [ Agent { _name = verifierName, _sess = Just s, _role = Just Vr, _id = 100 + s
          , _iniTerms = [Name verifierName]
          , _iniFrame = [ (Role Vr, Name verifierName), (Self, Name verifierName), (AbsName Vr, Name verifierName) ]
          , _indistActions = [] }
  | vHonestV v, s <- [1 .. vSess v] ]

protOf :: Variant -> ProtocolSpec
protOf v = ProtocolSpec
  { _spy = spyOf v, _roles = [Pr, Vr]
  , _honestAgents = proverAgents v ++ verifierAgents v
  , _actions = actionsOf v, _protName = "Schnorr-" ++ vName v }

-- ---------------------------------------------------------------------------
-- the four models
-- ---------------------------------------------------------------------------
k1, k2 :: Key
k1 = LKey 1
k2 = LKey 2

vHonest, vNoVerify, vRevealed, vLink, vRevealAnon, vBound :: Variant
vRevealAnon = Variant "reveal-anon" True True  True 1 [(Prover 1, [k1, k2]), (Prover 2, [k1, k2])]
vBound      = Variant "bound"       True False True 1 [(Prover 1, [k1])]
vHonest   = Variant "honest"   True  False True  1 [(Prover 1, [k1, k2])]
vNoVerify = Variant "noverify" False False True  1 [(Prover 1, [k1, k2])]
vRevealed = Variant "reveal"   True  True  True  1 [(Prover 1, [k1, k2])]
vLink     = Variant "link"     True  False False 2 [(Prover 1, [k1]), (Prover 2, [k2]), (Prover 3, [LKey 3])]

mHonest, mNoVerify, mRevealed, mLink, mRevealAnon, mBound :: [Trace]
mRevealAnon = build (protOf vRevealAnon)
mBound      = build (protOf vBound)
mHonest   = build (protOf vHonest)
mNoVerify = build (protOf vNoVerify)
mRevealed = build (protOf vRevealed)
mLink     = build (protOf vLink)

-- ---------------------------------------------------------------------------
-- properties
-- ---------------------------------------------------------------------------

-- | verifier x has completed its role
accepted :: Var -> Stmt
accepted x = EndLink (UVarAg x) (Role Vr, VarAg x)

-- | Proof of knowledge, de dicto: a verifier that accepts KNOWS that some
-- participant holds a preimage of the public value it accepted.
pok :: Stmt
pok = forAllHonest [VarAg "x"]
        (accepted "x" `imp`
           K (UVarAg "x")
             (ExistsKey (VarKey "k")
                (Link (UVarAg "x") (Hash (AbsKey KF1), Hash (VarKey "k"))
                   ∧ ExistsAg (VarAg "y") (Has (UVarAg "y") (VarKey "k")))))

-- | The state-based core of `pok`, without the knowledge operator: the public
-- value a verifier accepted has a preimage held by some participant.
pok0 :: Stmt
pok0 = forAllHonest [VarAg "x"]
        (accepted "x" `imp`
             (ExistsKey (VarKey "k")
                (Link (UVarAg "x") (Hash (AbsKey KF1), Hash (VarKey "k"))
                   ∧ ExistsAg (VarAg "y") (Has (UVarAg "y") (VarKey "k")))))

-- | No de re knowledge: there is no value k of which an accepting verifier
-- knows that it is the witness behind the public value.  Together with `pok`
-- this is the epistemic reading of a zero-knowledge proof of knowledge:
-- K_x (exists k ...) holds, (exists k) K_x (...) does not.
noDeRe :: Stmt
noDeRe = forAllHonest [VarAg "x"]
        (accepted "x" `imp`
           Neg (ExistsKey (VarKey "k")
                  (K (UVarAg "x")
                     (Link (UVarAg "x") (Hash (AbsKey KF1), Hash (VarKey "k"))
                        ∧ ExistsAg (VarAg "y") (Has (UVarAg "y") (VarKey "k"))))))

-- | Possession secrecy: neither the intruder nor a verifier ever holds a prover's secret.
secrecy :: Variant -> Stmt
secrecy v = Conj
  [ ForAllKey (VarKey "k")
      (Link (UName a) (AbsKey KF, VarKey "k") `imp`
         (Neg (Has (UAg (spyOf v)) (VarKey "k"))
            ∧ forAllHonest [VarAg "x"] (plays (UVarAg "x") Vr `imp` Neg (Has (UVarAg "x") (VarKey "k")))))
  | (a, _) <- vProvers v ]

-- | Minimal witness hiding w.r.t. the intruder: for no value k does the
-- intruder know that prover a uses k.
minHidingSpy :: Variant -> Stmt
minHidingSpy v = Conj
  [ ForAllKey (VarKey "k") (Neg (K (UAg (spyOf v)) (Link (UName a) (AbsKey KF, VarKey "k"))))
  | (a, _) <- vProvers v ]

-- | Total witness hiding (witness indistinguishability) w.r.t. the intruder:
-- once a has taken part, every candidate value remains possible for it.
totHidingSpy :: Variant -> Stmt
totHidingSpy v = Conj
  [ plays (UName a) Pr `imp` Neg (K (UAg (spyOf v)) (Neg (Link (UName a) (AbsKey KF, Grd (Key c)))))
  | (a, cs) <- vProvers v, c <- cs ]

-- | the same two notions w.r.t. every honest verifier
minHidingVer :: Variant -> Stmt
minHidingVer v = forAllHonest [VarAg "x"] (plays (UVarAg "x") Vr `imp` Conj
  [ ForAllKey (VarKey "k") (Neg (K (UVarAg "x") (Link (UName a) (AbsKey KF, VarKey "k"))))
  | (a, _) <- vProvers v ])

totHidingVer :: Variant -> Stmt
totHidingVer v = forAllHonest [VarAg "x"] (plays (UVarAg "x") Vr `imp` Conj
  [ plays (UName a) Pr `imp` Neg (K (UVarAg "x") (Neg (Link (UName a) (AbsKey KF, Grd (Key c)))))
  | (a, cs) <- vProvers v, c <- cs ])

-- | Strong unlinkability (CSF'24, by name, two sessions): the intruder does
-- not know that all prover sessions belong to one prover.
strongUnlink :: Variant -> Stmt
strongUnlink v = Neg (K (UAg (spyOf v))
  (existsName [VarName "t"]
     (forAllHonest [VarAg "x"]
        (Link (UVarAg "x") (Role Pr, VarAg "x") `imp` Link (UVarAg "x") (Self, VarName "t")))))

-- | Weak unlinkability of CSF'24, by name: there are no two distinct prover
-- agents of which the intruder knows that they have the same name.  The agents
-- are bound outside K, so this fails only if the intruder can also tell who
-- they are.
weakUnlink :: Variant -> Stmt
weakUnlink v = Neg (existsHonest [VarAg "x", VarAg "y"]
  (plays (UVarAg "x") Pr ∧ plays (UVarAg "y") Pr
     ∧ K (UAg (spyOf v))
         (ExistsName (VarName "t")
            (UVarAg "x" `named` VarName "t" ∧ UVarAg "y" `named` VarName "t"
               ∧ nEqI (UVarAg "x") (UVarAg "y")))))

-- | Minimal anonymity: the intruder never knows that a given prover took part.
minAnon :: Variant -> Stmt
minAnon v = Conj [ Neg (K (UAg (spyOf v)) (plays (UName a) Pr)) | (a, _) <- vProvers v ]

-- | Total anonymity: once somebody proved, every prover remains a possible participant.
totAnon :: Variant -> Stmt
totAnon v = Conj [ Neg (K (UAg (spyOf v)) (Neg (plays (UName a) Pr))) | (a, _) <- vProvers v ]

allDone :: Variant -> Trace -> Bool
allDone v tr = length (doneWith Pr 2 tr) == vSess v

-- ---------------------------------------------------------------------------
-- checks
-- ---------------------------------------------------------------------------
checks :: [Check]
checks =
  [ chk "S1"  vHonest     mHonest     "a witness is held by a participant (state-based)"   (const True)    pok0                       True
  , chk "S2"  vHonest     mHonest     "the verifier knows that a witness is held"          (const True)    pok                        True
  , chk "S3"  vHonest     mHonest     "the verifier has no de re knowledge of the witness" (const True)    noDeRe                     True
  , chk "S4"  vHonest     mHonest     "possession secrecy of the witness"                  (const True)    (secrecy vHonest)          True
  , chk "S5"  vHonest     mHonest     "minimal witness hiding, intruder"                   (const True)    (minHidingSpy vHonest)     True
  , chk "S6"  vHonest     mHonest     "total witness hiding, intruder"                     (const True)    (totHidingSpy vHonest)     True
  , chk "S7"  vHonest     mHonest     "minimal witness hiding, verifier"                   (const True)    (minHidingVer vHonest)     True
  , chk "S8"  vHonest     mHonest     "total witness hiding, verifier"                     (const True)    (totHidingVer vHonest)     True
  , chk "S9"  vNoVerify   mNoVerify   "a witness is held by a participant (state-based)"   (const True)    pok0                       False
  , chk "S10" vNoVerify   mNoVerify   "the verifier knows that a witness is held"          (const True)    pok                        False
  , chk "S11" vRevealed   mRevealed   "possession secrecy of the witness"                  (const True)    (secrecy vRevealed)        False
  , chk "S12" vRevealed   mRevealed   "minimal witness hiding, intruder"                   (const True)    (minHidingSpy vRevealed)   False
  , chk "S13" vRevealed   mRevealed   "total witness hiding, intruder"                     (const True)    (totHidingSpy vRevealed)   False
  , chk "S14" vRevealed   mRevealed   "the verifier has no de re knowledge of the witness" (const True)    noDeRe                     False
  , chk "S15" vRevealAnon mRevealAnon "possession secrecy of the witness"                  (const True)    (secrecy vRevealAnon)      False
  , chk "S16" vRevealAnon mRevealAnon "minimal witness hiding, intruder"                   (const True)    (minHidingSpy vRevealAnon) True
  , chk "S17" vBound      mBound      "possession secrecy of the witness"                  (const True)    (secrecy vBound)           True
  , chk "S18" vBound      mBound      "minimal witness hiding, intruder"                   (const True)    (minHidingSpy vBound)      False
  , chk "S19" vLink       mLink       "strong unlinkability of prover sessions"            (allDone vLink) (strongUnlink vLink)       False
  , chk "S20" vLink       mLink       "minimal anonymity of provers"                       (const True)    (minAnon vLink)            True
  , chk "S21" vLink       mLink       "total anonymity of provers"                         (allDone vLink) (totAnon vLink)            True
  -- further negative controls
  , chk "S22" vRevealed   mRevealed   "minimal witness hiding, verifier"                   (const True)    (minHidingVer vRevealed)   False
  , chk "S23" vRevealed   mRevealed   "total witness hiding, verifier"                     (const True)    (totHidingVer vRevealed)   False
  , chk "S24" vBound      mBound      "minimal anonymity of provers"                       (const True)    (minAnon vBound)           False
  -- weak unlinkability binds the two agents outside K: it holds here although S19 fails
  , chk "S25" vLink       mLink       "weak unlinkability of prover sessions"              (allDone vLink) (weakUnlink vLink)         True
  ]
  where chk i v m what sel prop e = Check i ("Schnorr/" ++ vName v) what (protOf v) m sel prop e

-- | sanity: honest sends are synthesizable; some verifier accepts; some honest proof is accepted
sanity :: [String]
sanity =
  [ "Schnorr/" ++ vName v ++ ": states=" ++ show (length m)
      ++ " honest-sends-synthesizable=" ++ show (honestSendsOK m)
      ++ " fresh-distinct=" ++ show (freshDistinct m)
      ++ " verifier-accepts=" ++ show (length [() | tr <- m, not (null (doneWith Vr 2 tr))])
      ++ " both-roles-complete=" ++ show (length [() | tr <- m, not (null (doneWith Vr 2 tr)), not (null (doneWith Pr 2 tr))])
      ++ " provers-complete=" ++ show (length [() | tr <- m, allDone v tr])
  | (v, m) <- [ (vHonest, mHonest), (vNoVerify, mNoVerify), (vRevealed, mRevealed), (vLink, mLink)
              , (vRevealAnon, mRevealAnon), (vBound, mBound) ] ]
