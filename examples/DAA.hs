{-|
Module      : DAA
Description : The signing phase of Direct Anonymous Attestation, symbolically.

A platform holds a secret f and a credential cert = sig_I(f) issued by the
issuer I during the join phase (which is not modelled: credentials are part of
the initial state).  To sign for a verifier's nonce nV the platform picks a
base zeta, forms the pseudonym N = nym(zeta, f) and proves

    DAA :  alpha_1 = sig_{beta_2}(alpha_0)   and   beta_1 = nym(beta_0, alpha_0)

with hidden components (f, cert, r) and public components (zeta, N, I, nV).

    V -> P : nV                      (random base)      |  < V , nV >   (basename)
    P -> V : zk_DAA( f , sig_I(f) , r ; zeta , nym(zeta,f) , I , nV )

  * random base : zeta is a fresh value;
  * basename    : zeta = h(V), fixed per verifier.

Models
  * honest   : one honest verifier, two platforms, verification on;
  * noverify : as above, the verifier does not run ver (negative control);
  * random   : three platforms, two signing sessions, the intruder as verifier;
  * basename : as random, with zeta = h(V) and two verifier names;
  * rogue    : as random, and the intruder holds platform 3's secret and credential;
  * clear    : as random, and the credential travels next to the proof (negative control).
-}
module DAA where
import ProtModel
import LogicSyntax
import HelperFunctions
import Checks
import Data.Maybe
import qualified Data.List as L

-- ---------------------------------------------------------------------------
-- statement and message patterns
-- ---------------------------------------------------------------------------

-- | DAA :  alpha_1 = sig_{beta_2}(alpha_0)  /\  beta_1 = nym(beta_0, alpha_0)
daa :: ZkStmt
daa = ZkStmt "DAA" [ (ZW 1, ZSign (ZP 2) (ZW 0)), (ZP 1, ZNym (ZP 0) (ZW 0)) ]

data Base = RandomBase | Basename deriving (Eq, Show)

data Variant = Variant
  { vName    :: String
  , vVerify  :: Bool    -- ^ the verifier runs ver on the proof
  , vBase    :: Base
  , vHonestV :: Bool    -- ^ honest verifier agents exist (otherwise the intruder verifies)
  , vSess    :: Int     -- ^ sessions per role
  , vPlats   :: [Int]   -- ^ platforms; platform i holds f_i and sig_I(f_i)
  , vRogue   :: [Int]   -- ^ platforms whose secret and credential the intruder holds
  , vClear   :: Bool    -- ^ the credential is sent in clear next to the proof
  }

issuer :: Term
issuer = Name (Issuer 1)

secretOf :: Int -> Term
secretOf i = Key (LKey i)

certOf :: Int -> Term
certOf i = Sign issuer (secretOf i)

zeta :: Variant -> AbsTerm
zeta v | vBase v == Basename = Hash (AbsName Vr)
       | otherwise           = AbsNonce NZ

-- | the proof as the platform builds it
proofP :: Variant -> AbsTerm
proofP v = Zk daa [AbsKey KF, Sign (AbsName Iss) (AbsKey KF), AbsNonce NRn]
                  [zeta v, Nym (zeta v) (AbsKey KF), AbsName Iss, AbsNonce NV]

-- | the proof as the verifier parses it: the signer of the hidden credential
-- is a variable of its own (DY), unrelated to the public issuer
proofV :: Variant -> AbsTerm
proofV v = Zk daa [AbsKey KF, Sign (AbsName DY) (AbsKey KF), AbsNonce NRn]
                  [zeta v, Nym (zeta v) (AbsKey KF), AbsName Iss, AbsNonce NV]

actionsOf :: Variant -> [Action]
actionsOf v =
     [ Send 1 Vr true [AbsNonce NV] challenge | vHonestV v ]
  ++ [ Rec  1 Pr trues challenge
     , Send 2 Pr true fresh msgP ]
  ++ [ Rec  2 Vr (true, post) (proofV v) | vHonestV v ]
  where
    challenge | vBase v == Basename = Pair (AbsName Vr) (AbsNonce NV)
              | otherwise           = AbsNonce NV
    fresh     | vBase v == Basename = [AbsNonce NRn]
              | otherwise           = [AbsNonce NZ, AbsNonce NRn]
    msgP      | vClear v            = Pair (Sign (AbsName Iss) (AbsKey KF)) (proofP v)
              | otherwise           = proofP v
    post      | vVerify v           = Verifies (UAbsName Vr) (proofV v)
              | otherwise           = true

verifierNames :: Variant -> [Name]
verifierNames v | vHonestV v          = [Verifier 1]
                | vBase v == Basename = [Verifier 1, Verifier 2]
                | otherwise           = []

-- | The intruder: a secret k0 of its own with a self-issued credential, the
-- verifier names, and the secrets and credentials of the rogue platforms.
spyOf :: Variant -> Agent
spyOf v = Agent
  { _name = Spy, _sess = Nothing, _role = Nothing, _id = 0
  , _iniTerms = [Key (LKey 0), Name Spy, PrivKey (Name Spy), issuer]
             ++ [Name n | n <- verifierNames v]
             ++ concat [[secretOf i, certOf i] | i <- vRogue v]
  , _iniFrame = []
  , _indistActions = [[a] | a <- actionsOf v]
  }

platformAgents :: Variant -> [Agent]
platformAgents v =
  [ Agent { _name = Prover i, _sess = Just s, _role = Just Pr, _id = n
          , _iniTerms = [secretOf i, certOf i, Name (Prover i), issuer]
          , _iniFrame = [ (Role Pr, Name (Prover i)), (Self, Name (Prover i)), (AbsName Pr, Name (Prover i))
                        , (AbsKey KF, secretOf i), (AbsName Iss, issuer) ]
          , _indistActions = [] }
  | ((s, i), n) <- zip [ (s, i) | s <- [1 .. vSess v], i <- vPlats v ] [1 ..] ]

verifierAgents :: Variant -> [Agent]
verifierAgents v =
  [ Agent { _name = nm, _sess = Just s, _role = Just Vr, _id = 100 + s
          , _iniTerms = [Name nm, issuer]
          , _iniFrame = [ (Role Vr, Name nm), (Self, Name nm), (AbsName Vr, Name nm), (AbsName Iss, issuer) ]
          , _indistActions = [] }
  | vHonestV v, s <- [1 .. vSess v], nm <- verifierNames v ]

protOf :: Variant -> ProtocolSpec
protOf v = ProtocolSpec
  { _spy = spyOf v, _roles = [Pr, Vr]
  , _honestAgents = platformAgents v ++ verifierAgents v
  , _actions = actionsOf v, _protName = "DAA-" ++ vName v }

-- ---------------------------------------------------------------------------
-- the six models
-- ---------------------------------------------------------------------------
vHonest, vHonestR, vNoVerify, vRandom, vBasename, vRogueM, vClearM :: Variant
vHonestR  = Variant "honest+rogue" True RandomBase True 1 [1, 2, 3] [3] False
vHonest   = Variant "honest"   True  RandomBase True  1 [1, 2]    []  False
vNoVerify = Variant "noverify" False RandomBase True  1 [1, 2]    []  False
vRandom   = Variant "random"   True  RandomBase False 2 [1, 2, 3] []  False
vBasename = Variant "basename" True  Basename   False 2 [1, 2, 3] []  False
vRogueM   = Variant "rogue"    True  RandomBase False 2 [1, 2, 3] [3] False
vClearM   = Variant "clear"    True  RandomBase False 2 [1, 2, 3] []  True

mHonest, mHonestR, mNoVerify, mRandom, mBasename, mRogue, mClear :: [Trace]
mHonestR  = build (protOf vHonestR)
mHonest   = build (protOf vHonest)
mNoVerify = build (protOf vNoVerify)
mRandom   = build (protOf vRandom)
mBasename = build (protOf vBasename)
mRogue    = build (protOf vRogueM)
mClear    = build (protOf vClearM)

-- ---------------------------------------------------------------------------
-- properties
-- ---------------------------------------------------------------------------
platNames :: Variant -> [Name]
platNames v = [Prover i | i <- vPlats v]

honestPlatNames :: Variant -> [Name]
honestPlatNames v = [Prover i | i <- vPlats v, i `notElem` vRogue v]

accepted :: Var -> Stmt
accepted x = EndLink (UVarAg x) (Role Vr, VarAg x)

-- | the state-based core of soundness: the pseudonym a verifier accepted is
-- nym(z, f) for a secret f that some participant holds together with a
-- credential on f by the issuer
certified :: Stmt
certified =
  ExistsNonce (VarNonce "z") (ExistsKey (VarKey "f")
    (Link (UVarAg "x") (Nym (AbsNonce NZ) (AbsKey KF), Nym (VarNonce "z") (VarKey "f"))
       ∧ ExistsAg (VarAg "y")
           (Has (UVarAg "y") (VarKey "f") ∧ Has (UVarAg "y") (Sign (Grd issuer) (VarKey "f")))))

-- | Soundness, state-based
sound0 :: Stmt
sound0 = forAllHonest [VarAg "x"] (accepted "x" `imp` certified)

-- | Soundness, de dicto: a verifier that accepts KNOWS that a certified
-- platform secret lies behind the pseudonym -- without knowing which.
sound :: Stmt
sound = forAllHonest [VarAg "x"] (accepted "x" `imp` K (UVarAg "x") certified)

-- | Possession secrecy of the platform secrets and credentials
secrecy :: Variant -> Stmt
secrecy v = Conj
  [ ForAllKey (VarKey "k")
      (Link (UName a) (AbsKey KF, VarKey "k") `imp`
         (Neg (Has (UAg (spyOf v)) (VarKey "k"))
            ∧ Neg (Has (UAg (spyOf v)) (Sign (Grd issuer) (VarKey "k")))))
  | a <- honestPlatNames v ]

-- | Strong unlinkability (CSF'24, by name, two sessions)
strongUnlink :: Variant -> Stmt
strongUnlink v = Neg (K (UAg (spyOf v))
  (existsName [VarName "t"]
     (forAllHonest [VarAg "x"]
        (Link (UVarAg "x") (Role Pr, VarAg "x") `imp` Link (UVarAg "x") (Self, VarName "t")))))

-- | Minimal anonymity of the given platforms
minAnon :: Variant -> [Name] -> Stmt
minAnon v as = Conj [ Neg (K (UAg (spyOf v)) (plays (UName a) Pr)) | a <- as ]

-- | Total anonymity of the given platforms
totAnon :: Variant -> [Name] -> Stmt
totAnon v as = Conj [ Neg (K (UAg (spyOf v)) (Neg (plays (UName a) Pr))) | a <- as ]

-- | Each of the given platforms, once it completes a signature, is recognised
-- by the intruder (expected for rogue platforms, and for those only)
tagged :: Variant -> [Int] -> Stmt
tagged v is = Conj
  [ EndLink (UName (Prover i)) (Role Pr, Grd (Name (Prover i))) `imp` K (UAg (spyOf v)) (plays (UName (Prover i)) Pr)
  | i <- is ]

-- state selectors -----------------------------------------------------------
allDone :: Variant -> Trace -> Bool
allDone v tr = length (doneWith Pr 2 tr) == vSess v

-- | the verifier names under which the completed sessions signed
basenames :: Trace -> [Term]
basenames tr = [ t | x <- doneWith Pr 2 tr, (AbsName Vr, t) <- frame x tr ]

distinctBases :: Variant -> Trace -> Bool
distinctBases v tr = allDone v tr && length (L.nub (basenames tr)) == vSess v

sameBase :: Variant -> Trace -> Bool
sameBase v tr = allDone v tr && length (L.nub (basenames tr)) == 1

noRogueSession :: Variant -> Trace -> Bool
noRogueSession v tr = allDone v tr && and [ _name x `elem` honestPlatNames v | x <- doneWith Pr 2 tr ]

-- ---------------------------------------------------------------------------
-- checks
-- ---------------------------------------------------------------------------
checks :: [Check]
checks =
  [ chk "D1"  vHonest   mHonest   "a certified secret is held by a participant (state-based)" (const True)              sound0                                      True
  , chk "D2"  vHonest   mHonest   "the verifier knows that a certified secret is held"        (const True)              sound                                       True
  , chk "D3"  vHonest   mHonest   "possession secrecy of secrets and credentials"             (const True)              (secrecy vHonest)                           True
  , chk "D4"  vHonestR  mHonestR  "a certified secret is held by a participant (state-based)" (const True)              sound0                                      True
  , chk "D5"  vHonestR  mHonestR  "the verifier knows that a certified secret is held"        (const True)              sound                                       True
  , chk "D6"  vNoVerify mNoVerify "a certified secret is held by a participant (state-based)" (const True)              sound0                                      False
  , chk "D7"  vNoVerify mNoVerify "the verifier knows that a certified secret is held"        (const True)              sound                                       False
  , chk "D8"  vRandom   mRandom   "strong unlinkability of signatures"                        (allDone vRandom)         (strongUnlink vRandom)                      True
  , chk "D9"  vRandom   mRandom   "minimal anonymity of platforms"                            (const True)              (minAnon vRandom (platNames vRandom))       True
  , chk "D10" vRandom   mRandom   "total anonymity of platforms"                              (allDone vRandom)         (totAnon vRandom (platNames vRandom))       True
  , chk "D11" vBasename mBasename "strong unlinkability, one basename"                        (sameBase vBasename)      (strongUnlink vBasename)                    False
  , chk "D12" vBasename mBasename "strong unlinkability, distinct basenames"                  (distinctBases vBasename) (strongUnlink vBasename)                    True
  , chk "D13" vBasename mBasename "minimal anonymity of platforms"                            (const True)              (minAnon vBasename (platNames vBasename))   True
  , chk "D14" vRogueM   mRogue    "a rogue platform's signature is recognised"                (const True)              (tagged vRogueM (vRogue vRogueM))           True
  , chk "D15" vRogueM   mRogue    "minimal anonymity of the other platforms"                  (const True)              (minAnon vRogueM (honestPlatNames vRogueM)) True
  , chk "D16" vRogueM   mRogue    "strong unlinkability among the other platforms"            (noRogueSession vRogueM)  (strongUnlink vRogueM)                      True
  , chk "D17" vClearM   mClear    "possession secrecy of secrets and credentials"             (const True)              (secrecy vClearM)                           False
  , chk "D18" vClearM   mClear    "minimal anonymity of platforms"                            (const True)              (minAnon vClearM (platNames vClearM))       False
  , chk "D19" vClearM   mClear    "strong unlinkability of signatures"                        (allDone vClearM)         (strongUnlink vClearM)                      False
  , chk "D20" vClearM   mClear    "total anonymity of platforms"                              (allDone vClearM)         (totAnon vClearM (platNames vClearM))       False
  , chk "D21" vRandom   mRandom   "platform 3's signature is recognised (no leak)"            (const True)              (tagged vRandom [3])                        False
  ]
  where chk i v m what sel prop e = Check i ("DAA/" ++ vName v) what (protOf v) m sel prop e

sanity :: [String]
sanity =
  [ "DAA/" ++ vName v ++ ": states=" ++ show (length m)
      ++ " honest-sends-synthesizable=" ++ show (honestSendsOK m)
      ++ " fresh-distinct=" ++ show (freshDistinct m)
      ++ " verifier-accepts=" ++ show (length [() | tr <- m, not (null (doneWith Vr 2 tr))])
      ++ " both-roles-complete=" ++ show (length [() | tr <- m, not (null (doneWith Vr 2 tr)), not (null (doneWith Pr 2 tr))])
      ++ " platforms-complete=" ++ show (length [() | tr <- m, allDone v tr])
      ++ " rogue-signs=" ++ show (length [() | tr <- m, or [_name x `notElem` honestPlatNames v | x <- doneWith Pr 2 tr]])
  | (v, m) <- [ (vHonest, mHonest), (vHonestR, mHonestR), (vNoVerify, mNoVerify), (vRandom, mRandom)
              , (vBasename, mBasename), (vRogueM, mRogue), (vClearM, mClear) ] ]
