{-# LANGUAGE GADTs #-}
module AKMA
  ( akmaStrong, akmapStrong          -- strong unlinkability of UE-AKIDs
  , akmaWeak,   akmapWeak            -- weak   unlinkability of UE-AKIDs
  , akmaPerAfStrong                  -- ablation: per-AF-only AKID
  , akmaCrossAf                      -- cross-AF attack witness
  , akmaNonVacuity, akmapNonVacuity  -- non-vacuity
  ) where

import ProtModel
import Data.Tree
import Data.Maybe
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as S
import HelperFunctions
import LogicSyntax

{-|
Module      : AKMA
Description : Privacy of the 5G AKMA procedure -- unlinkability of UE-AKIDs

Models the Ua*-phase of AKMA and checks "Unlinkability of UE-AKIDs and AFs"
(Def. 4 of Boureanu-Wesemeyer-Rajaona-Schneider-Treharne, EuroS&P 2025).

The Ua* observable is AKMA step 1:  UE --> AF : AKID , AF_ID.

The crux (paper Note 1, Sec. 5.2.4.1): in AKMA the AKID is GLOBAL -- one AKID
identifies a UE to *all* AFs -- so a UE that makes several AKMA requests presents
the *same* AKID each time and the attacker can link those requests, tracking the
UE.  This is structurally the Basic-Hash unlinkability failure (a fixed
identifier reused across sessions), so we reuse Phoebe's Basic-Hash-style
unlinkability formulae with the AKID (slot AbsKey KT) as the UE identity.

  * 'akma'  : AKID global -- akid(UE) is one key reused across the UE's requests.
     With more requests than UEs, the attacker knows (pigeonhole, in every
     indistinguishable world) that two requests share an AKID.  ATTACK.
  * 'akmap' : AKID freshly (re)generated per request (AKMA^p counteraction i:
     A-TID = KDF(.., AF_ID, ..), one AKID per AF_ID / registration), so no
     collision is forced.  HOLDS.

Abstractions: the trusted core and secure core<->AF channels are omitted (T10);
the AF is the request's addressee.  We keep the model to the single identifying
Ua* send, exactly as Basic-Hash keeps the tag's identifying emission.

Relies on the corrected key-possession-checked `analz`.
-}

-- ============================ PARAMETERS ==================================

maxSessions :: Int
maxSessions = 3          -- witness: three completed AKMA requests ...
-- ... presented by only two UEs across two AFs  =>  pigeonhole.

-- Hand-picked, minimal set of UE-requests, kept small so `build` stays tractable.
-- Each entry is (UE, AF, session): every UE contacts BOTH AFs, so an attack trace
-- can exhibit one global AKID re-appearing at two different AFs (cross-AF tracking).
ueRequests :: [(Name, Name, Int)]
ueRequests =
    [ (ue, af, sess)
    | sess <- [1 .. maxSessions]      -- one global "slot" per session
    , ue   <- [Tag 1, Tag 2]          -- two UEs
    , af   <- [Reader 1, Reader 2]     -- two AFs; each UE may contact either
    ]

-- Global AKID (AKMA): one AKID per UE, reused for every AF (paper's Note 1).
akidGlobal :: Name -> Term
akidGlobal (Tag i) = Key (LKey i)
akidGlobal _       = Key (LKey 0)

-- Per-AF AKID, fixed across registrations (ABLATION): distinct per (UE, AF) but
-- reused whenever the UE re-contacts the same AF -- shows per-AF derivation ALONE
-- is not enough (a UE re-contacting one AF stays linkable there).
akidPerAf :: Name -> Name -> Term
akidPerAf ue af = Key (LShared ue af)

-- AKMA^p AKID (HEADLINE): per AF_ID AND regenerated per registration
-- (counteraction i) -- a fresh AKID for every request, so nothing is ever reused.
akidFresh :: Name -> Name -> Int -> Term
akidFresh (Tag i) (Reader j) sess = Key (LKey (1000 * i + 100 * j + sess))
akidFresh _       _          sess = Key (LKey sess)

-- ============================ MESSAGE ====================================
--   AbsKey KT : the UE's AKID ;  AbsName R : the AF_ID.
request :: AbsTerm
request = Pair (AbsKey KT) (AbsName R)

actions :: [Action]
actions = [ Send 1 T true [] request ]   -- UE -> AF : AKID , AF_ID  (Ua* observable)

-- ============================ AGENTS =====================================

-- AKID assignment strategies.
data Akid = Global | PerAf | Fresh

pickAkid :: Akid -> Name -> Name -> Int -> Term
pickAkid Global ue af sess = akidGlobal ue
pickAkid PerAf  ue af sess = akidPerAf ue af
pickAkid Fresh  ue af sess = akidFresh ue af sess

ueAgents :: Akid -> [Agent]
ueAgents strat =
    [ Agent
        { _name  = ue , _sess = Just sess , _role = Just T , _id = idn
        , _iniTerms = [ theAkid, Name ue ]
        , _iniFrame =
            [ (Self,      Name ue)
            , (Role T,    Name ue)
            , (AbsName T, Name ue)
            , (AbsKey KT, theAkid)     -- this request's AKID
            , (AbsName R, Name af)     -- the AF contacted
            ]
        , _indistActions = []
        }
    | ((ue, af, sess), idn) <- zip ueRequests [1 ..]
    , let theAkid = pickAkid strat ue af sess
    ]

spy :: Agent
spy = Agent
    { _name = Spy , _sess = Nothing, _role = Nothing
    , _iniTerms = [ Key (LKey 0) ] , _iniFrame = [] , _id = 0
    , _indistActions = [ [a] | a <- actions ]
    }

mkSpec :: String -> Akid -> ProtocolSpec
mkSpec nm strat = ProtocolSpec
    { _spy = spy , _roles = [T, R]
    , _honestAgents = ueAgents strat
    , _actions = actions , _protName = nm }

akma      = mkSpec "AKMA"      Global   -- standard AKMA: global AKID
akmaPerAf = mkSpec "AKMAperAf" PerAf    -- ablation: per-AF AKID, fixed per registration
akmap     = mkSpec "AKMAp"     Fresh    -- AKMA^p: per-AF AKID regenerated per registration

-- ============================ PRIVACY NOTIONS ============================

-- Strong: the attacker knows every UE-request's AKID lies in a set of at most
-- (maxSessions-1) values -- so among `maxSessions` requests two share an AKID
-- (a UE is provably re-used / tracked).
negStrongUnlink :: Stmt
negStrongUnlink =
    K (UAg spy)
      ( existsKey akidVars
          ( forAllHonest [VarAg "x"]
              ( Link (UVarAg "x") (Role T, VarAg "x")
                ⇒ Disj [ Link (UVarAg "x") (AbsKey KT, av) | av <- akidVars ] ) ) )
  where akidVars = [ VarKey ("a" ++ show i) | i <- [1 .. maxSessions - 1] ]

-- Weak: two distinct honest UE-requests are known to carry the same AKID.
negWeakUnlink :: Stmt
negWeakUnlink =
    existsHonest [VarAg "x", VarAg "y"]
      ( UVarAg "x" `plays` T
      ∧ UVarAg "y" `plays` T
      ∧ K (UAg spy)
          ( existsKey [VarKey "a"]
              ( Link (UVarAg "x") (AbsKey KT, VarKey "a")
              ∧ Link (UVarAg "y") (AbsKey KT, VarKey "a")
              ∧ nEqI (UVarAg "x") (UVarAg "y") ) ) )

-- ============================ CHECKS =====================================

runCheck :: ProtocolSpec -> Stmt -> String
runCheck prot f =
    show (justHead [ tr | tr <- model
                        , truth (prot, model, tr) f
                        , countSessions T tr == maxSessions ])
  where model = build prot

akmaStrong, akmapStrong, akmaWeak, akmapWeak :: String
akmaStrong  = runCheck akma  negStrongUnlink
akmapStrong = runCheck akmap negStrongUnlink
akmaWeak    = runCheck akma  negWeakUnlink
akmapWeak   = runCheck akmap negWeakUnlink

-- ablation: per-AF AKID that is NOT regenerated per registration
akmaPerAfStrong :: String
akmaPerAfStrong = runCheck akmaPerAf negStrongUnlink

-- An attack witness that visibly spans BOTH AFs: the same UE (hence the same
-- global AKID) is tracked across two different AFs.
afOf :: Agent -> Maybe Name
afOf ag = listToMaybe [ a | (AbsName R, Name a) <- _iniFrame ag ]

spansTwoAFs :: Trace -> Bool
spansTwoAFs tr =
    or [ length (L.nub [ af | ag <- ues, _name ag == nm
                            , Just af <- [afOf ag] ]) >= 2
       | nm <- L.nub (map _name ues) ]
  where ues = aliveWithRole T tr

akmaCrossAf :: String
akmaCrossAf =
    show (justHead [ tr | tr <- model
                        , truth (akma, model, tr) negStrongUnlink
                        , countSessions T tr == maxSessions
                        , spansTwoAFs tr ])
  where model = build akma

akmaNonVacuity, akmapNonVacuity :: String
akmaNonVacuity  = show (length [ tr | tr <- build akma , countSessions T tr == maxSessions ])
akmapNonVacuity = show (length [ tr | tr <- build akmap, countSessions T tr == maxSessions ])
