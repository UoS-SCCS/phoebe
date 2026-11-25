{-|
Module      : Checks
Description : Shared machinery for the newer case studies (zero-knowledge, AKMA).

* an exact, bucketed knowledge oracle (same relation as `equiv`, but candidates
  are first narrowed down by conditions that `equiv` implies);
* a uniform notion of check: a property (a PL formula), evaluated at every
  reachable state of a model, with the expected outcome recorded next to it;
* model sanity checks (honest sends are synthesizable; non-vacuity counters).
-}
module Checks where
import ProtModel
import LogicSyntax
import HelperFunctions
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L

-- ---------------------------------------------------------------------------
-- Knowledge oracle
-- ---------------------------------------------------------------------------

-- | Everything `equiv ag` compares for equality on the nose: the protocol step,
-- the list of decipherable terms, the frame domain and the size of every image.
viewKey :: Agent -> Trace -> (Int, [Term], [AbsTerm], [Int])
viewKey ag tr = (step (_role ag) ag tr, dec, dom, cards)
  where
    trm   = terms ag tr
    frm   = frame ag tr
    dec   = filter (\t -> not (undeciph' ag trm t)) trm
    dom   = S.toList (S.fromList (map fst frm))
    cards = [length [() | (pt', _) <- frm, pt' == pt] | pt <- dom]

-- | `bucketOracle obs mdl` answers knowledge queries for the observers `obs`.
-- Two states related by `equiv ag` always have the same `viewKey ag`, so the
-- oracle only runs `equiv` inside one bucket.  The relation is unchanged.
bucketOracle :: [Agent] -> [Trace] -> KOracle
bucketOracle obs mdl = oracle
  where
    tables = M.fromList [ (ag, M.fromListWith (flip (++)) [(viewKey ag tr, [tr]) | tr <- mdl]) | ag <- obs ]
    oracle ag tr = case M.lookup ag tables of
      Just tbl -> [tr' | tr' <- M.findWithDefault [] (viewKey ag tr) tbl, equiv ag tr tr']
      Nothing  -> [tr' | tr' <- mdl, equiv ag tr tr']

-- ---------------------------------------------------------------------------
-- Checks
-- ---------------------------------------------------------------------------

data Check = Check
  { cId     :: String            -- ^ identifier, also the command-line option
  , cModel  :: String            -- ^ name of the model
  , cWhat   :: String            -- ^ name of the property
  , cProt   :: ProtocolSpec
  , cStates :: [Trace]           -- ^ the reachable states (shared between checks of one model)
  , cSel    :: Trace -> Bool     -- ^ states at which the property is evaluated
  , cProp   :: Stmt              -- ^ the property, stated positively
  , cExpect :: Bool              -- ^ True: expected to hold at every selected state
  }

-- | first selected state at which the property is false
violation :: Check -> Maybe Trace
violation = violationWith (\prot mdl -> bucketOracle (_spy prot : _honestAgents prot) mdl)

-- | the same, with a chosen knowledge oracle (used to compare the oracles)
violationWith :: (ProtocolSpec -> [Trace] -> KOracle) -> Check -> Maybe Trace
violationWith mk c = justHead [ tr | tr <- sel, not (truthWith kor (prot, mdl, tr) (cProp c)) ]
  where
    prot = cProt c
    mdl  = cStates c
    sel  = [tr | tr <- mdl, not (null tr), cSel c tr]
    kor  = mk prot mdl

runCheck :: Check -> String
runCheck = runCheckWith violation

-- | run a check with the pairwise oracle of ProtModel (for comparison only)
runCheckPairwise :: Check -> String
runCheckPairwise = runCheckWith (violationWith (\_ mdl -> pairwiseOracle mdl))

-- | `sat` of ProtModel restricted to selected states, with the bucketed oracle:
-- first selected state satisfying the formula
satBucketed :: ProtocolSpec -> Stmt -> (Trace -> Bool) -> Maybe Trace
satBucketed prot f sel = justHead [ tr | tr <- mdl, truthWith kor (prot, mdl, tr) f, sel tr ]
  where mdl = build prot
        kor = bucketOracle [_spy prot] mdl

runCheckWith :: (Check -> Maybe Trace) -> Check -> String
runCheckWith viol c =
    "[" ++ cId c ++ "] " ++ cModel c ++ " | " ++ cWhat c ++ " | "
    ++ outcome ++ " | " ++ (if ok then "as expected" else "UNEXPECTED")
    ++ " | states=" ++ show (length (cStates c)) ++ " selected=" ++ show nsel
    ++ witness
  where
    v       = viol c
    nsel    = length [() | tr <- cStates c, not (null tr), cSel c tr]
    holds   = v == Nothing
    ok      = holds == cExpect c && nsel > 0
    outcome = if holds then "HOLDS" else "FAILS"
    witness = case v of
                Nothing -> ""
                Just tr -> "\n  counterexample:\n" ++ concatMap (\e -> "    " ++ show e) tr

-- ---------------------------------------------------------------------------
-- Sanity checks on a model
-- ---------------------------------------------------------------------------

-- | Every message sent by an honest agent can be built from what that agent
-- holds at that point (its knowledge so far and the fresh values of the step).
-- The transition rule of the tool does not test this, so we test it here.
honestSendsOK :: [Trace] -> Bool
honestSendsOK mdl = and [ ok tr | tr <- mdl, not (null tr) ]
  where
    ok tr = case last tr of
      ESend _ (_, ag) fresh (_, m) ->
          synthable m (analz (_name ag) (sees ag (init tr) ++ map snd fresh))
      _ -> True

-- | the fresh values generated within one send are pairwise distinct
freshDistinct :: [Trace] -> Bool
freshDistinct mdl = and [ length (L.nub vs) == length vs | tr <- mdl, ESend _ _ fresh _ <- tr, let vs = map snd fresh ]

-- | agents of a role that have completed step i
doneWith :: RoleName -> Int -> Trace -> [Agent]
doneWith r i tr = [x | x <- aliveWithRole r tr, step (_role x) x tr >= i]

anyAll :: [a -> Bool] -> a -> Bool
anyAll ps x = all (\p -> p x) ps
