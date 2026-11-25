module Main where

import PrivAuth
import BasicHash
import TagReader0
import Feldhofer (satKeyLinkFeld, satNameLinkFeld, satKeyWeakLinkFeld, satNameWeakLinkFeld)
import HashLock (satNegStrongUnlinkabilityHL, satNegWeakUnlinkabilityHL)
import System.Environment (getArgs)
import Checks (Check, cId, runCheck, runCheckPairwise, satBucketed)
import qualified HashLock as HL
import qualified Feldhofer as FE
import qualified Schnorr
import qualified DAA
import qualified AKMAChecks
import AKMA (akmaStrong, akmaWeak, akmapStrong, akmapWeak, akmaPerAfStrong, akmaCrossAf, akmaNonVacuity, akmapNonVacuity)

-- | the newer case studies: every check has an identifier, which is also its option
newChecks :: [Check]
newChecks = Schnorr.checks ++ DAA.checks ++ AKMAChecks.checks

main :: IO ()

main = do
    args <- getArgs
    case args of 
       -- BASICHASH 
       ["1"] -> putStrLn satNegStrongLinkabilityBH -- 2tags,3sess: Attack 0.2 sec 
                                                  --  3tags,3sess: Nothing 20 sec
                                                  --  3tags,4sess: Attack 10 sec
                                                  --  4tags,5sess: ?
       ["2"] -> putStrLn satNegWeakUnlinkabilityBH -- 2tags, 3sess: Nothing 0.2 sec
                                                   -- 3tags, 3sess: Nothing 2sec
                                                   -- 3tags, 4sess: Nothing 31 sec
       -- PRIVAUTH
       ["a"] -> putStrLn privAuthGoal2A -- Nothing 34.63 sec 
       ["b"] -> putStrLn privAuthXGoal2A -- Nothing 0.42 sec
       ["c"] -> putStrLn privAuthGoal2C -- Nothing 27sec, (17s vs spy only) 
       ["d"] -> putStrLn privAuthXGoal2C -- Attack 0.4sec (0.3sec vs spy only) 
       ["e"] -> putStrLn privAuthGoal3 -- Nothing 17 sec
       ["f"] -> putStrLn privAuthXGoal3 -- Attack 0.05sec
       -- TAGREADER0
       ["A"] -> putStrLn satKeyLinkTR0 -- 2sess: Attack 14sec
                                       -- 3sess: ?
       ["B"] -> putStrLn satNameLinkTR0 -- 2sess: Nothing 45sec
                                        -- 3sess: ?
       ["C"] -> putStrLn satKeyWeakLinkTR0 -- 2sess:
                                           -- 3sess:
       ["D"] -> putStrLn satNameWeakLinkTR0 -- 2sess:
                                            -- 3sess:
       -- FELDHOFER (new; unlinkable per Hirschi-Baelde-Delaune / Baelde-Delaune-Moreau)
       ["F1"] -> putStrLn satNameLinkFeld     -- strong unlink by name  : Nothing/unlinkable (~90s)
       ["F2"] -> putStrLn satKeyLinkFeld      -- strong unlink by key   : Nothing/unlinkable (~90s)
       ["F3"] -> putStrLn satNameWeakLinkFeld -- weak unlink by name    : Nothing/unlinkable (~10s)
       ["F4"] -> putStrLn satKeyWeakLinkFeld  -- weak unlink by key     : Nothing/unlinkable (~10s)
       -- HASHLOCK (new; unlinkable per Hirschi-Baelde-Delaune)
       ["H1"] -> putStrLn satNegStrongUnlinkabilityHL -- 2 names/3 sess: Attack (pigeonhole)
       ["H2"] -> putStrLn satNegWeakUnlinkabilityHL   -- weak          : Nothing/unlinkable
       -- ZERO-KNOWLEDGE (Schnorr identification: S1..S25; DAA signing: D1..D21) and AKMA (original module: AK1..AKPNV; check framework: AKG1..AKF4)
       ["schnorr"] -> mapM_ (putStrLn . runCheck) Schnorr.checks
       ["daa"]     -> mapM_ (putStrLn . runCheck) DAA.checks
       ["akma"]    -> mapM_ (putStrLn . runCheck) AKMAChecks.checks
       ["sanity"]  -> mapM_ putStrLn (Schnorr.sanity ++ DAA.sanity ++ AKMAChecks.sanity)
       -- AKMA, original module: unlinkability of UE-AKIDs and AFs (Def. 4). AKMA fails, AKMA^p holds.
       ["AK1"] -> putStrLn akmaStrong        -- AKMA   strong unlink : Attack (Just)
       ["AK2"] -> putStrLn akmaWeak          -- AKMA   weak   unlink : Nothing
       ["AKP1"] -> putStrLn akmapStrong      -- AKMA^p strong unlink : holds  (Nothing)
       ["AKP2"] -> putStrLn akmapWeak        -- AKMA^p weak   unlink : Nothing
       ["AKA"] -> putStrLn akmaPerAfStrong   -- ablation: per-AF-only AKID : Attack (Just)
       ["AKX"] -> putStrLn akmaCrossAf       -- AKMA cross-AF attack witness
       ["AKNV"] -> putStrLn akmaNonVacuity   -- AKMA   non-vacuity
       ["AKPNV"] -> putStrLn akmapNonVacuity -- AKMA^p non-vacuity
       ["list"]    -> mapM_ (putStrLn . cId) newChecks
       -- the same check with the pairwise knowledge oracle (to compare outcome and time)
       ["pairwise", x] -> mapM_ (putStrLn . runCheckPairwise) [c | c <- newChecks, cId c == x]
       -- earlier case studies re-run with the bucketed oracle; the output must equal that of the plain option
       ["F1+"] -> print (satBucketed FE.feldhofer FE.nameLink FE.tagsDone)
       ["F2+"] -> print (satBucketed FE.feldhofer FE.keyLink  FE.tagsDone)
       ["H1+"] -> print (satBucketed HL.hashLock HL.negStrongUnlinkability HL.tagsOut)
       ["H2+"] -> print (satBucketed HL.hashLock HL.negWeakUnlinkability   HL.tagsOut)
       [x] | x `elem` map cId newChecks -> mapM_ (putStrLn . runCheck) [c | c <- newChecks, cId c == x]
       _ -> putStrLn "usage: phoebe <option>   (see Main.hs and README.md for the options)"



