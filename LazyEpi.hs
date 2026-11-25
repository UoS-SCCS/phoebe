{-# LANGUAGE GADTs #-}
-- | Experiment  -- step towards lazy epistemic checking.
--
-- Phoebe's reference evaluator `truth` checks  K_ag \phi  at a trace `tr` by
-- rescanning the WHOLE model and recomputing `equiv ag tr tr'` for every other
-- trace (ProtModel.truth', the K case).  The paper's stated next step is to
-- "check formulas with K at equivalence classes, not individual states"; the
-- dormant `satK`/`allSatK`/`truthK` in ProtModel already do this.
--
-- This program checks, on the Hash-Lock model, that the equivalence-class
-- engine returns  the same set of satisfying traces as the reference
-- `truth`, and times both.  Agreement is also a soundness check on `equiv`
-- (truth uses the direct equiv-neighbourhood of a state; the class engine uses
-- a transitive partition, so they coincide only if `equiv` is a genuine
-- equivalence relation).
module Main where

import ProtModel
import LogicSyntax
import HashLock (hashLock, spy, negStrongUnlinkability, negWeakUnlinkability, tagsOut)
import Checks (bucketOracle)
import Data.List (sort)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

timed :: String -> [Trace] -> IO [Trace]
timed label xs = do
  t0 <- getCPUTime
  let n = length xs           -- force
  n `seq` return ()
  t1 <- getCPUTime
  printf "  %-28s : %6d traces  (%.2fs)\n" label n (fromIntegral (t1 - t0) / 1e12 :: Double)
  return xs

check :: String -> Stmt -> IO Bool
check name f = do
  let model = build hashLock
  putStrLn ("=== " ++ name ++ " ===")
  eager <- timed "eager (truth, whole model)"
             [tr | tr <- model, truth (hashLock, model, tr) f]
  classy <- timed "class-based (allSatK spy)"
             (allSatK spy (hashLock, model) f)
  bucketed <- timed "bucketed oracle (Checks)"
             [tr | tr <- model, truthWith (bucketOracle [spy] model) (hashLock, model, tr) f]
  let ok = sort eager == sort classy && sort eager == sort bucketed
  printf "  satisfying-sets identical : %s\n\n" (show ok)
  return ok

main :: IO ()
main = do
  putStrLn "Hash-Lock: reference `truth` vs equivalence-class engine `allSatK spy`\n"
  a <- check "neg strong unlinkability" negStrongUnlinkability
  b <- check "neg weak unlinkability"   negWeakUnlinkability
  putStrLn (if a && b then "AGREEMENT: class-based engine matches the reference truth on all checks"
                      else "MISMATCH: see above (indicates `equiv` is not a sound equivalence for this engine)")
