{-# LANGUAGE GADTs #-}
{-|
Module      : LazyCheck
Description : Equivalence-class ("lazy over classes") epistemic checking for Phoebe.

Phoebe's reference `truth` evaluates  K_ag \phi  at a state by rescanning the whole
model and recomputing `equiv ag s s'` for every other state.  Following the
paper's own next step ("check formulas with K at equivalence classes, not
individual states"), this module partitions the model once per observer and
evaluates over classes, via the existing `satK`/`allSatK`/`truthK`.

Validated in LazyEpi to give the SAME satisfying-set as `truth` while being far
faster (≈186× on Hash-Lock strong unlinkability).

Applicability: the speedup applies to properties whose top connective is the
observer's own knowledge, i.e. `K obs \phi ` / `¬ K obs \phi` — the standard shape of
intruder-centric unlinkability (`K spy ...`).  For other shapes `truthK` falls
back to `truth` over each class, so results stay correct but the win is smaller.
-}
module LazyCheck (satEC, allSatEC) where

import ProtModel
import LogicSyntax

-- | Equivalence-class `sat` for a fixed observer.  Builds the model once and
--   reuses the observer's partition.  Returns a witness trace (head of a
--   satisfying class) or Nothing.
satEC :: ProtocolSpec -> Agent -> Stmt -> Maybe Trace
satEC prot observer f = satK observer (prot, build prot) f

-- | All traces in satisfying classes (equal, as a set, to
--   @[tr | tr <- build prot, truth (prot, build prot, tr) f]@ for observer-K
--   properties).
allSatEC :: ProtocolSpec -> Agent -> Stmt -> [Trace]
allSatEC prot observer f = allSatK observer (prot, build prot) f
