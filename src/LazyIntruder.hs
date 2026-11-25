{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : LazyIntruder
Description : An OFMC-style (Basin/Moedersheim/Vigano) Dolev-Yao deduction for
              Phoebe, structured as goal-directed constraint reduction.

This is the ground core of a *lazy* Dolev-Yao theory for Phoebe.  Instead of
materialising @synth(analz(IK))@ (the closure Phoebe itself abandoned as "too
costly", see the commented-out `synth` in Terms/LogicSyntax), derivability is
decided by:

  1. ANALYSIS  — close the intruder knowledge under decomposition
                 (projection, asymmetric decryption for messages sent to the
                 intruder, and symmetric decryption *only when the key is
                 itself derivable*); and
  2. GENERATION — a goal-directed check that a target is either known or can be
                 composed, recursing on demand and stopping as soon as the
                 answer is determined (no closure is built).

The OFMC "lazy intruder" additionally keeps intruder-chosen message parts
symbolic (variables) and pins them by unification; that variable layer is
specified in LAZY_DY_ROADMAP.md and built on the `analyze`/`generable` core
here.

NOTE (correctness): unlike Phoebe's knowledge-set `analz` (LogicSyntax), the
symmetric-decryption rule here requires the key to be derivable
(`k `elem` closure`).  Phoebe's `analz` uses `[x | SCrypt k x <- xs, k<-xs]`,
whose second generator shadows `k`, so it decrypts *every* symmetric ciphertext
regardless of key possession (demonstrated in LazyIntruderTest).
-}

module LazyIntruder
  ( analyze
  , generable
  , derivable
  ) where

import LogicSyntax
import HelperFunctions (closure)
import qualified Data.List as L

-- | ANALYSIS: close a set of ground terms under Dolev-Yao decomposition.
--   Rules (cf. OFMC analysis rules A_pair / A_scrypt / A_crypt):
--     * a pair/triple yields its components;
--     * {m}_i  (asymmetric, addressed to the intruder Spy) yields m;
--     * {|m|}_k (symmetric) yields m  ONLY IF k is already in the set;
--     * hashes and MACs are one-way (not decomposed).
analyze :: [Term] -> [Term]
analyze = closure step
  where
    step xs = L.nub $ xs
      ++ [a | Pair a _      <- xs]
      ++ [b | Pair _ b      <- xs]
      ++ [a | Triple a _ _  <- xs]
      ++ [b | Triple _ b _  <- xs]
      ++ [c | Triple _ _ c  <- xs]
      ++ [m | Crypt (Name Spy) m <- xs]          -- adec addressed to the intruder
      ++ [m | SCrypt k m <- xs, k `elem` xs]     -- sdec needs the key (correct DY)

-- | GENERATION: can @m@ be composed from the (already analysed) set @kn@?
--   Goal-directed and demand-driven: it recurses only into the structure of the
--   current goal and returns as soon as the verdict is fixed — no synth closure
--   is ever built (cf. OFMC generation rules G_pair / G_scrypt / G_unif).
generable :: [Term] -> Term -> Bool
generable kn m
  | m `elem` kn = True
  | otherwise = case m of
      Pair a b     -> generable kn a && generable kn b
      Triple a b c -> generable kn a && generable kn b && generable kn c
      Crypt a b    -> generable kn a && generable kn b   -- encrypt to a public principal a
      SCrypt k b   -> generable kn k && generable kn b
      Mac k b      -> generable kn k && generable kn b
      Hash b       -> generable kn b
      _            -> False                              -- atom not known

-- | The intruder can derive @m@ from knowledge @ik@ iff, after analysis, @m@ is
--   generable.  This is the ground decision  m ∈ synth(analz(IK)).
derivable :: [Term] -> Term -> Bool
derivable ik m = generable (analyze ik) m
