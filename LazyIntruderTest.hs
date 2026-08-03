{-# LANGUAGE GADTs #-}
-- | Validation of the lazy Dolev-Yao reducer (LazyIntruder) against Phoebe's
-- existing deduction, over a deterministic battery of (knowledge, target) pairs.
--
-- Oracle = Phoebe's  synthable m (analz Spy ik).  The lazy reducer agrees with
-- it on every case EXCEPT symmetric-decryption-without-the-key, where Phoebe's
-- `analz` over-approximates (its `sdec` does not check key possession); those
-- divergences are listed explicitly.
module Main where

import LogicSyntax
import LazyIntruder (derivable, analyze)
import HelperFunctions (lPowerSet)
import qualified Data.List as L

-- small term universe -------------------------------------------------------
a, i, n1, n2, n3, n4, k1, k2 :: Term
a  = Name Alice
i  = Name Spy
n1 = Nonce 1; n2 = Nonce 2; n3 = Nonce 3; n4 = Nonce 4
k1 = Key (LKey 1); k2 = Key (LKey 2)

-- base knowledge items (subsets of these form the intruder knowledge)
base :: [Term]
base = [ a, n1, k1
       , SCrypt k2 n2            -- {|n2|}_k2  (spy lacks k2 unless a subset adds it)
       , Crypt i n3              -- {n3}_i     (addressed to the intruder)
       , Pair n4 k2 ]           -- <n4,k2>    (pair giving up k2 and n4)

-- targets to try to derive
targets :: [Term]
targets =
  [ a, n1, n2, n3, n4, k1, k2
  , Pair n1 k1, SCrypt k1 n1, Crypt a n1, Hash n1, Mac k1 n1
  , SCrypt k2 n2, Pair n4 k2 ]

oracle :: [Term] -> Term -> Bool
oracle ik m = synthable m (analz Spy ik)

main :: IO ()
main = do
  let cases = [ (ik, m) | ik <- lPowerSet base, m <- targets ]
      results = [ (ik, m, derivable ik m, oracle ik m) | (ik, m) <- cases ]
      disagree = [ (ik, m, lz, ph) | (ik, m, lz, ph) <- results, lz /= ph ]
      nAgree = length results - length disagree
  putStrLn "Lazy DY reducer vs Phoebe (synthable . analz Spy)"
  putStrLn ("  total cases         : " ++ show (length results))
  putStrLn ("  agree               : " ++ show nAgree)
  putStrLn ("  disagree            : " ++ show (length disagree))
  putStrLn ""
  putStrLn "All disagreements are Phoebe deriving a value the standard DY cannot"
  putStrLn "(symmetric decryption without the key). Distinct (target, why) cases:"
  let leaks = L.nub [ (m, ik) | (ik, m, lz, ph) <- disagree, not lz, ph ]
  mapM_ (\(m, ik) -> putStrLn ("   target " ++ show m
                    ++ "  Phoebe=derivable, lazy=not, from ik=" ++ show ik))
        (take 6 leaks)
  let onlyLeakDir = all (\(_, _, lz, ph) -> ph && not lz) disagree
  putStrLn ""
  putStrLn ("every disagreement is Phoebe-over-derives (never the reverse)? "
            ++ show onlyLeakDir)
  putStrLn ""
  -- focused demonstration of the analz key-possession issue
  putStrLn "Focused check — {|n9|}_k5 with the spy lacking k5:"
  let ik0 = [SCrypt (Key (LKey 5)) (Nonce 9)]
  putStrLn ("   lazy   derivable n9 ? " ++ show (derivable ik0 (Nonce 9)) ++ "   (correct: False)")
  putStrLn ("   Phoebe derivable n9 ? " ++ show (oracle ik0 (Nonce 9)) ++ "   (analz leaks it: True)")
  putStrLn ("   lazy, with k5 added ? " ++ show (derivable (Key (LKey 5) : ik0) (Nonce 9)) ++ "   (now True)")
