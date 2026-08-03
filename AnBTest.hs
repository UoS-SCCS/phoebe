{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | Round-trip test for the Alice-and-Bob parser.
--
-- For each example we parse the @.anb@ spec, translate it to @[Action]@ using a
-- condition environment that supplies the (protocol-specific) test formulae,
-- and check the result equals the hand-written @actions@ copied verbatim from
-- the corresponding Phoebe module.  We also print the generated Haskell source.
module Main where

import AnB
import LogicSyntax
import Control.Monad (forM_)
import System.Exit (exitFailure, exitSuccess)
import Data.IORef

-- ===========================================================================
-- Expected actions + condition formulae, copied verbatim from the modules
-- ===========================================================================

-- ---- Basic-Hash (from BasicHash.hs) ---------------------------------------
bhPhi :: Stmt
bhPhi = ExistsKey (VarKey "x")
          ((VarKey "x" ∈ UAbsName R)
             ∧ (Link (UAbsName R)
                  ( Hash (Pair (AbsNonce NT) (AbsKey KT))
                  , Hash (Pair (Abs (AbsNonce NT)) (VarKey "x")))))

bhExpected :: [Action]
bhExpected =
  [ Send 1 T true [AbsNonce NT]
      (Pair (AbsNonce NT) (Hash (Pair (AbsNonce NT) (AbsKey KT))))
  , Rec  1 R (true, bhPhi)
      (Pair (AbsNonce NT) (Hash (Pair (AbsNonce NT) (AbsKey KT))))
  ]

-- ---- Tag-Reader (from TagReader0.hs) --------------------------------------
trFresh :: Stmt
trFresh = Neg (Has (UAbsName T) (Abs (AbsNonce NR)))

trMatch :: Stmt
trMatch = existsNonce [VarNonce "nr", VarNonce "nt"] ( existsKey [VarKey "kt"] $
          Conj [ Link (UAbsName R) (AbsKey KT, VarKey "kt")
               , Link (UAbsName R) (AbsNonce NR, VarNonce "nr")
               , Link (UAbsName R) (AbsNonce NT, VarNonce "nt")
               , Link (UAbsName R) (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)),
                                    SCrypt (VarKey "kt") (Pair (VarNonce "nr") (VarNonce "nt")))
               ] )

trExpected :: [Action]
trExpected =
  [ Send 1 T true [AbsNonce NT] (SCrypt (AbsKey KT) (AbsNonce NT))
  , Rec  1 R trues              (SCrypt (AbsKey KT) (AbsNonce NT))
  , Send 2 R true [AbsNonce NR] (SCrypt (AbsKey KT) (AbsNonce NR))
  , Rec  2 T (trFresh, true)    (SCrypt (AbsKey KT) (AbsNonce NR))
  , Send 3 T true []            (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
  , Rec  3 R (true, trMatch)    (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
  , Rec  3 R trues              (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
  ]

-- ---- PrivAuth (from PrivAuth.hs) ------------------------------------------
paPhi :: Stmt
paPhi = Conj
  [ Link (UAbsName C) (AbsName B, Abs (AbsName C))
  , Listed (UAbsName C) (PubKey (Abs (AbsName A)))
  ]

paExpected :: [Action]
paExpected =
  [ Send 1 A true      [AbsNonce NA]           (Crypt (AbsName B) (Pair (AbsName A) (AbsNonce NA)))
  , Rec  1 C trues                             (Crypt (AbsName B) (Pair (AbsName A) (AbsNonce NA)))
  , Send 2 C paPhi     [AbsNonce NC]           (Crypt (AbsName A) (Triple (AbsName C) (AbsNonce NA) (AbsNonce NC)))
  , Send 2 C (Neg paPhi) [AbsNonce N, AbsKey KK] (SCrypt (AbsKey KK) (AbsNonce N))
  , Rec  2 A trues                             (Crypt (AbsName A) (Triple (AbsName C) (AbsNonce NA) (AbsNonce NC)))
  , Rec  2 A trues                             (SCrypt (AbsKey KK) (AbsNonce N))
  ]

-- ---- Feldhofer (from Feldhofer.hs) ----------------------------------------
feldExpected :: [Action]
feldExpected =
  [ Send 1 R true [AbsNonce NR] (AbsNonce NR)
  , Rec  1 T trues              (AbsNonce NR)
  , Send 2 T true [AbsNonce NT] (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
  , Rec  2 R trues              (SCrypt (AbsKey KT) (Pair (AbsNonce NR) (AbsNonce NT)))
  , Send 3 R true []            (SCrypt (AbsKey KT) (Pair (AbsNonce NT) (AbsNonce NR)))
  , Rec  3 T trues              (SCrypt (AbsKey KT) (Pair (AbsNonce NT) (AbsNonce NR)))
  ]

-- ---- Hash-Lock (from HashLock.hs) -----------------------------------------
hlPhi :: Stmt
hlPhi = ExistsKey (VarKey "x")
          ((VarKey "x" ∈ UAbsName R)
             ∧ (Link (UAbsName R)
                  ( Hash (Triple (AbsNonce NR) (AbsNonce NT) (AbsKey KT))
                  , Hash (Triple (Abs (AbsNonce NR)) (Abs (AbsNonce NT)) (VarKey "x")))))

hlExpected :: [Action]
hlExpected =
  [ Send 1 R true [AbsNonce NR] (AbsNonce NR)
  , Rec  1 T trues              (AbsNonce NR)
  , Send 2 T true [AbsNonce NT] (Pair (AbsNonce NT) (Hash (Triple (AbsNonce NR) (AbsNonce NT) (AbsKey KT))))
  , Rec  2 R (true, hlPhi)      (Pair (AbsNonce NT) (Hash (Triple (AbsNonce NR) (AbsNonce NT) (AbsKey KT))))
  ]

-- ===========================================================================
-- Rendering (Action has no Show instance; build one from the parts)
-- ===========================================================================

showAction :: Action -> String
showAction (Send i r st fr m) =
  "Send " ++ show i ++ " " ++ show r ++ " (" ++ show st ++ ") "
    ++ show fr ++ " " ++ show m
showAction (Rec i r pp m) =
  "Rec " ++ show i ++ " " ++ show r ++ " " ++ show pp ++ " " ++ show m

-- ===========================================================================
-- Driver
-- ===========================================================================

runCase :: IORef Bool -> String -> FilePath -> [(String,Stmt)] -> [Action] -> IO ()
runCase okRef name path condEnv expected = do
  src <- readFile path
  let spec        = parseAnB src
      (got, _rls) = translate condEnv spec
  putStrLn ("===== " ++ name ++ " =====")
  if got == expected
    then putStrLn ("  round-trip: PASS (" ++ show (length got) ++ " actions match the hand-written module)")
    else do
      writeIORef okRef False
      putStrLn "  round-trip: FAIL"
      putStrLn ("  #generated=" ++ show (length got) ++ " #expected=" ++ show (length expected))
      forM_ (zip3 [0::Int ..] (pad got) (pad expected)) $ \(k, g, e) ->
        if g == e
          then return ()
          else do
            putStrLn ("   [" ++ show k ++ "] differ:")
            putStrLn ("      got : " ++ maybe "<none>" showAction g)
            putStrLn ("      want: " ++ maybe "<none>" showAction e)
  putStrLn ""
  putStrLn (genHs spec)
  where
    pad xs = map Just xs ++ repeat Nothing

main :: IO ()
main = do
  okRef <- newIORef True
  runCase okRef "BasicHash"  "examples/BasicHash.anb"  [("phi", bhPhi)]                          bhExpected
  runCase okRef "TagReader0" "examples/TagReader0.anb" [("fresh", trFresh), ("match", trMatch)]  trExpected
  runCase okRef "PrivAuth"   "examples/PrivAuth.anb"   [("phi", paPhi)]                          paExpected
  runCase okRef "Feldhofer"  "examples/Feldhofer.anb"  []                                        feldExpected
  runCase okRef "HashLock"   "examples/HashLock.anb"   [("phi", hlPhi)]                          hlExpected
  ok <- readIORef okRef
  if ok then putStrLn "ALL ROUND-TRIP CHECKS PASSED" >> exitSuccess
        else putStrLn "SOME CHECKS FAILED" >> exitFailure
