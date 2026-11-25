{-# LANGUAGE GADTs #-}
-- | Command-line front-end for the Alice-and-Bob parser.
--
--   anbgen path/to/Protocol.anb
--
-- Reads an @.anb@ spec and prints the generated Phoebe Haskell @roles@/@actions@
-- source to stdout (test formulae are referred to by name, exactly as the
-- hand-written modules do with their local @where@ definitions).

module Main where

import AnB
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      src <- readFile path
      putStr (genHs (parseAnB src))
    _ -> do
      prog <- getProgName
      hPutStrLn stderr ("usage: " ++ prog ++ " <file.anb>")
      exitFailure
