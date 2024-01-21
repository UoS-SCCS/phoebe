module Main where

import PrivAuth
import BasicHash
import TagReader0
import System.Environment (getArgs) 

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
                                       

