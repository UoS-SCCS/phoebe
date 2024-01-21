module HelperFunctions where
import Data.Map (Map, (!), fromList, keys, elems, union, findWithDefault, empty, toList)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Maybe
import Debug.Trace
import qualified Control.Monad as CM


map1 a b = fromList [(a,b)] 

-- | counting occurences
occur :: (Eq a) => a -> [a] -> Int
occur a as = length (filter (\x -> x == a) as) 

-- -- | list "powerset"
-- lPowerSet :: Ord a => [a] -> [[a]]  
-- lPowerSet ls = map S.toList (S.toList ( S.powerSet $ S.fromList ls))
 
lPowerSet :: [a] -> [[a]]
lPowerSet = CM.filterM (const [True, False])

justHead :: [a] -> Maybe a 
justHead [] = Nothing 
justHead (a:as) = Just a 

-- | >> prepend 0 [[1,2],[3,2],[4,3]]
--      [[0,1,2],[0,3,2],[0,4,3]]
prepend :: (Eq a) => a -> [[a]] -> [[a]]  
prepend a [] = []  
prepend a [bs] = [a:bs]  
prepend a (bs:bss) = (a:bs):(prepend a bss)  

-- | cross [0,1] [[2],[3],[4]]
--   [[0,2],[0,3],[0,4],[1,2],[1,3],[1,4]]
cross :: (Eq a) => [a] -> [[a]] -> [[a]]   
cross as bss = concat [prepend a bss | a <- as] 

-- |  combinations [[1,2],[4,5,6],[3]]
--    [[1,4,3],[1,5,3],[1,6,3],[2,4,3],[2,5,3],[2,6,3]]
combinations ::  (Eq a) => [[a]] -> [[a]]  
combinations [ts] = [[t]|t<-ts]  
combinations (ts:tss) = cross ts (combinations tss)

-- | union of the images of two functions
orf ::(Eq a)=> ([a]->[a]) -> ([a]->[a])->[a] ->[a]
orf f g xs = f xs `L.union` g xs

-- | union of the images of two functions
catf ::(Eq a)=> ([a]->[a]) -> ([a]->[a])->[a] ->[a]
catf f g xs = f xs ++ g xs

-- | union of the images of many functions
anyf :: (Eq a) => [[a]->[a]] -> [a] -> [a]    
anyf [f] xs = f xs  
anyf (f:fs) xs = f xs `L.union` anyf fs xs 

closure :: (Eq a) => ([a]->[a])-> [a] ->[a]
closure f hs 
   | length hs==length (f hs) = hs
   | otherwise = closure f (f hs)

isSublistOf :: Eq a => [a] -> [a] -> Bool   
isSublistOf l l' = L.intersect l l' == l


-- | Equivalence class by Daniel Fischer (https://stackoverflow.com/a/8262250) 
splitOffFirstGroup :: (a -> a -> Bool) -> [a] -> ([a],[a])
splitOffFirstGroup equal xs@(x:_) = L.partition (equal x) xs
splitOffFirstGroup _     []       = ([],[])

equivClasses _     [] = []
equivClasses equal xs = let (fg,rst) = splitOffFirstGroup equal xs
                              in fg : equivClasses equal rst

showListC :: Show a => [a] -> String 
showListC [] = ""
showListC [a] = show a 
showListC (a:as) = show a ++ "," ++ showListC as


showFrame :: (Show a, Show b) => [(a,b)] -> String 
showFrame [] = ""
showFrame [a] = showMapping a
showFrame (a:as) = showMapping a ++ "," ++ showFrame as

showMapping :: (Show a, Show b) => (a,b) -> String
showMapping (a,b) = "\n" ++ show a ++ "↦" ++ show b  
