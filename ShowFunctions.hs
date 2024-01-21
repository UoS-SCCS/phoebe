{-# LANGUAGE StandaloneDeriving, GADTs #-}
module ShowFunctions where
import ProtModel
import Data.Maybe
import Data.Tree               -- Use trees from Data.Tree module
import Terms
import HelperFunctions
import LogicSyntax

deriving instance Show IndexTerm
deriving instance Show Stmt
deriving instance Show Var


instance Show (Terms a)
  where
    show (Grd a) = "Grd" ++ show a
    show (Abs a) = "Abs" ++show a
    show (Const a) = show a
    show (Name a) = show a
    show (Nonce n) = "N"++show n
    show (VarAg x) = show x
    show (VarKey x) = show x
    show (VarName x) = show x
    show (Key (SsKey k)) = "KK"++show k
    show (Key (LKey k)) = "K"++show k
    show (AbsName a) = show a
    show (AbsNonce n) = show n
    show (AbsKey k) = show k
    show (AbsList a) = "S"++show a
    show (Role a) = "η"++show a
    show (Self) = "Self"
    show (Tuple ts) = show ts
    show (PubKey a) = "K"++show a
    show (PrivKey a) = "K-1"++show a
    show (Pair m m') = "("++show m++","++show m'++")"
    show (Triple m n p) = "("++show m++","++show n++","++show p++")"
    show (Crypt a m) = "{"++show m++"}_"++show a
    show (SCrypt k m) = "{|"++show m++"|}_"++show k
    show (Hash m) = "hash("++show m++")" 
    show (DCrypt m) = "DCrypt("++show m++")"
    show (DSCrypt m) = "DSCrypt("++show m++")"
    show (DHash m) = "DHash("++show m++")" 
    show (Proj1 m) = "Proj1("++show m++")" 
    show (Proj2 m) = "Proj2("++show m++")" 
    show (Proj3 m) = "Proj3("++show m++")" 
    

instance Show Agent 
  where
    show ag 
      | _name ag == Spy = show (_name ag) 
      | otherwise = "(" ++ show (_name ag) ++ "," ++ show (fromJust $ _role ag) ++ "," ++ show (fromJust $ _sess ag) ++"," ++show (wlist ag) ++ ")"

instance Show Name 
  where
    show Alice = "a"
    show Bob = "b"
    show Charlie = "c"
    show Spy = "i"
    show (Tag i) = "t"++show i
    show (Reader i) = "r"++show i

instance Show Key 
  where
    show (LKey i) = show i
    show (SsKey i) = show i

instance Show Event 
  where
    show (ESend i (r,ag) ms m) = 
      show i ++"."++show ag  ++ ":--|"++ showListC (snd (unzip ms))  ++ "|->" ++"" ++ show (snd m) ++ "\n"
    show (ERec  i (r,ag) st m) = 
      show i ++"."++show ag   ++ ":<-|"++ showListC (snd (unzip st)) ++ "|--" ++"" ++ show (snd m) ++ "\n"

showListC :: Show a => [a] -> String 
showListC [] = ""
showListC [a] = show a 
showListC (a:as) = show a ++ "," ++ showListC as

tree prot = drawTree (fmap show (buildT prot))
writeTree prot = writeFile (_protName prot ++ "_tree.txt") (tree prot) -- show the tree
writeLeaves prot = writeFile (_protName prot ++ "_leaves.txt") (unlines [show s| s<- build prot]) -- show the leaves line by line
writeSat prot frml = writeFile (_protName prot ++ "_sat.txt") (satHead prot frml ++ show (sat prot frml))  
writeAllSat prot frml = writeFile (_protName prot ++ "_allSat.txt") (allSatHead prot frml ++ unlines [show f| f<-allSat prot frml])  

satHead prot frml = "sat(" ++ show (_protName prot) ++ ", " ++ show frml ++ ")\n"
allSatHead prot frml = "allSat(" ++ show (_protName prot) ++ ", " ++ show frml ++ ")\n"
-- -- DEBUG 
-- writeEquivClass prot = writeFile (_protName prot ++ "_equivClasses.txt") (unlines ["\n\n" ++ show ag ++ unlines ([unlines [(show s )| s <- ss]++"end" | ss <- (equivClasses (equiv ag) (build prot))]) | ag <- [_spy prot]])
writeEquivClass prot = writeFile (_protName prot ++ "_equivClasses.txt") (unlines ["\n\n" ++ show ag ++ unlines (["{\n" ++ unlines [(show s ) ++ "     frame: " ++ show (links ag s)| s <- ss]++"}\n" | ss <- (equivClasses (equiv ag) (build prot))]) | ag <- [_spy prot]])
