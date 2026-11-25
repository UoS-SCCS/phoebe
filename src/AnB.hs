{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : AnB
Description : A prototype parser from an "Alice-and-Bob" style notation to the
              Phoebe Haskell representation of a protocol.


Scope of this first pass
------------------------
It parses a compact Alice-and-Bob spec (see the @examples/*.anb@ files) and
produces the /message-flow layer/ of a Phoebe protocol, i.e.

    * the list of protocol roles           (@[RoleName]@)
    * the list of send / receive actions   (@[Action]@)

together with a pretty-printer ('genHs') that emits the corresponding Haskell
source, exactly in the style of the hand-written example modules.

What it deliberately does NOT do yet
------------------------------------
The per-agent initial knowledge / frames / whitelists / substitutions are
protocol-specific (the paper and README flag this as a separate "automate
agent construction" TODO).  The full logical test formulae (e.g. the
Basic-Hash lookup, the LoRaWAN mac authentication) are full PL statements; a
spec refers to them /by name/ and the modeller supplies the 'Stmt' (this is the
same split the hand-written modules already use with their local @where phi = ..@
definitions).  'translate' takes an environment mapping those names to 'Stmt's.

The message-term translation, the send/receive splitting, step numbering,
fresh-term extraction, and else-branch handling are done fully mechanically and
are validated by 'AnBTest' against the hand-written @actions@ of BasicHash,
TagReader0 and PrivAuth.
-}



module AnB
  ( Sort(..)
  , AnBSpec(..)
  , Alt(..)
  , RecvCond
  , parseAnB
  , translate
  , genHs
  , parseMsgWith        -- exposed for testing the message parser in isolation
  ) where

import Data.Char (isSpace, isAlphaNum)
import Data.List (intercalate, isPrefixOf, foldl')
import LogicSyntax

-- ---------------------------------------------------------------------------
-- Surface syntax
-- ---------------------------------------------------------------------------

data Sort = SName | SNonce | SKey | SDatum
          | SStmt ZkStmt          -- ^ a declared zero-knowledge statement
  deriving (Eq, Show)

-- | @(pre, post)@ names for a single receive action.  'Nothing' means the
--   constant @true@.
type RecvCond = (Maybe String, Maybe String)

-- | One alternative of a protocol step.  A non-branching step has a single
--   'Alt'; a branching (if/else) step has two.
data Alt = Alt
  { aFrom     :: RoleName
  , aTo       :: RoleName
  , aMsg      :: AbsTerm
  , aFresh    :: [AbsTerm]      -- ^ newly generated nonces / short-term keys
  , aSendTest :: Maybe String   -- ^ name of the send test (branch 0 only; branch 1 is its negation)
  , aRecv     :: [RecvCond]     -- ^ one entry per receive action (usually a singleton)
  , aRecvMsg  :: Maybe AbsTerm  -- ^ the receiver's own parse of the message (annotation @recv_as@), if it differs
  }
  deriving (Show)

data AnBSpec = AnBSpec
  { sName  :: String
  , sRoles :: [RoleName]
  , sSorts :: [(String, Sort)]
  , sSteps :: [(Int, [Alt])]    -- ^ step number and its alternatives
  }
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Fixed lookup tables (identifier text -> constructor)
--
-- The identifier text equals the constructor name, so these tables just
-- encode which constructors currently exist in LogicSyntax.
-- ---------------------------------------------------------------------------

roleTable :: [(String, RoleName)]
roleTable = [("A",A),("B",B),("C",C),("T",T),("R",R),("DY",DY),("D",D),("S",S),("Pr",Pr),("Vr",Vr),("Iss",Iss)]

nonceTable :: [(String, NonceName)]
nonceTable =
  [ ("NA",NA),("NB",NB),("NC",NC),("N",N),("NT",NT),("NR",NR),("ND",ND)
  , ("DevNonce",DevNonce),("JoinNonce",JoinNonce)
  , ("NZ",NZ),("NRn",NRn),("NM",NM),("NV",NV) ]

keyTable :: [(String, KeyName)]
keyTable =
  [ ("KK",KK),("KT",KT),("NwkKey",NwkKey),("DevAddr",DevAddr),("DData",DData)
  , ("KF",KF),("KF1",KF1),("KF2",KF2),("KF3",KF3) ]

datumTable :: [(String, DatumName)]
datumTable = [("JoinEUI",JoinEUI),("DevEUI",DevEUI)]

look :: String -> [(String,a)] -> a
look s tbl = case lookup s tbl of
  Just x  -> x
  Nothing -> error ("AnB: unknown identifier " ++ show s
                    ++ " (not a declared/known role, nonce, key or datum)")

roleOf :: String -> RoleName
roleOf s = look s roleTable

-- ---------------------------------------------------------------------------
-- Sort resolution
-- ---------------------------------------------------------------------------

sortOf :: [(String,Sort)] -> String -> Sort
sortOf env s = case lookup s env of
  Just so -> so
  Nothing
    | s `elem` map fst roleTable -> SName    -- role/name atoms need no declaration
    | otherwise -> error ("AnB: identifier " ++ show s
                          ++ " has no declared sort (declare it under nonces/keys/data)")

resolveAtom :: [(String,Sort)] -> String -> AbsTerm
resolveAtom env s = case sortOf env s of
  SName  -> AbsName  (roleOf s)
  SNonce -> AbsNonce (look s nonceTable)
  SKey   -> AbsKey   (look s keyTable)
  SDatum -> AbsDatum (look s datumTable)
  SStmt _ -> error ("AnB: " ++ show s ++ " is a statement name; use it as zk_" ++ s ++ "( ... | ... )")

-- ---------------------------------------------------------------------------
-- Message tokeniser
-- ---------------------------------------------------------------------------

data Tok = TLB | TRB | TLBs | TRBs | TLA | TRA | TLP | TRP | TComma | TUnder | TId String
         | TBar | TEq | TAmp
  deriving (Eq, Show)

lexMsg :: String -> [Tok]
lexMsg [] = []
lexMsg s@(c:cs)
  | isSpace c              = lexMsg cs
  | "{|" `isPrefixOf` s    = TLBs : lexMsg (drop 2 s)
  | "|}" `isPrefixOf` s    = TRBs : lexMsg (drop 2 s)
  | c == '{'               = TLB  : lexMsg cs
  | c == '}'               = TRB  : lexMsg cs
  | c == '<'               = TLA  : lexMsg cs
  | c == '>'               = TRA  : lexMsg cs
  | c == '('               = TLP  : lexMsg cs
  | c == ')'               = TRP  : lexMsg cs
  | c == ','               = TComma : lexMsg cs
  | c == '_'               = TUnder : lexMsg cs
  | c == '|'               = TBar : lexMsg cs
  | c == '='               = TEq  : lexMsg cs
  | c == '&'               = TAmp : lexMsg cs
  | isIdentChar c          = let (w,rest) = span isIdentChar s in TId w : lexMsg rest
  | otherwise              = error ("AnB: unexpected character " ++ show c ++ " in message")

isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '\''

-- ---------------------------------------------------------------------------
-- Message parser (recursive descent) -> AbsTerm
-- ---------------------------------------------------------------------------

-- | Parse a message string (used by the step parser and exposed for testing).
parseMsgWith :: [(String,Sort)] -> String -> AbsTerm
parseMsgWith env str =
  case parseTerm env (lexMsg str) of
    (t, []) -> t
    (_, ts) -> error ("AnB: trailing tokens after message: " ++ show ts)

parseTerm :: [(String,Sort)] -> [Tok] -> (AbsTerm, [Tok])
parseTerm env toks = case toks of
  -- tuple  < a , b [ , c ] >
  (TLA:rest) ->
    let (items, rest') = parseTupleItems env rest
    in case items of
         [a,b]   -> (Pair a b, rest')
         [a,b,c] -> (Triple a b c, rest')
         [a]     -> (a, rest')                 -- <a> == a
         _       -> error "AnB: only pairs and triples are supported in < >"

  -- symmetric encryption {| m |}[_]K
  (TLBs:rest) ->
    let (m, rest1) = parseTerm env rest
    in case rest1 of
         (TRBs:rest2) ->
           let (k, rest3) = parseSubscript env rest2
           in (SCrypt (asKey k) m, rest3)
         _ -> error "AnB: expected |} to close {| ... |}"

  -- encryption  { m }[_]X   (sort-directed: key -> SCrypt, name -> Crypt)
  (TLB:rest) ->
    let (m, rest1) = parseTerm env rest
    in case rest1 of
         (TRB:rest2) ->
           let (k, rest3) = parseSubscript env rest2
           in (mkEnc k m, rest3)
         _ -> error "AnB: expected } to close { ... }"

  -- grouping  ( m )
  (TLP:rest) ->
    let (m, rest1) = parseTerm env rest
    in case rest1 of
         (TRP:rest2) -> (m, rest2)
         _ -> error "AnB: expected ) "

  -- proof term  zk_S( w1, ..., wk | p1, ..., pl )
  (TId "zk" : TUnder : TId st : TLP : rest) ->
    case lookup st env of
      Just (SStmt stmt) ->
        let (ws, r1) = parseArgs env TBar rest
            (ps, r2) = parseArgs env TRP r1
        in (Zk stmt ws ps, r2)
      _ -> error ("AnB: undeclared statement " ++ show st)

  -- application or atom
  (TId f : TLP : rest) -> parseApp env f rest
  (TId x : rest)       -> (resolveAtom env x, rest)

  _ -> error ("AnB: cannot parse message at " ++ show toks)

-- | items of a tuple, consuming the closing '>'
parseTupleItems :: [(String,Sort)] -> [Tok] -> ([AbsTerm], [Tok])
parseTupleItems env toks =
  let (t, rest) = parseTerm env toks
  in case rest of
       (TComma:rest') -> let (ts, rest'') = parseTupleItems env rest'
                         in (t:ts, rest'')
       (TRA:rest')    -> ([t], rest')
       _ -> error "AnB: expected , or > in tuple"

-- | comma-separated terms up to (and consuming) the given closing token
parseArgs :: [(String,Sort)] -> Tok -> [Tok] -> ([AbsTerm], [Tok])
parseArgs env close toks =
  let (t, rest) = parseTerm env toks
  in case rest of
       (TComma:rest') -> let (ts, rest'') = parseArgs env close rest' in (t:ts, rest'')
       (c:rest') | c == close -> ([t], rest')
       _ -> error ("AnB: expected , or " ++ show close ++ " in argument list")

-- | function applications:  hash(m) | mac(m,k) | pubk(A) | pk(A) | nym(z,f) | sig(A,m)
parseApp :: [(String,Sort)] -> String -> [Tok] -> (AbsTerm, [Tok])
parseApp env f rest = case f of
  "hash" -> let (m, r) = parseTerm env rest in (Hash m, expectRP r)
  "mac"  -> let (m, r1) = parseTerm env rest
            in case r1 of
                 (TComma:r2) -> let (k, r3) = parseTerm env r2
                                in (Mac (asKey k) m, expectRP r3)
                 _ -> error "AnB: mac( m , K ) needs a key argument"
  "pubk" -> pk rest
  "pk"   -> pk rest
  "nym"  -> case parseArgs env TRP rest of
              ([z, x], r) -> (Nym z x, r)
              _           -> error "AnB: nym( base , secret ) takes two arguments"
  "sig"  -> case parseArgs env TRP rest of
              ([a, m], r) -> (Sign a m, r)
              _           -> error "AnB: sig( signer , message ) takes two arguments"
  _      -> error ("AnB: unknown function symbol " ++ show f)
  where
    pk r = let (a, r') = parseTerm env r in (PubKey a, expectRP r')
    expectRP (TRP:r) = r
    expectRP _       = error ("AnB: expected ) closing " ++ f)

-- | An encryption subscript: optional '_' then a single atom.
parseSubscript :: [(String,Sort)] -> [Tok] -> (AbsTerm, [Tok])
parseSubscript env (TUnder:rest) = parseSubscript env rest
parseSubscript env (TId x : rest) = (resolveAtom env x, rest)
parseSubscript _ toks = error ("AnB: expected an encryption key/principal, got " ++ show toks)

-- | Sort-directed choice of asymmetric vs symmetric encryption.
mkEnc :: AbsTerm -> AbsTerm -> AbsTerm
mkEnc k@(AbsKey _) m = SCrypt k m
mkEnc a@(AbsName _) m = Crypt a m
mkEnc other _ = error ("AnB: cannot encrypt under " ++ hsAbsTerm other)

asKey :: AbsTerm -> AbsTerm
asKey k@(AbsKey _) = k
asKey other = error ("AnB: expected a key subscript, got " ++ hsAbsTerm other)

-- ---------------------------------------------------------------------------
-- Spec parser (line oriented)
-- ---------------------------------------------------------------------------

-- | Parse a whole @.anb@ document.
parseAnB :: String -> AnBSpec
parseAnB input =
  let ls        = filter (not . blank) (map stripComment (lines input))
      decls     = [l | l <- ls, isDecl l]
      stepLines = [l | l <- ls, not (isDecl l)]
      nm        = declValue "protocol" decls
      roles     = map roleOf (declWords "roles" decls)
      stmts     = [ parseStatement (unwords (drop 1 (words l))) | l <- decls, take 1 (words l) == ["statement"] ]
      sorts     = concat
                    [ [(zkName st, SStmt st) | st <- stmts]
                    , [(w, SNonce) | w <- declWords "nonces" decls]
                    , [(w, SKey)   | w <- declWords "keys"   decls]
                    , [(w, SDatum) | w <- declWords "data"   decls]
                    , [(w, SName)  | w <- declWords "names"  decls] ]
      steps     = parseSteps sorts stepLines
  in AnBSpec { sName = nm, sRoles = roles, sSorts = sorts, sSteps = steps }

blank :: String -> Bool
blank = all isSpace

stripComment :: String -> String
stripComment = go
  where
    go [] = []
    go ('#':_) = []
    go ('-':'-':_) = []
    go (c:cs) = c : go cs

isDecl :: String -> Bool
isDecl l = case words l of
  (w:_) -> w `elem` ["protocol","roles","nonces","keys","data","names","statement"]
  _     -> False

declValue :: String -> [String] -> String
declValue key ls = case declWords key ls of
  (w:_) -> w
  []    -> error ("AnB: missing declaration " ++ show key)

declWords :: String -> [String] -> [String]
declWords key ls =
  concat [ dropCommas (drop 1 (words l)) | l <- ls, take 1 (words l) == [key] ]
  where dropCommas = concatMap (wordsBy (== ','))

-- | A statement declaration:   NAME : lhs = rhs [ & lhs = rhs ]*
--   over witness placeholders W0, W1, ... and public placeholders P0, P1, ...
parseStatement :: String -> ZkStmt
parseStatement str =
  let (nm, body) = breakOn ':' str
  in ZkStmt (trim nm) (eqs (lexMsg body))
  where
    eqs toks =
      let (l, r1) = zkTerm toks
      in case r1 of
           (TEq:r2) -> let (r, r3) = zkTerm r2
                       in case r3 of
                            (TAmp:r4) -> (l, r) : eqs r4
                            []        -> [(l, r)]
                            _         -> error ("AnB: trailing tokens in statement " ++ show str)
           _ -> error ("AnB: expected = in statement " ++ show str)
    zkTerm (TId "hash" : TLP : r) = let (a, r1) = zkTerm r in (ZHash a, close r1)
    zkTerm (TId "nym"  : TLP : r) = let (a, b, r1) = two r in (ZNym a b, r1)
    zkTerm (TId "sig"  : TLP : r) = let (a, b, r1) = two r in (ZSign a b, r1)
    zkTerm (TLA : r) = let (a, r1) = zkTerm r
                       in case r1 of
                            (TComma:r2) -> let (b, r3) = zkTerm r2
                                           in case r3 of (TRA:r4) -> (ZPair a b, r4)
                                                         _        -> error "AnB: expected > in statement"
                            _ -> error "AnB: expected , in statement pair"
    zkTerm (TId ('W':ds) : r) | not (null ds) && all (`elem` ['0'..'9']) ds = (ZW (read ds), r)
    zkTerm (TId ('P':ds) : r) | not (null ds) && all (`elem` ['0'..'9']) ds = (ZP (read ds), r)
    zkTerm toks = error ("AnB: cannot parse statement term at " ++ show toks)
    two r = let (a, r1) = zkTerm r
            in case r1 of
                 (TComma:r2) -> let (b, r3) = zkTerm r2 in (a, b, close r3)
                 _ -> error "AnB: expected , in statement"
    close (TRP:r) = r
    close _       = error "AnB: expected ) in statement"

-- | Parse the ordered list of step lines, grouping '|' continuation lines
--   into the preceding step as extra alternatives.
parseSteps :: [(String,Sort)] -> [String] -> [(Int,[Alt])]
parseSteps env = go 1
  where
    go _ [] = []
    go n (l:ls)
      | isBranch l = error "AnB: '|' branch line without a preceding step"
      | otherwise  =
          let (conts, rest) = span isBranch ls
              alt0 = parseAlt env (dropStepNum l)
              alts = alt0 : map (parseAlt env . dropBranchMark) conts
          in (stepNum n l, alts) : go (stepNum n l + 1) rest

isBranch :: String -> Bool
isBranch l = case dropWhile isSpace l of ('|':_) -> True; _ -> False

dropBranchMark :: String -> String
dropBranchMark l = case dropWhile isSpace l of ('|':r) -> r; _ -> l

-- | Explicit @"3."@ step number, if present, else the running counter.
stepNum :: Int -> String -> Int
stepNum def l = case reads (takeWhile (/= '.') (dropWhile isSpace l)) of
  [(k, _)] | ('.' `elem` l) && numericPrefix l -> k
  _ -> def
  where numericPrefix s = case dropWhile isSpace s of
                            (c:_) -> c `elem` ['0'..'9']
                            _     -> False

dropStepNum :: String -> String
dropStepNum l =
  let l' = dropWhile isSpace l
  in case break (== '.') l' of
       (num, '.':rest) | all (`elem` ['0'..'9']) num && not (null num) -> rest
       _ -> l'

-- | Parse a single alternative:  FROM -> TO : MSG [ ; annotation ]*
parseAlt :: [(String,Sort)] -> String -> Alt
parseAlt env line =
  let (headPart, annParts) = splitAnns line
      (fromTo, msgStr) = breakOn ':' headPart
      (fromS, toS)     = breakArrow fromTo
      base = Alt { aFrom = roleOf (trim fromS)
                 , aTo   = roleOf (trim toS)
                 , aMsg  = parseMsgWith env (trim msgStr)
                 , aFresh = []
                 , aSendTest = Nothing
                 , aRecv = [(Nothing, Nothing)]
                 , aRecvMsg = Nothing }
  in foldl' (applyAnn env) base annParts

-- | Fold a single @; annotation@ into the alternative.
applyAnn :: [(String,Sort)] -> Alt -> String -> Alt
applyAnn env alt ann = case words ann of
  ("new":rest)        -> alt { aFresh = map (resolveAtom env) (splitCommaWords rest) }
  ["send_test", nm]   -> alt { aSendTest = Just nm }
  ["recv_pre", nm]    -> alt { aRecv = setLast (\(_,po) -> (Just nm, po)) (aRecv alt) }
  ["recv_post", nm]   -> alt { aRecv = setLast (\(pr,_) -> (pr, Just nm)) (aRecv alt) }
  ["recv"]            -> alt { aRecv = aRecv alt ++ [(Nothing, Nothing)] }
  ("recv_as":rest)    -> alt { aRecvMsg = Just (parseMsgWith env (unwords rest)) }
  []                  -> alt
  _                   -> error ("AnB: unrecognised annotation " ++ show ann)

setLast :: (a -> a) -> [a] -> [a]
setLast _ [] = []
setLast f xs = init xs ++ [f (last xs)]

-- ---------------------------------------------------------------------------
-- Translation to Phoebe [Action]
-- ---------------------------------------------------------------------------

-- | Translate a spec to @([Action],[RoleName])@.  The first argument resolves
--   the names of test formulae to actual 'Stmt's (constant @true@ for names not
--   present).
translate :: [(String, Stmt)] -> AnBSpec -> ([Action], [RoleName])
translate condEnv spec = (concatMap stepActions (sSteps spec), sRoles spec)
  where
    resolve Nothing  = true
    resolve (Just n) = case lookup n condEnv of
      Just s  -> s
      Nothing -> error ("AnB: undefined test formula " ++ show n
                        ++ " (supply it in the condition environment)")

    stepActions (i, alts) = sends ++ recs
      where
        branch0Test = case alts of (a0:_) -> aSendTest a0; _ -> Nothing
        sends =
          [ Send i (aFrom a) (sendCond k) (aFresh a) (aMsg a)
          | (k, a) <- zip [0 ..] alts ]
        recs =
          [ Rec i (aTo a) (resolve pre, resolve post) (maybe (aMsg a) id (aRecvMsg a))
          | a <- alts, (pre, post) <- aRecv a ]
        -- branch 0 uses its own test; later branches use the negation of it
        sendCond :: Int -> Stmt
        sendCond 0 = resolve branch0Test
        sendCond _ = Neg (resolve branch0Test)

-- ---------------------------------------------------------------------------
-- Haskell source generator (message-flow layer)
-- ---------------------------------------------------------------------------

-- | Emit the Haskell @actions@ / @roles@ source for a spec, using condition
--   /names/ verbatim (as the hand-written modules do with local @where@ defs).
genHs :: AnBSpec -> String
genHs spec = unlines $
  [ "-- Generated by AnB.hs from an Alice-and-Bob spec"
  , "roles :: [RoleName]"
  , "roles = [" ++ intercalate ", " (map show (sRoles spec)) ++ "]"
  , ""
  , "actions :: [Action]"
  , "actions ="
  ] ++ indentList (concatMap stepSrc (sSteps spec))
  where
    stepSrc (i, alts) = sends ++ recs
      where
        branch0 = case alts of (a0:_) -> aSendTest a0; _ -> Nothing
        sends = [ sendSrc i k a | (k, a) <- zip [0 :: Int ..] alts ]
        recs  = [ recSrc i (aTo a) pre post (maybe (aMsg a) id (aRecvMsg a))
                | a <- alts, (pre, post) <- aRecv a ]
        sendSrc i' k a =
          "Send " ++ show i' ++ " " ++ show (aFrom a) ++ " "
            ++ condSrc k ++ " ["
            ++ intercalate "," (map hsAbsTerm (aFresh a)) ++ "] "
            ++ hsAbsTerm (aMsg a)
        condSrc 0 = nameOr "true" branch0
        condSrc _ = "(Neg " ++ nameOr "true" branch0 ++ ")"
    recSrc i r pre post m =
      "Rec " ++ show i ++ " " ++ show r ++ " "
        ++ recCond pre post ++ " " ++ hsAbsTerm m
    recCond Nothing Nothing = "trues"
    recCond pre post = "(" ++ nameOr "true" pre ++ "," ++ nameOr "true" post ++ ")"
    nameOr d Nothing  = d
    nameOr _ (Just n) = n

indentList :: [String] -> [String]
indentList [] = ["    [ ]"]
indentList (x:xs) = ("    [ " ++ x) : map ("    , " ++) xs ++ ["    ]"]

-- | Render an abstract term as Haskell constructor source.
hsAbsTerm :: AbsTerm -> String
hsAbsTerm t = case t of
  AbsName r     -> "(AbsName " ++ show r ++ ")"
  AbsNonce n    -> "(AbsNonce " ++ show n ++ ")"
  AbsKey k      -> "(AbsKey " ++ show k ++ ")"
  AbsDatum d    -> "(AbsDatum " ++ show d ++ ")"
  PubKey a      -> "(PubKey " ++ hsAbsTerm a ++ ")"
  Pair a b      -> "(Pair " ++ hsAbsTerm a ++ " " ++ hsAbsTerm b ++ ")"
  Triple a b c  -> "(Triple " ++ hsAbsTerm a ++ " " ++ hsAbsTerm b ++ " " ++ hsAbsTerm c ++ ")"
  Crypt a m     -> "(Crypt " ++ hsAbsTerm a ++ " " ++ hsAbsTerm m ++ ")"
  SCrypt k m    -> "(SCrypt " ++ hsAbsTerm k ++ " " ++ hsAbsTerm m ++ ")"
  Hash m        -> "(Hash " ++ hsAbsTerm m ++ ")"
  Mac k m       -> "(Mac " ++ hsAbsTerm k ++ " " ++ hsAbsTerm m ++ ")"
  Nym z f       -> "(Nym " ++ hsAbsTerm z ++ " " ++ hsAbsTerm f ++ ")"
  Sign a m      -> "(Sign " ++ hsAbsTerm a ++ " " ++ hsAbsTerm m ++ ")"
  Zk st ws ps   -> "(Zk (ZkStmt " ++ show (zkName st) ++ " " ++ show (zkEqs st) ++ ") ["
                     ++ intercalate "," (map hsAbsTerm ws) ++ "] ["
                     ++ intercalate "," (map hsAbsTerm ps) ++ "])"
  _             -> error "AnB: hsAbsTerm: unsupported term shape"

-- ---------------------------------------------------------------------------
-- Tiny string helpers
-- ---------------------------------------------------------------------------

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace

-- | split on the first occurrence of a separator char
breakOn :: Char -> String -> (String, String)
breakOn ch s = case break (== ch) s of
  (a, _:b) -> (a, b)
  (a, [])  -> (a, "")

-- | split "A -> B" on the first arrow "->"
breakArrow :: String -> (String, String)
breakArrow = go ""
  where
    go acc ('-':'>':rest) = (reverse acc, rest)
    go acc (c:cs)         = go (c:acc) cs
    go acc []             = error ("AnB: missing -> in " ++ show (reverse acc))

splitAnns :: String -> (String, [String])
splitAnns s = case splitOn ';' s of
  (h:anns) -> (h, map trim anns)
  []       -> (s, [])

-- generic splitters -------------------------------------------------

splitOn :: Char -> String -> [String]
splitOn ch = wordsBy (== ch)

splitCommaWords :: [String] -> [String]
splitCommaWords = splitCommaWordsStr . unwords

splitCommaWordsStr :: String -> [String]
splitCommaWordsStr = filter (not . null) . map trim . wordsBy (== ',')

wordsBy :: (Char -> Bool) -> String -> [String]
wordsBy p s = case dropWhile p s of
  "" -> []
  s' -> w : wordsBy p s''
        where (w, s'') = break p s'
