{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Language.Haskell.Exts hiding (layout, Var)
import Text.Show.Pretty (ppShow)
import System.Environment
import Data.List (nub)
import Text.Printf (printf)

-- Represents: A GADT data declaration
--  Example:
--    data BTree a b where
--      BLeaf :: a -> BTree a b
--      BNode :: b -> BTree a b -> BTree a b -> BTree a b
-- Contents:
--  String:    GADT Name.
--               From Example: "BTree"
--  DeclHead:  The abstract syntax representation of the data declaration. Used for pretty printing in proper syntax. Defined in Language.Haskell.Exts.Syntax
--               From Example, this represents the "BTree a b"
type GADT = (String, DeclHead SrcSpanInfo, [GADTConstructor])

-- Represents: A GADT constructor
--   Example: BLeaf :: a -> BTree a b
-- Contents:
--   String:   Constructor Name.
--               From Example: "BLeaf"
--   Type:     The abstract syntax representation of the type declaration for the constructor. Used for pretty printing. Defined in Language.Haskell.Exts.Syntax
--               From Example: Represents: 'a -> BTree a b'
--   [String]: A list of type variables use in the type declaration for the constructor. Use in forall generation
--               From Example: ["a", "b"]
--   [Bool]:   A list that represents whether a function argument is the GADT type, and thus needs to be replaced in the fold generation
--               From Example: [False, True]
type GADTConstructor = (String, Type SrcSpanInfo, [String], [Bool])

-- main for generator. calls functions to read in filenames, run the
-- generator and write the output file
main :: IO ()
main = do
        --ifile <- getInFileName
        --ofile <- getOutFileName
        args <- getArgs
        case args of
            [ifile, ofile] -> do
                result <- parseFile ifile
                let hModule = (fromParseResult result)
                    gDataDecl = separate hModule
                    parseResult = ppShow gDataDecl
                    gadt = simplifyGADT gDataDecl
                putStrLn $ prettyPrint gDataDecl ++ "\n\n"
                putStrLn $ genAllFunctions gadt
                --writeFile ofile parseResult
                putStrLn "\nGeneration successful\n"

            _ -> putStrLn "Wrong number of args. Example: Main infile outfile"

-- =======================================================================================
-- |                                Top Level Generators                                 |
-- =======================================================================================
genAllFunctions :: GADT -> String
genAllFunctions gadt =
    printf "type MNat f g = forall c1 c2. f c1 c2 -> g c1 c2\n\
           \\n\
           \%s\n\n\
           \%s\n\n\
           \-- === Fold/Build Rule ===\n\
           \-- %s"
           (genFold gadt)
           (genBuild gadt)
           (genRule gadt)

genFold :: GADT -> String
genFold (gadtName, gadtHead, constructors) =
    printf "%s ::\n\
           \  %s ->\n\
           \  forall %s. %s -> %s\n\
           \%s"
        funcName
        (genType gadtName constructors)
        (join " " $ getTypeVariablesHead gadtHead)
        (prettyPrint gadtHead)
        (prettyPrint $ convertHead gadtHead)
        (genFoldFunctions funcName constructors)
    where funcName = "fold" ++ gadtName

genBuild :: GADT -> String
genBuild (gadtName, _, constructors) =
    printf "%s :: (forall f.\n\
           \  %s ->\n\
           \      MNat c f) -> MNat c %s\n\
           \%s g = g %s"
           funcName
           (genType gadtName constructors)
           gadtName
           funcName
           (join " " $ map (\(constrName, _, _, _) -> constrName) constructors)
   where funcName = "build" ++ gadtName

genRule :: GADT -> String
genRule (gadtName, _, constructors) =
    printf "%s %s . %s g = g %s"
        ("fold" ++ gadtName)
        functions
        ("build" ++ gadtName)
        functions
    where functions = genFunctions $ length constructors


-- =======================================================================================
-- |                                  Generator Helpers                                  |
-- =======================================================================================

genType :: String -> [GADTConstructor] -> String
genType gadtName constructors =
    (join " ->\n  " $ map (genTypeLine gadtName) constructors)

genTypeLine :: String -> GADTConstructor -> String
genTypeLine gadtName (_, constrType, typeVariables, _) =
    printf "(%s%s)"
        forallSection
        (prettyPrint $ convert gadtName constrType)
    where forallSection = if length typeVariables /= 0
                          then printf "forall %s. " (join " " typeVariables)
                          else ""

genFoldFunctions :: String -> [GADTConstructor] -> String
genFoldFunctions funcName constructors =
    (join "\n" $ map (genFoldFunctionLine funcName len) $ zip [1..len] constructors)
    where len = length constructors

genFoldFunctionLine :: String -> Int -> (Int, GADTConstructor) -> String
genFoldFunctionLine funcName len (n, (constrName, _, _, needFolds)) =
    printf "%s %s (%s %s) = %s %s"
        funcName
        (genFunctions len)
        constrName
        (genVariables $ length needFolds)
        (genFn n)
        (join " " $ map genVarOrFoldCall (zip [1..length needFolds] needFolds))
    where
        genVarOrFoldCall :: (Int, Bool) -> String
        genVarOrFoldCall (n, shouldFold) =
            if shouldFold
            then printf "(%s %s v_%d)" funcName (genFunctions len) n
            else genVar n

simplifyGADT :: Decl SrcSpanInfo -> GADT
simplifyGADT (GDataDecl _ _ _ gadtHead _ constructors _) =
    (gadtName, gadtHead, map (simplifyGADTConstructor gadtName) constructors)
        where gadtName = getHeadName gadtHead

simplifyGADTConstructor :: String -> GadtDecl SrcSpanInfo -> GADTConstructor
simplifyGADTConstructor gadtName (GadtDecl _ constrName _ constrType) = (getFromName constrName, constrType, getTypeVariables constrType, shouldReplace gadtName constrType)

-- =======================================================================================
-- |                               Abstract Syntax Getters                               |
-- =======================================================================================

-- Generates a list of the type variables in a declared Type.
-- Example:
--   Given a Type representing:
--      a -> (b -> [(c, d)] -> Int) -> Expr a d
--   returns:
--      ["a", "b", "c", "d"]
getTypeVariables :: Language.Haskell.Exts.Type l -> [String]
getTypeVariables  decType = nub $ getTypeVariables' decType
getTypeVariables' decType = case decType of
    --When we find a type variable, extract its string representation
    TyVar _ name                            -> [getFromName name]

    -- Recursive calls to find TyVar's
    TyForall _ _ _ t1                       -> getTypeVariables' t1
    TyFun _ t1 t2                           -> getTypeVariables' t1 ++ getTypeVariables' t2
    TyTuple _ _ types                       -> concat $ map getTypeVariables' types
    TyUnboxedSum _ types                    -> concat $ map getTypeVariables' types
    TyList _ t1                             -> getTypeVariables' t1
    TyApp _ t1 t2                           -> getTypeVariables' t1 ++ getTypeVariables' t2
    TyParArray _ t1                         -> getTypeVariables' t1
    TyParen _ t1                            -> getTypeVariables' t1
    TyInfix _ t1 _ t2                       -> getTypeVariables' t1 ++ getTypeVariables' t2
    TyKind _ t1 _                           -> getTypeVariables' t1
    TyPromoted _ (PromotedList _ _ types)   -> concat $ map getTypeVariables' types
    TyPromoted _ (PromotedTuple _ types)    -> concat $ map getTypeVariables' types
    TyEquals _ t1 t2                        -> getTypeVariables' t1 ++ getTypeVariables' t2
    TyBang _ _ _ t1                         -> getTypeVariables' t1

    -- Unhandled Types. These contain no possible type variable information
    -- TyCon      - Unused because we don't want constructor names, only type variables
    -- TyPromoted - When not dealing with a PromotedList or PromotedTuple, there is no useful type info
    -- TySplit
    -- TyWildCard
    -- TyQuasiQuote
    _  -> []

-- Similar to getTypeVariables, this function finds all of the type variables specified
-- in a data declaration's head (data {head} = ...)
-- Example:
--   Given a DeclHead representing:
--      data Expr a b = ...
--   Returns: ["a", "b"]
getTypeVariablesHead gadtHead = nub $ getTypeVariablesHead' gadtHead
getTypeVariablesHead' (DHApp _ x1 x2) = getTypeVariablesHead' x1 ++ getFromTyVarBind x2
getTypeVariablesHead' (DHead _ _) = []

-- Extracts the string name of a data declaration
-- Example:
--   Given a DeclHead representing:
--     data Expr a b = ...
--   Returns: "Expr"
getHeadName (DHApp _ x _) = getHeadName x
getHeadName (DHead _ x)   = getFromName x

-- Extracts the string representation of a type variable out of its abstract syntax representation
getFromTyVarBind (UnkindedVar _ name) = [getFromName name]
getFromTyVarBind (KindedVar _ name _) = [getFromName name]

-- Extracts the string representation of a qualified name out of its abstract syntax representation
getFromQName (Qual _ _ name) = getFromName name
getFromQName (UnQual _ name) = getFromName name
getFromQName (Special _ _)   = "" --We don't care about special constructors

-- Extracts the string representation of an identifier (Name) out of its abstract syntax representation
getFromName (Ident _ name) = name
getFromName (Symbol _ name) = name

-- Placeholder function that returns the first abstract syntax declaration in a module.
-- Currently being used to retrieve a GADT from a file where the GADT is the first declared item in the file.
separate (Module _ _ _ _ [x]) = x


shouldReplace gadtName constrType = safeInit $ shouldReplace' gadtName constrType
shouldReplace' gadtName constrType = case constrType of
    TyFun _ t1 t2   -> shouldReplace' gadtName t1 ++ shouldReplace' gadtName t2
    TyCon _ name    -> [getFromQName name == gadtName]
    TyApp _ t1 t2   -> handleApp gadtName t1
    TyVar _ name    -> [False]
    TyParen _ t1    -> [False]
    _               -> []

handleApp gadtName (TyApp _ t1 t2) = handleApp gadtName t1 ++ handleApp gadtName t2
handleApp gadtName (TyCon _ name) = [getFromQName name == gadtName]
handleApp gadtName _ = []

-- =======================================================================================
-- |                              Abstract Syntax Modifiers                              |
-- =======================================================================================

convertHead (DHApp l x1 x2) = DHApp l (convertHead x1) x2
convertHead (DHead l (Ident l2 name)) = DHead l (Ident l2 "f")

convert name (TyFun l t1 t2) = TyFun l (convert name t1) (convert name t2)
convert name (TyApp l t1 t2) = TyApp l (convert name t1) (convert name t2)
convert name (TyCon l qname) = TyCon l (convertQ name qname)
convert name x = x

convertQ name (UnQual l (Ident l2 ident)) = if name == ident
                                         then UnQual l (Ident l2 "f")
                                         else UnQual l (Ident l2 ident)
convertQ name x = x

-- =======================================================================================
-- |                                  General Utilities                                  |
-- =======================================================================================
genFn :: Int -> String
genFn n = printf "f_%d" n

genVar :: Int -> String
genVar n = printf "v_%d" n

genFunctions len = join " " $ map genFn [1..len]
genVariables len = join " " $ map genVar [1..len]

join :: String -> [String] -> String
join sep [] = []
join sep [x] = x
join sep (x:xs) = x ++ sep ++ (join sep xs)

joinR :: String -> [String] -> String
joinR sep [] = []
joinR sep xs = join sep xs ++ sep

-- A safe version of Prelude.init. Does not throw errors on []
-- Returns the entire list, minus the first element.
safeInit [] = []
safeInit xs = init xs

-- Gets input file name from stdin
getInFileName :: IO String
getInFileName = do putStrLn "Input file: "
                   ifile <- getLine
                   return ifile

-- Gets input file name from stdin
getOutFileName :: IO String
getOutFileName = do putStrLn "Output file: "
                    ofile <- getLine
                    return ofile

-- =======================================================================================
-- |             Code Generated By Program, Place Here To Test Compilability             |
-- =======================================================================================
type MNat f g = forall c1 c2. f c1 c2 -> g c1 c2

data Expr a b where
    Var :: a -> Expr a b
    IConst :: Int -> Expr a Int
    RConst :: Float -> Expr a Float
    PProd :: Expr a b -> Expr a b -> Expr a b
    SIMul :: Expr a b -> Int -> Expr a b
    SRMul :: Expr a b -> Float -> Expr a Float

foldExpr ::
  (forall a b. a -> f a b) ->
  (forall a. Int -> f a Int) ->
  (forall a. Float -> f a Float) ->
  (forall a b. f a b -> f a b -> f a b) ->
  (forall a b. f a b -> Int -> f a b) ->
  (forall a b. f a b -> Float -> f a Float) ->
  forall a b. Expr a b -> f a b
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (Var v_1) = f_1 v_1
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (IConst v_1) = f_2 v_1
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (RConst v_1) = f_3 v_1
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (PProd v_1 v_2) = f_4 (foldExpr f_1 f_2 f_3 f_4 f_5 f_6 v_1) (foldExpr f_1 f_2 f_3 f_4 f_5 f_6 v_2)
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (SIMul v_1 v_2) = f_5 (foldExpr f_1 f_2 f_3 f_4 f_5 f_6 v_1) v_2
foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (SRMul v_1 v_2) = f_6 (foldExpr f_1 f_2 f_3 f_4 f_5 f_6 v_1) v_2

buildExpr :: (forall f.
  (forall a b. a -> f a b) ->
  (forall a. Int -> f a Int) ->
  (forall a. Float -> f a Float) ->
  (forall a b. f a b -> f a b -> f a b) ->
  (forall a b. f a b -> Int -> f a b) ->
  (forall a b. f a b -> Float -> f a Float) ->
      MNat c f) -> MNat c Expr
buildExpr g = g Var IConst RConst PProd SIMul SRMul

-- ============================
data Boo a b where
        Foo :: a -> ([c] -> Boo a b) -> Boo a a
        Joe :: a -> Boo (b -> Boo a b) Int -> Boo a a
        Lin :: a -> (b -> Int) -> Boo a b

foldBoo ::
  (forall a c b. a -> ([c] -> Boo a b) -> f a a) ->
  (forall a b. a -> f (b -> Boo a b) Int -> f a a) ->
  (forall a b. a -> (b -> Int) -> f a b) ->
  forall a b. Boo a b -> f a b
foldBoo f_1 f_2 f_3 (Foo v_1 v_2) = f_1 v_1 v_2
foldBoo f_1 f_2 f_3 (Joe v_1 v_2) = f_2 v_1 (foldBoo f_1 f_2 f_3 v_2)
foldBoo f_1 f_2 f_3 (Lin v_1 v_2) = f_3 v_1 v_2

buildBoo :: (forall f.
  (forall a c b. a -> ([c] -> Boo a b) -> f a a) ->
  (forall a b. a -> f (b -> Boo a b) Int -> f a a) ->
  (forall a b. a -> (b -> Int) -> f a b) ->
      MNat c f) -> MNat c Boo
buildBoo g = g Foo Joe Lin

-- === Fold/Build Rule ===
-- foldBoo f_1 f_2 f_3 . buildBoo g = g f_1 f_2 f_3




-- ==== From paper
--foldExpr :: (forall a b. a -> f a b) ->
--    (forall a. Int -> f a Int) ->
--    (forall a. Float -> f a Float) ->
--    (forall a b. f a b -> f a b -> f a b) ->
--    (forall a b. f a b -> Int -> f a b) ->
--    (forall a b. f a b -> Float -> f a Float) ->
--    forall a b. Expr a b -> f a b
--foldExpr v i r p si sr (Var t)     = v t
--foldExpr v i r p si sr (IConst t)  = i t
--foldExpr v i r p si sr (RConst t)  = r t
--foldExpr v i r p si sr (PProd t u) = p (foldExpr v i r p si sr t) (foldExpr v i r p si sr u)
--foldExpr v i r p si sr (SIMul t n) = si (foldExpr v i r p si sr t) n
--foldExpr v i r p si sr (SRMul t n) = sr (foldExpr v i r p si sr t) n



