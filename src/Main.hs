-- Written by Austin Keener (2018)
-- In collaboration with Dr. Patricia Johann
--
-- References:
--  * Foundations for Structured Programming with GADTs by Patricia Johann and Neil Ghani

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Language.Haskell.Exts hiding (layout, Var)
import Text.Show.Pretty (ppShow)
import System.Environment
import Data.List (nub, isInfixOf)
import Text.Printf (printf)
import Data.Maybe (fromJust, isJust, isNothing)
import Control.Monad (mapM_)

-- Represents: A GADT data declaration, simplified for ease of use from the more complex
--             Abstract Syntax Representation provided by Haskell Src Exts
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

-- Represents: A GADT constructor, simplified for ease of use from the more complex Abstract Syntax Representation provided by Haskell Src Exts
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

type ConstructorErrorDetail = (String, [TypeErrorDetail])
type TypeErrorDetail = ([Type SrcSpanInfo], String)

-- main for generator. calls functions to read in filenames, run the
-- generator and write the output file
main :: IO ()
main = do
        args <- getArgs
        case args of
            [ifile, ofile] -> do
                result <- parseFile ifile
                let hModule = (fromParseResult result)
                    gDataDecl = separate hModule
                    parseResult = ppShow gDataDecl
                    gadt = simplifyGADT gDataDecl
                    validationResult = validateGadt gadt
                    --genResult = printf "%s\n\n%s" (prettyPrint gDataDecl) (genAllFunctions gadt)
                    genResult = genAllFunctions gadt

                putStrLn "---------- Input GADT ----------"
                putStrLn $ prettyPrint gDataDecl
                showFirst gadt

                putStrLn "\n----------- Results ------------"
                if isNothing validationResult
                    then do
                        putStrLn genResult
                        writeFile ofile $ printf "%s\n\n%s" (prettyPrint gDataDecl) genResult  -- Generate Code
                        --writeFile ofile $ parseResult                                        -- Abstract Syntax
                        putStrLn $ printf "\nGeneration successful. Result also saved at: %s\n" ofile

                    else do
                        putStrLn "The provided GADT is not a positive datatype, thus we cannot generate code for it."
                        putStrLn "\n---- Errors ----"
                        mapM_ printErrors $ fromJust validationResult

            _ -> putStrLn "Wrong number of args. Example: shortcut-fusion-gen infile outfile"

-- =======================================================================================
-- |                                    Type Handling                                    |
-- =======================================================================================
--0: not GADT
--0: GADT, thus fold
--1: GADT output, thus post compose
--2: GADT input, thus pre-compose

data Foo a where
    J :: ((Foo a -> Int) -> Int) -> Foo a

fold :: (((c a -> Int) -> Int) -> c a) -> Foo a -> c a
fold j (J y) = j (\g -> y (\r -> g (fold j r)))

-- If constructor is: (J y), replacement is j,
--  then j + below
-- for none:   y
-- for fold:   (fold j y)

-- These require recursion on y.
-- for a pre:  (\g -> y (\r -> g (fold j r)))
-- for a post: (fold j) . y

conGen :: GADTConstructor -> String
conGen gadtConstr = join "\n" $ map (toGens' "fold" "j") $ zip parts [1..length parts]
    where
        parts = conParts gadtConstr



conParts :: GADTConstructor -> [GTree (Type SrcSpanInfo)]
conParts gadtConstr = parts
    where
        tree@(Node _ allParts) = typeTree gadtConstr
        parts = safeInit allParts

toGens' :: String -> String -> (GTree (Type SrcSpanInfo), Int) -> String
toGens' fn f (part, v) = toGens fn f (genVar v) part

-- foldName, 'f_1 .. f_n', f_#, type
toGens :: String -> String -> String -> GTree (Type SrcSpanInfo) -> String
toGens fn f v (Leaf None _)   = v
toGens fn f v (Leaf Fold _)   = printf "(%s %s %s)" fn f v --('foldName' 'f_1 f_2' 'v_1')
toGens fn f v (Leaf Pre  _)   = printf "(%s %s %s)" fn f v --('foldName' 'f_1 f_2' 'v_1')
toGens fn f v (Node None tys) = toGens2 fn f v tys
toGens fn f v (Node Pre  tys) = toGens2 fn f v tys--printf "(\\g -> %s %s)" v $ toGens2 fn f "g" tys
toGens fn f v (Node Post tys) = printf "((%s %s) . %s)" fn f $ toGens2 fn f v tys

--current (wrong): (\v_3_1       -> v_3 (\g       -> v_3_1 (\g_1 -> g (foldBoo f_1 f_2 f_3 g_1))))
--needed  (right): (\v_3_1       -> v_3 (\v_3_1_1 -> v_3_1 (foldBoo f_1 f_2 f_3 v_3_1_1)))

-- Examples
--                 (\g     g2    -> v_3 (\g_1     -> g     (foldBoo f_1 f_2 f_3 g_1))     g2)
--                 (\v_3_1 v_3_2 -> v_3 (\v_3_1_1 -> v_3_1 (foldBoo f_1 f_2 f_3 v_3_1_1)) v_3_2)

toGens2 fn f vv tys = if isInfixOf tysVars tysGen
                 then vv
                 else printf "(\\%s -> %s %s)"
                        (join " " tysVars)
                        vv
                        (join " " tysGen)
    where
        tysParts = safeInit tys
        tysVars  = map (\n -> printf "%s_%s" vv $ show n) [1..length tysParts]
        tysGen   = map (\(p, v) -> toGens fn f v p) $ zip tysParts tysVars
{-
    needs to either be
    1) v_1  or
    2) (\x_1 x_2 x_3 -> v_1 x_1 (toGens x_2 ty) (toGens x_3 ty))

    1: if all parts are Leaf, or all are Node-None (recursively)
    2: else

    question: Can we do this without a "bool"
    options:
      1) call function to determine if good or need gen
      2) call function and either get v_1 or gen (mutual recursion)
        how? Map
        return?
          needs to have either the gen value
          or provided value. Can check if provided == returned for "needed gen"
-}

data Handling = None
              | Fold
              | Pre
              | Post
    deriving Show

data GTree a  where
    Node :: Handling -> [GTree a] -> GTree a
    Leaf :: Handling -> a -> GTree a
        deriving Show

showFirst :: GADT -> IO ()
showFirst (_, _, x : xs) =
    do
        --putStrLn $ treeToString 0 $ typeTree x
        --putStrLn $ ppShow $ stringTree $ typeTree x
        putStrLn $ conGen x

stringTree :: GTree (Type SrcSpanInfo) -> GTree String
stringTree (Leaf h ty) = Leaf h $ prettyPrint ty
stringTree (Node h ts) = Node h $ map stringTree ts

treeToString :: Int -> GTree (Type SrcSpanInfo) -> String
treeToString level (Leaf _ ty) = prettyPrint ty
treeToString level (Node _ ts) =
    printf "(%s)" $ join " -> " $ map (treeToString (level + 1)) ts

typeTree :: GADTConstructor -> GTree (Type SrcSpanInfo)
typeTree (constrName, constrType, _, _) = toTree' constrType

toTree' :: Type SrcSpanInfo -> GTree (Type SrcSpanInfo)
toTree' ty = case getParts ty of
    [x] -> toTree 1 x
    xs  -> Node None $ map (toTree 1) xs

toTree :: Int -> Type SrcSpanInfo -> GTree (Type SrcSpanInfo)
toTree level ty@(TyFun _ t1 t2) = Node (nodeHandling "Boo" level tys) tys
    where tys = map (toTree (level + 1)) $ getParts ty
toTree level (TyParen _ t1)     = toTree level t1
toTree level ty                 = Leaf (leafHandling (level - 1) "Boo" ty) ty

nodeHandling gadtName level tys
    | level == 0         = error "unknown"
    | level `mod` 2 == 1 = nodePost gadtName tys
    | otherwise          = nodePre tys

nodePre []  = None
nodePre (ty:tys) = case ty of
    (Leaf Pre _) -> Pre
    _            -> nodePre tys

nodePost gadtName tys =
    if containsGadt gadtName $ getTy $ last tys
        then Post
        else None

isLeaf (Leaf _ _) = True
isLeaf _ = False
getTy (Leaf _ ty) = ty

leafHandling level gadtName ty =
    if containsGadt gadtName ty
        then if level == 0
            then Fold
            else Pre
        else None

containsGadt gadtName ty = case ty of
    TyApp _ t1 t2   -> containsGadt gadtName t1
    TyCon _ name    -> getFromQName name == gadtName
    _               -> False
-- =======================================================================================
-- |                           Validation and Error Printing                             |
-- =======================================================================================

validateGadt :: GADT -> Maybe [ConstructorErrorDetail]
validateGadt (gadtName, _, constructors) = maybeListToMaybe $ map (validateGadtConstructor gadtName) constructors

-- this can be considered level 0
validateGadtConstructor :: String -> GADTConstructor -> Maybe ConstructorErrorDetail
validateGadtConstructor gadtName (constrName, constrType, _, _) = addConstructorName constrName $ mergeAndAddParent constrType $ map (isValid checkArgs gadtName) (getParts constrType)

-- if args aren't GADT. (levels 1, 3, 5, etc)
checkArgs :: String -> Type SrcSpanInfo -> Maybe [TypeErrorDetail]
checkArgs ident ty = if (not . null) argErrors
                     then Just argErrors
                     else partErrors
    where
        parts            = getParts ty
        args             = safeInit parts
        argErrors        = map toArgError $ filter (hasIdent ident) args
        partErrors       = mergeAndAddParent ty $ map (isValid checkOutput ident) parts
        toArgError arg = ([ty, arg], "Contains the GADT {where} it shouldn't (args)")

-- if output isn't GADT. (levels 2, 4, 6, etc)
checkOutput :: String -> Type SrcSpanInfo -> Maybe [TypeErrorDetail]
checkOutput ident ty = if hasIdent ident output
                       then Just [outputError]
                       else partErrors
    where
        parts              = getParts ty
        output             = last parts
        partErrors         = mergeAndAddParent ty $ map (isValid checkArgs ident) parts
        outputError        = ([ty, output], "Contains GADT {where} it shouldn't (output)")

hasIdent ident ty = case ty of
    TyForall _ _ _ t          -> hasIdent ident t
    TyParen _ t               -> hasIdent ident t
    TyList _ t                -> hasIdent ident t
    TyTuple _ _ ts            -> any (hasIdent ident) ts
    TyApp _ t1 t2             -> hasIdent ident t1 || hasIdent ident t2
    TyCon _ qname             -> getFromQName qname == ident
    _                         -> False

isValid :: (String -> Type SrcSpanInfo -> Maybe [TypeErrorDetail])
            -> String
            -> Type SrcSpanInfo
            -> Maybe [TypeErrorDetail]
isValid handle ident ty = case ty of
    TyFun _ _ _               -> handle ident ty
    TyParen _ t               -> isValid handle ident t
    TyList _ t                -> isValid handle ident t
    TyTuple _ _ ts            -> mergeAndAddParent ty $ map (isValid handle ident) ts
    _                         -> Nothing

getParts :: Type SrcSpanInfo -> [Type SrcSpanInfo]
getParts (TyFun _ t1 t2) = t1 : getParts t2
getParts t = [t]

-- =====================
-- | Error Combinators |
-- =====================

mergeAndAddParent :: Type SrcSpanInfo -> [Maybe [TypeErrorDetail]] -> Maybe [TypeErrorDetail]
mergeAndAddParent parentType errors = addParentType parentType $ mergeErrors errors

addConstructorName :: String -> Maybe [TypeErrorDetail] -> Maybe ConstructorErrorDetail
addConstructorName constrName maybeErrors = case maybeErrors of
    Just errors -> Just (constrName, errors)
    Nothing     -> Nothing

addParentType :: Type SrcSpanInfo -> Maybe [TypeErrorDetail] -> Maybe [TypeErrorDetail]
addParentType ty maybeErr = case maybeErr of
    Just errors -> Just $ map (\(typePath, error) -> (ty : typePath, error)) errors
    Nothing     -> Nothing

mergeErrors :: [Maybe [TypeErrorDetail]] -> Maybe [TypeErrorDetail]
mergeErrors maybes = if (not . null) errors
                     then Just errors
                     else Nothing
    where errors = maybesToErrors maybes

maybesToErrors :: [Maybe [TypeErrorDetail]] -> [TypeErrorDetail]
maybesToErrors maybes = concat $ map fromJust $ filter isJust maybes

maybeListToMaybe :: [Maybe a] -> Maybe [a]
maybeListToMaybe maybes = case values of
        [] -> Nothing
        xs -> Just xs
    where values = map fromJust $ filter isJust maybes

-- ==================
-- | Error Printing |
-- ==================

printErrors :: ConstructorErrorDetail -> IO ()
printErrors (constrName, typeErrors) =
    do
        putStrLn $ constrName ++ ":"
        mapM_ (putStrLn . handleError) typeErrors
        putStrLn "----\n"

handleError :: TypeErrorDetail -> String
handleError (typePath, error) =
    printf " Problem: %s\n\
           \ Path:\n\
           \%s\n"
           error
           tt
    where tt = join "\n" $ map handlePathLine $ zip typePath [1 .. length typePath]

handlePathLine :: (Type SrcSpanInfo, Int) -> String
handlePathLine (typePath, level) =
    printf "   L%s: %s" (show level) (prettyPrint typePath)

-- =======================================================================================
-- |                                Top Level Generators                                 |
-- =======================================================================================

-- Generates all code required for all functions, including
-- the Fold, Build, Fold/Build rule, and MNat type synonym.
-- This is the main entry for generation.
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

-- Generates the Fold function for a GADT
-- Given a simplified Abstract Syntax Representation of a GADT (simplifyGADT),
--  this will return a String containing the Fold Function.
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

-- Generates the Build function for a GADT
-- Given a simplified Abstract Syntax Representation of a GADT (simplifyGADT),
--  this will return a String containing the Build Function.
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

-- Generates the Fold/Build rule for a GADT
-- Given a simplified Abstract Syntax Representation of a GADT (simplifyGADT),
--  this will return a String containing the Fold/Build rule.
-- The Fold/Build rule is used for compiler optimizations and is not a function that can be directly executed
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
-- All documentation in this group (Generator Helpers), when refering to an example GADT,
--  will be refering to a BTree as defined below:
--
-- data BTree a b where
--    BLeaf :: a -> BTree a b
--    BNode :: b -> BTree a b -> BTree a b -> BTree a b
--
-- ###################################### IMPORTANT ######################################
-- Additionally, anywhere "AST(name)" is seen, it means that the datavalue is the Abstract
-- Syntax Tree for that piece of data. For the actual type, refer to the function's type.
-- #######################################################################################

-- Generates the entire function type for a Fold or Build based on the
--  data constructors of a GADT.
-- The types for both Fold and Build can be generate in the same function as their types are almost identical.
--
-- Example:
--   Given the BTree GADT:
--     genType "BTree" [AST(BLeaf), AST(BNode)]
--   Returns:
--     "(forall a b. a -> f a b) ->\n\
--     \  (forall b a. b -> f a b -> f a b -> f a b)"
genType :: String -> [GADTConstructor] -> String
genType gadtName constructors =
    (join " ->\n  " $ map (genTypeLine gadtName) constructors)


-- A helper function for genType, this function generates 1 line of the
-- total type function, based on the GADT data constructor provided to it.
--
-- Example:
--   Given the AST for BNode:
--     genTypeLine "BTree" AST(BNode)
--   Returns:
--     "(forall b a. b -> f a b -> f a b -> f a b)"
genTypeLine :: String -> GADTConstructor -> String
genTypeLine gadtName (_, constrType, typeVariables, _) =
    printf "(%s%s)"
        forallSection
        (prettyPrint $ convert gadtName constrType)
    where forallSection = if length typeVariables /= 0
                          then printf "forall %s. " (join " " typeVariables)
                          else ""

-- Generates the entire function body for Fold.
-- Note: Does not generate the type. Refer to getType for type generation.
--
-- Example:
--   Given the BTree GADT:
--     genFoldFunctions "BTree" [AST(BLeaf), AST(BNode)]
--   Returns: foldExpr f_1 f_2 f_3 f_4 f_5 f_6 (Var v_1) = f_1 v_1
--     "foldBTree f_1 f_2 (BLeaf v_1) = f_1 v_1\n
--      foldBTree f_1 f_2 (BNode v_1 v_2 v_3) = f_2 v_1 (foldBTree f_1 f_2 v_2) (foldBTree f_1 f_2 v_3)"
genFoldFunctions :: String -> [GADTConstructor] -> String
genFoldFunctions funcName constructors =
    (join "\n" $ map (genFoldFunctionLine funcName len) $ zip [1..len] constructors)
    where len = length constructors

-- A helper function for  genFoldFunctions, this function generates a single
-- function body line, based on the GADT data constructor provided to it.
--
-- params:
--  funcName:   Name of the fold function, which is the concatination of "fold" and the GADT name (example, for BTree:         "foldBTree")
--  len:        The total amount of data constructors in the GADT.                                (example, for BTree:                   2)
--  n:          The number of the replacement function to use for this line. (f_n)                (example, for BNode:                   2)
--  constrName: The name of the GADT data constructor                                             (example, for BNode:             "BNode")
--  needFolds:  A list of booleans, each representing a variable, true if it needs to fold.       (example, for BNode: [False, True, True])
--
-- Example:
--   Given the AST for BNode:
--     genFoldFunctionLine "BTree" 2 AST(BNode)
--   Returns:
--     "foldBTree f_1 f_2 (BNode v_1 v_2 v_3) = f_2 v_1 (foldBTree f_1 f_2 v_2) (foldBTree f_1 f_2 v_3)"
genFoldFunctionLine :: String -> Int -> (Int, GADTConstructor) -> String
genFoldFunctionLine funcName len (n, constr@(constrName, _, _, needFolds)) =
    printf "%s %s (%s %s) = %s %s"
        funcName
        (genFunctions len)
        constrName
        (genVariables $ length needFolds)
        fnName
        (join " " $ map (toGens' funcName (genFunctions len)) $ zip parts [1..length parts])
        --(join " " $ map genVarOrFoldCall (zip [1..length needFolds] needFolds))
    where
        fnName = genFn n
        parts = conParts constr
        genVarOrFoldCall :: (Int, Bool) -> String
        genVarOrFoldCall (n, shouldFold) =
            if shouldFold
            then printf "(%s %s v_%d)" funcName (genFunctions len) n
            else genVar n

-- Simplifies a complex AST for a GADT into a simpler, easier to use GADT representation
-- Refer to the GADT type synonym for more information.
--
-- Example:
--   Given the Haskell Src Ext for BTree:
--     simplifyGADT AST(BTree)
--   Returns:
--     ("BTree", AST(BTreeHead), [GADTConstructor(BLeaf), GADTConstructor(BNode)])
simplifyGADT :: Decl SrcSpanInfo -> GADT
simplifyGADT (GDataDecl _ _ _ gadtHead _ constructors _) =
    (gadtName, gadtHead, map (simplifyGADTConstructor gadtName) constructors)
        where gadtName = getHeadName gadtHead

-- Simplifies a complex AST for a GADT data constructor into a simpler, easier to use constructor representation.
-- Refer to the GADTConstructor type synonym for more information.
--
-- Example:
--   Given the Haskell Src Ext for BNode:
--     simplifyGADTConstructor "BTree" AST(BNode)
--   Returns:
--     ("BNode", AST(BNodeType), ["b", "a"], [False, True, True])
simplifyGADTConstructor :: String -> GadtDecl SrcSpanInfo -> GADTConstructor
simplifyGADTConstructor gadtName (GadtDecl _ constrName _ constrType) = (getFromName constrName, constrType, getTypeVariables constrType, shouldFold gadtName constrType)

-- =======================================================================================
-- |                               Abstract Syntax Getters                               |
-- =======================================================================================

-- Generates a list of the type variables in a declared Type.
-- Example:
--   Given a Type representing:
--      a -> (b -> [(c, d)] -> Int) -> Expr a d
--   returns:
--      ["a", "b", "c", "d"]
getTypeVariables :: Type l -> [String]
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
getTypeVariablesHead :: DeclHead l -> [String]
getTypeVariablesHead gadtHead = nub $ getTypeVariablesHead' gadtHead
getTypeVariablesHead' (DHApp _ x1 x2) = getTypeVariablesHead' x1 ++ [getFromTyVarBind x2]
getTypeVariablesHead' (DHead _ _) = []

-- Extracts the string name of a data declaration
-- Example:
--   Given a DeclHead representing:
--     data Expr a b = ...
--   Returns: "Expr"
getHeadName :: DeclHead l -> String
getHeadName (DHApp _ x _) = getHeadName x
getHeadName (DHead _ x)   = getFromName x

-- Extracts the string representation of a type variable (TyVarBind) out of its abstract syntax representation
getFromTyVarBind :: TyVarBind l -> String
getFromTyVarBind (UnkindedVar _ name) = getFromName name
getFromTyVarBind (KindedVar _ name _) = getFromName name

-- Extracts the string representation of a qualified name (QName) out of its abstract syntax representation
getFromQName :: QName l -> String
getFromQName (Qual _ _ name) = getFromName name
getFromQName (UnQual _ name) = getFromName name
getFromQName (Special _ _)   = "" --We don't care about special constructors

-- Extracts the string representation of an identifier (Name) out of its abstract syntax representation
getFromName :: Name l -> String
getFromName (Ident _ name) = name
getFromName (Symbol _ name) = name

-- Placeholder function that returns the first abstract syntax declaration in a module.
-- Currently being used to retrieve a GADT from a file where the GADT is the first declared item in the file.
separate (Module _ _ _ _ [x]) = x

-- Given a GADT name and a AST for a GADT data constructor Type
-- recursively finds all constructor variables and determines if they will need to be
-- folded when generating the Fold function by seeing if the
-- constructor variable's "name" is the same as the GADT name
--
-- Example:
--   Given the BNode Type:
--     shouldFold "BTree" AST(BNodeType)
--   Returns:
--     [False, True, True]'
shouldFold :: String -> Type l -> [Bool]
shouldFold gadtName constrType = safeInit $ shouldFold' gadtName constrType   -- we use safeInit because we want to always throw away the last value in the list
shouldFold' gadtName constrType = case constrType of                          -- as it is always the GADT type and should not be considered when generating a list
    TyFun _ t1 t2   -> shouldFold' gadtName t1 ++ shouldFold' gadtName t2     -- of constructor variables.
    TyCon _ name    -> [getFromQName name == gadtName]
    TyApp _ t1 t2   -> shouldFoldApp gadtName t1
    TyVar _ name    -> [False]
    TyParen _ t1    -> [False]
    _               -> []

-- Helper function for shouldFold. Recursively calls itself until it finds the Type Constructor declaration (TyCon)
-- in a type so that it can compare the GADT name to the TyCon name. If they are the same, this function will return
-- a list of [True]. Otherwise, it will return a list of [False].
--
-- Example:
--   Given that shouldFold is working on the AST(BNodeType): b -> BTree a b -> BTree a b -> BTree a b
--   This function will eventually receive one of the BTree a b ASTs.
--   Thus, given:
--     shouldFoldApp "BTree" AST(BTreeABType)
--       where AST(BTreeABType) is in the form:
--         (TyApp _
--            (TyApp _
--               (TyCon _ "BTree")
--               (TyVar _ "a")
--            )
--            (TyVar _ "b")
--         )
--   Returns:
--     [True]
shouldFoldApp :: String -> Type l -> [Bool]
shouldFoldApp gadtName (TyApp _ t1 t2) = shouldFoldApp gadtName t1 ++ shouldFoldApp gadtName t2
shouldFoldApp gadtName (TyCon _ name) = [getFromQName name == gadtName]
shouldFoldApp gadtName _ = []

-- =======================================================================================
-- |                              Abstract Syntax Modifiers                              |
-- =======================================================================================

-- Changes the identifier in a data declaration head to be "f".
-- We do this so that we can easily reuse the AST for a Data declaration to pretty print it.
-- Example:
--   Given the AST representing the head: data BTree a b =
--     convertHead AST(BTreeHead)
--   Returns:
--     AST(FHead), where FHead: data f a b = ...
--
-- This means that if we use prettyPrint on AST(FHead), it would print "f a b"
convertHead :: DeclHead l -> DeclHead l
convertHead (DHApp l x1 x2) = DHApp l (convertHead x1) x2
convertHead (DHead l (Ident l2 name)) = DHead l (Ident l2 "f")

-- Changes the identifer in Type Application to "f" if the provided "name"
-- is the same as the Type Constructor's identifier
-- Example:
--   Given the AST for BNode: a -> BTree a b -> BTree a b -> BTree a b
--     convert "BTree" AST(BNode)
--   Returns:
--     AST representing: a -> f a b -> f a b -> f a b
--
-- This means that if we use prettyPrint, it would print "a -> f a b -> f a b -> f a b"
convert :: String -> Type l -> Type l
convert name (TyFun l t1 t2) = TyFun l (convert name t1) (convert name t2)
convert name (TyApp l t1 t2) = TyApp l (convert name t1) (convert name t2)
convert name (TyCon l qname) = TyCon l (convertQ name qname)
convert name x = x

-- Changes the identifier of a Unqualified Name to "f" if the provided "name"
-- is the same as the QName's identifier
convertQ :: String -> QName l -> QName l
convertQ name (UnQual l (Ident l2 ident)) = if name == ident
                                         then UnQual l (Ident l2 "f")
                                         else UnQual l (Ident l2 ident)
convertQ name x = x

-- =======================================================================================
-- |                                  General Utilities                                  |
-- =======================================================================================

-- Creates a string of "f_#", where # is 'n'
genFn :: Int -> String
genFn n = printf "f_%d" n

-- Creates a string of "v_#", where # is 'n'
genVar :: Int -> String
genVar n = printf "v_%d" n

-- Creates a string of "f_1 f_2 f_3 .. f_n", given 'n'
genFunctions :: Int -> String
genFunctions len = join " " $ map genFn [1..len]

-- Creates a string of "v_1 v_2 v_3 .. v_n", given 'n'
genVariables :: Int -> String
genVariables len = join " " $ map genVar [1..len]

-- Similar to Javascript's .join(string) function, concats all items in a list
-- with a separator between each item.
join :: String -> [String] -> String
join sep [] = []
join sep [x] = x
join sep (x:xs) = x ++ sep ++ (join sep xs)

-- Same as the join function, except it also places the separator after the last item as well.
joinR :: String -> [String] -> String
joinR sep [] = []
joinR sep xs = join sep xs ++ sep

-- A safe version of Prelude.init. Does not throw errors on []
-- Returns the entire list, minus the first element.
safeInit [] = []
safeInit xs = init xs

-- =======================================================================================
-- |             Code Generated By Program, Placed Here To Test Compilability            |
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
        Foo :: a -> (b -> Boo a b) -> ((Boo a b -> a) -> [c]) -> Boo a a
        Joe :: a -> Boo (b -> Boo a b) Int -> Boo a a
        Lin :: a -> (b -> Int) -> Boo a b

foldBoo ::
  (forall a b c. a -> (b -> f a b) -> ((f a b -> a) -> [c]) -> f a a) ->
  (forall a b. a -> f (b -> Boo a b) Int -> f a a) ->
  (forall a b. a -> (b -> Int) -> f a b) ->
  forall a b. Boo a b -> f a b
foldBoo f_1 f_2 f_3 (Foo v_1 v_2 v_3) = f_1 v_1 ((foldBoo f_1 f_2 f_3) . v_2) (\v_3_1 -> v_3 (\v_3_1_1 -> v_3_1 (foldBoo f_1 f_2 f_3 v_3_1_1)))
foldBoo f_1 f_2 f_3 (Joe v_1 v_2) = f_2 v_1 (foldBoo f_1 f_2 f_3 v_2)
foldBoo f_1 f_2 f_3 (Lin v_1 v_2) = f_3 v_1 v_2

-- ============================
{-data Boo a b where
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

-}
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


-- =======================================================================================
-- |             Code left over from experimentation. Remove at a later date.            |
-- =======================================================================================

{-
showLevels :: GADT -> String
showLevels (gadtName, gadtHead, constr : xs) = levels constr

levels :: GADTConstructor -> String
levels (constrName, constrType, typeVars, replacementList) =
    join "\n" $ map (\(n, t) -> printf "%d: %s" n (prettyPrint t)) (getLevels 0 constrType)

getLevelZero :: Type SrcSpanInfo -> [(Int, Type SrcSpanInfo)]
getLevelZero (TyFun l t1 t2) = getLevelZero t1 ++ getLevelZero t2
getLevelZero t = [(0, t)]

getLevels :: Int -> Type SrcSpanInfo -> [(Int, Type SrcSpanInfo)]
getLevels n (TyFun l t1 t2) = getLevels n t1 ++ getLevels n t2
getLevels n (TyParen l t@(TyFun _ _ _)) = getLevels (n + 1) t
getLevels n (TyParen l t)   = getLevels n t -- [(n + 1, t)]
getLevels n t               = [(n, t)]
-}


