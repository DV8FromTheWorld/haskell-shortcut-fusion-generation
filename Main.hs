{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Language.Haskell.Exts hiding (layout, Var)
import Text.Show.Pretty (ppShow)
import System.Environment
import Data.List (nub)

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
                    gadtName = getGadtName gDataDecl
                    parseResult = ppShow gDataDecl
                    allDecls = getDecls gDataDecl
                    firstDecl = head allDecls
                    gadt = simplifyGADT gDataDecl
                --writeFile ofile parseResult
                --putStrLn parseResult
                putStrLn $ prettyPrint gDataDecl ++ "\n\n"
                putStrLn $ generateFold gadt
                putStrLn "Generation successful\n"
                
            _ -> putStrLn "Wrong number of args. Example: Main infile outfile"
         --s <- readFile ifile
         -- writeFile ofile (genStuff s)
         --putStrLn $ head (separateLines s)
         --
         
generateFold (gadtName, gadtHead, constructors) = 
    funcName ++ " :: "
    ++ (joinR " ->\n  " $ map (generateTypeSignature gadtName) constructors)
    ++ "forall a b. " ++ (prettyPrint gadtHead) ++ " -> f a b\n"
    ++ (join "\n" $ map (generateFoldLine funcName (length constructors)) $ zip [1..length constructors] constructors)
        where funcName = "fold" ++ gadtName
    
generateTypeSignature gadtName (_, constrType, typeVariables, _) = 
    "("
    ++ forallSection
    ++ (prettyPrint $ convert gadtName constrType)
    ++ ")"
        where forallSection = if length typeVariables /= 0
                              then "forall " ++ (join " " typeVariables) ++ ". "
                              else ""
            
generateFoldLine funcName len (n, constr) = funcName ++ " " ++ (joinR " " ["f_" ++ show i | i <- [1..len]]) ++ getThing funcName len n constr
getThing funcName len n (name, _, _, needFolds) = 
                                "(" ++ name ++ " " ++ (generateVariables $ length needFolds) ++ ") = " ++ genFn n ++ " "
                                ++ (join " " $ map (\(n, b) -> if not b then genVar n else "(" ++ funcName ++ " " ++ generateFunctions len ++ " v_" ++ show n ++ ")") (zip [1..length needFolds] needFolds))
 
generateFunctions len = join " " $ map genFn [1..len]
generateVariables len = join " " $ map genVar [1..len]
genFn n = "f_" ++ show n
genVar n = "v_" ++ show n

join sep [] = []
join sep [x] = x
join sep (x:xs) = x ++ sep ++ (join sep xs)

joinR sep [] = []
joinR sep xs = join sep xs ++ sep

simplifyGADT :: Decl SrcSpanInfo -> GADT
simplifyGADT (GDataDecl _ _ _ gadtHead _ constructors _) = 
    (gadtName, gadtHead, map (simplifyGADTConstructor gadtName) constructors)
        where gadtName = getHeadName gadtHead

simplifyGADTConstructor :: String -> GadtDecl SrcSpanInfo -> GADTConstructor
simplifyGADTConstructor gadtName (GadtDecl _ constrName _ constrType) = (getFromName constrName, constrType, getTypeVariables constrType, shouldReplace gadtName constrType)

getTypeVariables decType = nub $ getTypeVariables' decType
getTypeVariables' (TyFun l t1 t2) = getTypeVariables t1 ++ getTypeVariables t2
getTypeVariables' (TyApp l t1 t2) = getTypeVariables t1 ++ getTypeVariables t2
getTypeVariables' (TyVar l name) = [getFromName name]
getTypeVariables' _ = []


shouldReplace gadtName constrType = safeInit $ shouldReplace' gadtName constrType

safeInit [] = []
safeInit xs = init xs
                            
shouldReplace' gadtName (TyFun l t1 t2) = shouldReplace' gadtName t1 ++ shouldReplace' gadtName t2
shouldReplace' gadtName (TyCon l name) = [getFromQName name == gadtName]
shouldReplace' gadtName (TyApp l t1 t2) = handleApp gadtName t1
shouldReplace' gadtName (TyVar l name) = [False]
shouldReplace' _ _ = []

--shouldReplace gadtName (TyCon l name) = [getFromQName name == gadtName]
--shouldReplace _ _ = []

handleApp gadtName (TyApp l t1 t2) = handleApp gadtName t1 ++ handleApp gadtName t2
handleApp gadtName (TyCon l name) = [getFromQName name == gadtName]
handleApp gadtName _ = []



separate (Module _ _ _ _ [x]) = x
getGadtName (GDataDecl _ _ _ x _ _ _) = getHeadName x
getDecls (GDataDecl _ _ _ _ _ x _) = x

getHeadName (DHApp _ x _) = getHeadName x
getHeadName (DHead _ x)   = getFromName x

getFromQName (Qual _ _ name) = getFromName name
getFromQName (UnQual _ name) = getFromName name
getFromQName (Special _ _) = "" --We don't care about special constructors

getFromName (Ident _ name) = name
getFromName (Symbol _ name) = name

getGadtDeclDesc (GadtDecl _ name _ decType) = getFromName name
                                        ++ " :: "
                                        ++ (prettyPrint $ convert "Expr" decType)
                                        
getDecType (GadtDecl _ _ _ decType) = decType
                                        
getAllDesc name decls = map (prettyPrint . (convert name) . getDecType) decls

convert name (TyFun l t1 t2) = TyFun l (convert name t1) (convert name t2)
convert name (TyApp l t1 t2) = TyApp l (convert name t1) (convert name t2)
convert name (TyCon l qname) = TyCon l (convertQ name qname)
convert name x = x

convertQ name (UnQual l (Ident l2 ident)) = if name == ident
                                         then UnQual l (Ident l2 "f")
                                         else UnQual l (Ident l2 ident)
convertQ name x = x

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
                    
-- == Tests ==
data Expr a b where
    Var :: a -> Expr a b
    IConst :: Int -> Expr a Int
    RConst :: Float -> Expr a Float
    PProd :: Expr a b -> Expr a b -> Expr a b
    SIMul :: Expr a b -> Int -> Expr a b
    SRMul :: Expr a b -> Float -> Expr a Float

    
-- ====== Generated from above GADT
foldExpr :: (forall a b. a -> f a b) ->
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




