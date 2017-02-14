{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase #-}
-- | Anastasia: ANnotated ASTs (Automated, SImple, Awesome).
module Language.Annotated (makeAnnotationLenses, Annotated (..)) where


import Language.Haskell.TH
import Lens.Simple
import Control.Monad
import Data.Foldable (foldl')

-- | Generates lenses to the first type parameter of each
-- datatype. The parameter should be in the first data parameter of
-- constructors. Constructors that don't qualify for that are ignored
-- and would raise an error at run-time. Currently the constructors of
-- GADTs are not supported.
makeAnnotationLenses :: [Name] -> Q [Dec]
makeAnnotationLenses = liftM concat . mapM makeAnnotationLenses'

makeAnnotationLenses' :: Name -> Q [Dec]
makeAnnotationLenses' name =
  do info <- reify name
     case info of
       TyConI dec -> case dec of
         DataD _ _ typeVars _ constructors _ -> makeAnnotationDec name typeVars constructors
         _ -> myError name "not a data-type"
       _   -> myError name "not a type name"

myError :: Name -> String -> Q [Dec]
myError name reason = reportError ("Can't generate an annotation lens for " ++ show name ++ ": " ++ reason) >> return []

makeAnnotationDec :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
makeAnnotationDec name [tyVar] ctors =
  do let at = varT (getTVName tyVar)
     let tyT = conT name
     d <- instanceD (cxt []) [t|Annotated $tyT|] [at >>= (`makeAnnotationLens` ctors)]
     return [d]
makeAnnotationDec name _ _ = myError name  "the data-type is required to have one type parameter (the annotation)"

makeAnnotationLens :: Type -> [Con] -> Q Dec
makeAnnotationLens aty ctors =
  let getterName = mkName "getter"
      setterName = mkName "setter"
  in do (ClassOpI annName _ _ ) <- reify (mkName "ann")
        funD annName
          [clause [] (normalB $ appE (appE (varE $ mkName "lens") (varE getterName)) (varE setterName))
                  [funD getterName [getter]
                  ,funD setterName [setter]]]
  where getter =
          let x = mkName "x"
          in do matchers <- liftM concat $  mapM getConMatch ctors
                clause [varP x] (normalB $ caseE (varE x) $ map return matchers) []
        getConMatch (NormalC n tys) = case tys of
          -- the first parameter of a constructor has the annotation type (`aty`)
          ((_,ty):rest) | ty == aty ->
                          do annotName <- newName "a"
                             m <- match (conP n $ (varP annotName):(map (const wildP) rest ))
                                      (normalB (varE annotName)) []
                             return [m]
                                      
          _ ->
            do reportWarning ("Constructor " ++ show n ++ " does not have an annotation parameter; attempting to invoke the lens on it will result in a run-time pattern-match failure")
               return []
        getConMatch _ =
          do reportError "Currently annotation lenses only work for regular constructors"
             return []
             
        setter = let x = mkName "x"
                     a = mkName "a"
                 in do matchers <- liftM concat $ mapM (setConMatch a) ctors
                       clause [varP x, varP a] (normalB $ caseE (varE x) $ map return matchers) []
        setConMatch an (NormalC n tys) = case tys of
          -- the first parameter of a constructor has the annotation type (`aty`)
          ((_,ty):rest) | ty == aty ->
                          do restNames <- mapM (const $ newName "x") rest
                             m <- match (conP n $ wildP:(map varP restNames))
                                  (normalB $
                                   foldl' appE
                                   (appE (conE n) (varE an)) $ map varE restNames) []
                             return [m]
                                      
          _ -> return []
        setConMatch _ _ =
          do reportError "Currently annotation lenses only work for regular constructors"
             return []
  
getTVName :: TyVarBndr -> Name
getTVName (PlainTV name) = name
getTVName (KindedTV name _) = name

-- | A class for annotated ASTs. Allows reading/writing the annotation
-- field of constructors.
class Annotated x where
  ann :: Lens' (x a) a

