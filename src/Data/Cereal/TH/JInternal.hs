{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Data.Cereal.TH.JInternal where

import Data.Serialize
import Prelude
import Data.Maybe (isJust)
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Lib
import Data.Word
import Data.Foldable
import Data.Traversable
import Control.Monad
import Data.Functor
import Data.Text (Text)
import           TH.ReifySimple
import qualified Data.ByteString        as S
import           Data.Maybe (fromMaybe, isJust, mapMaybe)
import           Data.List (isSuffixOf)

requiredSuffix :: String
requiredSuffix = "TH"

makeCerealCustom :: Name -> Name -> Q [Dec]
makeCerealCustom name hv = makeCerealInternal (Just hv) name

makeCerealIdentity :: Name -> Q [Dec]
makeCerealIdentity = makeCerealInternal (Just $ mkName "Identity")

makeCereal :: Name -> Q [Dec]
makeCereal = makeCerealInternal Nothing

makeCerealInternal :: Maybe Name -> Name -> Q [Dec]
makeCerealInternal higherKindType name = do
  info <- reifyDatatype name
  case info of
    DatatypeInfo { datatypeName
                 , datatypeVars -- Not supported yet
                 , datatypeCons
                 } -> do
      newDatatypeName <- getNameSuffixRemoved' Nothing datatypeName requiredSuffix
      let
        constrNameStr constructor =
          case (constructorName constructor) of
            Name (OccName occName) _ -> occName
        instanceType = case higherKindType of
                        Just v -> AppT (ConT ''Serialize) $ AppT (ConT newDatatypeName) (ConT v)
                        _ -> AppT (ConT ''Serialize) $ ConT newDatatypeName
        funcDecl =
          [ getDecl, putDecl ]
        putDecl = funD 'put (datatypeCons <&> putClause)
        getDecl =
          let
            qSpecificConstructorGetsBindingsAndNames :: Q [(Dec, Name, String)]
            qSpecificConstructorGetsBindingsAndNames =
              for datatypeCons $ \constructor@(ConstructorInfo { constructorName, constructorVariant, constructorFields }) ->
                do
                  newConstructorName <- getNameSuffixRemoved (Just constructorVariant) constructorName requiredSuffix
                  let
                    constrName = nameBase newConstructorName
                  name <- newName $ "get_" <> constrName
                  decl <- valD (varP name) (getBodyForConstructor constructor) []
                  pure (decl, name, constrName)
            getBody = do
              constrNameBinding <- newName "constructor"
              specificConstructorGetsBindingsAndNames <- qSpecificConstructorGetsBindingsAndNames
              let
                bindCnstrName = bindS (varP constrNameBinding) (appTypeE (varE 'get) (conT ''Text))
                matches :: [Q Match]
                matches =
                  specificConstructorGetsBindingsAndNames <&>
                    (\(_, binding, constrName) ->
                      match (litP (stringL constrName)) (normalB (varE binding)) [])
                catchAll :: Q Match
                catchAll = do
                  xName <- newName "x"
                  match
                    (varP xName)
                    (normalB
                      (appE
                        (varE 'fail)
                        (infixApp
                          (infixE
                            (Just (litE (stringL "Unexpected Tag: ")))
                            (varE '(<>))
                            (Just (appE (varE 'show) (varE xName))))
                          (varE '(<>))
                          (infixE
                            (Just (litE (stringL " for type: ")))
                            (varE '(<>))
                            (Just (appE (varE 'show) (litE (stringL $ nameBase name)))))
                        )
                      )
                    ) []
                branchBasedOnConstr =
                  noBindS $
                  caseE (varE constrNameBinding) (matches <> [catchAll])
                bytesToRead = mkName "bytesToRead"
                lenRead = bindS (varP bytesToRead) (varE 'getWord32be)
                body = normalB $ doE [bindCnstrName, branchBasedOnConstr]
                declrs = specificConstructorGetsBindingsAndNames <&> (\(d, _, _) -> pure d)
              valD (varP 'get) body declrs
          in getBody
        getBodyForConstructor (ConstructorInfo { constructorName, constructorVariant, constructorFields }) = do
          newConstructorName <- getNameSuffixRemoved (Just constructorVariant) constructorName requiredSuffix
          attrBindingNames <-
            replicateM (length constructorFields) (newName "attr")
          let fields =  filter (\(_,ty,_) -> notDeprecated ty) $ zipWith3 (\ty tagNum attrBindingName -> (attrBindingName,ty,tagNum)) constructorFields ([0..] :: [Int]) attrBindingNames
              newAttrBindingNames = (\(attrBindingName,_,_) ->  attrBindingName) <$> fields
          let
            bindings = fields <&> (\(newAttrBindingName,ty,tagNum) -> if isMaybeType ty then bindS (varP newAttrBindingName) [|getNestedWithTagNumMaybe tagNum get|] else bindS (varP newAttrBindingName) [|getNestedWithTagNum tagNum get|])
            pureValue = foldl (\app v -> appE app (varE v)) (conE newConstructorName) newAttrBindingNames
            returnStmt = noBindS $ appE (varE 'pure) pureValue
            doBlockBody = bindings <> [returnStmt]
          normalB $ doE doBlockBody
        putClause datatypeCon@(ConstructorInfo { constructorName, constructorVariant, constructorFields }) = do
          newConstructorName <- getNameSuffixRemoved (Just constructorVariant) constructorName requiredSuffix
          attrBindingNames <-
            replicateM (length constructorFields) (newName "attr")
          let fields =  filter (\(_,ty,_) -> notDeprecated ty) $ zipWith3 (\ty tagNum attrBindingName -> (attrBindingName,ty,tagNum)) constructorFields [0..] attrBindingNames
              newAttrBindingNames = (\(attrBindingName,_,_) ->  attrBindingName) <$> fields
          case constructorVariant of
            NormalConstructor ->
              let
                bindings = varP <$> newAttrBindingNames
              in
                clause [conP newConstructorName bindings ] (putBody newConstructorName fields) []
            RecordConstructor names ->
              let
                namesWithType = zip names constructorFields
                notDeprecatedNames = fst <$> filter (\(name,ty) -> notDeprecated ty) namesWithType
                bindings =
                  zip notDeprecatedNames (varP <$> newAttrBindingNames)
                    <&> (\(name, qPat) -> qPat <&> (name,))
              in clause [recP newConstructorName bindings ] (putBody newConstructorName fields) []
        putBody :: Name -> [(Name,Type,Int)] -> Q Body
        putBody consName fields =
          let
            putConstr =
              noBindS $ appE (varE 'put) (sigE (litE (stringL (nameBase consName))) (conT ''Text))
            putStmts =
              fields <&>
                (\(name,ty,i) -> if isMaybeType ty then noBindS [| putNestedWithTagNumMaybe i $(varE name) |] else noBindS [| putNestedWithTagNum i (put $(varE name)) |])
          in
            normalB $ (doE (putConstr : putStmts))
      pure <$>
        instanceD (pure []) (pure instanceType) (funcDecl)

isMaybeType :: Type -> Bool
isMaybeType (AppT ty ((AppT (ConT con) _))) = (nameBase con == "Maybe") || (case ty of
                                                                              ConT con2 ->  nameBase con2 == "Maybe"
                                                                              _         ->  False)
isMaybeType (AppT (ConT con) _) =  (nameBase con == "Maybe")
isMaybeType _ = False

notDeprecated :: Type -> Bool
notDeprecated (AppT ty ((AppT (ConT con) _))) = (not (nameBase con == "Deprecated")) && (case ty of
                                                                                          ConT con2 ->  not (nameBase con2 == "Deprecated")
                                                                                          _         ->  True)
notDeprecated (AppT (ConT con) _) = not (nameBase con == "Deprecated")
notDeprecated _ = True

{-# INLINE putNestedWithTagNum #-}
putNestedWithTagNum :: Word32 -> Put -> Put
putNestedWithTagNum tagNum putVal = do
    let bs = runPut putVal
    putWord32be tagNum
    putWord32be $ toEnum (S.length bs)
    putByteString bs

{-# INLINE putNestedWithTagNumMaybe #-}
putNestedWithTagNumMaybe :: Serialize a => Word32 -> Maybe a -> Put
putNestedWithTagNumMaybe tagNum (Just val) = putNestedWithTagNum tagNum (put val)
putNestedWithTagNumMaybe _ Nothing = putByteString (S.empty)  

getNameSuffixRemoved :: Maybe ConstructorVariant -> Name -> String -> Q Name
getNameSuffixRemoved consVar name suffix
  | let dtName = nameBase name, isSuffixOf suffix dtName = let lookupName = (take (length dtName - length suffix) dtName) 
      in lookupValueName lookupName >>= \case
        Just name'  -> return name'
        _           -> case consVar of
                        (Just (RecordConstructor _)) -> fail $ "Unable to look up data type " ++ lookupName ++ ". Possible solution is to make data type with suffix " ++ requiredSuffix ++ " removed."
                        _                            -> return $ name
  | otherwise = case consVar of 
                  (Just (RecordConstructor _)) -> fail $ requiredSuffix ++ " suffix not found for RecordConstructor Variant"
                  _                            -> return $ name

getNameSuffixRemoved' :: Maybe ConstructorVariant -> Name -> String -> Q Name
getNameSuffixRemoved' consVar name suffix
  | let dtName = nameBase name, isSuffixOf suffix dtName = let lookupName = (take (length dtName - length suffix) dtName) 
      in lookupTypeName lookupName >>= \case
        Just name'  -> return name'
        _           -> case consVar of
                        (Just (RecordConstructor _)) -> fail $ "Unable to look up data type " ++ lookupName ++ ". Possible solution is to make data type with suffix " ++ requiredSuffix ++ " removed."
                        _                            -> return $ name
  | otherwise = case consVar of 
                  (Just (RecordConstructor _)) -> fail $ requiredSuffix ++ " suffix not found for RecordConstructor Variant"
                  _                            -> return $ name

makeDataTypeDeriving :: Name -> [String] -> Q [Dec]
makeDataTypeDeriving name dcs = do
    info <- reify name
    case info of
       TyConI (DataD ctx dtName tyVBs mkind ((RecC recName varBangTypes):[]) _) -> do 
           dtName'  <- removeSuffix dtName requiredSuffix
           recName' <- removeSuffix recName requiredSuffix
           return $ (DataD ctx dtName' tyVBs mkind ((RecC recName' (removeDeprecated varBangTypes)):[]) [DerivClause Nothing (map (ConT . mkName) dcs)]):[]
       _                                                -> return []
    where 
        removeDeprecated varBangTypes = [(nm,bg,ty) | (nm,bg,ty) <- varBangTypes, notDeprecated ty]

removeSuffix :: Name -> String -> Q Name
removeSuffix name1 suffix
    | let nameStr = nameBase name1, isSuffixOf suffix nameStr = return $ mkName $ take (length nameStr - length suffix) nameStr
    | otherwise = fail $ requiredSuffix ++ " suffix is not present on the type or constructer"