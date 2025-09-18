--  File     : BinaryFactory.hs
--  Author   : Ashutosh Rishi Ranjan
--  Purpose  : Deriving AST Types to be Binary instances
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module BinaryFactory
       where

import           AST
import           Control.Monad
import           Crypto.Hash
import           Data.Binary          as B
import           Config               (magicVersion)
import           UnivSet
import qualified Data.ByteString.Lazy as BL
import qualified Data.List            as List
import           Text.Parsec.Pos      (SourcePos, newPos, sourceColumn,
                                       sourceLine, sourceName)
import           Util
import Options (LogSelection(Builder))
import Data.List


-- * Self Deriving instances
instance Binary Visibility
instance Binary Determinism
instance Binary StringDelim
instance Binary BracketStyle
instance Binary Token
instance Binary SourceInfo
instance Binary t => Binary (Placed t)
instance Binary ArgFlowType
instance Binary ResourceSpec
instance Binary FlowDirection
instance Binary PrimFlow
instance Binary TypeVarName
instance Binary TypeSpec
instance Binary TypeFlow
instance Binary Exp
instance Binary StringVariant
instance Binary GlobalInfo
instance Binary Generator
instance Binary Stmt
instance Binary ProcFunctor
instance Binary ParamInfo
instance Binary Prim
instance Binary PrimVarName
instance Binary PrimArg
instance Binary ProcAnalysis
instance Binary GlobalFlows
instance Binary CallSiteProperty
instance Binary InterestingCallProperty

-- Procedures
instance Binary ProcSpec
instance Binary ProcImpln
instance Binary PrimProto
instance Binary PrimParam
instance Binary ProcBody
instance Binary PrimFork
instance Binary ProcVariant
instance Binary SuperprocSpec
instance Binary ProcDef
instance Binary ProcProto
instance Binary Param
instance Binary ResourceFlowSpec
-- Module implementation
instance Binary ModuleImplementation
instance Binary ResourceImpln
instance Binary TypeRepresentation
instance Binary ImportSpec
-- Module
instance Binary Module
instance Binary PubProcInfo
instance Binary ModuleInterface
instance Binary Pragma

instance Binary ProcModifiers
instance Binary Inlining
instance Binary Impurity
instance Binary Item
instance Binary TypeProto
instance Binary TypeModifiers
instance Binary TypeImpln
-- * Manual Serialisation

instance Binary EncodedLPVM

instance Binary t => Binary (UnivSet t)
instance Binary SourcePos where
  put pos = do put $ sourceName pos
               put $ sourceLine pos
               put $ sourceColumn pos

  get = liftM3 newPos get get get


-- * Encoding


-- | A Module is encoding by creating an 'EncodedLPVM' type which wraps the
-- Module `m` and all its sub-modules. This type is serialised and prefixed
-- with 4 magic bytes.
encodeModule :: ModSpec -> Compiler BL.ByteString
encodeModule m = do
    let msg = "Unable to get loaded Module for binary encoding."
    -- func to get get a trusted loaded Module from it's spec
    let getm name = trustFromJustM msg $ getLoadedModule name
    descendents <- sameOriginModules m
    mods <- mapM getm (m:descendents)
    let encoded = B.encode $ makeEncodedLPVM mods
    return $ BL.append (BL.pack magicVersion) encoded



-- * Decoding


decodeModule :: [ModSpec] -> BL.ByteString -> Compiler (Either String [Module])
decodeModule required bs = do
    let (magic, rest) = BL.splitAt 4 bs
    logMsg Builder $ "Magic word = " ++ show magic
                     ++ " ; should = " ++ show (BL.pack magicVersion)
    if magic == BL.pack magicVersion
        then do
          logMsg Builder "Magic word matched"
          case B.decodeOrFail rest of
            Left _ -> return $ Left "Error decoding LPVM bytes."
            Right (_, _, lpvm) -> do
                logMsg Builder "B.decodeOrFail worked; decoding."
                Right <$> decodeEncodedLPVM required lpvm
        else do
          logMsg Builder "Magic word mismatched!"
          return $ Left "Invalid Wybe object code or compiler version mismatch."


decodeEncodedLPVM ::  [ModSpec] -> EncodedLPVM -> Compiler [Module]
decodeEncodedLPVM required (EncodedLPVM ms) = do
    logMsg Builder $ "Decoded modules:\n"
                     ++ intercalate ", " (show . modSpec <$> ms)
    if List.all (`elem` specs) required
    then return ms
    else return []
  where
    specs = List.map modSpec ms


-- * Hashing functions

sha1 :: BL.ByteString -> Digest SHA1
sha1 = hashlazy

hashItems :: [Item] -> String
hashItems = show . sha1 . encode

hashInterface :: ModuleInterface -> InterfaceHash
hashInterface = Just . show . sha1 . encode
