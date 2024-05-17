--  File     : Blocks.hs
--  Author   : Ashutosh Rishi Ranjan
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE TupleSections #-}

module LLVM ( llvmMapBinop, llvmMapUnop
              ) where

import           AST
-- import           Debug.Trace
-- import           ASTShow
-- import           BinaryFactory
-- import           Codegen
-- import           Resources
-- import           Config                          (wordSize, wordSizeBytes)
-- import           Util                            (maybeNth, lift2,
--                                                   (|||), (&&&))
-- import           Snippets
-- import           Control.Monad                   as M
-- import           Control.Monad.Extra             (ifM)
-- import           Control.Monad.Trans             (lift, liftIO)
-- import           Control.Monad.Trans.Class
-- import           Control.Monad.Trans.Except
-- import           Control.Monad.Trans.State
-- import           Data.Char                       (ord)
-- import           Data.Foldable
-- import           Data.List                       as List
-- import           Data.List.Predicate
import           Data.Map                        as Map
-- import qualified Data.Set                        as Set
-- import           Data.String
-- import           Data.Functor                    ((<&>))
-- import           Data.Word                       (Word32)
-- import           Data.Maybe                      (fromMaybe, isJust, catMaybes, isNothing, maybeToList)
-- import           Flow                            ((|>))
-- -- import qualified LLVM.AST                        as LLVMAST
-- -- import qualified LLVM.AST.Constant               as C
-- -- import qualified LLVM.AST.Float                  as F
-- -- import qualified LLVM.AST.FloatingPointPredicate as FP
-- -- import qualified LLVM.AST.Global                 as G
-- -- import           LLVM.AST.Instruction
-- -- import qualified LLVM.AST.IntegerPredicate       as IP
-- -- import           LLVM.AST.Operand                hiding (PointerType, operands)
-- -- import           LLVM.AST.Type
-- -- import           LLVM.AST.Typed
-- -- import qualified LLVM.AST.Attribute              as A (FunctionAttribute(..))
-- -- import           LLVM.Pretty                     (ppllvm)

-- import qualified Data.ByteString                 as BS
-- import qualified Data.ByteString.Char8           as B8
-- import qualified Data.ByteString.Lazy            as BL
-- import qualified Data.ByteString.Short           as BSS
-- import           Options                         (LogSelection (Blocks))
-- import           Unsafe.Coerce
-- import           System.FilePath
-- import qualified UnivSet
-- import Control.Exception (assert)
-- import Data.Set (Set)

----------------------------------------------------------------------------
-- Instruction maps                                                       --
----------------------------------------------------------------------------


-- | A map of arithmetic binary operations supported through LLVM to
-- their Codegen module counterpart.
llvmMapBinop :: Map String
                (TypeFamily, TypeRepresentation -> TypeRepresentation)
llvmMapBinop =
    Map.fromList [
            -- Integer arithmetic
            ("add",  (IntFamily, id)),
            ("sub",  (IntFamily, id)),
            ("mul",  (IntFamily, id)),
            ("udiv", (IntFamily, id)),
            ("sdiv", (IntFamily, id)),
            ("urem", (IntFamily, id)),
            ("srem", (IntFamily, id)),
            -- Integer comparisions
            ("icmp_eq",  (IntFamily, const $ Bits 1)),
            ("icmp_ne",  (IntFamily, const $ Bits 1)),
            ("icmp_ugt", (IntFamily, const $ Bits 1)),
            ("icmp_uge", (IntFamily, const $ Bits 1)),
            ("icmp_ult", (IntFamily, const $ Bits 1)),
            ("icmp_ule", (IntFamily, const $ Bits 1)),
            ("icmp_sgt", (IntFamily, const $ Bits 1)),
            ("icmp_sge", (IntFamily, const $ Bits 1)),
            ("icmp_slt", (IntFamily, const $ Bits 1)),
            ("icmp_sle", (IntFamily, const $ Bits 1)),
            -- Bitwise operations
            ("shl",  (IntFamily, id)),
            ("lshr", (IntFamily, id)),
            ("ashr", (IntFamily, id)),
            ("or",   (IntFamily, id)),
            ("and",  (IntFamily, id)),
            ("xor",  (IntFamily, id)),

            -- Floating point arithmetic
            ("fadd", (FloatFamily, id)),
            ("fsub", (FloatFamily, id)),
            ("fmul", (FloatFamily, id)),
            ("fdiv", (FloatFamily, id)),
            ("frem", (FloatFamily, id)),
            -- Floating point comparisions
            ("fcmp_eq",  (FloatFamily, const $ Bits 1)),
            ("fcmp_ne",  (FloatFamily, const $ Bits 1)),
            ("fcmp_slt", (FloatFamily, const $ Bits 1)),
            ("fcmp_sle", (FloatFamily, const $ Bits 1)),
            ("fcmp_sgt", (FloatFamily, const $ Bits 1)),
            ("fcmp_sge", (FloatFamily, const $ Bits 1))
           ]

-- | A map of unary llvm operations wrapped in the 'Codegen' module.
llvmMapUnop :: Map String (TypeFamily, TypeFamily)
llvmMapUnop =
    Map.fromList [
            ("uitofp", (IntFamily, FloatFamily)),
            ("sitofp", (IntFamily, FloatFamily)),
            ("fptoui", (FloatFamily, IntFamily)),
            ("fptosi", (FloatFamily, IntFamily))
           ]
