{-# OPTIONS -XTupleSections #-}
--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.
module Normalise (normalise, normaliseItem) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Flatten
import Unbranch
import Config (wordSize)


-- |Normalise a list of file items, storing the results in the current module.
normalise :: ([ModSpec] -> Compiler ()) -> [Item] -> Compiler ()
normalise modCompiler items = do
    mapM_ (normaliseItem modCompiler) items
    -- liftIO $ putStrLn "File compiled"
    -- every module imports stdlib
    addImport ["wybe"] (ImportSpec (Just Set.empty) Nothing)
    -- Now generate main proc if needed
    stmts <- getModule stmtDecls 
    unless (List.null stmts)
      $ normaliseItem modCompiler 
            (ProcDecl Public (ProcProto "" [] initResources) 
                          (List.reverse stmts) Nothing)

-- |The resources available at the top level
-- XXX this should be all resources with initial values
initResources :: [ResourceFlowSpec]
-- initResources = [ResourceFlowSpec (ResourceSpec ["wybe"] "io") ParamInOut]
initResources = [ResourceFlowSpec (ResourceSpec ["wybe","io"] "io") ParamInOut]


-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: ([ModSpec] -> Compiler ()) -> Item -> Compiler ()
normaliseItem modCompiler (TypeDecl vis (TypeProto name params) rep items pos) 
  = do
    let rep' = normaliseTypeRepresentation rep
    ty <- addType name (TypeDef (length params) rep' pos) vis
    let eq1 = ProcDecl Public
              (ProcProto "=" [Param "x" ty ParamOut Ordinary,
                              Param "y" ty ParamIn Ordinary] [])
              [Unplaced $
               ForeignCall "llvm" "move" [] [Unplaced $
                                             Var "y" ParamIn Ordinary,
                                             Unplaced $
                                             Var "x" ParamOut Ordinary]]
              Nothing
    let eq2 = ProcDecl Public
              (ProcProto "=" [Param "y" ty ParamIn Ordinary,
                              Param "x" ty ParamOut Ordinary] [])
              [Unplaced $
               ForeignCall "llvm" "move" [] [Unplaced $
                                             Var "y" ParamIn Ordinary,
                                             Unplaced $
                                             Var "x" ParamOut Ordinary]]
              Nothing
    normaliseSubmodule modCompiler name (Just params) vis pos (eq1:eq2:items)
normaliseItem modCompiler (ModuleDecl vis name items pos) = do
    normaliseSubmodule modCompiler name Nothing vis pos items
normaliseItem _ (ImportMods vis modspecs pos) = do
    mapM_ (\spec -> addImport spec (importSpec Nothing vis)) modspecs
normaliseItem _ (ImportItems vis modspec imports pos) = do
    addImport modspec (importSpec (Just imports) vis)
normaliseItem _ (ResourceDecl vis name typ init pos) =
  addSimpleResource name (SimpleResource typ init pos) vis
normaliseItem modCompiler (FuncDecl vis (FnProto name params resources) 
               resulttype result pos) =
  let flowType = Implicit pos
  in  normaliseItem modCompiler
   (ProcDecl
    vis
    (ProcProto name (params ++ [Param "$" resulttype ParamOut flowType]) 
     resources)
    [maybePlace (ProcCall [] "=" Nothing [Unplaced $ Var "$" ParamOut flowType, result])
     pos]
    pos)
normaliseItem _ item@(ProcDecl _ _ _ _) = do
    (item',tmpCtr) <- flattenProcDecl item
    addProc tmpCtr item'
normaliseItem modCompiler (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor modCompiler vis (last modspec) modparams proto pos
normaliseItem _ (StmtDecl stmt pos) = do
    updateModule (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})


normaliseTypeRepresentation :: TypeRepresentation -> TypeRepresentation
normaliseTypeRepresentation "i" = "i" ++ show wordSize
normaliseTypeRepresentation "f" = "i" ++ show wordSize
normaliseTypeRepresentation other = other


normaliseSubmodule :: ([ModSpec] -> Compiler ()) -> Ident -> 
                      Maybe [Ident] -> Visibility -> OptPos -> 
                      [Item] -> Compiler ()
normaliseSubmodule modCompiler name typeParams vis pos items = do
    dir <- getDirectory
    parentModSpec <- getModuleSpec
    let subModSpec = parentModSpec ++ [name]
    addImport subModSpec (importSpec Nothing vis)
    -- Add the submodule to the submodule list of the implementation
    updateImplementation $
        updateModSubmods (\sm-> Map.insert name subModSpec sm)
    enterModule dir subModSpec typeParams
    case typeParams of
      Nothing -> return ()
      Just _ ->
        updateImplementation 
        (\imp ->
          let set = Set.singleton $ TypeSpec parentModSpec name []
          in imp { modKnownTypes = Map.insert name set $ modKnownTypes imp })
    normalise modCompiler items
    mods <- exitModule
    unless (List.null mods) $ modCompiler mods
    return ()


-- |Add a contructor for the specified type.
addCtor :: ([ModSpec] -> Compiler ()) -> Visibility -> Ident -> [Ident] ->
           FnProto -> OptPos -> Compiler ()
addCtor modCompiler vis typeName typeParams (FnProto ctorName [] _) pos = do
    let typespec = TypeSpec [] typeName $ 
                   List.map (\n->TypeSpec [] n []) typeParams
    let flowType = Implicit pos
    ctorValue <- getModuleImplementationField modConstCtorCount
    updateImplementation (\imp -> imp { modConstCtorCount = ctorValue + 1 })
    normaliseItem modCompiler
      (ProcDecl Public (ProcProto ctorName
                        [Param "$" typespec ParamOut Ordinary] [])
       [Unplaced $ ForeignCall "llvm" "move" []
        [Unplaced $ Typed (IntValue $ fromIntegral ctorValue) typespec True,
         Unplaced $ Var "$" ParamOut Ordinary]]
       pos)
addCtor modCompiler vis typeName typeParams (FnProto ctorName params _) pos = do
    let typespec = TypeSpec [] typeName $ 
                   List.map (\n->TypeSpec [] n []) typeParams
    let flowType = Implicit pos
    tagValue <- getModuleImplementationField modNonConstCtorCount
    updateImplementation (\imp -> imp { modNonConstCtorCount = tagValue + 1 })
    fields <- mapM (\(Param var typ _ _) -> fmap (var,) $ fieldSize typ) params
    let (fields',size) = 
          List.foldl (\(lst,offset) (var,sz) ->
                       let aligned = alignOffset offset sz
                       in (((var,aligned):lst),aligned + sz))
          ([],0) fields
    -- XXX this should replace the following call, but it causes type errors, because
    --     it can't work out the type of $rec.
    -- normaliseItem modCompiler $
    --   ProcDecl Public (ProcProto ctorName 
    --                     (params++[Param "$" typespec ParamOut Ordinary]) [])
    --    ([Unplaced $ ForeignCall "lpvm" "alloc" []
    --       [Unplaced $ IntValue $ fromIntegral size,
    --        Unplaced $ Typed (Var "$rec" ParamOut Ordinary) typespec False]]
    --      ++
    --      (reverse $ List.map (\(var,aligned) ->
    --                            (Unplaced $ ForeignCall "lpvm" "mutate" []
    --                             [Unplaced $ Var "$rec" ParamInOut flowType,
    --                              Unplaced $ IntValue $ fromIntegral aligned,
    --                              Unplaced $ Var var ParamIn flowType]))
    --       fields')
    --     ++
    --     [Unplaced $ ForeignCall "llvm" "or" []
    --      [Unplaced $ Var "$rec" ParamIn Ordinary,
    --       Unplaced $ IntValue $ fromIntegral tagValue,
    --       Unplaced $ Var "$" ParamOut Ordinary]])
    --    pos
    normaliseItem modCompiler
      (FuncDecl Public (FnProto ctorName params []) typespec
       (Unplaced $ Where
        ([Unplaced $ ForeignCall "lpvm" "alloc" []
          [Unplaced $ StringValue typeName, Unplaced $ StringValue ctorName,
           Unplaced $ Var "$rec" ParamOut flowType]]
         ++
         (List.map (\(Param var _ dir paramFlowType) ->
                     (Unplaced $ ForeignCall "lpvm" "mutate" []
                      [Unplaced $ StringValue $ typeName,
                       Unplaced $ StringValue ctorName,
                       Unplaced $ StringValue var,
                       Unplaced $ Var "$rec" ParamInOut flowType,
                       Unplaced $ Var var ParamIn paramFlowType]))
          params))
        (Unplaced $ Var "$rec" ParamIn flowType))
       pos)
    mapM_ (addGetterSetter modCompiler vis typespec ctorName pos) params


-- |The number of bytes occupied by a value of the specified type.  If the
--  type is boxed, this is the word size.
fieldSize :: TypeSpec -> Compiler Int
fieldSize _ = return wordSize

-- |The number of bytes occupied by a value of the specified type.  This is
--  the actual size of a value of the type, regardless of boxing.
-- typeSize :: TypeSpec -> Compiler Int


-- |Given a tentative offset into a structure and the size of the thing at 
--  that offset, return the appropriate actual offset based on the size.
--  Our approach is never to align anything on more than a word size
--  boundary, anything bigger than that is aligned to the word size.
--  For smaller things 
alignOffset :: Int -> Int -> Int
alignOffset offset size =
    let alignment = if size > wordSize
                    then wordSize
                    else fromJust $ find ((0==) . (size`mod`)) $ 
                         reverse $ List.map (2^) 
                         [0..floor $ logBase 2 $ fromIntegral wordSize]
    in ((offset + alignment - 1) `div` alignment) * alignment


-- |Add a getter and setter for the specified type.
addGetterSetter :: ([ModSpec] -> Compiler ()) -> Visibility -> TypeSpec ->
                   Ident -> OptPos -> Param -> Compiler ()
addGetterSetter modCompiler vis rectype ctorName pos
                    (Param field fieldtype _ _) = do
    normaliseItem modCompiler $ FuncDecl vis
      (FnProto field [Param "$rec" rectype ParamIn Ordinary] [])
      fieldtype 
      (Unplaced $ ForeignFn "lpvm" "access" []
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamIn Ordinary])
      pos
    normaliseItem modCompiler $ ProcDecl vis 
      (ProcProto field 
       [Param "$rec" rectype ParamInOut Ordinary,
        Param "$field" fieldtype ParamIn Ordinary] [])
      [Unplaced $ ForeignCall "lpvm" "mutate" []
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamInOut Ordinary,
        Unplaced $ Var "$field" ParamIn Ordinary]]
       pos
