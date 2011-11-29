-- ----------------------------------------------------------------------------
-- | Handle conversion of CmmData to LLVM code.
--

module LlvmCodeGen.Data (
        genLlvmData, resolveLlvmDatas, resolveLlvmData
    ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base

import BlockId
import CLabel
import OldCmm

import FastString
import qualified Outputable

import Data.Maybe


-- ----------------------------------------------------------------------------
-- * Constants
--

-- | The string appended to a variable name to create its structure type alias
structStr :: LMString
structStr = fsLit "_struct"

-- ----------------------------------------------------------------------------
-- * Top level
--

-- | Pass a CmmStatic section to an equivalent Llvm code. Can't
-- complete this completely though as we need to pass all CmmStatic
-- sections before all references can be resolved. This last step is
-- done by 'resolveLlvmData'.
genLlvmData :: (Section, CmmStatics) -> LlvmM LlvmUnresData
genLlvmData (sec, Statics lbl xs) = do
    label <- strCLabel_llvm lbl
    let static  = map genData xs

        types   = map getStatTypes static
        getStatTypes (Left  x) = cmmToLlvmType $ cmmLitType x
        getStatTypes (Right x) = getStatType x

        strucTy = LMStruct types
        alias   = LMAlias ((label `appendFS` structStr), strucTy)
    return (lbl, sec, alias, static)


resolveLlvmDatas :: [LlvmUnresData] -> [LlvmData]
                 -> LlvmM [LlvmData]
resolveLlvmDatas [] ldata
  = return ldata

resolveLlvmDatas (udata : rest) ldata
  = do ndata <- resolveLlvmData udata
       resolveLlvmDatas rest (ldata ++ [ndata])

-- | Fix up CLabel references now that we should have passed all CmmData.
resolveLlvmData :: LlvmUnresData -> LlvmM LlvmData
resolveLlvmData (lbl, sec, alias, unres) = do
    label             <- strCLabel_llvm lbl
    (static, refs)    <- resDatas unres ([], [])
    let refs'          = catMaybes refs
        struct         = Just $ LMStaticStruc static alias
        link           = if (externallyVisibleCLabel lbl)
                            then ExternallyVisible else Internal
        const          = isSecConstant sec
        glob           = LMGlobalVar label alias link Nothing Nothing const
    return (refs' ++ [LMGlobal glob struct], [alias])


-- | Should a data in this section be considered constant
isSecConstant :: Section -> Bool
isSecConstant Text                    = True
isSecConstant Data                    = False
isSecConstant ReadOnlyData            = True
isSecConstant RelocatableReadOnlyData = True
isSecConstant UninitialisedData       = False
isSecConstant ReadOnlyData16          = True
isSecConstant (OtherSection _)        = False


-- ----------------------------------------------------------------------------
-- ** Resolve Data/CLabel references
--

-- | Resolve data list
resDatas :: [UnresStatic] -> ([LlvmStatic], [Maybe LMGlobal])
         -> LlvmM ([LlvmStatic], [Maybe LMGlobal])

resDatas [] (stat, glob)
  = return (stat, glob)

resDatas (cmm : rest) (stats, globs)
  = do (nstat, nglob) <- resData cmm
       resDatas rest (stats ++ [nstat], globs ++ nglob)

-- | Resolve an individual static label if it needs to be.
--
-- We check the 'LlvmEnv' to see if the reference has been defined in this
-- module. If it has we can retrieve its type and make a pointer, otherwise
-- we introduce a generic external definition for the referenced label and
-- then make a pointer.
resData :: UnresStatic -> LlvmM (LlvmStatic, [Maybe LMGlobal])

resData (Right stat) = return (stat, [Nothing])

resData (Left cmm@(CmmLabel l)) = do
    label <- strCLabel_llvm l
    ty <- funLookup label
    let lmty = cmmToLlvmType $ cmmLitType cmm
    case ty of
            -- Make generic external label defenition and then pointer to it
            Nothing -> do
                let glob@(LMGlobal var _) = genStringLabelRef label
                    ptr  = LMStaticPointer var
                funInsert label (pLower $ getVarType var)
                return (LMPtoI ptr lmty, [Just glob])
            -- Referenced data exists in this module, retrieve type and make
            -- pointer to it.
            Just ty' ->
                let var = LMGlobalVar label (LMPointer ty')
                            ExternallyVisible Nothing Nothing False
                    ptr  = LMStaticPointer var
                in return (LMPtoI ptr lmty, [Nothing])

resData (Left (CmmLabelOff label off)) = do
    (var, glob) <- resData (Left (CmmLabel label))
    let offset = LMStaticLit $ LMIntLit (toInteger off) llvmWord
    return (LMAdd var offset, glob)

resData (Left (CmmLabelDiffOff l1 l2 off)) = do
    (var1, glob1) <- resData (Left (CmmLabel l1))
    (var2, glob2) <- resData (Left (CmmLabel l2))
    let var = LMSub var1 var2
        offset = LMStaticLit $ LMIntLit (toInteger off) llvmWord
    return (LMAdd var offset, glob1 ++ glob2)

resData _ = panic "resData: Non CLabel expr as left type!"

-- ----------------------------------------------------------------------------
-- * Generate static data
--

-- | Handle static data
genData :: CmmStatic -> UnresStatic

genData (CmmString str) =
    let v  = map (\x -> LMStaticLit $ LMIntLit (fromIntegral x) i8) str
        ve = v ++ [LMStaticLit $ LMIntLit 0 i8]
    in Right $ LMStaticArray ve (LMArray (length ve) i8)

genData (CmmUninitialised bytes)
    = Right $ LMUninitType (LMArray bytes i8)

genData (CmmStaticLit lit)
    = genStaticLit lit


-- | Generate Llvm code for a static literal.
--
-- Will either generate the code or leave it unresolved if it is a 'CLabel'
-- which isn't yet known.
genStaticLit :: CmmLit -> UnresStatic
genStaticLit (CmmInt i w)
    = Right $ LMStaticLit (LMIntLit i (LMInt $ widthInBits w))

genStaticLit (CmmFloat r w)
    = Right $ LMStaticLit (LMFloatLit (fromRational r) (widthToLlvmFloat w))

-- Leave unresolved, will fix later
genStaticLit c@(CmmLabel        _    ) = Left $ c
genStaticLit c@(CmmLabelOff     _   _) = Left $ c
genStaticLit c@(CmmLabelDiffOff _ _ _) = Left $ c

genStaticLit (CmmBlock b) = Left $ CmmLabel $ infoTblLbl b

genStaticLit (CmmHighStackMark)
    = panic "genStaticLit: CmmHighStackMark unsupported!"


-- -----------------------------------------------------------------------------
-- * Misc
--

-- | Error Function
panic :: String -> a
panic s = Outputable.panic $ "LlvmCodeGen.Data." ++ s

