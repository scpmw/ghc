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


resolveLlvmDatas :: [LlvmUnresData] -> LlvmM [LlvmData]
resolveLlvmDatas = mapM resolveLlvmData

-- | Fix up CLabel references now that we should have passed all CmmData.
resolveLlvmData :: LlvmUnresData -> LlvmM LlvmData
resolveLlvmData (lbl, sec, alias, unres) = do
    label             <- strCLabel_llvm lbl
    static            <- resDatas unres
    let struct         = Just $ LMStaticStruc static alias
        link           = if (externallyVisibleCLabel lbl)
                            then ExternallyVisible else Internal
        const          = if isSecConstant sec then Constant else Global
        glob           = LMGlobalVar label alias link Nothing Nothing const
    return ([LMGlobal glob struct], [alias])

-- | Should a data in this section be considered constant
isSecConstant :: Section -> Bool
isSecConstant Text                    = True
isSecConstant ReadOnlyData            = True
isSecConstant RelocatableReadOnlyData = True
isSecConstant ReadOnlyData16          = True
isSecConstant Data                    = False
isSecConstant UninitialisedData       = False
isSecConstant (OtherSection _)        = False


-- ----------------------------------------------------------------------------
-- ** Resolve Data/CLabel references
--

-- | Resolve data list
resDatas :: [UnresStatic] -> LlvmM [LlvmStatic]

resDatas cmms = mapM resData cmms

-- | Resolve an individual static label if it needs to be.
--
-- We check the 'LlvmEnv' to see if the reference has been defined in this
-- module. If it has we can retrieve its type and make a pointer, otherwise
-- we introduce a generic external definition for the referenced label and
-- then make a pointer (see @getCmmStatic@).
resData :: UnresStatic -> LlvmM LlvmStatic

resData (Right stat) = return stat

resData (Left cmm@(CmmLabel l)) = do
    var <- getGlobalPtr =<< strCLabel_llvm l
    let ptr = LMStaticPointer var
        lmty = cmmToLlvmType $ cmmLitType cmm
    return $ LMPtoI ptr lmty

resData (Left (CmmLabelOff label off)) = do
    var <- resData (Left (CmmLabel label))
    let offset = LMStaticLit $ LMIntLit (toInteger off) llvmWord
    return $ LMAdd var offset

resData (Left (CmmLabelDiffOff l1 l2 off)) = do
    var1 <- resData (Left (CmmLabel l1))
    var2 <- resData (Left (CmmLabel l2))
    let var = LMSub var1 var2
        offset = LMStaticLit $ LMIntLit (toInteger off) llvmWord
    return $ LMAdd var offset

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

