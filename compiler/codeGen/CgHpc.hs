-----------------------------------------------------------------------------
--
-- Code generation for coverage
--
-- (c) Galois Connections, Inc. 2006
--
-----------------------------------------------------------------------------

module CgHpc (cgTickBox, cgInstrument, hpcTable) where

import OldCmm
import CLabel
import Module
import OldCmmUtils
import CgUtils
import CgMonad
import HscTypes

cgTickBox :: Module -> Int -> Code
cgTickBox mod n = do
       let tick_box = (cmmIndex W64
                       (CmmLit $ CmmLabel $ mkHpcTicksLabel $ mod)
                       n
                      )
       stmtsC [ CmmStore tick_box
                         (CmmMachOp (MO_Add W64)
                                               [ CmmLoad tick_box b64
                                               , CmmLit (CmmInt 1 W64)
                                               ])
              ] 


-- | Adds instrumentation to the given code-gen output. Returns the ID
-- associated with the code.
cgInstrument :: Int -> Code -> Code
cgInstrument instr code = do

      -- Generate rest of code, publish instrumentation ID in monad
      withInstr instr code

hpcTable :: Module -> HpcInfo -> Code
hpcTable this_mod (HpcInfo hpc_tickCount _) = do
                        emitDataLits (mkHpcTicksLabel this_mod) $
                                        [ CmmInt 0 W64
                                        | _ <- take hpc_tickCount [0::Int ..]
                                        ]

hpcTable _ (NoHpcInfo {}) = error "TODO: impossible"
