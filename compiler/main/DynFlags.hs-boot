
module DynFlags where

import Platform

data DynFlags

targetPlatform :: DynFlags -> Platform
pprUserLength :: DynFlags -> Int
pprCols :: DynFlags -> Int

