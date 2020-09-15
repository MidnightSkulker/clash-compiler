{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Transformations
  ( transformationsPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Types (Int(..))

import Clash.GHC.PartialEval.Primitive.Strategy

transformationsPrims :: HashMap Text PrimImpl
transformationsPrims = HashMap.fromList
  [ ("EmptyCase", liftId)
  , ("Clash.Transformations.eqInt", primEqInt)
  , ("Clash.Transformations.removedArg", liftId)
  , ("Clash.Transformations.undefined", liftId)
  , ("Clash.Transformations.ref", liftId)

    -- Not transformations, but must be saved from defaulting to core.
  , ("Clash.Explicit.BlockRam.blockRam#", liftId)
  , ("Clash.Explicit.BlockRam.blockRamU#", liftId)
  , ("Clash.Explicit.BlockRam.blockRam1#", liftId)
  , ("Clash.Explicit.BlockRam.File.blockRamFile#", liftId)

  , ("Clash.Explicit.Testbench.assert", liftId)
  , ("Clash.Explicit.Testbench.assertBitVector", liftId)
  , ("Clash.Explicit.Testbench.tbClockGen", liftId)
  , ("Clash.Explicit.Testbench.tbEnableGen", liftId)

  , ("Clash.Signal.Internal.clockGen", liftId)
  , ("Clash.Signal.Internal.delay#", liftId)
  , ("Clash.Signal.Internal.register#", liftId)
  , ("Clash.Signal.Internal.asyncRegister#", liftId)
  , ("Clash.Signal.Internal.syncRegister#", liftId)
  , ("Clash.Signal.Internal.unsafeFromReset", liftId)
  , ("Clash.Signal.Internal.unsafeToReset", liftId)
  , ("Clash.Signal.Internal.resetGenN", liftId)

  , ("Clash.NFDataX.deepErrorX", liftId)
  , ("Clash.NFDataX.rnfx", liftId)
  , ("Clash.NFDataX.hasUndefined", liftId)
  , ("Clash.NFDataX.ensureSpine", liftId)

  , ("Clash.XException.errorX", liftId)
  , ("Clash.XException.seqX", liftId)
  , ("Clash.XException.deepseqX", liftId)
  , ("Clash.XException.hwSeqX", liftId)

  , ("Clash.Intel.ClockGen.altpll", liftId)

  , ("Clash.Xilinx.ClockGen.clockWizard", liftId)
  , ("Clash.Xilinx.ClockGen.clockWizardDifferential", liftId)
  ]

primEqInt :: PrimImpl
primEqInt =
  liftBinary $ \x y ->
    let !(I# _) = x
        !(I# _) = y
     in x == y
