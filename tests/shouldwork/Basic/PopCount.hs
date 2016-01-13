{-# LANGUAGE MagicHash #-}
module PopCount where

import CLaSH.Prelude
import GHC.Word
import Data.Bits

topEntity :: Word -> Int
topEntity = popCount

testInput :: Signal Word
testInput = stimuliGenerator $(v [1::Word,3,8,50,0])

expectedOutput :: Signal Int -> Signal Bool
expectedOutput = outputVerifier $(v ([1,2,1,3,0]::[Int]))
