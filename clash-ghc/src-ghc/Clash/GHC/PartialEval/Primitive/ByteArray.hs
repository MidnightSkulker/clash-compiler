{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.ByteArray
  ( byteArrayPrims
  ) where

import Control.Monad.IO.Class
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Primitive.ByteArray as BA
import Data.Text (Text)

import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.ToAst
import Clash.GHC.PartialEval.Primitive.Unboxed

byteArrayPrims :: HashMap Text PrimImpl
byteArrayPrims = HashMap.fromList
  [ ("GHC.Prim.newByteArray#", primNewByteArray)
  , ("GHC.Prim.setByteArray#", liftId)
  , ("GHC.Prim.writeWordArray#", liftId)
  , ("GHC.Prim.unsafeFreezeByteArray#", primUnsafeFreezeByteArray)
  , ("GHC.Prim.sizeofByteArray#", primSizeofByteArray)
  , ("GHC.Prim.getSizeofMutableByteArray#", liftId)
  , ("GHC.Prim.indexWordArray#", liftId)
  , ("GHC.Prim.resizeMutableByteArray#", liftId)
  , ("GHC.Prim.shrinkMutableByteArray#", liftId)
  , ("GHC.Prim.copyByteArray#", liftId)
  , ("GHC.Prim.readWordArrray#", liftId)
  ]

primNewByteArray :: PrimImpl
primNewByteArray e p args
  | [Right _s, Left x, Left y] <- args
  = do size <- boxInt <$> fromValueForce e x
       resTy <- resultType p args
       mba <- liftIO (BA.newByteArray size)
       ba <- liftIO (BA.unsafeFreezeByteArray mba)

       toValue (UTuple2 (y, Ref Nothing (UByteArray ba))) resTy

  | otherwise
  = empty

primUnsafeFreezeByteArray :: PrimImpl
primUnsafeFreezeByteArray e p args
  | [Right _s, Left x, Left y] <- args
  = do !ba <- fromValueForce @(Ref UByteArray) e x
       resTy <- resultType p args

       toValue (UTuple2 (y, ba)) resTy

  | otherwise
  = empty

primSizeofByteArray :: PrimImpl
primSizeofByteArray e p args
  | [Left x] <- args
  = do !ba <- boxByteArray . refValue <$> fromValueForce @(Ref UByteArray) e x
       resTy <- resultType p args

       toValue (UInt (BA.sizeofByteArray ba)) resTy

  | otherwise
  = empty
