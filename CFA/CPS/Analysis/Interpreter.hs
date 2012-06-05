{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.CPS.Analysis.Interpreter where

import Data.IORef
import Data.Map as Map
import Data.Set as Set
import Control.Applicative

import CFA.CPS
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner
import CFA.Store

data A = A

data IOAddr = MkIOAddr { unIOAddr :: IORef (Val IOAddr) } deriving (Eq)
instance Show IOAddr where
  show a = "{IOAddr ...}"

readIOAddr :: IOAddr -> IO (Val IOAddr)
readIOAddr = readIORef . unIOAddr

writeIOAddr :: IOAddr -> Val IOAddr -> IO ()
writeIOAddr = writeIORef . unIOAddr

instance Analysis IO IOAddr where
  fun ρ (Lam l) = return $ Clo (l, ρ)
  fun ρ (Ref v) = readIOAddr (ρ ! v)

  arg ρ (Lam l) = return $ Clo (l, ρ)
  arg ρ (Ref v) = readIOAddr (ρ!v)

  -- TODO: why does arg return a Set?
  addr $= v = writeIOAddr addr v

  alloc v = MkIOAddr <$> newIORef undefined

  tick _ _ go = go

instance FPCalc IO (PΣ IOAddr) where
  -- no fixed point calculations here...
  hasSeen _ = return False
  markSeen _ = return ()

instance GarbageCollector IO (PΣ IOAddr) where
  gc _ = return ()
  
interpret :: CExp -> IO ()
interpret c = explore c 
