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

data IOAddr = MkIOAddr { unIOAddr :: IORef (Val IOAddr) } 
     deriving (Eq)
instance Show IOAddr where show a = "{IOAddr ...}"

readIOAddr :: IOAddr -> IO (Val IOAddr)
readIOAddr = readIORef . unIOAddr

writeIOAddr :: IOAddr -> Val IOAddr -> IO ()
writeIOAddr = writeIORef . unIOAddr

instance Analysis IO IOAddr where
  fun ρ (Lam l) = return $ Clo (l, ρ)
  fun ρ (Ref v) = readIOAddr (ρ ! v)

  arg ρ (Lam l) = return $ Clo (l, ρ)
  arg ρ (Ref v) = readIOAddr (ρ!v)

  addr $= v = writeIOAddr addr v
  alloc v = MkIOAddr <$> newIORef undefined
  tick _ _ = return ()

interpret :: CExp -> IO (PΣ IOAddr)
interpret e = go (e, ρ0)
    where go :: (PΣ IOAddr) -> IO (PΣ IOAddr)
          go s = do s' <- mnext s 
                    case s' of x@(Exit, _) -> return x
                               y           -> go y
