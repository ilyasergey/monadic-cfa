module Util where

mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (a,c) = (f a, c)

mapSnd :: (b -> c) -> (a, b) -> (a,c)
mapSnd f (a,b) = (a, f b)

