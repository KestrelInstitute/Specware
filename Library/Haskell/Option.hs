{-# OPTIONS -fno-warn-duplicate-exports #-}

module Option ( module Option, module Compare, module Function, module Maybe ) where
import Compare
import Function
import Maybe

option__compare :: ((a, a) -> Ordering) -> (Maybe a, Maybe a) -> Ordering
option__compare comp(Just x, Just y) = comp(x, y)
option__compare comp(Nothing, Just _) = LT
option__compare comp(Just _, Nothing) = GT
option__compare comp(Nothing, Nothing) = EQ

mapOption :: (a -> b) -> Maybe a -> Maybe b
mapOption f Nothing = Nothing
mapOption f (Just x) = Just (f x)

option__isoOption :: (a -> b) -> Maybe a -> Maybe b
option__isoOption iso_elem = mapOption iso_elem