{-# OPTIONS -fno-warn-duplicate-exports #-}

module Option ( module Option, module Compare, module Function ) where
import Compare
import Function
data Option__Option a = None
                      | Some a

option__some_p :: Option__Option a -> Bool
option__some_p None = False
option__some_p _ = True

option__none_p :: Option__Option a -> Bool
option__none_p None = True
option__none_p _ = False

option__compare :: ((a, a) -> Ordering) -> 
                   (Option__Option a, Option__Option a) -> Ordering
option__compare comp(Some x, Some y) = comp(x, y)
option__compare comp(None, Some _) = LT
option__compare comp(Some _, None) = GT
option__compare comp(None, None) = EQ

option__mapOption :: (a -> b) -> Option__Option a -> Option__Option b
option__mapOption f None = None
option__mapOption f (Some x) = Some (f x)

option__isoOption :: (a -> b) -> Option__Option a -> Option__Option b
option__isoOption iso_elem = option__mapOption iso_elem