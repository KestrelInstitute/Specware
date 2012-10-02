module Boolean ( module Boolean ) where

(~~~) :: (a -> Bool) -> a -> Bool
(~~~) p x = not (p x)

(&&&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
infixr 6 &&&
(p1 &&& p2) x = p1 x && p2 x

(|||) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
infixr 5 |||
(p1 ||| p2) x = p1 x || p2 x

bool__TRUE :: a -> Bool
bool__TRUE x = True

bool__FALSE :: a -> Bool
bool__FALSE x = False