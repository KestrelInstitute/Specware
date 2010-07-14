{-# OPTIONS -fno-warn-duplicate-exports #-}

module SW_Integer ( module SW_Integer, module Compare, module Function ) where
import Compare
import Function

integer__divides :: Int -> Int -> Bool
infixl 4 `integer__divides`
x `integer__divides` y = y == 0 || x `mod` y == 0

integer__multipleOf :: Int -> Int -> Bool
infixl 4 `integer__multipleOf`
x `integer__multipleOf` y = y `integer__divides` x

integer__divC :: Int -> Int -> Int
infixl 6 `integer__divC`
i `integer__divC` j = 
  if i `rem` j == 0 || signum i /= signum j then 
    i `quot` j
  else 
    i `quot` j + 1

integer__modC :: Int -> Int -> Int
infixl 6 `integer__modC`
i `integer__modC` j = i - j * (i `integer__divC` j)

integer__modE :: Int -> Int -> Int
infixl 6 `integer__modE`
i `integer__modE` j = i `mod` abs j

integer__divR :: Int -> Int -> Int
infixl 6 `integer__divR`
i `integer__divR` j = 
  if 2 * abs (i `mod` j) < abs j then 
    i `div` j
  else 
    i `div` j + 1

integer__modR :: Int -> Int -> Int
infixl 6 `integer__modR`
i `integer__modR` j = i - j * (i `integer__divR` j)

integer__euclidianDivision_p :: (Int, Int, Int, Int) -> Bool
integer__euclidianDivision_p(i, j, q, r) = 
  i == j * q + r && 0 <= r && r < abs j

integer__divE :: Int -> Int -> Int
infixl 6 `integer__divE`
i `integer__divE` j = i `div` abs j * signum j