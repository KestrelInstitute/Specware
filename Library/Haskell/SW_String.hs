{-# OPTIONS -fno-warn-duplicate-exports #-}

module SW_String ( module SW_String, module SW_Char, module SW_List ) where
import SW_Char
import SW_List

string__translate :: (Char -> String) -> String -> String
string__translate subst s = concat (map subst (id s))

string__newline :: String
string__newline = "\n"

boolean__show :: Bool -> String
boolean__show x = if x then "true" else "false"

natConvertible :: String -> Bool
natConvertible s = 
  let cs = id s in any isDigit cs && all isDigit cs

explodedStringToNat :: [Char] -> Int
explodedStringToNat l = 
  sw_foldl (\(result, dig) -> result * 10 + ord dig - 48) 0 l

integer__intConvertible :: String -> Bool
integer__intConvertible s = 
  let cs = id s in 
  any isDigit cs 
    && (all isDigit cs 
          || head cs == '-' && all isDigit (tail cs))

stringToInt :: String -> Int
stringToInt s = 
  let e_s = id s in 
  case e_s of 
    firstchar : r_s -> 
        if firstchar == '-' then 
          negate (explodedStringToNat r_s)
        else 
          explodedStringToNat e_s

char__show :: Char -> String
char__show c = id ([c])

compare__show :: Ordering -> String
compare__show GT = "Greater"
compare__show EQ = "Equal"
compare__show LT = "Less"

option__show :: (a -> String) -> Maybe a -> String
option__show shw Nothing = "None"
option__show shw (Just x) = "(Some " ++ shw x ++ ")"

list__show :: String -> [String] -> String
list__show sep [] = ""
list__show sep ([hd]) = hd
list__show sep (hd_1 : tl) = hd_1 ++ sep ++ list__show sep tl