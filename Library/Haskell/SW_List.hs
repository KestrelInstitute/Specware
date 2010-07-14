{-# OPTIONS -fno-warn-duplicate-exports #-}

module SW_List ( module SW_List, module Option, module SW_Integer, module List ) where
import Option
import SW_Integer
import List

list__definedOnInitialSegmentOfLength :: (Int -> Maybe a) -> Int -> Bool
infixl 4 `list__definedOnInitialSegmentOfLength`
f `list__definedOnInitialSegmentOfLength` n = 
  (error "Trying to evaluate a univeral quanitification.") 
    && (error "Trying to evaluate a univeral quanitification.")

list__lengthOfListFunction :: (Int -> Maybe a) -> Int
list__lengthOfListFunction f = error "Trying to evaluate a \"the\" expression."

list__list :: (Int -> Maybe a) -> [a]
list__list f = 
  let
    loop = 
      \i -> 
        case f i of 
          Nothing -> []
          Just x -> x : loop (i + 1) 
  in 
  loop 0

(@@) :: [a] -> Int -> Maybe a
infixl 8 @@
[] @@ i = Nothing
(hd : tl) @@ 0 = Just hd
(hd : tl) @@ (i + 1) = tl @@ i

list__list_1 :: [a] -> Int -> Maybe a
list__list_1 l i = l @@ i

list__tabulate :: (Int, (Int -> a)) -> [a]
list__tabulate(n, f) = 
  let
    loop = 
      \(i, result) -> 
        if i == 0 then 
          result
        else 
          let i_1 = i - 1 in loop(i_1, f i_1 : result) 
  in 
  loop(n, [])

list__ofLength_p :: Int -> [a] -> Bool
list__ofLength_p n l = length l == n

list__nonEmpty_p :: [a] -> Bool
list__nonEmpty_p [] = False
list__nonEmpty_p _ = True

list__single :: a -> [a]
list__single x = [x]

list__theElement :: [a] -> a
list__theElement ([hd]) = hd

list__subFromLong :: ([a], Int, Int) -> [a]
list__subFromLong(l, i, n) = take n (drop i l)

list__subFromTo :: ([a], Int, Int) -> [a]
list__subFromTo(l, i, j) = list__subFromLong(l, i, j - i)

list__suffix :: ([a], Int) -> [a]
list__suffix(l, n) = drop (length l - n) l

list__removeSuffix :: ([a], Int) -> [a]
list__removeSuffix(l, n) = take (length l - n) l

(<|) :: [a] -> a -> [a]
infixl 6 <|
[] <| x = [x]
(hd : tl) <| x = hd : tl <| x

list__exists1_p :: (a -> Bool) -> [a] -> Bool
list__exists1_p p [] = False
list__exists1_p p (hd : tl) = 
  p hd && not (any p tl) || list__exists1_p p tl

list__foralli_p :: ((Int, a) -> Bool) -> [a] -> Bool
list__foralli_p p l = 
  let
    loop = 
      \(l_1, i) -> 
        case l_1 of 
          [] -> True
          hd : tl -> p(i, hd) && loop(tl, i + 1) 
  in 
  loop(l, 0)

sw_foldl :: ((b, a) -> b) -> b -> [a] -> b
sw_foldl f base [] = base
sw_foldl f base (hd : tl) = sw_foldl f (f(base, hd)) tl

sw_foldr :: ((a, b) -> b) -> b -> [a] -> b
sw_foldr f base [] = base
sw_foldr f base (hd : tl) = f(hd, sw_foldr f base tl)

list__equiLong :: [a] -> [b] -> Bool
infixl 4 `list__equiLong`
l1 `list__equiLong` l2 = length l1 == length l2

list__map2 :: ((a, b) -> c) -> ([a], [b]) -> [c]
list__map2 f([], []) = []
list__map2 f(hd1 : tl1, hd2 : tl2) = 
  f(hd1, hd2) : list__map2 f(tl1, tl2)

list__map3 :: ((a, b, c) -> d) -> ([a], [b], [c]) -> [d]
list__map3 f([], [], []) = []
list__map3 f(hd1 : tl1, hd2 : tl2, hd3 : tl3) = 
  f(hd1, hd2, hd3) : list__map3 f(tl1, tl2, tl3)

list__removeNones :: [Maybe a] -> [a]
list__removeNones [] = []
list__removeNones (Just x : tl) = x : list__removeNones tl
list__removeNones (Nothing : tl_1) = list__removeNones tl_1

list__matchingOptionLists_p :: ([Maybe a], [Maybe b]) -> Bool
list__matchingOptionLists_p([], []) = True
list__matchingOptionLists_p(Just _ : tl1, Just _ : tl2) = 
  list__matchingOptionLists_p(tl1, tl2)
list__matchingOptionLists_p(Nothing : tl1_1, Nothing : tl2_1) = 
  list__matchingOptionLists_p(tl1_1, tl2_1)
list__matchingOptionLists_p(xx0, xx) = False

list__mapPartial :: (a -> Maybe b) -> [a] -> [b]
list__mapPartial f [] = []
list__mapPartial f (hd : tl) = 
  case f hd of 
    Just x -> x : list__mapPartial f tl
    Nothing -> list__mapPartial f tl

list__mapPartial2 :: ((a, b) -> Maybe c) -> ([a], [b]) -> [c]
list__mapPartial2 f([], []) = []
list__mapPartial2 f(hd1 : tl1, hd2 : tl2) = 
  case f(hd1, hd2) of 
    Just x -> x : list__mapPartial2 f(tl1, tl2)
    Nothing -> list__mapPartial2 f(tl1, tl2)

list__mapPartial3 :: ((a, b, c) -> Maybe d) -> ([a], [b], [c]) -> [d]
list__mapPartial3 f([], [], []) = []
list__mapPartial3 f(hd1 : tl1, hd2 : tl2, hd3 : tl3) = 
  case f(hd1, hd2, hd3) of 
    Just x -> x : list__mapPartial3 f(tl1, tl2, tl3)
    Nothing -> list__mapPartial3 f(tl1, tl2, tl3)

list__allEqualElements_p :: Eq a => [a] -> Bool
list__allEqualElements_p [] = True
list__allEqualElements_p (hd : tl) = all (\x -> x == hd) tl

list__extendLeft :: ([a], a, Int) -> [a]
list__extendLeft(l, x, n) = 
  let len = length l in 
  if n == len then l else x : list__extendLeft(l, x, n - 1)

list__extendRight :: ([a], a, Int) -> [a]
list__extendRight(l, x, n) = 
  l ++ (replicate (n - length l) x)

list__equiExtendLeft :: ([a], [b], a, b) -> ([a], [b])
list__equiExtendLeft(l1, l2, x1, x2) = 
  if length l1 < length l2 then 
    (list__extendLeft(l1, x1, length l2), l2)
  else 
    (l1, list__extendLeft(l2, x2, length l1))

list__equiExtendRight :: ([a], [b], a, b) -> ([a], [b])
list__equiExtendRight(l1, l2, x1, x2) = 
  if length l1 < length l2 then 
    (list__extendRight(l1, x1, length l2), l2)
  else 
    (l1, list__extendRight(l2, x2, length l1))

list__shiftLeft :: ([a], a, Int) -> [a]
list__shiftLeft(l, x, n) = drop n (l ++ (replicate n x))

list__shiftRight :: ([a], a, Int) -> [a]
list__shiftRight(l, x, n) = 
  list__removeSuffix((replicate n x) ++ l, n)

list__rotateLeft :: ([a], Int) -> [a]
list__rotateLeft(l, n) = 
  let n_1 = n `mod` length l in 
  (drop n_1 l) ++ (take n_1 l)

list__rotateRight :: ([a], Int) -> [a]
list__rotateRight(l, n) = 
  let n_1 = n `mod` length l in 
  list__suffix(l, n_1) ++ list__removeSuffix(l, n_1)

list__unflattenL :: ([a], [Int]) -> [[a]]
list__unflattenL(l, []) = []
list__unflattenL(l, len : lens_1) = 
  (take len l) : list__unflattenL(drop len l, lens_1)

list__unflatten :: ([a], Int) -> [[a]]
list__unflatten(l, n) = 
  if null l then 
    []
  else 
    (take n l) : list__unflatten(drop n l, n)

list__noRepetitions_p :: Eq a => [a] -> Bool
list__noRepetitions_p [] = True
list__noRepetitions_p (hd : tl) = 
  hd `notElem` tl && list__noRepetitions_p tl

list__increasingNats_p :: [Int] -> Bool
list__increasingNats_p [] = True
list__increasingNats_p ([_]) = True
list__increasingNats_p (x : y : tl) = 
  x < y && list__increasingNats_p (y : tl)

list__rightmostPositionSuchThat :: ([a], (a -> Bool)) -> Maybe Int
list__rightmostPositionSuchThat(l, p) = 
  let
    loop = 
      \(l_1, i, result) -> 
        case l_1 of 
          [] -> result
          hd : tl -> 
              loop(tl, i + 1, if p hd then Just i else result) 
  in 
  loop(l, 0, Nothing)

list__positionOf :: Eq a => ([a], a) -> Int
list__positionOf(l, x) = 
  case findIndex (\y -> y == x) l of 
    Just pos -> pos

list__prefixOf_p :: Eq a => ([a], [a]) -> Bool
list__prefixOf_p([], l2) = True
list__prefixOf_p(hd1 : tl1, hd2 : tl2) = 
  hd1 == hd2 && list__prefixOf_p(tl1, tl2)
list__prefixOf_p(l1, l2) = False

list__sublistAt_p :: Eq a => ([a], Int, [a]) -> Bool
list__sublistAt_p(subl, i, supl) = list__prefixOf_p(subl, drop i supl)

list__positionsOfSublist :: Eq a => ([a], [a]) -> [Int]
list__positionsOfSublist(subl, supl) = 
  let
    loop = 
      \(supl', i) -> 
        case supl' of 
          [] -> if null subl then [i] else []
          _ : tl -> 
              if list__prefixOf_p(subl, supl') then 
                i : loop(tl, i + 1)
              else 
                loop(tl, i + 1) 
  in 
  loop(supl, 0)

list__leftmostPositionOfSublistAndFollowing :: Eq a => ([a], [a]) -> 
                                                       Maybe (Int, [a])
list__leftmostPositionOfSublistAndFollowing(subl, supl) = 
  let
    loop = 
      \(supl', i) -> 
        case supl' of 
          [] -> if null subl then Just (i, []) else Nothing
          _ : tl -> 
              if list__prefixOf_p(subl, supl') then 
                Just (i, drop (length subl) supl')
              else 
                loop(tl, i + 1) 
  in 
  loop(supl, 0)

list__rightmostPositionOfSublistAndPreceding :: Eq a => ([a], [a]) -> 
                                                        Maybe (Int, [a])
list__rightmostPositionOfSublistAndPreceding(subl, supl) = 
  let
    loop = 
      \(supl', i, lastPosFound) -> 
        case supl' of 
          [] -> if null subl then Just i else lastPosFound
          _ : tl -> 
              if list__prefixOf_p(subl, supl') then 
                loop(tl, i + 1, Just i)
              else 
                loop(tl, i + 1, lastPosFound) 
  in 
  case loop(supl, 0, Nothing) of 
    Just i_1 -> Just (i_1, take i_1 supl)
    Nothing -> Nothing

splitAt3 :: ([a], Int) -> ([a], a, [a])
splitAt3(l, i) = (take i l, l !! i, drop (i + 1) l)

list__splitAtLeftmost :: (a -> Bool) -> [a] -> Maybe ([a], a, [a])
list__splitAtLeftmost p l = 
  case findIndex p l of 
    Just i -> Just (splitAt3(l, i))
    Nothing -> Nothing

list__splitAtRightmost :: (a -> Bool) -> [a] -> Maybe ([a], a, [a])
list__splitAtRightmost p l = 
  case list__rightmostPositionSuchThat(l, p) of 
    Just i -> Just (splitAt3(l, i))
    Nothing -> Nothing

list__findLeftmost :: (a -> Bool) -> [a] -> Maybe a
list__findLeftmost p [] = Nothing
list__findLeftmost p (hd : tl) = 
  if p hd then Just hd else list__findLeftmost p tl

list__findRightmost :: (a -> Bool) -> [a] -> Maybe a
list__findRightmost p l = 
  let
    loop = 
      \(l_1, result) -> 
        case l_1 of 
          [] -> result
          hd : tl -> 
              if p hd then 
                loop(tl, Just hd)
              else 
                loop(tl, result) 
  in 
  loop(l, Nothing)

list__findLeftmostAndPreceding :: (a -> Bool) -> [a] -> Maybe (a, [a])
list__findLeftmostAndPreceding p l = 
  case findIndex p l of 
    Nothing -> Nothing
    Just i -> Just (l !! i, take i l)

list__findRightmostAndFollowing :: (a -> Bool) -> [a] -> Maybe (a, [a])
list__findRightmostAndFollowing p l = 
  case list__rightmostPositionSuchThat(l, p) of 
    Nothing -> Nothing
    Just i -> Just (l !! i, drop i l)

delete_all :: Eq a => a -> [a] -> [a]
delete_all x [] = []
delete_all x (hd : tl) = 
  if x == hd then 
    delete_all x tl
  else 
    hd : delete_all x tl

list__diff :: Eq a => ([a], [a]) -> [a]
list__diff([], l2) = []
list__diff(hd : tl, l2) = 
  if hd `elem` l2 then 
    list__diff(tl, l2)
  else 
    hd : list__diff(tl, l2)

list__longestCommonPrefix :: Eq a => ([a], [a]) -> [a]
list__longestCommonPrefix(hd1 : tl1, hd2 : tl2) = 
  if hd1 == hd2 then 
    hd1 : list__longestCommonPrefix(tl1, tl2)
  else 
    []
list__longestCommonPrefix(l1, l2) = []

list__longestCommonSuffix :: Eq a => ([a], [a]) -> [a]
list__longestCommonSuffix(l1, l2) = 
  reverse (list__longestCommonPrefix(reverse l1, reverse l2))

list__permutation_p :: [Int] -> Bool
list__permutation_p prm = 
  list__noRepetitions_p prm 
    && (let n = length prm in all (\i -> i < n) prm)

list__permute :: ([a], [Int]) -> [a]
list__permute(l, prm) = 
  let n = length l in 
  list__list
     (\i -> 
        if i < n then l @@ list__positionOf(prm, i) else Nothing)

list__permutationOf :: Eq a => [a] -> [a] -> Bool
infixl 4 `list__permutationOf`
l1 `list__permutationOf` l2 = 
  let
    deleteOne = 
      \(x, l) -> 
        case l of 
          [] -> Nothing
          hd : tl -> 
              if hd == x then 
                Just tl
              else 
                case deleteOne(x, tl) of 
                  Just l_1 -> Just (hd : l_1)
                  Nothing -> Nothing 
  in 
  case l1 of 
    [] -> null l2
    x_1 : l1' -> 
        case deleteOne(x_1, l2) of 
          Just l2' -> l1' `list__permutationOf` l2'
          Nothing -> False

list__compare :: ((a, a) -> Ordering) -> ([a], [a]) -> Ordering
list__compare comp(hd1 : tl1, hd2 : tl2) = 
  case comp(hd1, hd2) of 
    EQ -> list__compare comp(tl1, tl2)
    result -> result
list__compare comp([], []) = EQ
list__compare comp([], l2) = LT
list__compare comp(l1, []) = GT