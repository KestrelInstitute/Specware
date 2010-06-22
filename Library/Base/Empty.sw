(* In Specware, any spec S that does not import any other spec explicitly,
imports spec /Library/Base implicitly. Unless S resides under the
Specware4/Library/Base/ directory, in which case it has no implicit imports. The
latter exception prevents some of the base specs from attempting to import
themselves through the implicit importing of spec Base.

This Empty spec is useful in those rare occasions in which a user might want to
not import (implicitly) any of the base specs. By import Empty, a spec
effectively starts as a clean slate, without the base specs. *)


spec

proof Haskell -verbatim
fst_of_3 :: (a, b, c) -> a
fst_of_3(x, _, _) = x
snd_of_3 :: (a, b, c) -> b
snd_of_3(_, x, _) = x
third_of_3 :: (a, b, c) -> c
third_of_3(_, _, x) = x
fst_of_4 :: (a, b, c, d) -> a
fst_of_4(x, _, _, _) = x
snd_of_4 :: (a, b, c, d) -> b
snd_of_4(_, x, _, _) = x
third_of_4 :: (a, b, c, d) -> c
third_of_4(_, _, x, _) = x
fourth_of_4 :: (a, b, c, d) -> d
fourth_of_4(_, _, _, x) = x
fst_of_5 :: (a, b, c, d, e) -> a
fst_of_5(x, _, _, _, _) = x
snd_of_5 :: (a, b, c, d, e) -> b
snd_of_5(_, x, _, _, _) = x
third_of_5 :: (a, b, c, d, e) -> c
third_of_5(_, _, x, _, _) = x
fourth_of_5 :: (a, b, c, d, e) -> d
fourth_of_5(_, _, _, x, _) = x
fifth_of_5 :: (a, b, c, d, e) -> e
fifth_of_5(_, _, _, _, x) = x
fst_of_6 :: (a, b, c, d, e, f) -> a
fst_of_6(x, _, _, _, _, _) = x
snd_of_6 :: (a, b, c, d, e, f) -> b
snd_of_6(_, x, _, _, _, _) = x
third_of_6 :: (a, b, c, d, e, f) -> c
third_of_6(_, _, x, _, _, _) = x
fourth_of_6 :: (a, b, c, d, e, f) -> d
fourth_of_6(_, _, _, x, _, _) = x
fifth_of_6 :: (a, b, c, d, e, f) -> e
fifth_of_6(_, _, _, _, x, _) = x
sixth_of_6 :: (a, b, c, d, e, f) -> f
sixth_of_6(_, _, _, _, _, x) = x
fst_of_7 :: (a, b, c, d, e, f, g) -> a
fst_of_7(x, _, _, _, _, _, _) = x
snd_of_7 :: (a, b, c, d, e, f, g) -> b
snd_of_7(_, x, _, _, _, _, _) = x
third_of_7 :: (a, b, c, d, e, f, g) -> c
third_of_7(_, _, x, _, _, _, _) = x
fourth_of_7 :: (a, b, c, d, e, f, g) -> d
fourth_of_7(_, _, _, x, _, _, _) = x
fifth_of_7 :: (a, b, c, d, e, f, g) -> e
fifth_of_7(_, _, _, _, x, _, _) = x
sixth_of_7 :: (a, b, c, d, e, f, g) -> f
sixth_of_7(_, _, _, _, _, x, _) = x
seventh_of_7 :: (a, b, c, d, e, f, g) -> g
seventh_of_7(_, _, _, _, _, _, x) = x
fst_of_8 :: (a, b, c, d, e, f, g, h) -> a
fst_of_8(x, _, _, _, _, _, _, _) = x
snd_of_8 :: (a, b, c, d, e, f, g, h) -> b
snd_of_8(_, x, _, _, _, _, _, _) = x
third_of_8 :: (a, b, c, d, e, f, g, h) -> c
third_of_8(_, _, x, _, _, _, _, _) = x
fourth_of_8 :: (a, b, c, d, e, f, g, h) -> d
fourth_of_8(_, _, _, x, _, _, _, _) = x
fifth_of_8 :: (a, b, c, d, e, f, g, h) -> e
fifth_of_8(_, _, _, _, x, _, _, _) = x
sixth_of_8 :: (a, b, c, d, e, f, g, h) -> f
sixth_of_8(_, _, _, _, _, x, _, _) = x
seventh_of_8 :: (a, b, c, d, e, f, g, h) -> g
seventh_of_8(_, _, _, _, _, _, x, _) = x
eighth_of_8 :: (a, b, c, d, e, f, g, h) -> h
eighth_of_8(_, _, _, _, _, _, _, x) = x
fst_of_9 :: (a, b, c, d, e, f, g, h, i) -> a
fst_of_9(x, _, _, _, _, _, _, _, _) = x
snd_of_9 :: (a, b, c, d, e, f, g, h, i) -> b
snd_of_9(_, x, _, _, _, _, _, _, _) = x
third_of_9 :: (a, b, c, d, e, f, g, h, i) -> c
third_of_9(_, _, x, _, _, _, _, _, _) = x
fourth_of_9 :: (a, b, c, d, e, f, g, h, i) -> d
fourth_of_9(_, _, _, x, _, _, _, _, _) = x
fifth_of_9 :: (a, b, c, d, e, f, g, h, i) -> e
fifth_of_9(_, _, _, _, x, _, _, _, _) = x
sixth_of_9 :: (a, b, c, d, e, f, g, h, i) -> f
sixth_of_9(_, _, _, _, _, x, _, _, _) = x
seventh_of_9 :: (a, b, c, d, e, f, g, h, i) -> g
seventh_of_9(_, _, _, _, _, _, x, _, _) = x
eighth_of_9 :: (a, b, c, d, e, f, g, h, i) -> h
eighth_of_9(_, _, _, _, _, _, _, x, _) = x
ninth_of_9 :: (a, b, c, d, e, f, g, h, i) -> i
ninth_of_9(_, _, _, _, _, _, _, _, x) = x
fst_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> a
fst_of_10(x, _, _, _, _, _, _, _, _, _) = x
snd_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> b
snd_of_10(_, x, _, _, _, _, _, _, _, _) = x
third_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> c
third_of_10(_, _, x, _, _, _, _, _, _, _) = x
fourth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> d
fourth_of_10(_, _, _, x, _, _, _, _, _, _) = x
fifth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> e
fifth_of_10(_, _, _, _, x, _, _, _, _, _) = x
sixth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> f
sixth_of_10(_, _, _, _, _, x, _, _, _, _) = x
seventh_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> g
seventh_of_10(_, _, _, _, _, _, x, _, _, _) = x
eighth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> h
eighth_of_10(_, _, _, _, _, _, _, x, _, _) = x
ninth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> i
ninth_of_10(_, _, _, _, _, _, _, _, x, _) = x
tenth_of_10 :: (a, b, c, d, e, f, g, h, i, j) -> j
tenth_of_10(_, _, _, _, _, _, _, _, _, x) = x
end-proof

endspec
