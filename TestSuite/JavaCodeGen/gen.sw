G = let GO = spec def package = "gcd" endspec in
  generate java GCD with GO

F = let FO = spec def package = "factorial" endspec in
  generate java Factorial with FO

P = let PO = spec def package = "points" endspec in
  generate java Points with PO

L = let LO = spec def package = "lists" endspec in
  generate java Lists with LO

M = let MO = spec def package = "mergesort" endspec in
  generate java MergeSort with MO

E = let EO = spec def package = "expressions" endspec in
  generate java Expressions with EO

H = let HO = spec def package = "higherorder" endspec in
  generate java HigherOrder with HO

%S = let SO = spec def package = "setsaslists" endspec in
%  generate java SetsAsLists with SO

T = let TO = spec def package = "tutorial" endspec in
  generate java tutorial/MatchingRefinements#FindMatches with TO

B = let BO = spec def package = "bitstrings" endspec in
  generate java bitstrings/BitStringRef with BO
