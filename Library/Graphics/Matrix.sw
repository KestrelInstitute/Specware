Matrix qualifying spec 

type Matrix a

type Index  = Nat
type Indices = List Index

op [a] dimensions : Matrix a -> Indices

op [a] uniformMatrix (dimensions : Indices) (initial_value : a) : Matrix a

op [a] getRegion (matrix: Matrix a) (bottom : Indices) (top : Indices) : Matrix a
op [a] putRegion (matrix: Matrix a) (bottom : Indices) (top : Indices) (region: Matrix a) : Matrix a

op [a] get : Matrix a -> Indices -> a
op [a] put : Matrix a -> Indices -> a -> ()

op [a,b] map (f : a -> b) (matrix: Matrix a) : Matrix b

op [a,b] foldl (f : b * a -> b) (base: b) (matrix: Matrix a) : b
op [a,b] foldr (f : a * b -> b) (base: b) (matrix: Matrix a) : b

op [a,b] foldli (f : Indices * b * a -> b) (base: b) (matrix: Matrix a) : b
op [a,b] foldri (f : Indices * a * b -> b) (base: b) (matrix: Matrix a) : b

end-spec
