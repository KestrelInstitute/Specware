Image qualifying spec 

import Pixel

type FileName    = String
type Image
type Row         = Nat
type Column      = Nat
type Coordinates = Row * Column

op height : Image -> Row
op width  : Image -> Column
op size   : Image -> Coordinates

op get    : Image -> Coordinates -> Pixel
op put    : Image -> Coordinates -> Pixel -> ()

op getregion (image: Image) (bottom : Row) (left : Column) (top: Row) (right: Column) : Image
op putregion (image: Image) (bottom : Row) (left : Column) (region: Image) : Image

op map (f : Nat -> Nat) (image: Image) : Image

op [a] foldl (f : a * Pixel -> a) (base: a) (image: Image) : a
op [a] foldr (f : Pixel * a -> a) (base: a) (image: Image) : a

op [a] foldli (f : a * Pixel * Coordinates -> a) (base: a) (image: Image) : a
op [a] foldri (f : Pixel * a * Coordinates -> a) (base: a) (image: Image) : a

%% might want routines to process subregions

op readImageFile (filename : FileName) : Image
op writeImageFile (filename : FileName) (image : Image) : ()

end-spec
