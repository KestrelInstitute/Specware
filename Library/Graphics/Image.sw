Image qualifying spec 

import Pixel

type Image p  % p should be one of the pixel types

type FileName    = String
type Row         = Nat
type Column      = Nat
type Coordinates = Row * Column

op [p] height : Image p -> Row
op [p] width  : Image p -> Column
op [p] size   : Image p -> Coordinates

op [p] pixelType : Image p -> PixelKind  % result should correspond to p

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  Polymorphic functions for processing all kinds of images.
%%%  These can be used directly.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op [p] getregion (image: Image p) (bottom : Row) (left : Column) (top: Row) (right: Column) : Image p
op [p] putregion (image: Image p) (bottom : Row) (left : Column) (region: Image p) : Image p

op [p] get : Image p -> Coordinates -> p
op [p] put : Image p -> Coordinates -> p -> ()

op [p] map (f : p -> p) (image: Image p) : Image p

op [a,p] foldl (f : a * p -> a) (base: a) (image: Image p) : a
op [a,p] foldr (f : p * a -> a) (base: a) (image: Image p) : a

op [a,p] foldli (f : a * p * Coordinates -> a) (base: a) (image: Image p) : a
op [a,p] foldri (f : p * a * Coordinates -> a) (base: a) (image: Image p) : a

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% The following are designed to ensure that functions passed to higher-order polymorphic 
%%% routines here are type-consistent with the dynamically observed types of the images they
%%% are processing.  (I.e., they implement a poor man's substitute for reified types.)
%%%
%%% Each uses a deliberate pun between the typename used in the return type (e.g. 'Image Gray1') 
%%% and the opname for the first arg to the polymorphic function (e.g. 'Gray1').
%%%
%%% The polymorphic functions use that first argument to enforce dynamic runtime type-checking 
%%% of the actual observed images.
%%%
%%% The monomorphic returned type should (by type contagion) force consistent typing of the 
%%% functions passed to the higher-order functions above (map, foldl, etc.).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Avoid using these functions directly:

op [p] readImageFile  (pixeltype : PixelKind) (filename : FileName) : Image p               % pixeltype (an op) should correspond to p (a pixel type)
op [p] writeImageFile (pixeltype : PixelKind) (filename : FileName) (image : Image p) : ()  % pixeltype (an op) should corrsepond to p (a pixel type)

%%% Instead, use these which are tailored to specific file types:

op readImageFile_SingleFloat  (filename : FileName) : Image SingleFloat = readImageFile SingleFloat filename  
op readImageFile_DoubleFloat  (filename : FileName) : Image DoubleFloat = readImageFile DoubleFloat filename
op readImageFile_Bit1         (filename : FileName) : Image Bit1        = readImageFile Bit1        filename
op readImageFile_Bit2         (filename : FileName) : Image Bit2        = readImageFile Bit2        filename
op readImageFile_Bit4         (filename : FileName) : Image Bit4        = readImageFile Bit4        filename
op readImageFile_Bit8         (filename : FileName) : Image Bit8        = readImageFile Bit8        filename
op readImageFile_Bit16        (filename : FileName) : Image Bit16       = readImageFile Bit16       filename
op readImageFile_Bit32        (filename : FileName) : Image Bit32       = readImageFile Bit32       filename
op readImageFile_GrayFixnum   (filename : FileName) : Image GrayFixnum  = readImageFile GrayFixnum  filename
op readImageFile_GraySingle   (filename : FileName) : Image GraySingle  = readImageFile GraySingle  filename
op readImageFile_GrayDouble   (filename : FileName) : Image GrayDouble  = readImageFile GrayDouble  filename
op readImageFile_RGB4         (filename : FileName) : Image RGB4        = readImageFile RGB4        filename
op readImageFile_RGB8         (filename : FileName) : Image RGB8        = readImageFile RGB8        filename
op readImageFile_RGB16        (filename : FileName) : Image RGB16       = readImageFile RGB16       filename
op readImageFile_RGBsingle    (filename : FileName) : Image RGBSingle   = readImageFile RGBSingle   filename
op readImageFile_RGBdouble    (filename : FileName) : Image RGBDouble   = readImageFile RGBDouble   filename
op readImageFile_RGBA4        (filename : FileName) : Image RGBA4       = readImageFile RGBA4       filename
op readImageFile_RGBA8        (filename : FileName) : Image RGBA8       = readImageFile RGBA8       filename
op readImageFile_RGBA16       (filename : FileName) : Image RGBA16      = readImageFile RGBA16      filename
op readImageFile_RGBASingle   (filename : FileName) : Image RGBASingle  = readImageFile RGBASingle  filename
op readImageFile_RGBADouble   (filename : FileName) : Image RGBADouble  = readImageFile RGBADouble  filename

op writeImageFile_SingleFloat (filename : FileName) (image : Image SingleFloat) : () = writeImageFile SingleFloat filename image
op writeImageFile_DoubleFloat (filename : FileName) (image : Image DoubleFloat) : () = writeImageFile DoubleFloat filename image
op writeImageFile_Bit1        (filename : FileName) (image : Image Bit1)        : () = writeImageFile Bit1        filename image
op writeImageFile_Bit2        (filename : FileName) (image : Image Bit2)        : () = writeImageFile Bit2        filename image
op writeImageFile_Bit4        (filename : FileName) (image : Image Bit4)        : () = writeImageFile Bit4        filename image
op writeImageFile_Bit8        (filename : FileName) (image : Image Bit8)        : () = writeImageFile Bit8        filename image
op writeImageFile_Bit16       (filename : FileName) (image : Image Bit16)       : () = writeImageFile Bit16       filename image
op writeImageFile_Bit32       (filename : FileName) (image : Image Bit32)       : () = writeImageFile Bit32       filename image
op writeImageFile_GrayFixnum  (filename : FileName) (image : Image GrayFixnum)  : () = writeImageFile GrayFixnum  filename image
op writeImageFile_GraySingle  (filename : FileName) (image : Image GraySingle)  : () = writeImageFile GraySingle  filename image
op writeImageFile_GrayDouble  (filename : FileName) (image : Image GrayDouble)  : () = writeImageFile GrayDouble  filename image
op writeImageFile_RGB4        (filename : FileName) (image : Image RGB4)        : () = writeImageFile RGB4        filename image
op writeImageFile_RGB8        (filename : FileName) (image : Image RGB8)        : () = writeImageFile RGB8        filename image
op writeImageFile_RGB16       (filename : FileName) (image : Image RGB16)       : () = writeImageFile RGB16       filename image
op writeImageFile_RGBsingle   (filename : FileName) (image : Image RGBSingle)   : () = writeImageFile RGBSingle   filename image
op writeImageFile_RGBdouble   (filename : FileName) (image : Image RGBDouble)   : () = writeImageFile RGBDouble   filename image
op writeImageFile_RGBA4       (filename : FileName) (image : Image RGBA4)       : () = writeImageFile RGBA4       filename image
op writeImageFile_RGBA8       (filename : FileName) (image : Image RGBA8)       : () = writeImageFile RGBA8       filename image
op writeImageFile_RGBA16      (filename : FileName) (image : Image RGBA16)      : () = writeImageFile RGBA16      filename image
op writeImageFile_RGBASingle  (filename : FileName) (image : Image RGBASingle)  : () = writeImageFile RGBASingle  filename image
op writeImageFile_RGBADouble  (filename : FileName) (image : Image RGBADouble)  : () = writeImageFile RGBADouble  filename image

end-spec
