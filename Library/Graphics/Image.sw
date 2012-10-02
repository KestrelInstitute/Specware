Image qualifying spec 

import Matrix

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type PixelMode  = | Misc | Bit | Gray | RGB | RGBA

type NumberType = | Nat | Float 

type Image p = {pixel_mode  : PixelMode, 
                number_type : NumberType,
                width       : Nat,
                matrix      : Matrix p}

%% handcoded interface calls this to build image structure:
op [p] mkImage (pixel_mode  : PixelMode, 
                number_type : NumberType,
                width       : Nat,
                matrix      : Matrix p) 
 : Image p = 
 {pixel_mode  = pixel_mode,
  number_type = number_type,
  width       = width,
  matrix      = matrix}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type FileName = String

op [p] readImageFile  (filename : FileName) : Option (Image p)

op [p] writeImageFile (filename : FileName) (image : Image p) : ()  

end-spec
