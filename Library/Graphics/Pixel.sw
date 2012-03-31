Pixel qualifying spec

op mostPositiveFixnum : Nat                          % implementation dependent  (2**29 for SBCL)

type RGB  a = a * a * a                              % in progress: there might not be a MetaSlang type that corresponds to the actual lisp structure
type RGBA a = {red: a, green: a, blue: a, alpha : a} % in progress: there might not be a MetaSlang type that corresponds to the actual lisp structure

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% These are the 21 known pixel types:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type SingleFloat                                     % we should have an IEEE Float spec(!)
type DoubleFloat
type Bit1        = {n : Nat | n < 2**1}
type Bit2        = {n : Nat | n < 2**2}
type Bit4        = {n : Nat | n < 2**4}
type Bit8        = {n : Nat | n < 2**8}
type Bit16       = {n : Nat | n < 2**16}
type Bit32       = {n : Nat | n < 2**32}
type GrayFixnum  = {n : Nat | n <= mostPositiveFixnum}
type GraySingle
type GrayDouble
type RGB4        = RGB  Bit4
type RGB8        = RGB  Bit8
type RGB16       = RGB  Bit16
type RGBSingle   = RGB  SingleFloat
type RGBDouble   = RGB  DoubleFloat
type RGBA4       = RGBA Bit4
type RGBA8       = RGBA Bit8
type RGBA16      = RGBA Bit16
type RGBASingle  = RGBA SingleFloat
type RGBADouble  = RGBA DoubleFloat

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Poor man's type class -- these 21 constructors correspond to the 17 pixel types:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type PixelKind = | SingleFloat 
                 | DoubleFloat 
                 | Bit1       
                 | Bit2       
                 | Bit4       
                 | Bit8       
                 | Bit16      
                 | Bit32      
                 | GrayFixnum  
                 | GraySingle  
                 | GrayDouble  
                 | RGB4        
                 | RGB8        
                 | RGB16       
                 | RGBSingle   
                 | RGBDouble   
                 | RGBA4       
                 | RGBA8       
                 | RGBA16      
                 | RGBASingle  
                 | RGBADouble  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% The low-level implementation could (within lisp) dynamically box and unbox 
%%% each pixel to have an instance of the following type, allowing generic 
%%% metaslang functions to dispatch appropriately, but that would be rather 
%%% expensive, so for now at least, this approach is not used:
%%% 
%%% type Pixel = | SingleFloat SingleFloat
%%%              | DoubleFloat DoubleFloat
%%%              | Gray1       Bit1
%%%              | Gray2       Bit2
%%%              | Gray4       Bit4
%%%              | Gray8       Bit8
%%%              | Gray16      Bit16
%%%              | Gray32      Bit32
%%%              | GrayFixnum  Fixnum
%%%              | GraySingle  SingleFloat
%%%              | GrayDouble  DoubleFloat
%%%              | RGB4        RGB4
%%%              | RGB8        RGB8
%%%              | RGB16       RGB16
%%%              | RGBSingle   RGBSingle
%%%              | RGBDouble   RGBDouble
%%%              | RGBA4       RGBA4
%%%              | RGBA8       RGBA8
%%%              | RGBA16      RGBA16
%%%              | RGBASingle  RGBASingle
%%%              | RGBADouble  RGBADouble
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
