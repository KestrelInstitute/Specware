Pixel qualifying spec

type SingleFloat % ?
type DoubleFloat % ?

op mostPositiveFixnum : Nat % implementation dependent  (2**29 for SBCL)

type Bit1   = {n : Nat | n < 2**1}
type Bit2   = {n : Nat | n < 2**2}
type Bit4   = {n : Nat | n < 2**4}
type Bit8   = {n : Nat | n < 2**8}
type Bit16  = {n : Nat | n < 2**16}
type Bit32  = {n : Nat | n < 2**32}
type Fixnum = {n : Nat | n <= mostPositiveFixnum}

type RGB  a = {red: a, green: a, blue: a}
type RGBA a = {red: a, green: a, blue: a, alpha : a}

type Pixel =
  | Single      SingleFloat
  | Double      DoubleFloat
      
  | Gray1       Bit1
  | Gray2       Bit2
  | Gray4       Bit4
  | Gray8       Bit8
  | Gray16      Bit16
  | Gray32      Bit32
  | GrayFixnum  Fixnum
  | GraySingle  SingleFloat
  | GrayDouble  DoubleFloat

  | RGB4        RGB Bit4
  | RGB8        RGB Bit8
  | RGB16       RGB Bit16
  | RGBsingle   RGB SingleFloat
  | RGBdouble   RGB DoubleFloat

  | RGBA4       RGBA Bit4
  | RGBA8       RGBA Bit8
  | RGBA16      RGBA Bit16
  | RGBASingle  RGBA SingleFloat
  | RGBADouble  RGBA DoubleFloat

end-spec
