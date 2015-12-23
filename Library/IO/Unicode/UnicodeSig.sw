(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


Unicode qualifying spec

  import /Library/IO/Primitive/IO

  type UChar = (Nat | legal_uchar?)  % not much choice here
  type UChars  = List UChar          % name emphasises list implementation, which facilitates pattern matching
  type UString                       % probably just UChars, but might want a more compact representation

  def legal_uchar? n = (n < 65536)   % actually much more complex than this 
                                     % At least from XML perspective, not all 16 bit values are characters.
                                     % and some characters can be more than 16 bits, 
                                     % From the grammar given in the normative XML web site:
                                     %  Char ::=  #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF] 
                                     %  /* any Unicode character, excluding the surrogate blocks, FFFE, and FFFF. */

  %% ------------------------------------------------------------------------

  op uchar : Char -> UChar

  def uchar = Char.ord

  op print_uchar  : UChar -> String  % may need to encode it, so might need encoding function as first argument
                                     % unless there is a standard Unicode -> ASCII encoding

  %% ------------------------------------------------------------------------

  op string       : UString -> String

  op ustring      : String  -> UString

  op null         : UString

  op null?        : UString -> Bool
  op non_null?    : UString -> Bool
  op length       : UString -> Nat

  op ^  infixl 25 : UString * UString -> UString

  op substring?   : UString * UString -> Bool

  %% op find         : UString -> UString -> Option Nat
  %% op find_pattern : UString -> UString -> Option (Nat * Nat)

  %% ------------------------------------------------------------------------

  op nth  : UString * Nat -> Option UChar

  op all? : (UChar -> Bool) -> UString -> Bool

  op in?  : UChar * UString -> Bool

  %% ------------------------------------------------------------------------

  type Bytes = List Byte
  type Byte  = (Nat | byte?)

  def byte? n = (n < 256)

  type Encoding = UChars -> Bytes   % UTF-8, UTF-16, JIS, etc.
  type Decoding = Bytes  -> UChars  % UTF-8, UTF-16, JIS, etc.

  def null_encoding (chars : UChars) : Bytes  = chars
  def null_decoding (bytes : Bytes)  : UChars = bytes

  op read_unicode_chars_from_file : Filename * Decoding -> Option UChars

  op write_unicode_chars_to_file  : UChars * Filename * Encoding -> ()

endspec
