
Unicode qualifying spec

  import /Library/IO/Primitive/IO

  sort UChar = (Nat | legal_uchar?)  % not much choice here
  sort UChars  = List UChar          % name emphasises list implementation, which facilitates pattern matching
  sort UString                       % probably just UChars, but might want a more compact representation

  def legal_uchar? n = (n < 65536)

  %% ------------------------------------------------------------------------

  op uchar : Char -> UChar

  def uchar = Char.ord

  op print_uchar  : UChar -> String  % may need to encode it as several ascii characters

  %% ------------------------------------------------------------------------

  op string       : UString -> String

  op ustring      : String  -> UString

  op null         : UString

  op null?        : UString -> Boolean
  op non_null?    : UString -> Boolean
  op length       : UString -> Nat

  op ^  infixl 11 : UString * UString -> UString

  op substring?   : UString * UString -> Boolean

  %% op find         : UString -> UString -> Option Nat
  %% op find_pattern : UString -> UString -> Option (Nat * Nat)

  %% ------------------------------------------------------------------------

  op nth  : UString * Nat -> Option UChar

  op all? : (UChar -> Boolean) -> UString -> Boolean

  op in?  : UChar * UString -> Boolean

  %% ------------------------------------------------------------------------

  sort Bytes = List Byte
  sort Byte  = (Nat | byte?)

  def byte? n = (n < 256)

  sort Encoding = UChars -> Bytes   % UTF-8, UTF-16, JIS, etc.
  sort Decoding = Bytes  -> UChars  % UTF-8, UTF-16, JIS, etc.

  def null_encoding (chars : UChars) : Bytes  = chars
  def null_decoding (bytes : Bytes)  : UChars = bytes

  op read_unicode_chars_from_file : Filename * Decoding -> Option UChars

  op write_unicode_chars_to_file  : UChars * Filename * Encoding -> ()

endspec
