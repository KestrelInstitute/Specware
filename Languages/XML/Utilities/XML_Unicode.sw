(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  import /Library/IO/Unicode/UnicodeSig
  import /Library/IO/Unicode/UStringAsList

  %% ------------------------------------------------------------------------
  %% Characters:

  def UChar.open_angle   = uchar #<        % "lt" is xml convention, but would cause infix clash with Nat.lt
  def UChar.close_angle  = uchar #>        % for consistency with "open_angle"
  def UChar.amp          = uchar #&        % name chosen to adhere to XML conventions

  def UChar.X            = uchar #X
  def UChar.x            = uchar #x
  def UChar.M            = uchar #M
  def UChar.m            = uchar #m
  def UChar.L            = uchar #L
  def UChar.l            = uchar #l

  def UChar.open_paren   = uchar #(
  def UChar.close_paren  = uchar #)
  def UChar.vertical_bar = uchar #\x7C

  def UChar.equal_sign   = uchar #=
  def UChar.period       = uchar #.
  def UChar.comma        = uchar #,
  def UChar.semicolon    = uchar #;
  def UChar.percent      = uchar #%
  def UChar.double_quote = uchar #\x22
  def UChar.apostrophe   = uchar #\x27     (* single quote *)

  def UChar.colon        = uchar #:
  def UChar.minus        = uchar #-
  def UChar.underbar     = uchar #_

  def UChar.tab          = uchar #\x09     (* = #\t *)
  def UChar.linefeed     = uchar #\x0A     (* = #\n *)
  def UChar.return       = uchar #\x0D     (* = #\r *)
  def UChar.space        = uchar #\x20     (* = #\s *)
  def UChar.newline      = UChar.linefeed  (* = #\n *)

  %% ------------------------------------------------------------------------
  %% Strings:

  def UString.space         = ustring " "

  def UString.open_angle    = ustring "<"   % "lt" is xml convention, but would cause infix clash with Nat.lt
  def UString.close_angle   = ustring ">"   % for consistency with "open_angle"
  def UString.amp           = ustring "&"   % name chosen to adhere to XML conventions

  def UString.open_paren    = ustring "("
  def UString.close_paren   = ustring ")"

  def UString.vertical_bar  = ustring "|"
  def UString.back_slash    = ustring "/"
  def UString.question_mark = ustring "?"

  def UString.equal_sign    = ustring "="

  def UString.period        = ustring "."
  def UString.comma         = ustring ","
  def UString.semicolon     = ustring ";"
  def UString.colon         = ustring ":"

  def UString.percent       = ustring "%"

  def UString.double_quote  = ustring "\""  (* " this comment balances quotes for emacs *)
  def UString.apostrophe    = ustring "'"   (* single quote *)

  %% ------------------------------------------------------------------------

endspec