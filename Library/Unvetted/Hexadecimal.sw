(*
2005:10:18
AC

Currently Metaslang does not feature hexadecimal literals to denote natural
numbers. This spec ameliorates that problem by providing the capability to
write hexadecimal numbers in the form of a list of hexadecimal digits. This
leverages Metaslang's convenient built-in syntax for lists. Using this spec,
the natural number whose hexadecimal representation is CA53FE can be written
as hex [C,A,5,3,F,E].


ISSUE:

Op hex can be made more efficient by making it tail-recursive. But we have
favored specification clarity vs. efficiency. Indeed, the more efficient
version should be obtained as a refinement of the op given in this spec.

*)


Hex qualifying spec

  (* The following type captures a hexadecimal digit as the natural numbers 0
  thru 15. The first ten, i.e. 0 thru 9, are indeed the first ten hexadecimal
  digits. The last six, i.e. 10 thru 15, are actually the values of the last
  six hexadecimal digits. *)

  type HexDigit = {x : Nat | x < 16}

  (* The following constant definitions identify the last six actual
  hexadecimal digits, i.e. A thru F, with the last six hexadecimal digits
  introduced by the previous type. *)

   op A : HexDigit
  def A = 10

   op B : HexDigit
  def B = 11

   op C : HexDigit
  def C = 12

   op D : HexDigit
  def D = 13

   op E : HexDigit
  def E = 14

   op F : HexDigit
  def F = 15

  (* A hexadecimal number is a non-empty list of digits. An empty list does
  not really make sense. *)

  type HexNumber = {digits : List HexDigit | ~ (null digits)}

  (* The following function maps such a list to its numeric value, which is a
  natural number. *)

   op hex : HexNumber -> Nat
  def hex hexNo =
    if length hexNo = 1 then hd hexNo % only member
    else hex (butLast hexNo) * 16 + last hexNo

  (* At this point, the hexadecimal number CA53FE can be written as

    hex [C,A,5,3,F,E]

  Of course, the number can also be written as hex [12,10,5,3,15,14], but that
  form would mostly defeat the purpose of this spec. *)

endspec
