(*
2007:07:05
AC
A spec of AIDs, a concept used in smart cards.

*)


AID qualifying spec

  import BitSequences

  (* Following ISO 7816-5, an AID (= Application IDentifier) consists of an
  RID (= Resource IDentifier) and a PIX (= Proprietary Identifier eXtension).
  The RID consists of 5 bytes, while the PIX consists of 0 to 11 bytes. *)

  type AID = {rid : {bs : FSeq Byte | length bs = 5},
              pix : {bs : FSeq Byte | length bs <= 11}}

  % flatten AID to one byte sequence:
  op flatten (aid:AID) : {bs : FSeq Byte | length bs <= 16} = aid.rid ++ aid.pix

  % length of (flattened) AID:
  op length (aid:AID) : Nat = length (flatten aid)

  % construct AID from byte sequence (of appropriate length):
  op unflatten (bs: FSeq Byte | length bs <= 16) : AID =
    {rid = prefix(bs,5), pix = removePrefix(bs,5)}

endspec
