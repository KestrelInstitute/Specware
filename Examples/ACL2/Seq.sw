spec

type Seq a = 
  | SeqNil 
  | SeqCons a * (Seq a)

op [a] SeqAppend (x:Seq a, y:Seq a) : Seq a =
case x of
  | SeqNil -> y
  | SeqCons (hd,tl) -> SeqCons (hd, SeqAppend (tl, y)) 

op [a] SeqRev (x:Seq a) : Seq a =
case x of
  | SeqNil -> SeqNil
  | SeqCons (hd,tl) -> SeqAppend (SeqRev tl, SeqCons (hd,SeqNil))

end-spec