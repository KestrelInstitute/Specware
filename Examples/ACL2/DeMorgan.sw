DeMorgan = spec

  import /Library/Base/Empty

  op bnot (x:Boolean) : Boolean = if x then false else true
  op bor (x:Boolean,y:Boolean) : Boolean = if x then true else y
  op band (x:Boolean,y:Boolean) : Boolean = if x then y else false

end-spec