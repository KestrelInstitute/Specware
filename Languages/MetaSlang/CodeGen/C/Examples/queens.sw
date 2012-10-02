
spec

  import BitString#IntAsBitString

  op queens: Nat -> Nat
  def queens k =
    let k2bitk = leftShift(One,k-1) in
    queens0(0,0,k,k2bitk,complement(Zero),complement(Zero),complement(Zero))

  def queens0(cnt,currentCol,k,k2bitk,free_rws,free_ups,free_dns) =
    %let _ = writeLine("cnt="^(Integer.toString cnt)^", currentCol="^(Integer.toString currentCol)) in
    if currentCol = k then cnt + 1
    else
      let free_cols = andBits(free_rws, andBits(free_ups, free_dns)) in
      doLoop(cnt,0,k,k2bitk,free_cols,currentCol,free_rws,free_ups,free_dns)

    def doLoop(cnt,col,k,k2bitk,free_cols,currentCol,free_rws,free_ups,free_dns) =
      if col < k then
	let cols_as_bits = leftShift(One,col) in
	let cnt = 
	if notZero(andBits(free_cols, cols_as_bits)) then
	  queens0(cnt,currentCol+1,k,k2bitk,
		  xorBits(free_rws, cols_as_bits),
		  orBits(leftShift( xorBits(free_ups, cols_as_bits), 1), One),
		  orBits(rightShift(xorBits(free_dns, cols_as_bits), 1), k2bitk))
	else cnt
	in
	  doLoop(cnt,col+1,k,k2bitk,free_cols,currentCol,free_rws,free_ups,free_dns)
      else cnt

    def main() =
      let N = 15 in
      let def nlist(n,m) = if n>m then [] else cons(n,nlist(n+1,m)) in
      let indices = nlist(1,N) in
      app (fn(i) ->
	   let cnt = queens i in
	   writeLine("queens("^(Integer.toString i)^") = "^(Integer.toString cnt))
	  ) indices
endspec

