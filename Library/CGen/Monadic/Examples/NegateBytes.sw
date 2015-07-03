S1 = spec
  import /Library/General/TwosComplementNumber
  import /Library/General/SizedNats

  op negateByte (n: Nat8) : Nat8 = toNat (not (bits (n,8)))

  %% This spec contains a challenge problem for C generation.  The
  %% challenge is to generate C code that implements the Specware
  %% function negateBytes:

  %% Take a list of Bytes and negate each of
  %% them, returning the list of negations.
  op negateBytes (input : List Nat8) : List Nat8 =
    map negateByte input

  %% The generated C code that we want looks like this

  %% // Assumes src and dest point to arrays of length (at least) len.  
  %% // Assumes no overlap between src and dest.
  %% void negateBytes (unsigned char *src, 
  %%                   unsigned char *dest,
  %%                   unsigned int len) 
  %% {
  %%   unsigned int i;
  %%   i = 0;
  %%   while (i < len) {
  %%     dest[i] = ~src[i]; // Negate the byte
  %%     i = i + 1;
  %%   }
  %% }

end-spec

S2 = spec
  import S1

  (* Type signature that more closely matches the C we want to generate. This
  function says that the "output" of the function is the new value of dest; the
  value of src cannot change. The precondition only worries about the lengths,
  as the overlap conditions are handled by permissions, below. *)
  op negateBytes_Cspec (src : List Nat8, dest : List Nat8, len : Nat16 |
                          len <= length src && len <= length dest) :
    { l:List Nat8 | l = negateBytes (prefix (src, len)) ++ suffix (dest, len) }

end-spec

S3 = spec
  import S2

  op [a] repeat_n (n: Nat) (body: a -> a) : a -> a =
    if n = 0 then (fn st -> st) else (fn st -> repeat_n (n-1) body (body st))

  op [a] WHILE (cnd: a -> Bool) (body: a -> a |
                                   fa (st) ex (n) ~(cnd (repeat_n n body st))) : a -> a =
    fn st -> if cnd st then WHILE cnd body (body st) else st

  op [a,b] withVarDecl (init: b, body : (a*b) -> (a*b)) : a -> a =
    fn st -> (body (st, init)).1

  op [a] BLOCK (fs: List (a -> a)) : a -> a =
    case fs of
      | [] -> (fn st -> st)
      | f::fs' ->
        (fn st -> BLOCK fs' (f st))

  op [a,b] ASSIGN (set: a -> b -> a, val: a -> b) : a -> a =
    fn st -> set st (val st)

  op [a,b] FUNBODY (body: a -> a, ret: a -> b) : a -> b =
    fn st -> ret (body st)

  op plusNat16 (n1 : Nat16, n2 : Nat16 | fitsInNBits? 16 (n1 + n2)) : Nat16 =
    n1 + n2

  (* Now we define negateBytes_Cspec in a way that closely matches the C we want
  to generate; this is stil in progress... *)
  op negateBytes_Cspec (src : List Nat8, dest : List Nat8, len : Nat16 |
                          len <= length src && len <= length dest) : List Nat8 =
    FUNBODY
    (withVarDecl
       (0 : Nat16,
        WHILE
          (fn st -> st.2 < len)
          (BLOCK
             [ASSIGN ((fn st -> fn v ->
                         ((st.1.1, update (st.1.2, st.2, v), st.1.3), st.2)),
                      (fn st -> st.1.1 @ st.2)),
              ASSIGN ((fn st -> fn v -> ((st.1.1, st.1.2, st.1.3), v)),
                      (fn st -> plusNat16 (st.2, 1)))]
             )),
       (fn st -> st.1)) (src,dest,len)

  (* FIXME: still need the statement of correctness (in progress) *)

end-spec
