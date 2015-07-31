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

  % ------------------------------------------------------------------------------

  
  proof Isa negateByte_Obligation_subtype
  by (simp add: Nat__fitsInNBits_p_def)
  end-proof
  
  proof Isa negateByte_Obligation_subtype0
  by (simp add: Nat__fitsInNBits_p_def length_greater_0_iff)
  end-proof
  
  proof Isa negateByte_Obligation_subtype1
  apply (simp add: Nat__fitsInNBits_p_def length_greater_0_iff)
  apply (cut_tac bs = "not_bs (toBits (n, 8))" in Bits__toNat_bound2)
  apply (simp add: Nat__fitsInNBits_p_def length_greater_0_iff, simp)
  end-proof
end-spec

S2 = spec
  import S1

  (* Type signature that more closely matches the C we want to generate. This
  function says that the "output" of the function is the new value of dest; the
  value of src cannot change. The precondition only worries about the lengths,
  as the overlap conditions are handled by permissions, below. *)
  op negateBytes_Cspec (source : List Nat8, dest : List Nat8, size : Nat16 |
                        size <= length source && size <= length dest):
    { l:List Nat8 | l = negateBytes (prefix (source, size)) ++ removePrefix (dest, size) }
  

end-spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Eddy's Program Structures for mimicking C
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Program_Structures = spec
  import /Library/General/SizedNats

  op [a] repeat_n (n: Nat) (body: a -> a) : a -> a
  =
    if n = 0 then (fn st -> st) else (fn st -> repeat_n (n-1) body (body st))

  op [a] WHILE (cnd: a -> Bool) 
      (body: a -> a | fa (st) ex (n) ~(cnd (repeat_n n body st))) : a -> a 
  =
    fn st -> if cnd st then WHILE cnd body (body st) else st

  op [a,b] withVarDecl (init: b, body : (a*b) -> (a*b)) : a -> a 
  =
    fn st -> (body (st, init)).1

  op [a] BLOCK (fs: List (a -> a)) : a -> a 
  =
    case fs of
      | [] -> (fn st -> st)
      | f::fs' ->
        (fn st -> BLOCK fs' (f st))

  op [a,b] ASSIGN (set: a -> b -> a, val: a -> b) : a -> a 
  =
    fn st -> set st (val st)

  op [a,b] FUNBODY (body: a -> a, ret: a -> b) : a -> b 
  =
    fn st -> ret (body st)

  op plusNat16 (n1 : Nat16, n2 : Nat16 | fitsInNBits? 16 (n1 + n2)) : Nat16 
  =
    n1 + n2

  % ------------- the proofs --------------------
    
  proof Isa repeat_n ()
  apply (auto)
  sorry
  termination
  by (relation "measure (\<lambda>(n,body,st). n)", auto)
  end-proof

  proof Isa WHILE ()
  by auto
  termination (* no generic termination of WHILE *)
  sorry
  end-proof

    
end-spec


% ------------------------------------------------------------
% Introduce abstract state, using observers
% ------------------------------------------------------------

S3 = spec
  import Program_Structures
  import S2

  type State
  op  src: State -> List Nat8
  op  dst: State -> List Nat8
  op  len: State -> Nat16
  op  ret: State -> List Nat8 
  
  def ret (st:State)  = dst st 
    
  op init (source : List Nat8, dest : List Nat8, size : Nat16) :
     {st:State | src st = source && dst st = dest && len st = size}

  op negateBytes_1  (st:State | len st <= length (src st) && len st <= length (dst st))
  :
  { st' : State 
  |     len st' = len st
     && src st' = src st
     && dst st' = negateBytes (prefix (src st, len st)) ++ removePrefix (dst st, len st)
  }
    
  op negateBytes_Cspec (source : List Nat8, dest : List Nat8, size : Nat16 |
                        size <= length source && size <= length dest): List Nat8
  =  
  FUNBODY (negateBytes_1, ret) (init (source,dest,size))

  % ------------- the proofs --------------------
    
  proof Isa negateBytes_Cspec_Obligation_subtype
  apply (frule_tac source=source in init_subtype_constr, simp_all)
  apply (frule_tac source=source in init_subtype_constr1, simp_all)
  apply (frule_tac source=source in init_subtype_constr2, simp_all)
  apply (frule_tac source=source in init_subtype_constr3, simp_all)
  apply (frule negateBytes_1_subtype_constr, simp_all) 
  apply (frule negateBytes_1_subtype_constr1, simp_all) 
  apply (frule negateBytes_1_subtype_constr2, simp_all) 
  apply (simp add: FUNBODY_def ret_def)
  end-proof
end-spec

% ------------------------------------------------------------
% Refine map to while
% ------------------------------------------------------------

ListThms = spec % Theorems that should be included in List.sw

theorem list_eq_nth is [a]
  fa (l1: List a, l2 : List a)
    (l1 = l2) = (length l1 = length l2 && (fa (i:Nat) i < length l1 => l1@i = l2@i))

theorem map_prefix is [a,b]
  fa (f: a -> b, l: List a, n:Nat)  n <= length l =>
    map f (prefix (l, n)) = prefix (map f l, n) 

theorem length_append is [a]
  fa (l1: List a, l2: List a) 
    length (l1 ++ l2) = length l1 + length l2

theorem length_map is [a,b]
  fa (f: a -> b, l: List a)  
    length (map f l) = length l

% wichtig und aehnliches    len <= ... -> len pre ++ suf b = len b
  % ------------- the proofs --------------------
    
   proof Isa list_eq_nth
   by (simp add: list_eq_iff_nth_eq)
   end-proof
   
   proof Isa map_prefix
   by (simp add: take_map)
   end-proof
end-spec 

% ------------------------------------------------------------
S4 = spec
   import S3
   import ListThms

end-spec

% ------------------------------------------------------------
S5a = S4
   { at (negateBytes_1)     
      { move [f, n, f, n]
      ; lr list_eq_nth
      }                     
   }      
% ------------------------------------------------------------
S5 = S4
   { at (negateBytes_1)     
      { unfold negateBytes  
      ; unfold ret
      ; simplify
      ; lr map_prefix
      ; move [f, n, f, n]
      ; lr list_eq_nth
      ; move w 
      ; lr length_append
      ; rl map_prefix
      ; lr length_map
      ; lr length_prefix
      ; lr length_removePrefix         
      }                     
   }       
   % --------------------------------------------------------------------
   % transformation fails to emit the correct proof
   %
   % handish proof is
   %
   % by (simp add: map_prefix negateBytes_def)
    % --------------------------------------------------------------------

    %  ... und danach muss ich es wieder zuruecktransformieren ... nicht unbedingt ???
    % next: fa i. dst'[i] = ( +++ )[i]
    %       --> fa i<len. dst'[i] = neg src [i] && fa i> len dst'[i] = dst[i]
    % need thms about nth, prefix, removePrefix, map, append
    %
    % specify generic while_bound:
    %    l' = [i=0; WHILE i < bound do x[i] = f (a[i]) end; return x] (l)
    %    =>
    %    fa i<bound l'[i] = f(l,a[i]) && fa i > bound l[i] = l[i]
    % 
    % this gives an algorithm scheme for while generation
    
S6 = transform S5 by {finalizeCoType(State)}
   % --------------------------------------------------------------------
   % transformation fails to emit the correct proof
   %
   % handish proof is a lot of work
   % --------------------------------------------------------------------
   

 
   
   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Eddy's handwiritten solution
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  

S_Eddy = spec
  import Program_Structures
  import S2

  (* Now we define negateBytes_Cspec in a way that closely matches the C we want
  to generate; this is stil in progress... *)
  op negateBytes_Cspec1 (src : List Nat8, dest : List Nat8, len : Nat16 |
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Below is a semantic object for Eddy's C generator that shows what the final
%% program should look like at the end of the derivation (before CGen)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

S_final = spec
  import S3
  import /Library/CGen/Monadic/C_DSL
  %%import /Library/CGen/Monadic/GenerateC

  op negateBytes_obj : ExtDecl =
    FUNCTION_m (TN_void, "negateBytes",
                [(TN_pointer TN_uchar, "src"),
                 (TN_pointer TN_uchar, "dest"),
                 (TN_uint, "len")],
              BLOCK_m ([(TN_uint, "i")],
                       [ASSIGN_m (LVAR_m "i", ICONST_m "0"),
                        WHILE_m (LT_m (VAR_m "i", VAR_m "len"),
                                 BLOCK_m
                                   ([],
                                [ASSIGN_m (LSUBSCRIPT_m (VAR_m "dest", VAR_m "i"),
                                           NOT_m (SUBSCRIPT_m (VAR_m "src", VAR_m "i"))),
                                 ASSIGN_m (LVAR_m "i", ADD_m (VAR_m "i", ICONST_m "1"))]))
                     ]))
   

  (* This is the specification for the syntax, in the form of a top-level
  external declaration, whose semantics equals copyBytes *)
  op negateBytes_C : { d:TranslationUnitElem | evalTranslationUnitElem d = negateBytes_obj }

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Need to load lisp for GenerateC.sw before running this!
% ----------------------------------------------------------------------
% NegateBytes_impl =
% transform NegateBytes_spec by
%   { at negateBytes_C { unfold negateBytes; generateC}
%   ; makeDefsFromPostConditions [negateBytes_C]
%   }
% 
% Examples_printed = spec
%   import Examples_impl, CPrettyPrinter
% 
%   op negateBytes_String : String = printTranslationUnitToString [negateBytes_C]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

          end-spec


          

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: Fill the gap between S2 and the semantic object in S_final.
%
% 
% STEPS:
% 
% 1. a handish derivation in Specware
% 2. formal proofs in Isabelle
% 3. Transformations that construct both
%
% mimic the steps in acl2, see README-acl2 in TCPcrypt
% ------------------------------------------------------------------------------
% 
% Refinement steps (one spec each)
% 
% - Add state: op -> stateful op where we use (L1 := map f L2) st
% 
% - refine the recursion into a while loop (tail recursion seems to be closer)
%   stateful map -> stateful while (simulate if Eddy's version doesn't help)
%
% - DTRE: refine data type from list to array (weakening types)
%    stateful list -> stateful array via
%   Use conversions between array and list and go on from there.
%   i.e. specify f list -> arr2list (f-arr (list2arr) list
%        and then figure out f-arr
%   then convert generatete stateful while to arrays accordingly
% - Later represent arrays via pointers (another DTRE)
% 
% Automate these steps
% - First proof thms about the whole
% - create specware transformation for that (with proof emission)
% 
%   
% We have no transforms for most of these steps so it has to be a refine def
%   
%   
%   in ACL2 they have macros for algorithm theories and the like in MUSE
%   look at MUSE Derivations / ACL2
%   
% - getting full proofs is what we eventually need
%  
% - need to prove that memory bounds are kept etc. loop invariants 
%   Complain if anything makes no sense
% 
%

% I need something like
% 
% L1 = listmap f L2
% <=>
% forall i L1[i] = f(L[i])
% <=>
% L1 is the result of
% 
% i:-=0; while i<len {L1[i] := l[i]}
% 
% where len  = length L
%

% ----------------------------------------------------------------------------
