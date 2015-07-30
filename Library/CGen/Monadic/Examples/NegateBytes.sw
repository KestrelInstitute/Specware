NegateBytes = spec
  import /Library/General/BitList

  %% This spec contains a challenge problem for C generation.  The
  %% challenge is to generate C code that implements the Specware
  %% function negateBytes:

  %% Take a list of Bytes and negate each of
  %% them, returning the list of negations.

  op negateBytes (input : Bytes) : Bytes =
    case input of
    | [] -> []
    | hd::tl -> (not hd)::negateBytes tl

  %% The generated C code might look like this:

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

  %% The final theorem proved might look something like this.  The
  %% stubs below need to be filled in!  Eddy can help us better match
  %% this up with his notions:

  type CState
  type CFunction
  %% TODO: What about errors, etc.:
  op runCFunction (f: CFunction, s: CState) : CState


  type Pointer
  op extractBytes (s:CState, ptr:Pointer, len:Nat) : Bytes

  axiom extractBytes_len is
    fa (st:CState, ptr:Pointer, len:Nat)
       length (extractBytes (st, ptr, len)) = len

  %% What happens if we're out of memory ???

  %% Should say that the arrays are allocated and dont overlap, etc.(what else?):
  %% TODO: How to indicate that the arguments on which the function will be 
  %%       invoked are src, dest, and len (they should be on the stack, I guess)?

  op precond (s:CState, src:Pointer, dest:Pointer, len:Nat) : Bool

  op NegateBytes_C : CFunction  %% This is the op to generate!

  axiom negateC_correct is
    fa(s:CState, src:Pointer, dest:Pointer, len:Nat) 
      %% Or use Nat32 instead of Nat?
      precond (s, src, dest, len) =>
        %% Running the function and then extracting the answer:
        extractBytes(runCFunction(NegateBytes_C, s), dest, len) = 
        %% Is the same as extracting the input and then running the spec:
        negateBytes(extractBytes(s,src,len))

  % negateC_correct has to be an axiom, because it is not provable yet
  % it will become provable once we refined everything

end-spec


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% So what we want to have is a pointer (src) pointing at the beginning of the
% input array (list), the intended length of the input list (len), and a 
% pointer (dest) pointing at the beginning of the output array (list).
% After executing the C function the output array should contain the result of 
% negating the bytes of the input array. We don't care about what happens to
% the input bytes in the state as long as we get the correct output. 
% 
% The synthesis will make sure that there are no errors like overlapping arrays,
% out of memory etc. since in this case we wouldn't be able to satisfy the axiom
%
% We will refine until we can prove the axiom with what we have.
% Much will depend on how we model extractBytes but first we worry about the 
% algorithmic structure
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                 
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Eddy's Program Structures for mimicking C
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Program_Structures = spec
  import /Library/General/SizedNats

  op [a,b] FUNBODY (body: a -> a, ret: a -> b) : a -> b 
  =
    fn st -> ret (body st)

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

  op [a] repeat_n (n: Nat) (body: a -> a) : a -> a
  =
    if n = 0 then (fn st -> st) else (fn st -> repeat_n (n-1) body (body st))

  op [a] WHILE (cnd: a -> Bool) 
      (body: a -> a | fa (st) ex (n) ~(cnd (repeat_n n body st))) : a -> a 
  =
    fn st -> if cnd st then WHILE cnd body (body st) else st

  % ------------- the proofs --------------------
    
  proof Isa repeat_n ()
  apply (auto)
  sorry
  termination
  by (relation "measure (\<lambda>(n,body,st). n)", auto)
  end-proof

  proof Isa WHILE ()
  by auto
  termination (* no termination proof of WHILE yet *)
  sorry
  end-proof

    
end-spec

              
               
               
             
 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Specify a stateful version of negateBytes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Stateful = spec
  import Program_Structures
  import NegateBytes 

  op  inp: CState -> Bytes
  op  out: CState -> Bytes
  
  op NegateBytes_C_1 (st: CState)
  :
  { st' : CState  |  out st' = negateBytes (inp st) } 

      
  op init (input : Bytes) : {st:CState | inp st = input}

  op NegateBytes_1 (input : Bytes) : Bytes 
  =  
  FUNBODY (NegateBytes_C_1, out) (init input)

  theorem negateBytes_1_correct is
     fa (input: Bytes) NegateBytes_1 input = negateBytes input

  proof Isa negateBytes_1_correct
  by (simp add: NegateBytes_1_def FUNBODY_def
                init_subtype_constr init_subtype_constr1 
                NegateBytes_C_1_subtype_constr
     )
  end-proof

end-spec




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Refine input / output observers to extracting bytes at a memory position
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


WithPointers = spec
  import Stateful

  % 
  op src : Pointer
  op dst : Pointer
  op len : Nat

  def inp (st:CState) = extractBytes (st, src, len)
  def out (st:CState) = extractBytes (st, dst, len)



end-spec


WithPointers1 = WithPointers
   { at (NegateBytes_C_1, init, NegateBytes_1)  
      { unfold inp
      ; unfold out
      }
   }


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% The above refinement gives us the spec below
% Unfortunately the emmitted proofs don't go through
%
% Let's worry about that later, Isabelle works fine on 
% the spec below
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

WithPointers_by_hand = spec

  import Program_Structures
  import NegateBytes 

  op src : Pointer
  op dst : Pointer
  op len : Nat

  op NegateBytes_C_1 (st: CState)
  :
  { st' : CState  |   extractBytes (st', dst, len)
                    = negateBytes (extractBytes (st, src, len)) } 
  
  op init (input : Bytes) : {st:CState | extractBytes (st, src, len) = input}

  op NegateBytes_1 (input : Bytes) : Bytes 
  =  
  FUNBODY (NegateBytes_C_1, fn st -> extractBytes (st, dst, len)) (init input)

  theorem negateBytes_1_correct is
     fa (input: Bytes) NegateBytes_1 input = negateBytes input

  proof Isa negateBytes_1_correct
  by (simp add: NegateBytes_1_def FUNBODY_def
                init_subtype_constr init_subtype_constr1 
                NegateBytes_C_1_subtype_constr
     )
  end-proof
  
end-spec


% This is close to where we want to be
% We now have to convert the spec of NegateBytes_C_1 into the spec 
% of a CFunction that runCFunction converts into NegateBytes_C_1
% 
% for now we consider runCFunction to be the identity
% 
% And of course we have to synthesize code for NegateBytes_C_1  




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Introduce algorithm structures
%%
%% I need some new theorems about lists for that
%% move these into List.sw later
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


ListThms = spec 

  theorem list_eq_nth is [a]                                     
    fa (l1: List a, l2 : List a)                                 
      (l1 = l2) = (length l1 = length l2                         
                   && (fa (i:Nat) i < length l1 => l1@i = l2@i)) 
                                                                 
  theorem length_map is [a,b]                                    
    fa (f: a -> b, l: List a)                                    
      length (map f l) = length l                                
                                   
  theorem map_nth is [a,b]                                    
    fa (f: a -> b, l: List a, i:Nat)  i < length l =>
      (map f l) @ i = f (l@i)                               

  % ------------- the proofs --------------------
    
   proof Isa list_eq_nth
   by (simp add: list_eq_iff_nth_eq)
   end-proof
   
end-spec 


WithPointers2 = spec
   import WithPointers_by_hand   % or WithPointers1
   import ListThms

   theorem negateBytes_with_map_op is
      fa (bs : Bytes)  negateBytes bs = List.map (Bits.not) bs

  % ------------- the proofs --------------------
    
   proof Isa negateBytes_with_map_op
      by (induct bs, auto)
   end-proof
   
end-spec


% ------------------------------------------------------------
S1 = WithPointers2
   { at (NegateBytes_C_1)     
      { lr list_eq_nth
      ; repeat {lr negateBytes_with_map_op}
      ; lr length_map
      ; repeat {lr extractBytes_len}
      ; lr map_nth
      }                     
   }      


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
