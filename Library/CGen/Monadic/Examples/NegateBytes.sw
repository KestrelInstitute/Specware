(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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

  % ---------------------------------------------

  theorem negateBytes_1_correct is
     fa (input: Bytes) NegateBytes_1 input = negateBytes input

  % ------------- the proofs --------------------

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

  % To be precise we would have to make src,dst, and len input parameters of 
  % the C program NegateBytes_C_1 
  %
  % The axiom negateC_correct needs to be modified accordingly
  %
  % I'll deal with that later


  op NegateBytes_C_1 (st: CState)
  :
  { st' : CState  |   extractBytes (st', dst, len)
                    = negateBytes (extractBytes (st, src, len)) } 
  
  op init (input : Bytes) : {st:CState | extractBytes (st, src, len) = input}

  op NegateBytes_1 (input : Bytes) : Bytes 
  =  
  FUNBODY (NegateBytes_C_1, fn st -> extractBytes (st, dst, len)) (init input)

  % ---------------------------------------------

  theorem negateBytes_1_correct is
     fa (input: Bytes) NegateBytes_1 input = negateBytes input

  % ------------- the proofs --------------------

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
%% Prepare the introduction of algorithmic structures by switching from a
%% global view (list equality) in the spec of NegateBytes_C_1 to a local one 
%% (component-wise equality) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% ------------------------------------------------------------
% I need some new theorems about lists for that
% move these into List.sw later
% ------------------------------------------------------------
ListThms = spec 

  theorem list_eq_nth is [a]                                     
    fa (l1: List a, l2 : List a)                                 
      (l1 = l2) = (length l1 = length l2                         
                   && (fa (i:Nat) i < length l2 => l1@i = l2@i)) 
                                                                 
  theorem length_map is [a,b]                                    
    fa (f: a -> b, l: List a)                                    
      length (map f l) = length l                                
                                   
  theorem map_nth is [a,b]                                    
    fa (f: a -> b, l: List a, i:Nat)  i < length l =>
      map f l @ i = f (l@i)                               
        
  % ------------- the proofs --------------------
    
   proof Isa list_eq_nth
   by (simp add: list_eq_iff_nth_eq)
   end-proof
   
end-spec 


% ------------------------------------------------------------


GlobalView = spec
   import WithPointers_by_hand   % or WithPointers1
   import ListThms

   theorem negateBytes_with_map_op is
      fa (bs : Bytes)  negateBytes bs = List.map (Bits.not) bs
         
  % Specware doesn't rewrite with the precondition
  % I'll worry about this later and drop it for now

  theorem map_nth2 is [a,b]
    fa (f: a -> b, l: List a, i:Nat)  % i < length l =>
      map f l @ i = f (l@i)    
      
  % ------------- the proofs --------------------
    
   proof Isa negateBytes_with_map_op
      by (induct bs, auto)
   end-proof
   
end-spec


% ------------------------------------------------------------


LocalView = GlobalView
   { at (NegateBytes_C_1)     % The order of rewrites is crucial 
      { lr negateBytes_with_map_op
      ; lr list_eq_nth
      ; repeat {lr length_map}
      ; lr map_nth2
      ; repeat {lr extractBytes_len}
      ; SimpStandard
      }                     
   }      


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Refine CState and extractBytes, introduce arrays as structurs on CState
%%
%% We make state a map from addresses to bytes 
%% This permits direct access and updates 
%% - pointers will become addresses
%% - extractBytes will extract a list of bytes beginning at an address
%% - arrays are an auxiliary construct 
%%   modelled as a submap of a given length beginning at an address
%%
%% TODO: deal with addresses that are out of range
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

WithCState = spec
  import LocalView
  import /Library/General/Map

  type Address = Nat % Nat32 ?? I need to be able to add
  
  type CState  = Map (Address, Byte)
  type Pointer = Address

  
  op get (st:CState) (addr:Address): Byte            
  = st @ addr
  op :=  ((st:CState, addr:Address), val:Byte) infixl 20 : CState
  = update st addr val


  % get requires addr to be in range --> Isabelle obligations
    
  op interval (start:Address) (howmany:Nat) : List Address
  =
    if howmany = 0 
       then [] 
       else start :: (interval (start+1) (howmany-1))
  
  def extractBytes (st, ptr, len) = map (get st) (interval ptr len)
  
  % ------------------------------------------------
  % Lifting a function to a state based one

  op [a] lift(f:a->a) : (CState -> a) -> (CState -> a)
  = 
       (fn var -> fn st -> f (var st))

  % ------------------------------------------------
  % Variables of type Nat ... this is not clean yet, since we only have Nat8
  % if we convert bytes to Nat
  %
  % I should make this polymorphic ... later
  %
  % I prefix ops on natvars with a @

  type NatVar = Pointer   % should that be CState -> Nat ???
      
  op @! (st:CState, i:NatVar) infixl 20 : Nat         = toNat (st@i)
  
  % --------------------------------

  op @: (i:NatVar)                   : CState -> Nat  = fn st -> st@!i

  op @< (i:NatVar, j:Nat) infixl 20  : CState -> Bool = fn st -> st@!i < j

  op @+ (i:NatVar, j:Nat)  infixl 20 : CState -> Nat  = fn st -> st@!i + j

  op @0                              : CState -> Nat  = fn st -> 0
  
  op @= (i:NatVar, val:CState->Nat) infixl 20 : CState -> CState 
  =
    fn st -> (st, i) := byte (val st)
  

  % ----------------------------------------------------
  % I should make this polymorphic, not specific to bytes
  %
  % I prefix ops on arrays with a $
  % ----------------------------------------------------

  type Array = Pointer % Right now we're missing the bounds
                       % add this later
  
  op $! ((st:CState, a:Array), i:Nat) infixl 20 : Byte = get st (a+i)
  
  % --------------------------------

  op $: (a:Array, i:Nat) infixl 20 : CState -> Byte = fn st ->  st @ (a+i)
  
  op $= ((a:Array, i:NatVar), var:CState->Byte) infixl 20 : CState -> CState
  =
   fn st -> (st, a+(st@!i)) := var st
  
  % ---------------------------------------------
  
  theorem interval_nth is
    fa (start:Address, howmany:Nat, i:Nat) % i < howmany =>
       interval start howmany @ i = start + i

end-spec



WithCState1 = WithCState
   { at (NegateBytes_C_1)  
      { repeat {unfold extractBytes}
      ; repeat {lr map_nth2}
      ; repeat {lr interval_nth}
      ; repeat {fold $!}        
      }
   ; at (init)
      { unfold extractBytes
      }
   }





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Introduce algorithm structures
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% so far I only have a spec with quantifiers over list components, 
% not the algorithmic structure for determining it.

WhileSemantics = spec
   import WithCState1
    
    op i : NatVar % must declare this IN the program, not globally
                  % need a variant of withVarDecl for that

    theorem WHILE_simple_array is
    fa (st:CState ,st':CState, a:Array, b:Array, lg:Nat, f:Byte->Byte)
       
      (st' = 
        BLOCK 
         [ i @= @0,
          WHILE ( i @< lg)
                (BLOCK [ (b,i) $= (lift f) (a$:i), 
                         i @= (i @+ 1)
                       ]
                )
         ] st)
       =>
      (fa(i:Nat) i<lg => (st',b)$!i  =  f ((st,a)$!i))

  % ------------- the proofs --------------------
    
end

WhileSemantics1 = WhileSemantics 
   { at (NegateBytes_C_1)  
      { strengthen WHILE_simple_array
      ; lr _.eta           % not sure why I need to qualify this
      }
   }


GetAlgorithm = transform WhileSemantics1 by {finalizeCoType(CState)}

   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% The above refinement gives us the spec below
% Unfortunately the emmitted proofs don't go through
%
% On top of that Isabelle has severe problems with the 
% translated infix notations. I'll worry about this later.
% First let's see if the refinement goes through. 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


WhileSemantics_by_hand = spec
  import WhileSemantics 

  refine def NegateBytes_C_1 (st: CState) 
  =
    (BLOCK 
         [ i @= @0,
          WHILE ( i @< len)
                (BLOCK [ (dst,i) $= (lift Bits.not) (src$:i), 
                         i @= (i @+ 1)
                       ]
                )
         ]
        ) st
end-spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
