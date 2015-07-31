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

 
  %% This is the op to generate!
  %% Use Nat32 instead of Nat?
  op NegateBytes_C (src:Pointer, dest:Pointer, len:Nat): CFunction  

  % Spec of NegateBytes_C is 
  %  Running the function and then extracting the answer:
  %  Is the same as extracting the input and then running the spec

  axiom negateC_correct is
    fa(s:CState, src:Pointer, dest:Pointer, len:Nat) 
      precond (s, src, dest, len) =>
        extractBytes( runCFunction (NegateBytes_C(src,dest,len), s), dest, len)
        = 
        negateBytes(extractBytes(s,src,len))

end-spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Continue similar to NegateBytes.sw but aim at true top-down development
% and try to avoid Isabelle issues with notation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The axiom negateC_correct is actually a specification of both NegateBytes_C
% and runCFunction. I first have to separate the two 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
Separated = spec
  import NegateBytes 

  op NegateBytes_C_run 
     (st:CState, src:Pointer, dest:Pointer, len:Nat 
     | precond (st, src, dest, len)
     )
     : 
     {st':CState |  extractBytes (st', dest, len)
                  = negateBytes  (extractBytes(st,src,len))
     }

  % We have a derivation for most of NegateBytes_C_run in NegateBytes.sw
  % ust have to do it cleaner

  % this leaves us with the following requirement on NegateBytes_C
  % and runCFunction
  
  axiom negateC_correct2 is
    fa(st:CState, src:Pointer, dest:Pointer, len:Nat) 
      runCFunction (NegateBytes_C(src,dest,len), st)
      =
      NegateBytes_C_run (st, src, dest, len)
  
  % TODO: prove that negateC_correct is now a theorem

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % a trivial solution would be  CFunction = CState -> CState
  % thus runCFunction would become (almost) identity 
  % and  NegateBytes_C (almost) the same as NegateBytes_C_run
  % 
  % This probably not what we want, 
  % rather have CFunction to be a syntactical representation of C code
  % and runCFunction be something similar to "evalProgram" in C.sw
  % This is now completely independent
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
end-spec