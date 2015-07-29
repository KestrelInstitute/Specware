spec
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

  %% Should say that the arrays are allocated and dont overlap, etc. (what else?):
  %%TODO: How to indicate that the arguments on which the function will be invoked
  %% are src, dest, and len (they should be on the stack, I guess)?
  op precond (s:CState, src:Pointer, dest:Pointer, len:Nat) : Bool

  op NegateBytes_C : CFunction  %% This is the op to generate!

  theorem negateC_correct is
    fa(s:CState, src:Pointer, dest:Pointer, len:Nat) 
      %% Or use Nat32 instead of Nat?
      precond (s, src, dest, len) =>
        %% Running the function and then extracting the answer:
        extractBytes(runCFunction(NegateBytes_C, s), dest, len) = 
        %% Is the same as extracting the input and then running the spec:
        negateBytes(extractBytes(s,src,len))

end-spec