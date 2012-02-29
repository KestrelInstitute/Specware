%% NOTE: The following files should be kept in sync:
%% Specware4/Library/CGen/CTargetParameters.sw
%% vTPM/CTargetParameters.sw

C qualifying spec

import Library/All

(* See spec CTarget for an explanation of the following items. *)

op CHAR_BIT : Nat = 8

op plainCharsAreSigned : Bool = false

op sizeof_short : Nat =  2
op sizeof_int   : Nat =  4
op sizeof_long  : Nat =  8
op sizeof_llong : Nat = 16

endspec
