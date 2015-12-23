(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

C qualifying spec

%% import /Library/General/TwosComplementNumber
%% import /Library/General/FunctionExt
%% import /Library/General/OptionExt

(* See spec CTarget for an explanation of the following items. *)

op CHAR_BIT : Nat = 8
proof Isa [simp] end-proof

op plainCharsAreSigned : Bool = false

op sizeof_short : Nat =  2
op sizeof_int   : Nat =  4
op sizeof_long  : Nat =  8
op sizeof_llong : Nat = 16

endspec
