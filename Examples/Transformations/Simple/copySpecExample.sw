(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Example application of a trivial identity transformation on specs.

A = spec
  op f : Nat
end-spec

%% Creates spec B, identical to spec A.
B = A{copySpec}