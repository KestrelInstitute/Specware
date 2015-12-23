(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* The following specs contain some examples that should be handled by gen-c-thin.

The user should tell the C code generator which type(s) and op(s) code should be
generated from, and the C code generator should generate code for them, along
with those that they depend on (recursively), but ignore all other types and
ops. 

*)



Example1 = E1 qualifying spec
import CTarget

type Matrix_2_4 = (Array (Array Sint | ofLength? 4) | ofLength? 2)
% typedef int Matrix_2_4[2][4];

endspec


%TODO change gen-c-thin to preserve the order of these in the generated file
Example2 = E2 qualifying spec
import CTarget

type Point2D = {x:Slong, y:Slong}
% typedef struct {long x; long y;} Point2D;

type Point3D = {x:Sllong, y:Sllong, z:Sllong}
% typedef struct {long long x; long long y; long long z;} Point3D;

endspec



Example3 = E3 qualifying spec
import CTarget

type Vector_0 = (Array Uint | ofLength? 0)
% reject

endspec



Example4 = E4 qualifying spec
import CTarget

import Example2 % points 2D and 3D

type Line2D = {startp:Point2D, endp:Point2D}
% typedef struct {Point2D endp; Point2D startp;} Line2D;

type Curve3D_10pts = (Array Point3D | ofLength? 10)
% typedef Point3D Curve3D_10pts[10];

type CurveAndLine = {curve:Curve3D_10pts, line:Line2D}
% typedef struct {Curve3D_10pts curve; Line2D line;} CurveAndLine;

endspec



Example5 = E5 qualifying spec
import CTarget

type T? = Uint
% reject

endspec



Example6 = E6 qualifying spec
import CTarget

import Example1 % matrix 2x4

type Matrix_2_4 = (Array (Array Slong | ofLength? 4) | ofLength? 2)
% reject, or disambiguate with E1.Matrix_2_4

endspec



Example7 = E7 qualifying spec
import CTarget

type T = Byte
% reject -- Byte not defined in terms of C types

endspec



Example8 = E8 qualifying spec
import CTarget

op f (x:Sshort) : Slong = slongOfSint (-_1_sint (sintOfSshort x))
% long f(short x) { return (-x); }

proof isa E8__f_Obligation_subtype
  apply (drule C__sint_range, auto)
  apply (subst C__sintOfSshort_def, subst C__mathIntOfSint_sintOfMathInt)
  apply (erule C__sintOfSshort_Obligation_subtype)
  apply (drule C__sshort_range, simp)
end-proof

endspec


Example9 = E9 qualifying spec
import CTarget

import Example4 % curves, lines, points

op g (cal:CurveAndLine) : Sllong = (cal.curve @_sint (sintConstant 4 hex)).z
% long long g(CurveAndLine cal) { return cal.curve[0x4].z; }

proof Isa E9__g_Obligation_subtype0
  apply (auto simp add: C__sintConstant_def)
  (** can't prove the rest. Operation g is not well-typed.
      We lack information about the number of components of cal which must be 
      at least 4 **)
  sorry
end-proof

endspec



Example10 = E10 qualifying spec
import CTarget

op h () : Ushort = ushortOfUint (uintConstant 0 dec)
% unsigned short h (void) { return 0; }  % TODO, do we want to explicitly cast the 0 to unsigned short?  The current C generator does so.

endspec



Example11 = E11 qualifying spec
import CTarget

op k () : Ullong = ullongConstant 7 dec
% unsigned long long k(void) { return 7ULL; }

endspec



Example12 = E12 qualifying spec
import CTarget

op k12 (i : Uint, j : Uint) : Ullong = 
  if test ((uintConstant 10 oct) <_uint i) && test (i <_uint j) && test (j <_uint (uintConstant 100 hex)) then
    (ullongOfUint (i *_uint j)) *_ullong ullongConstant 7 dec
  else
    (ullongOfUint (i *_uint (j *_uint uintConstant 7 dec)))

endspec



Example13 = E13 qualifying spec
import CTarget

op k13 (i : Uint, j : Uint) : Uint = 
  if test (i ==_uint (uintConstant 0 dec)) then
    (i *_uint j) *_uint (i *_uint j)
  else if test (i ==_uint (uintConstant 1 dec)) then
    (i *_uint j) *_uint (i +_uint j)
  else if test (i ==_uint (uintConstant 2 dec)) then
    (i *_uint j) +_uint (i *_uint j)
  else if test (i ==_uint (uintConstant 3 dec)) then
    (i *_uint j) +_uint (i +_uint j)
  else if test (i ==_uint (uintConstant 4 dec)) then
    (i +_uint j) *_uint (i *_uint j)
  else if test (i ==_uint (uintConstant 5 dec)) then
    (i +_uint j) *_uint (i +_uint j)
  else if test (i ==_uint (uintConstant 6 dec)) then
    (i +_uint j) +_uint (i *_uint j)
  else 
    (i +_uint j) +_uint (i +_uint j)

endspec



Example14 = E14 qualifying spec
import CTarget
op foo (x:Uint) : Uint
endspec
%% The C generator should generate a declaration in the .h file for the
%% undefined function foo (and nothing in the .c file).
%% Current output (in .h file):
%% extern unsigned int foo (unsigned int x);
%% Is the extern needed?



Example15 = E15 qualifying spec
import CTarget
op bar (x:Sint) : Sint = sint0
endspec
%% The C generator should give an error, because sint0 is a function that is not
%% in the subset we are going to translate. TODO if the C generator hits an op from C target that we do not plan to translate, perhaps it should stop its slicing?



Example16 = E16 qualifying spec
import CTarget
op bar : Uint = (uintConstant 0 dec)
endspec
% TODO Should this be translated as a constant or a 0-ary function?
%unsigned int bar = 0;
% or:
%unsigned int bar () {return 0;}


Example17 = E17 qualifying spec
import CTarget
op bar : Uint = (uintConstant 0 dec)
op bar2 : Uint = (uintConstant 0 dec) +_uint bar
endspec
%% Example showing that making bar2 a constant can cause problems, because it refers to bar.

%%TODO The C generator should not translate bar as a constant.
%% TODO: currently, we get: CGen error: We do not allow let terms inside expressions (they must be at the statement level)
Example18 = E18 qualifying spec
  import CTarget
  op bar : Uint = let x = (uintConstant 0 dec) in x +_uint x
endspec

%Example with one function calling another
Example19 = E19 qualifying spec
  import CTarget
  op f (x:Uint) : Uint = x +_uint (uintConstant 0 dec)
  op g (x:Uint) : Uint = f x
endspec
