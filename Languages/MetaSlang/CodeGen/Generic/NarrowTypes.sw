(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

NarrowTypes qualifying spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport
import /Languages/MetaSlang/Transformations/Interpreter


op SpecTransform.abcd (spc: Spec) (msg : String) : Spec =
 let _ = writeLine("--------------------") in
 let _ = writeLine("abcd: " ^ msg) in
 let _ = writeLine("Nat.Nat32 = " ^ anyToString (findTheType (spc, Qualified("Nat", "Nat32")))) in
 let _ = writeLine("Int.Int32 = " ^ anyToString (findTheType (spc, Qualified("Int", "Int32")))) in
 let _ = writeLine("--------------------") in
 spc

type TypeInfos = List TypeInfo

op nPos (pos : Position) : Position = 
 let
   def printLCB (line,column,byte) = show line ^ "." ^ show column 
 in
 let s = 
     case pos of 
       | Internal "no position"       -> "from an internal source"
       | Internal x                   -> "via " ^ x
       | String   (s,    left, right) -> "from some string at " ^ (printLCB left) ^ "-" ^ (printLCB right)
       | File     (file, left, right) -> "from " ^ file     ^ " at " ^ (printLCB left) ^ "-" ^ (printLCB right)
       | _ -> " at " ^ print pos
 in
 Internal ("via narrowTypes " ^ s)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op int_type : MSType = Base (Qualified ("Integer", "Int"), [], noPos)
op nat_type : MSType = Base (Qualified ("Integer", "Nat"), [], noPos)

op add (n as Fun (_, n_type, _) : MSTerm, m : Nat) : MSTerm = 
 let m = Fun (Nat m, nat_type, noPos) in
 let plus =
     Fun (Op (Qualified ("Integer", "+"), Nonfix),
          %% type is tailored for adding one
          Arrow (Product ([("1", n_type), ("2", nat_type)], noPos),
                 int_type,
                 noPos),
          noPos)
 in
 Apply (plus,
        Record ([("1", n), ("2", m)], noPos), 
        noPos) 


op times (m : Nat, n as Fun (_, n_type, _) : MSTerm) : MSTerm = 
 let m = Fun (Nat m, nat_type, noPos) in
 let times =
     Fun (Op (Qualified ("Integer", "*"), Nonfix),
          %% type is tailored for multiplying by two
          Arrow (Product ([("1", nat_type), ("2", n_type)], noPos),
                 int_type,
                 noPos),
          noPos)
  in
  Apply (times, 
         Record ([("1", m), ("2", n)], noPos), 
         noPos)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op find_applicable_types (term       : MSTerm,
                          old_type   : MSType,
                          type_infos : TypeInfos,
                          spc        : Spec)
 : MSTypes =
 foldl (fn (applicable_types, info) ->
         case info.dfn of
            | Subtype (t1, pred,   _) -> 
              (case eval (Apply (pred, term, noPos), spc) of
                 | Bool true -> 
                   let name = primaryTypeName info  in
                   let t1   = Base (name, [], noPos) in
                   if exists? (fn t2 -> equalType? (t1, t2)) applicable_types then
                     applicable_types
                   else
                     t1 |> applicable_types
                 | _ -> applicable_types)
            | _ -> applicable_types)
       [old_type]
       type_infos

op find_minimal_types (types : MSTypes, spc : Spec) : MSTypes =
 let 
   def sub? (t1, t2) =
     possiblySubtypeOf? (t1, t2, spc) 
 in
 foldl (fn (types, t1) ->
          if exists? (fn t2 -> sub? (t2, t1)) types then
            types
          else 
            %% keep elements satisfying filter
            let others = filter (fn t2 -> ~ (sub? (t2, t1))) types in
            t1 |> others)
       []
       types


op type_with_smallest_range (n : MSTerm, minimal_types : MSTypes, spc : Spec) : MSType =
 let
   def expanded (t1 : MSType) =
     case t1 of
       | Base (name, _, _) -> 
         (case findTheType (spc, name) of
            | Some info -> info.dfn
            | _ -> t1)
       | _ -> t1

   def tight? typ n =
     %% return true if the type is defined as a subtype using a predicate 
     %% that is true for n, but false for either n+1 or 2*n
     % let _ = writeLine("") in
     % let _ = writeLine("Testing type " ^ printType typ) in
     case expanded typ of
       | Subtype (_, pred, _) -> 
         % let _ = writeLine("Predicate is " ^ printTerm pred) in
         let test_a  = Apply (pred, n, noPos) in
         let value_a = eval  (test_a, spc)    in
         (case value_a of
            | Bool true ->
              % let _ = writeLine("True for " ^ printTerm n) in
              let n_+_1   = add (n, 1)                 in
              let test_b  = Apply (pred, n_+_1, noPos) in
              let value_b = eval  (test_b, spc)        in
              (case value_b of
                 | Bool false -> 
                   % let _ = writeLine("False for " ^ printTerm n_+_1) in
                   true
                 | _ ->
                   let n_+_2   = add (n, 2)                  in
                   let test_c  = Apply (pred, n_+_2,  noPos) in
                   let value_c = eval  (test_c, spc)         in
                   (case value_c of
                      | Bool false -> 
                        % let _ = writeLine("False for " ^ printTerm n_+_2) in
                        true
                      | _ ->
                        let twice_n = times (2, n)                  in
                        let test_d  = Apply (pred, twice_n,  noPos) in
                        let value_d = eval  (test_d, spc)           in
                        (case value_d of
                           | Bool false -> 
                             % let _ = writeLine("False for " ^ printTerm twice_n) in
                             true
                           | _ ->
                             % let _ = writeLine("True for all three larger n's") in
                             false)))
            | _ -> 
              % let _ = writeLine("false for " ^ printTerm n) in
              false)
       | _ -> 
         % let _ = writeLine("Type is not a subtype") in
         false
     
 in
 %% TODO: This could be revised to compare the ranges of predicates used to 
 %%       define subtypes of Int.
 %%
 %%       E.g., we could define optional min, max values for such a predicate,
 %%       then use those to compute ranges for a type and find the narrowest ones.
 %%
 %%       op min (p : Int -> Bool) : Option Int = 
 %%         if ex (i : Int) fa (j : Int) (p j => i <= j) then
 %%           Some (the (i : Int) fa (j : Int) (p j => i <= j))
 %%         else
 %%           None
 %%
 %%       op max (p : Int -> Bool) : Option Int = 
 %%         if ex (i : Int) fa (j : Int) (p j => j <= i) then
 %%           Some (the (i : Int) fa (j : Int) (p j => j <= i))
 %%         else
 %%           None
 %%
 let tight_types =
     foldl (fn (types, t1) ->
              if tight? t1 n then
                t1 |> types
              else
                types)
           []
           minimal_types
 in
 % let _ = app (fn t1 -> writeLine(printTerm twice_n ^ " does not have type " ^ printType t1)) types_that_fail_on_twice_n in
 case tight_types of
   | [] ->
     let t1 :: t2 = minimal_types in
     % let _ = writeLine(";;; Choosing arbitrary new type for " ^ printTerm n ^ " : " ^ printType t1 ^
     %                    ", ignoring types: " ^ (foldl (fn (s, t3) -> s ^ " " ^ printType t3) "" t2))
     % in
     t1
   | [t1] ->
     % let _ = writeLine(";;; Choosing minimal type with narrowest range for " ^ printTerm n ^ " : " ^ printType t1) in
     t1
   | t1 :: t2 ->
     % let _ = writeLine(";;; Choosing arbitrary type with narrow range for " ^ printTerm n ^ " : " ^ printType t1 ^ 
     %                    ", ignoring types: " ^ (foldl (fn (s, t3) -> s ^ " " ^ printType t3) "" t2)) 
     % in
     t1
     

op find_narrowest_nat_type (term               : MSTerm,
                            old_type           : MSType,
                            numeric_type_infos : TypeInfos,
                            spc                : Spec)
 : MSType =
 let applicable_types = find_applicable_types (term, old_type, numeric_type_infos, spc) in
 let minimal_types    = find_minimal_types    (applicable_types,                   spc) in
 % let _ = writeLine("") in
 % let _ = writeLine("====================") in
 % let _ = app (fn t1 -> writeLine(printTerm term ^ "  : " ^ printType t1)) minimal_types in
 % let _ = writeLine("---") in
 if exists? (fn t1 -> equalType? (t1, old_type)) minimal_types then 
   let _ = writeLine(";;; Keeping old type: " ^ printTerm term ^ " : " ^ printType old_type) in
   % let _ = writeLine("====================") in
   old_type 
 else 
   case minimal_types of
     | [t1] -> 
       % let _ = writeLine(";;; Choosing unique new type for " ^ printTerm term ^ " : " ^ printType t1) in
       % let _ = writeLine("====================") in
       t1
     | _::_ ->
       type_with_smallest_range (term, minimal_types, spc)
     | [] -> 
       let _ = writeLine(";;; Confusion: keeping old type for " ^ printTerm term ^ " : " ^ printType old_type) in
       % let _ = writeLine("====================") in
       old_type

op restrict_fn_type (t1 : MSTerm, t2 : MSTerm, spc : Spec) : MSTerm =
 case t1 of
   | Fun (name, typ, p2) ->
     (case arrowOpt (spc, typ) of
        | Some (domain, range) ->
          let p1 = typeAnn typ in
          let t2_type = inferType (spc, t2) in
          Fun (name, Arrow (t2_type, range, nPos p1), nPos p2) 
        | _ ->
          t1)
   | _ ->
     t1

op narrow_types (numeric_types : TypeInfos, spc : Spec) (tm : MSTerm) : MSTerm =
 case tm of
   | Fun (Nat n, old_type, p1) -> 
     let new_type = find_narrowest_nat_type (tm, old_type, numeric_types, spc) in
     if equalType? (old_type, new_type) then
       tm
     else
       Fun (Nat n, new_type, nPos p1)

   | Apply  (t1, t2,         p1) -> 
     let restricted_t1 = restrict_fn_type (t1, t2, spc) in
     Apply (restricted_t1, t2, nPos p1)

   | Lambda (rules,          _) -> tm
   | Let    (bindings, body, _) -> tm
   | _ ->
     tm

op SpecTransform.narrowTypes (spc : Spec) : Spec =
 let int_type = Qualified ("Integer", "Int") in
 let numeric_types = 
     foldTypeInfos (fn (info, numeric_types) -> 
                      case subtypeOf (info.dfn, int_type, spc) of
                        | Some _ -> 
                          let _ = writeLine(";;; Numeric type: " ^ show (primaryTypeName info)) in
                          info |> numeric_types
                        | _ -> numeric_types)
                   []
                   spc.types
 in
 mapSpec (narrow_types (numeric_types, spc), 
          fn typ -> typ, 
          fn pat -> pat) spc


end-spec
