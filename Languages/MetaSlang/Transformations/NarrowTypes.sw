NarrowTypes qualifying spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport
import /Languages/MetaSlang/Transformations/Interpreter

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

op int_type : MSType = Base (Qualified ("Integer", "Int"), [], noPos)
op nat_type : MSType = Base (Qualified ("Integer", "Nat"), [], noPos)

op times_for_n (Fun (_, n_type, _) : MSTerm) : MSTerm = 
  Fun (Op (Qualified ("Integer", "*"), Nonfix),
       %% type is tailored for twice n
       Arrow (Product ([("1", nat_type), ("2", n_type)], noPos),
              n_type,
              noPos),
       noPos)

op two : MSTerm = Fun (Nat 2, nat_type, noPos)

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
 let twice_n = Apply (times_for_n n, 
                      Record ([("1", two), ("2", n)], noPos), 
                      noPos) 
 in
 % let _ = writeLine(printTerm twice_n ^ " : " ^ printType (termType twice_n)) in
 let
   def expanded (t1 : MSType) =
     case t1 of
       | Base (name, _, _) -> 
         (case findTheType (spc, name) of
            | Some info -> info.dfn
            | _ -> t1)
       | _ -> t1

   def clearly_fails? t1 =
     case t1 of
       | Subtype (_, pred, _) -> 
         let test  = Apply (pred, twice_n, noPos) in
         let value = eval  (test, spc)            in
         (case value of
            | Bool false -> true
            | _ -> false)
       | _ -> false
 in
 let types_that_fail_on_twice_n =
     foldl (fn (types, t1) ->
              if clearly_fails? (expanded t1) then
                t1 |> types
              else
                types)
           []
           minimal_types
 in
 % let _ = app (fn t1 -> writeLine(printTerm twice_n ^ " does not have type " ^ printType t1)) types_that_fail_on_twice_n in
 case types_that_fail_on_twice_n of
   | [] ->
     let t1 :: t2 = minimal_types in
     let _ = writeLine(";;; Choosing arbitrary new type: " ^ printTerm n ^ " : " ^ printType t1 ^
                         ", ignoring types: " ^ (foldl (fn (s, t3) -> s ^ " " ^ printType t3) "" t2))
     in
     t1
   | [t1] ->
     let _ = writeLine(";;; Choosing minimal type with narrowest range: " ^ printTerm n ^ " : " ^ printType t1) in
     t1
   | t1 :: t2 ->
     let _ = writeLine(";;; Choosing arbitrary type with narrow range: " ^ printTerm n ^ " : " ^ printType t1 ^ 
                         ", ignoring types: " ^ (foldl (fn (s, t3) -> s ^ " " ^ printType t3) "" t2)) 
     in
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
       % let _ = writeLine(";;; Choosing unique new type: " ^ printTerm term ^ " : " ^ printType t1) in
       % let _ = writeLine("====================") in
       t1
     | _::_ ->
       type_with_smallest_range (term, minimal_types, spc)
     | [] -> 
       let _ = writeLine(";;; Confusion: keeping old type: " ^ printTerm term ^ " : " ^ printType old_type) in
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
