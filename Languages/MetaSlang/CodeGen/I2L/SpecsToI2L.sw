SpecsToI2L qualifying spec 

%% Stand-alone C-code generation for specs
import /Library/Legacy/DataStructures/ListPair

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Printer
import /Languages/MetaSlang/Specs/Environment
import /Languages/MetaSlang/CodeGen/LanguageMorphism

import /Languages/I2L/I2L

op CUtils.cString (id : String) : String  % TODO: defined in CUtils.sw

type S2I_Context = {
                    specname       : String,             % not (yet) used
                    isToplevel     : Bool,               % not used
                    useRefTypes    : Bool,               % always true
                    constrOps      : List   QualifiedId, % not used, constrOps are distinguished by their name (contain "__")
                    currentOpType  : Option QualifiedId,
                    ms_spec        : Spec,
                    lms            : LanguageMorphisms,
                    translations   : Translations
                    }

op default_S2I_Context (ms_spec : Spec) : S2I_Context =
 {
  specname       = "",
  isToplevel     = false,
  useRefTypes    = true,
  constrOps      = [],
  currentOpType  = None,
  ms_spec        = ms_spec,
  lms            = [],
  translations   = []
  }

op qid2TypeName (Qualified (q, id) : QualifiedId, 
                 ctxt              : S2I_Context) 
 : I_TypeName = 
 %% Possibly rename using pragma info for type map
 let match =
     findLeftmost (fn translation -> 
                     case translation of
                       | Type trans ->
                         (case trans.source of
                            | [x, y] -> q = x && id = y
                            | [y]    -> id = y
                            | _ -> false)
                       | _ ->
                         false)
                  ctxt.translations
 in
 case match of
   | Some (Type match) -> 
     (case match.target of
        | Name [x, y] -> (x,  y)
        | Name [y]    -> ("", y)
        | _ -> (q,  id))
   | _ -> (q, id)

op qid2OpName (Qualified (q, id) : QualifiedId, 
               ctxt              : S2I_Context) 
 : I_OpName = 
 %% Possibly rename using pragma info for type map
 let match =
     findLeftmost (fn translation -> 
                     case translation of
                       | Op trans ->
                         (case trans.source of
                            | [x, y] -> q = x && id = y
                            | [y]    -> id = y
                            | _ -> false)
                       | _ ->
                         false)
                  ctxt.translations
 in
 case match of
   | Some (Op match) -> 
     (case match.target of
        | Name [x, y] -> 
          (case match.fixity of
             | Some Prefix  -> (x,  "prefix_"  ^ y)
             | Some Postfix -> (x,  "postfix_" ^ y)
             | _ ->            (x,  y))
        | Name [y] -> 
          (case match.fixity of
             | Some Prefix  -> ("", "prefix_"  ^ y)
             | Some Postfix -> ("", "postfix_" ^ y)
             | _ ->            ("", y))
        | _ ->  (q, id))
   | _ -> (q, id)

op qid2VarName (Qualified (q, id) : QualifiedId, 
                ctxt              : S2I_Context) 
 : I_VarName = 
 %% Vars are not renamed
 (q, id)


op unsetToplevel (ctxt : S2I_Context) : S2I_Context =
 ctxt << {isToplevel = false}

op setCurrentOpType (qid : QualifiedId, ctxt : S2I_Context) : S2I_Context = 
 ctxt << {currentOpType = Some qid}

op mkInOpStr (ctxt : S2I_Context) : String =
 case ctxt.currentOpType of
   | Some qid -> "in op \"" ^ (printQualifiedId qid) ^ "\": "
   | _ -> ""

op useConstrCalls? (ctxt : S2I_Context) : Bool =
 case ctxt.currentOpType of
   
   | None -> true
     
   | Some (qid as Qualified (q, id)) -> % ~(member (qid, ctxt. constrOps))
     let expl = explode q ++ explode id in
     let (indl, _) = 
         foldl (fn ((indl, n), c) -> 
                  if c = #_ then 
                    (n::indl, n+1) 
                  else 
                    (indl, n+1))
               ([], 0) 
               expl 
     in
     %% indl records positions of _'s in name
     case indl of
       
       | n :: m :: _ -> 
         %% if the name ends with __xyz then we assume its a constructor
         %% Note that indl could be something like (27 26 10) if the name has one or more additional _'s
         %% preceeding the final __xyz, so [n :: m] would be the wrong pattern to search for.
         %% See bug 161:  "C generation failed for constructors with args of complex types"
         if n = m+1 then
           false
         else 
           false
           
       | _ -> true

op generateI2LCodeSpec (ms_spec         : Spec,
                        use_ref_types?  : Bool, 
                        constructor_ops : List QualifiedId,
                        lms             : LanguageMorphisms,
                        natives         : Natives,
                        translations    : Translations)
 : I_ImpUnit =
 generateI2LCodeSpecFilter (ms_spec,
                            use_ref_types?,
                            constructor_ops,
                            fn _ -> true,    % desire all types
                            fn _ -> true,    % desire all ops
                            lms,
                            natives,
                            translations)

op generateI2LCodeSpecFilter (ms_spec       : Spec,
                              useRefTypes?  : Bool, 
                              constrOps     : List QualifiedId,
                              desired_type? : QualifiedId -> Bool,
                              desired_op?   : QualifiedId -> Bool,
                              lms           : LanguageMorphisms,
                              natives       : Natives,
                              translations  : Translations)
 : I_ImpUnit =
 let
   def print_qid (q, id, explicit_q?) =
     if explicit_q? then
       q ^ "." ^ id
     else if q = UnQualified then
       id
          else 
            "[" ^ q ^ ".]" ^ id        
 in
 let ctxt = {specname       = "", 
             isToplevel     = true, 
             useRefTypes    = useRefTypes?,
             constrOps      = constrOps,
             currentOpType  = None,
             ms_spec        = ms_spec,
             lms            = lms,
             translations   = translations}
 in
 let i_opdefs =
     foldriAQualifierMap (fn (q, id, opinfo, i_opdefs) ->
                            let qid = Qualified (q, id) in
                            %% to be considered, op must be desired and not translate to native op
                            if (exists? (fn translation ->
                                           case translation of
                                             | Op trans | trans.native? ->
                                               if trans.source = [q, id] then
                                                 let _ = writeLine ("Avoiding C generation for natively defined op: " ^ print_qid (q, id, true)) in
                                                 true
                                               else if trans.source = [id] then
                                                 let _ = writeLine ("Avoiding C generation for natively defined op: " ^ print_qid (q, id, false)) in
                                                 true
                                               else
                                                 false
                                             | _ -> false)
                                        translations)
                              then
                                i_opdefs
                            else if nativeOp? ([q,id], natives) then
                              let _ = writeLine ("Avoiding C generation for natively defined op: " ^ print_qid (q, id, true)) in
                              i_opdefs
                            else if desired_op? qid then
                              let i_opdef = opinfo2declOrDefn (qid, opinfo, None, ctxt) in
                              i_opdefs ++ [i_opdef]
                            else
                              let _ = writeLine ("Avoiding C generation for undesired op: " ^ print_qid (q, id, false)) in
                              i_opdefs)
                         []
                         ms_spec.ops
 in
 let i_typedefs =
     foldlSpecElements (fn (i_typedefs, el) ->
                          case el of
                            | TypeDef (name as Qualified (q, id), _) ->
                              if (exists? (fn translation ->
                                             case translation of
                                               | Type trans | trans.native? ->
                                                 if trans.source = [q, id] then
                                                   let _ = writeLine ("Avoiding C generation for natively defined type: " ^ print_qid (q, id, true)) in
                                                   true
                                                 else if trans.source = [id] then
                                                   let _ = writeLine ("Avoiding C generation for natively defined type: " ^ print_qid (q, id, false)) in
                                                   true
                                                 else
                                                   false
                                               | _ -> false)
                                          translations)
                                then
                                  i_typedefs
                              else if nativeType? ([q,id], natives) then
                                let _ = writeLine ("Avoiding C generation for natively defined type: " ^ print_qid (q, id, true)) in
                                i_typedefs
                              else if desired_type? name then
                                (case findTheType (ms_spec, name) of
                                   | Some typeinfo ->
                                     case typeinfo2typedef (name, typeinfo, ctxt) of
                                       | Some i_typedef ->
                                         i_typedefs ++ [i_typedef]
                                       | _ ->
                                         i_typedefs)
                              else
                                let _ = writeLine ("Avoiding C generation for undesired type: " ^ print_qid (q, id, false)) in
                                i_typedefs
                            | _ ->
                              i_typedefs)
                       []
                       ms_spec.elements
 in
 let res : I_ImpUnit = 
     {
      name     = "",    %s pc.name:String,
      includes = [],
      decls    = {
                  typedefs = i_typedefs,
                  
                  opdecls  = foldl (fn | (l3, OpDecl d) -> l3++[d] 
                                       | (l4, _)        -> l4)
                                   []
                                   i_opdefs,
                  
                  funDecls = foldl (fn | (l5, FunDecl d)                    -> l5++[d]
                                       | (l6, FunDefn {decl = d, body = _}) -> l6++[d]
                                       | (l7, _)                            -> l7)
                                   [] 
                                   i_opdefs,

                  funDefns = foldl (fn | (l8, FunDefn d) -> l8++[d] 
                                       | (l9, _)         -> l9)
                                   []
                                   i_opdefs,

                  varDecls = foldl (fn | (l10, VarDecl d) -> l10++[d] 
                                       | (l11, _)         -> l11)
                                   [] 
                                   i_opdefs,

                  mapDecls = foldl (fn | (l12, MapDecl d) -> l12++[d] 
                                       | (l13, _)         -> l13)
                                   [] 
                                   i_opdefs
                 }
      }
 in
 res

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                    %
%                       TYPES -> I2L.TYPES                           %
%                                                                    %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(*
 *  transforms a typeinfo into a type definition; the name of the type
 *  is the unqualified name, the qualifier is ignored.
 *)
op typeinfo2typedef (qid     : QualifiedId,
                     ms_info : TypeInfo,
                     ctxt    : S2I_Context)
 : Option I_TypeDefinition =
 if definedTypeInfo? ms_info then
   let (ms_tvs, ms_type) = unpackFirstTypeDef ms_info in
   let i_typename = qid2TypeName (qid, ctxt) in
   Some (i_typename, type2itype (ms_tvs, ms_type, ctxt))
 else
   None 

type LeLt   = | LE  | LT
type MinMax = | Min | Max

op find_simple_constant_bounds (ms_term : MSTerm) : Option (Int * Int) =
 %% returns Some (m, n) if the type directly expresses the inclusive range [m, n], otherwise None
 let 
   def eval_const tm =
     %% todo: could be smarter, but for now just recognizes constant terms such as 10 or -10, but not 3+4 or 2**8, etc.
     case tm of
       | Fun   (Nat m, _, _)                                                             -> Some m
       | Apply (Fun (Op (Qualified ("IntegerAux", "-"), _), _, _), Fun (Nat m, _, _), _) -> Some (-m)
       | _ -> None
         
   def find_min_bound vid tm1 tm2 =
     %% look for simple constant lower bounds such as '-10 < x', 'x >= 100', etc. 
     let maybe_min =
         case (vid, tm1, tm2) of
           | ("<",  bound,           Var ((v, _), _)) -> Some (bound, LT, v)
           | ("<=", bound,           Var ((v, _), _)) -> Some (bound, LE, v)
           | (">",  Var ((v, _), _), bound          ) -> Some (bound, LT, v)
           | (">=", Var ((v, _), _), bound          ) -> Some (bound, LE, v)
           | _ -> None
     in
     case maybe_min of
       | Some (tm, pred, v) | v = vid -> 
         (case eval_const tm of
            | Some m -> Some (if pred = LE then m else m + 1) % want bound <= v
            | _ -> None)
       | _ -> None
         
   def find_max_bound vid tm1 tm2 =
     %% similar, but look for upper bounds such as 'x < -10', 'x <= 100', etc.
     let maybe_max = 
         case (vid, tm1, tm2) of
           | ("<",  Var ((v, _), _), bound          ) -> Some (v, LT, bound)
           | ("<=", Var ((v, _), _), bound          ) -> Some (v, LE, bound)
           | (">",  bound,           Var ((v, _), _)) -> Some (v, LT, bound)
           | (">=", bound,           Var ((v, _), _)) -> Some (v, LE, bound)
           | _ -> None
     in
     case maybe_max of
       | Some (v, pred, tm) | v = vid ->
         (case eval_const tm of
            | Some m -> Some (if pred = LE then m else m - 1) % want v <= bound
            | _ -> None)
       | _ -> None
         
   def find_bound tm vid =
     case (tm : MSTerm) of
       | Apply (Fun (Op (Qualified ("Integer", id), _), _, _),
                Record ([("1", tm1), ("2", tm2)], _),
                _)
         ->
         (case find_min_bound id tm1 tm2 of
            | Some m -> Some (Min, m)
            | _ ->
              case find_max_bound id tm1 tm2 of
                | Some m -> Some (Max, m)
                | _ -> None)
       | _ -> None
         
 in
 case ms_term of
   | Lambda ([(VarPat ((vid, _), _),
               Fun (Bool true, _, _),
               Apply  (Fun (And, _, _), 
                       Record ([("1",tm1), ("2",tm2)], _), 
                       _))],
             _)
     ->
     (let r1 = find_bound tm1 vid in 
      let r2 = find_bound tm2 vid in
      %% Some (true.  m) indicates inclusive min restriction
      %% Some (false. n) indicates inclusive max restriction
      case (r1, r2) of
        | (Some (Min, m), Some (Max, n)) -> Some (m, n)
        | (Some (Max, n), Some (Min, m)) -> Some (m, n)
        | _ -> None)
     
   | Lambda ([(VarPat ((X, _), _),
               Fun (Bool true, _, _),
               Apply (Fun (Op (Qualified (_, "intFitsInNBits?-1-1"), _), _, _),
                      Record ([(_, Fun (Nat n, _, _)),
                               (_, Var ((X0, _),  _))],
                              _),
                      _)
               )],
             _)
     | X = X0 ->  
       let m = 2 ** (n-1) in
       Some (- m, m -1)
          
   | Lambda ([(VarPat ((X, _), _),
               Fun (Bool true, _, _),
               Apply (Fun (Op (Qualified (_, fits_in_pred), _), _, _),
                      Var ((X0, _), _),
                      _)
               )],
             _)
     | X = X0 -> 
       (case fits_in_pred of
          | "intFitsIn1Bits?"  -> Some (-1,0)
          | "intFitsIn8Bits?"  -> Some (- (2**7),2**7-1)
          | "intFitsIn16Bits?" -> Some (- (2**15),2**15-1)
          | "intFitsIn32Bits?" -> Some (- (2**31),2**31-1)
          | _ -> None)
     
   | _ -> None
     
op type2itype (ms_tvs  : TyVars,
               ms_type : MSType,
               ctxt    : S2I_Context)
 : I_Type =
 
 let 
   def bounded_list_type? ms_element_type pred =
     %% a bit of overkill, but this is just stopgap code, so...
     case unfold_bounded_list_type ms_element_type pred of
       | Some _ -> true
       | _ -> false
         
   def unfold_bounded_list_type ms_element_type pred =
     let i_element_type = type2itype (ms_tvs, ms_element_type, unsetToplevel ctxt) in
     case pred of
       | Lambda ([(VarPat ((pred_var, _), _),
                   Fun (Bool true, _, _),
                   pred_body)],
                 _)
         -> 
         (case pred_body of
            | Apply (Fun (cmp, _, _),
                     Record ([arg1, arg2], _),
                     _) 
              ->
              let
                def check_length_term ((_,length_op), (_,constant_term), min_const) =
                  let _ = 
                      case length_op of
                        | Apply (Fun (Op (Qualified (_, "length"), _), _, _),
                                 length_arg, 
                                 _)
                          ->
                          (case length_arg of
                             | Var ((length_var, _), _) -> if length_var = pred_var then Some () else None
                             | _ -> None)
                        | _ -> None
                  in
                  let const = constant_term_Int_value (constant_term, ctxt) in
                  if const < min_const then None else Some const
              in
              (case cmp of
                 | Op (Qualified (_, compare_sym), _) ->
                   (case compare_sym of
                      | ">"  -> (case check_length_term (arg2, arg1, 2) of | Some const -> Some (I_BoundedList (i_element_type, const - 1)) | _ -> None)
                      | "<"  -> (case check_length_term (arg1, arg2, 2) of | Some const -> Some (I_BoundedList (i_element_type, const - 1)) | _ -> None)
                      | "<=" -> (case check_length_term (arg1, arg2, 1) of | Some const -> Some (I_BoundedList (i_element_type, const))     | _ -> None)
                      | ">=" -> (case check_length_term (arg2, arg1, 1) of | Some const -> Some (I_BoundedList (i_element_type, const))     | _ -> None)
                      | _ -> None)
                 | Eq ->         case check_length_term (arg1, arg2, 1) of | Some const -> Some (I_BoundedList (i_element_type, const))     | _ -> None)
            | _ -> None)
       | _ -> None
 in
 let ms_utype = unfoldToSpecials (ms_type, ctxt) in
 case ms_utype of
   
   % ----------------------------------------------------------------------
   % primitives
   % ----------------------------------------------------------------------
   
   | Boolean _                                         -> I_Primitive I_Bool
   | Base (Qualified ("Nat",       "Nat"),    [],   _) -> I_Primitive I_Nat
   | Base (Qualified ("Integer",   "Int"),    [],   _) -> I_Primitive I_Int
   | Base (Qualified ("Character", "Char"),   [],   _) -> I_Primitive I_Char
   | Base (Qualified ("String",    "String"), [],   _) -> I_Primitive I_String
  %| Base (Qualified ("Float",     "Float"),  [],   _) -> I_Primitive I_Float
   
   | Base (Qualified (_,           "Ptr"),    [t1], _) -> I_Ref (type2itype (ms_tvs, t1, ctxt)) 
     
   % ----------------------------------------------------------------------
   
  % reference type
  %| Base (Qualified ("ESpecPrimitives", "Ref"), [ms_type], _) -> Ref (type2itype (ms_tvs, ms_type, ctxt))
   
  %| Base (Qualified (_, "List"), [ms_ptyp], _) ->
  %    let i_ptype = type2itype (ms_vs, ms_ptyp, ctxt) in
  %    List i_ptype
   
  %| Base (Qualified (_, "List"), [ms_ptyp], _) ->
  %  System.fail ("sorry, this version of the code generator doesn't support lists.")
  %         
  %     System.fail ("if using List type, please add a term restricting "^
  %     "the length of the list\n       "^
  %     "(e.g. \"{l:List ("^printType ms_ptyp ^")| length l <= 32}\")")

   % ----------------------------------------------------------------------
   
   | Subtype (Base (Qualified ("Nat", "Nat"), [], _), pred, _)
     ->
     (case pred of
        %% {x : Nat -> x < n} where n is a Nat
        | Lambda ([(VarPat ((X, _), _),
                    Fun (Bool true, _, _),
                    Apply (Fun (Op (Qualified (_, pred), _), _, _),
                           Record ([(_, Var ((X0, _),  _)),
                                    (_, Fun (Nat n, _, _))],
                                   _),
                           _)
                    )],
                  _)
          ->
          if X = X0 then 
            (case pred of
               | "<=" ->  I_BoundedNat (n + 1)
               | "<"  ->  I_BoundedNat n
               | _    ->  I_Primitive  I_Nat)
          else 
            I_Primitive I_Nat
            
        | Lambda ([(VarPat ((X, _), _),
                    Fun (Bool true, _, _),
                    Apply (Fun (Op (Qualified (_, "fitsInNBits?-1-1"), _), _, _),
                           Record ([(_, Fun (Nat n, _, _)),
                                    (_, Var ((X0, _), _))],
                                   _),
                           _)
                    )],
                  _)
          | X = X0 -> 
            I_BoundedNat (2**n)
          
          
        | Lambda ([(VarPat ((X, _), _),
                    Fun (Bool true, _, _),
                    Apply (Fun (Op (Qualified (_, fits_in_pred), _), _, _),
                           Var ((X0, _), _),
                           _)
                    )],
                  _)
          | X = X0 -> 
            (case fits_in_pred of
               | "fitsIn1Bits?"  -> I_BoundedNat (2**1)
               | "fitsIn8Bits?"  -> I_BoundedNat (2**8)
               | "fitsIn16Bits?" -> I_BoundedNat (2**16)
               | "fitsIn32Bits?" -> I_BoundedNat (2**32)
               | _ -> I_Primitive I_Nat)
          
        | _ ->
          I_Primitive I_Nat)
     
   | Subtype (Base (Qualified ("Integer", "Int"), [], _), pred, _) ->
     (case find_simple_constant_bounds pred of
        | Some (m, n) -> % Inclusive bounds.
          if m = 0 then
            I_BoundedNat n
          else
            I_BoundedInt (m-1, n+1) % I_BoundedInt takes an open interval.
        | _ ->
          let _ = writeLine "FindSimpleConstantBounds failed" in
          I_Primitive I_Int)
     
   % ----------------------------------------------------------------------
   % special form for list types, term must restrict length of list
   % the form of the term must be {X:List T | length X < N}
   % where N must be a constant term evaluating to a positive Nat
   % length X <= N, N > length X , N >= length X, N = length X can also be used
   % ----------------------------------------------------------------------
  
   | Subtype (Base (Qualified ("List", "List"), [ms_element_type], _), pred, _) 
     | bounded_list_type? ms_element_type pred ->
       % given the restriction above, the following must succeed
       let Some i_type = unfold_bounded_list_type ms_element_type pred in
       i_type
          
   % ----------------------------------------------------------------------
   % for arrow types make a distinction between products and argument lists:
   % op foo (n:Nat, m:Nat) -> Nat must be called with two Nats
   % ----------------------------------------------------------------------
  
   | Arrow (ms_typ1, ms_typ2, _) ->
     let ms_typ1 = unfoldToSpecials (ms_typ1, ctxt) in
    %let ms_typ1 = unfoldToProduct (spc, ms_typ1) in
     (case ms_typ1 of
        | Product (ms_fields, _) ->
          let i_types = map (fn (_, ms_type) -> 
                              let ms_type = unfoldToSpecials (ms_type, ctxt) in
                              type2itype (ms_tvs, ms_type, unsetToplevel ctxt)) 
                            ms_fields
          in
          let i_typ = type2itype (ms_tvs, ms_typ2, unsetToplevel ctxt) in
          I_FunOrMap (i_types, i_typ)
        | _ -> 
          let dom_i_type =
              case type2itype (ms_tvs, ms_typ1, unsetToplevel ctxt) of
                | I_Tuple i_types -> i_types
                | i_typ -> [i_typ]
          in
          I_FunOrMap (dom_i_type, 
                      type2itype (ms_tvs, ms_typ2, unsetToplevel ctxt)))
     
   % ----------------------------------------------------------------------

   | Product (ms_fields, _) ->
     if numbered? ms_fields then
       let i_types = 
           map (fn (_, ms_type) -> 
                  type2itype (ms_tvs, ms_type, unsetToplevel ctxt)) 
               ms_fields 
       in
       if i_types = [] then I_Void else I_Tuple i_types
     else
       let i_structfields = 
           map (fn (id, ms_type) -> 
                  (id, type2itype (ms_tvs, ms_type, unsetToplevel ctxt)))
               ms_fields
       in
       if i_structfields = [] then I_Void else I_Struct i_structfields
         
   % ----------------------------------------------------------------------

   | CoProduct (ms_fields, _) ->
     let i_unionfields = 
         map (fn | (id, None)         -> (id, I_Void)
                 | (id, Some ms_type) -> (id, type2itype (ms_tvs, ms_type, unsetToplevel ctxt)))
             ms_fields
     in
     I_Union i_unionfields
     
   % ----------------------------------------------------------------------
     
   | TyVar _ -> 
     if ctxt.useRefTypes then 
       I_Any
     else
       fail ("sorry, this version of the code generator doesn't support polymorphic types.")

   % ----------------------------------------------------------------------
   % use the base types as given, assume that the original definition has been checked
   % ----------------------------------------------------------------------
  
   | Base (qid, _, _) -> 
     let i_typename = qid2TypeName (qid, ctxt) in
     I_Base i_typename
     
   | Subtype (ms_type, ms_term, _) -> % ignore the term...
     type2itype (ms_tvs, ms_type, ctxt)
     
   | Quotient (ms_type, ms_term, _) -> % ignore the term...
     type2itype (ms_tvs, ms_type, ctxt)
     
   | _ ->
     fail ("sorry, code generation doesn't support the use of this type:\n       "
             ^ printType ms_type)

op constant_term_Int_value (ms_term : MSTerm, ctxt : S2I_Context) : Int =
 let 
   def err () = 
     let _ = print ms_term in
     fail ("cannot evaluate the constant value of term " ^ printTerm ms_term)
 in
 case ms_term of
   | Fun (Nat n, _, _) -> n
   | Fun (Op (qid, _), _, _) -> 
     (case getOpDefinition (qid, ctxt) of
        | Some tm -> constant_term_Int_value (tm, ctxt)
        | _ -> err ())
   | _ -> err ()
     
     
(*
 *  returns the definition term of the given op, if it exists in the given spec.
 *)

op getOpDefinition (Qualified (q, id) : QualifiedId, ctxt : S2I_Context) : Option MSTerm =
 case findAQualifierMap (ctxt.ms_spec.ops, q, id) of
   | Some info ->
     if definedOpInfo? info then
       Some (firstOpDefInnerTerm info)
     else
       None
   | _ -> None

(*
 *  unfolds a type, only if it is an alias for a Product, otherwise it's left unchanged;
 *  this is used to "normalize" the arrow types, i.e. to detect, whether the first argument of
 *  an arrow type is a product or not. Only "real" products are unfolded, i.e. type of the
 *  form (A1 * A2 * ... * An) are unfolded, not those of the form {x1:A1,x2:A2,...,xn:An}
 *)

op unfoldToProduct (ms_type : MSType, ctxt : S2I_Context) : MSType =
 let
   def unfoldRec ms_type =
     let ms_utype = unfoldBaseKeepPrimitives (ms_type, ctxt) in
     if ms_utype = ms_type then ms_type else unfoldRec ms_utype
       
 in
 let ms_utype = unfoldRec ms_type in
 case ms_utype of
   | Product (fields, _) -> if numbered? fields then ms_utype else ms_type
   | _ -> ms_type
     
op unfoldToCoProduct (ms_type : MSType, ctxt : S2I_Context) : MSType =
 let
   def unfoldRec ms_type =
     let ms_utype = unfoldBase (ctxt.ms_spec, ms_type) in
     if ms_utype = ms_type then ms_type else unfoldRec ms_utype
       
 in
 let ms_utype = unfoldRec ms_type in
 case ms_utype of
   | CoProduct (fields, _) -> ms_utype
   | _ -> ms_type

% unfold to special type in order to get the necessary information to generate code
% e.g. unfold to type of the form {n:Nat|n<C} which is needed to generate arrays

op unfoldToSpecials (ms_type : MSType, _ : S2I_Context) : MSType = 
 ms_type

op unfoldToSpecials1 (ms_type : MSType, ctxt : S2I_Context) : MSType =
 let
   def unfoldToSpecials0 ms_type =
     let
       def unfoldRec ms_type =
         let ms_utype = unfoldBaseKeepPrimitives (ms_type, ctxt) in
         if ms_utype = ms_type then ms_type else unfoldRec ms_utype
     in
     let ms_utype = unfoldRec ms_type in
     case ms_utype of
       % this corresponds to a term of the form {x:Nat|x<C} where C must be a Integer const
       | Subtype (Base (Qualified (_, "Nat"), [], _),
                  Lambda ([(VarPat ((X, _), _), 
                            Fun (Bool true, _, _),
                            Apply (Fun (Op (Qualified (_, "<"), _), _, _),
                                   Record ([(_, Var ((X0, _),   _)),
                                            (_, Fun (Nat n, _,  _))],
                                           _),
                                   _))],
                          _),
                  _) 
         -> 
         if X = X0 then ms_utype else ms_type
       | _ -> ms_type
 in
 mapType (fn tm -> tm, unfoldToSpecials0, fn pat -> pat) ms_type
  
op normalizeArrowTypesInSpec (ctxt : S2I_Context) : Spec =
 mapSpec (fn tm -> tm,
          fn | Arrow (typ1,                         typ2, X) -> 
               Arrow (unfoldToProduct (typ1, ctxt), typ2, X)
             | typ -> typ,
          fn pat -> pat) 
         ctxt.ms_spec

op unfoldBaseKeepPrimitives (ms_type : MSType, ctxt : S2I_Context) : MSType =
 case ms_type of
   | Base (qid, ms_types, a) ->
     (case AnnSpec.findTheType (ctxt.ms_spec, qid) of
        | Some info ->
          (if ~ (definedTypeInfo? info) then
             ms_type
           else
             let (ms_tvs, ms_type2) = unpackFirstTypeDef info in
             let
               def continue () =
                 let ms_stype = substType (zip (ms_tvs, ms_types), ms_type2) in
                 unfoldBaseKeepPrimitives (ms_stype, ctxt)
             in
             case ms_type of
               | Boolean                                         _  -> ms_type
               | Base (Qualified ("Nat",     "Nat"),    [],      _) -> ms_type
               | Base (Qualified ("Integer", "Int"),    [],      _) -> ms_type
               | Base (Qualified ("Char",    "Char"),   [],      _) -> ms_type
               | Base (Qualified ("String",  "String"), [],      _) -> ms_type
                 
               | Base (Qualified ("List",    "List"),   [ms_ptype],  X) ->
                 Base (Qualified ("List",    "List"),   
                       [unfoldBaseKeepPrimitives (ms_ptype, ctxt)], 
                       X)
                 
               | Base (Qualified ("Option",  "Option"), [ms_ptype],  X) ->
                 Base (Qualified ("Option",  "Option"), 
                       [unfoldBaseKeepPrimitives (ms_ptype, ctxt)],
                       X)
                 
               | _ -> continue ())
        | _ -> ms_type)
   | _ -> ms_type
     

% this is used to distinguish "real" product from "record-products"
op [a] numbered? (fields : List (String * a)) : Bool =
 let
   def aux? (i, fields) =
     case fields of
       | [] -> true
       | (id, _) :: fields -> id = show i && aux? (i + 1, fields)
 in
 aux? (1, fields)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                    %
%                       TERMS -> I2L.EXPRESSIONS                     %
%                                                                    %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type opInfoResult = | OpDecl  I_Declaration 
                    | FunDecl I_FunDeclaration
                    | FunDefn I_FunDefinition
                    | VarDecl I_Declaration
                    | MapDecl I_FunDeclaration
                    | Skip


op opinfo2declOrDefn (qid         : QualifiedId,
                      ms_info     : OpInfo,
                      optParNames : Option (List String),
                      ctxt        : S2I_Context)
 : opInfoResult =
 let Qualified (q, id) = qid in
 let (ms_tvs, ms_type, _) = unpackFirstOpDef ms_info in
 let 

   def qid2str (Qualified (q, id)) =
     if q = UnQualified then id else q ^ "." ^ id
       
   def getParamNames (ctxt, tm) =
     let 
       def err () = 
         let prefix = case ctxt.currentOpType of 
                        | Some qid -> "in op "^ qid2str qid ^ ":\n" 
                        | _ -> ""
         in
         prefix ^ "unsupported operator definition format:\n       " ^ printTerm tm
     in
     case tm of
       | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
         let plist =
             case pat of
           
               | VarPat ((id, _), _) -> 
                 [cString id]
             
               | RecordPat (plist, _) -> 
                 map (fn | (_,VarPat ((id, _), _)) -> cString id
                         | _ -> fail (err ()))
                     plist
             
               | RestrictedPat (VarPat ((id, _), _), _, _) -> 
                 [cString id]
             
               | RestrictedPat (RecordPat (plist, _), _, _) -> 
                 map (fn | (_,VarPat ((id, _), _)) -> cString id
                         | _ -> fail (err ()))
                     plist
             
               | _ -> 
                 fail (err ())
         in
         (plist,body)
       | _ -> fail (err ())

   def alignTypes pnames i_types =
     %% given one var and a list of types, convert list of types to a tuple type
     case (pnames, i_types) of
       | ([_], [_])   -> i_types
       | ([_], _)     -> [I_Tuple i_types]
       | (_,   [typ]) -> map (fn _ -> I_Void) pnames  % TODO: fix this
       | _            -> i_types
         
 in
 let Qualified (q, lid) = qid in
 let qid0     = Qualified (q, "__" ^ lid ^ "__")                 in
 let id       = qid2OpName (qid, ctxt)                           in
 let id0      = qid2OpName (qid0, ctxt)                          in
 let ms_type  = unfoldToArrow (ctxt.ms_spec, ms_type)            in
 let i_type   = type2itype (ms_tvs, ms_type, unsetToplevel ctxt) in
 let ctxt     = setCurrentOpType (qid, ctxt)                     in
 case i_type of 
   | I_FunOrMap (i_types, i_rtype) ->
     if definedOpInfo? ms_info then
       let ms_tm = firstOpDefInnerTerm ms_info         in
      %let ms_tm = liftUnsupportedPattern (ms_tm, spc)    in  % must do this in prior pass before pattern match compilation
       let (pnames, ms_body) = getParamNames (ctxt, ms_tm) in
       let i_types = alignTypes pnames i_types in
       let i_decl  = {name       = id,
                      params     = zip (pnames, i_types),
                      returntype = i_rtype}
       in
       let i_expr = term2expression (ms_body, ctxt) in
       FunDefn {decl = i_decl,
                body = I_Exp i_expr} % functional function body
     else
       let i_params = 
           case optParNames of
             | Some pnames -> 
               let i_types = alignTypes pnames i_types in
               zip (pnames, i_types)
             | _ -> 
               map (fn i_type -> ("", i_type)) i_types
       in
       FunDecl {name       = id,
                params     = i_params,
                returntype = i_rtype}
   | _ -> 
     let opt_i_expr = 
         if definedOpInfo? ms_info then
           let ms_tm = firstOpDefInnerTerm ms_info in
           Some (term2expression (ms_tm, ctxt))
         else
           None
     in
     OpDecl (id, i_type, opt_i_expr)

% --------------------------------------------------------------------------------

op term2expression (ms_term : MSTerm, ctxt : S2I_Context) : I_TypedExpr =
 let ms_type  = inferType (ctxt.ms_spec, ms_term) in
 let ms_type  = unfoldBaseKeepPrimitives (ms_type,          ctxt) in
 let i_expr   = term2expression_internal (ms_term, ms_type, ctxt) in
 let i_type   = type2itype ([], ms_type, unsetToplevel ctxt)      in
 %% TODO: cast? used to be set to true for failWith forms.
 let cast? = false in
 {expr = i_expr, typ = i_type, cast? = cast?}

op term2expression_internal (ms_term : MSTerm, 
                             ms_type : MSType, 
                             ctxt    : S2I_Context)
 : I_Expr =
 
 % Accord hack:
 % checks, whether the given id is an outputop of the espec; if yes is has to be
 % replaced by a VarDeref/FunCallDeref, as done below
 %    let def isOutputOp (varid as (spcname,lid)) =
 %          let outputops = ctxt.espc.interface.outputops in
 %    (spcname = ctxt.espc.spc.name) && lid in? outputops)
 %    in
 
 case ms_term of
   | Apply      (t1,            t2,  _) -> term2expression_apply  (t1,  t2,    ms_term, ms_type, ctxt)
   | Record     (fields,             _) -> term2expression_record (fields,     ms_term,          ctxt)
   | Let        ([(pat,deftm)], tm,  _) -> term2expression_let    (pat, deftm, tm,               ctxt)
   | Var        ((id, _),            _) -> I_Var ("", id)
   | Fun        (fun,           typ, _) -> term2expression_fun    (fun, typ,   ms_term,          ctxt)
   | IfThenElse (t1, t2, t3,         _) -> I_IfExpr (term2expression (t1, ctxt),
                                                     term2expression (t2, ctxt),
                                                     term2expression (t3, ctxt))
   | Seq        (tms,                _) -> I_Comma (map (fn tm -> term2expression (tm, ctxt)) tms)
   | TypedTerm  (tm, typ,            _) -> let typed_expr = term2expression (tm, ctxt) in typed_expr.expr  % TODO: add cast? ??
   | _ -> 
     % Bind, The, LetRec, Lambda, Transform, Pi, And, Any 
     let s = "Unrecognized term in term2expression: " ^ printTerm ms_term in
     let _ = writeLine s in
     I_Str s
     
op alt_index (x : Id, ms_type : MSType, ctxt : S2I_Context) : Nat =
 let 
   def aux (n, alts) =
     case alts of
       | [] -> 0
       | (alt, _) :: alts ->
         if alt = x then 
           n
         else
           aux (n + 1, alts)
 in
 case unfoldToCoProduct (ms_type, ctxt) of
   | CoProduct (alts, _) -> aux (1, alts)
   | _ -> 
     let _ = writeLine ("Type is not a coproduct, so index is 0: " ^ printType ms_type) in
     0

op term2expression_fun (ms_fun  : MSFun, 
                        ms_type : MSType, 
                        ms_term : MSTerm, 
                        ctxt    : S2I_Context)
 : I_Expr =
 
 % This is called when a Fun occurs "standalone", i.e. not in the context of an apply.
 % We restrict the possible forms to those not having an arrow type, 
 % i.e. we don't support functions as objects
 % Not, And, Or, etc,. should never occur "standalone", so we don't look for them here
 % See process_t1 below for case where Fun is applied.
 let 
   def make_embedder (ms_type, id, arg?) =
     let i_selector = {name  = id, 
                       index = alt_index (id, ms_type, ctxt)} 
     in
     if useConstrCalls? ctxt then
       case ms_type of
         
         | Base (qid, _, _) ->
           let i_fname = qid2OpName (qid, ctxt) in
           I_ConstrCall (i_fname, i_selector, [])
           
         | Boolean _ -> 
           I_ConstrCall (("Boolean", "Boolean"), i_selector, [])
           
         | _ -> 
           I_AssignUnion (i_selector, None)
     else
       I_AssignUnion (i_selector, None)
       
 in
 
 if arrowType? (ms_type, ctxt) then
   case ms_fun of
     | Op    (qid, _)     -> 
       % let _ = writeLine("Ok. arrow type for ms_term = " ^ printTerm ms_term ^ ", type = " ^ printType ms_type) in
       I_VarRef (qid2OpName (qid, ctxt))
     | Embed (id,  false) -> 
       let Arrow (_, ms_rng, _) = ms_type in
       term2expression_apply_fun (ms_fun,
                                  ms_term, 
                                  [], 
                                  Record ([], noPos), 
                                  [], 
                                  ms_term, 
                                  ms_rng, 
                                  ctxt)
     | _ -> 
       fail ("sorry, functions as objects (higher-order functions) are not yet supported:\n" ^ printTerm ms_term)
 else
   case ms_fun of
     | Nat    n -> I_Int  n
     | String s -> I_Str  s
     | Char   c -> I_Char c
     | Bool   b -> I_Bool b
       
     | Op (qid, _) -> 
       let i_fname = qid2OpName (qid, ctxt) in
       %if isOutputOp varname then VarDeref varname else 
       I_Var i_fname
       
     | Embed (id,arg?) -> 
       make_embedder (ms_type, id, arg?)
     | _ -> 
       fail (mkInOpStr ctxt ^ "unsupported Fun: " ^ printTerm ms_term)
       
op getExprs4Args (ms_args : MSTerms, ctxt : S2I_Context) : List I_TypedExpr = 
 map (fn ms_arg -> term2expression (ms_arg, ctxt)) ms_args
 
op term2expression_apply (ms_t1   : MSTerm,
                          ms_t2   : MSTerm,
                          ms_term : MSTerm,
                          ms_type : MSType,
                          ctxt    : S2I_Context)
 : I_Expr =
 let ms_args = 
     % extract the list of argument terms from a record term given
     % as second argument of an Apply term
     case ms_t2 of
       | Record (ms_fields, _) ->
         if numbered? ms_fields then
           map (fn (_, ms_tm) -> ms_tm) ms_fields
         else
           [ms_t2]
       | _ -> [ms_t2]
 in
 case getBuiltinExpr (ms_t1, ms_args, ctxt) of
   | Some i_expr -> i_expr
   | _ ->
     let ms_orig_lhs = ms_t1 in
     let
     
        def getProjectionList (ms_tm, projids) =
          case ms_tm of
            | Apply (Fun (Project id, _, _), t2, _) -> getProjectionList (t2, id::projids)
            | _ -> (projids, ms_tm)
              
              % this is a sub-def, because we collect and skip projections
        def process_t1 (ms_t1, projections) =
          case ms_t1 of
            
            | TypedTerm (ms_tm, _, _) -> process_t1 (ms_tm, projections)
              
            | Var ((id, _), _) ->
              let i_exprs   = getExprs4Args (ms_args, ctxt)  in
              let i_varname = qid2VarName (mkUnQualifiedId id, ctxt) in % don't rename vars with pragma info

              % infer the type of the original lhs to get the real type of the map
              % taking all the projections into account

              let ms_lhs_type = inferType (ctxt.ms_spec, ms_orig_lhs)            in
              let ms_lhs_type = unfoldToSpecials (ms_lhs_type, ctxt)             in
              let i_lhs_type  = type2itype ([], ms_lhs_type, unsetToplevel ctxt) in
              I_FunCall (i_varname, projections, i_exprs)
              
            | Fun (ms_fun, _, _) -> 
              term2expression_apply_fun (ms_fun, 
                                         ms_orig_lhs, 
                                         projections, 
                                         ms_t2, 
                                         ms_args, 
                                         ms_term, 
                                         ms_type, 
                                         ctxt)
            | _ ->
              case getProjectionList (ms_t1, []) of
                | (prjs as (_::_), ms_t1) -> process_t1 (ms_t1, prjs)
                | _ -> 
                  % handle special cases:
                  case simpleCoProductCase (ms_term, ctxt) of
                    | Some i_expr -> i_expr
                    | _ ->
                      let msg = mkInOpStr ctxt ^ "cannot yet handle: " ^ printTerm ms_t1 in
                      let _ = writeLine msg in
                      I_Str msg
                      
     in
     process_t1 (ms_t1, [])
     
op term2expression_apply_fun (ms_fun      : MSFun, 
                              ms_orig_lhs : MSTerm,
                              projections : List Id, 
                              ms_t2       : MSTerm,
                              ms_args     : MSTerms,
                              ms_term     : MSTerm, 
                              ms_type     : MSType, 
                              ctxt        : S2I_Context)
 : I_Expr =
 case ms_fun of
   | Op (qid, _) ->
     let i_exprs     = getExprs4Args (ms_args, ctxt)                    in
     let i_fname     = qid2OpName (qid, ctxt)                           in
     % infer the type of the original lhs to get the real type of the map
     % taking all the projections into account
     let ms_lhs_type = inferType (ctxt.ms_spec, ms_orig_lhs)            in
     let ms_lhs_type = unfoldToSpecials (ms_lhs_type, ctxt)             in
     let i_lhs_type  = type2itype ([], ms_lhs_type, unsetToplevel ctxt) in
     %if isOutputOp varname then MapAccessDeref (varname, i_lhs_type, projections, exprs) else 
     if isVariable (ctxt, qid) then
       I_MapAccess (i_fname, i_lhs_type, projections, i_exprs)
     else
       I_FunCall (i_fname, projections, i_exprs)
       
   | Embed (id, _) ->
     let 
       def mkExpr2 () = term2expression (ms_t2, ctxt)
     in
     if projections = [] then
       % let typ = foldType (typ, spc) in
       let selector = {name  = id, 
                       index = alt_index (id, ms_type, ctxt)} 
       in
       if useConstrCalls? ctxt then
         case ms_type of
           
           | Base (qid, _, _) ->
             let i_fname = qid2OpName (qid, ctxt) in
             let i_exprs = case ms_t2 of
                             | Record (ms_fields, b) ->
                               if numbered? ms_fields then
                                 map (fn (_, ms_tm) -> term2expression (ms_tm, ctxt)) ms_fields
                               else 
                                 [mkExpr2 ()]
                               | _ -> 
                                 [mkExpr2 ()]
             in
             I_ConstrCall (i_fname, selector, i_exprs)
             
           | Boolean _ -> 
             let i_exprs = case ms_t2 of
                             | Record (ms_fields, b) ->
                               if numbered? ms_fields then
                                 map (fn (_, ms_tm) -> term2expression (ms_tm, ctxt)) ms_fields
                               else 
                                 [mkExpr2 ()]
                               | _ -> 
                                 [mkExpr2 ()]
             in
             I_ConstrCall (("Boolean", "Boolean"), selector, i_exprs)
             
           | _ -> 
             I_AssignUnion (selector, Some (mkExpr2 ()))
       else 
         I_AssignUnion (selector, Some (mkExpr2 ()))
         
     else 
       fail (mkInOpStr ctxt ^ "not handled as fun to be applied: " ^ anyToString ms_fun)
       
   | Embedded id -> 
     let ms_lhs_type = inferType (ctxt.ms_spec, ms_orig_lhs) in
     let index =
         case unfoldToArrow (ctxt.ms_spec, ms_lhs_type) of
           | Arrow (ms_super_type, Bool, _) ->
             %% type of a predicate used to test for variants among a coproduct
             alt_index (id, ms_super_type, ctxt)
           | _ ->
             let _ = writeLine ("Expected arrow type: " ^ printType ms_lhs_type) in
             0
     in
     let selector = {name = id, index = index} in
     I_Embedded (selector, term2expression (ms_t2, ctxt))
     
   | Select id ->
     let i_expr2 = term2expression (ms_t2, ctxt) in
     if projections = [] then 
       % let union = I_Project (expr2, "alt") in
       % let (_,ityp2) = expr2 in
       % I_Select ((union, ityp2), id)
       I_Select (i_expr2, id)
     else 
       fail (mkInOpStr ctxt ^ "not handled as selection: " ^ anyToString id
               ^ " given projections " ^ anyToString projections)
       
   | Project id ->
     let i_expr2 = term2expression (ms_t2, ctxt) in
     if projections = [] then 
       I_Project (i_expr2, id)
     else 
       fail (mkInOpStr ctxt ^ "not handled as projection: " ^ anyToString id
               ^ " given projections " ^ anyToString projections)
       
   | _ ->
     let msg = mkInOpStr ctxt ^ "not handled as fun to be applied: " ^ anyToString ms_fun in
     let _ = writeLine (anyToString ms_fun) in 
     let _ = writeLine msg in
     I_Str msg
     
op term2expression_let (ms_pat : MSPattern,
                        ms_def : MSTerm,
                        ms_tm  : MSTerm, 
                        ctxt   : S2I_Context) 
 : I_Expr =
 % let's can only contain one pattern/term entry (see parser)
 let i_def_exp = term2expression (ms_def, ctxt) in
 let i_exp     = term2expression (ms_tm,  ctxt) in
 
 case ms_pat of

   | WildPat _ ->
     I_Comma [i_def_exp, i_exp]
     
   | VarPat ((_, Product ([], _)), _) ->
     I_Comma [i_def_exp, i_exp]
     
   | VarPat ((id, ms_type), _) ->
     let i_type = type2itype ([], ms_type, unsetToplevel ctxt) in
     I_Let (id, i_type, i_def_exp, i_exp)
     
   | _ -> 
     fail (mkInOpStr ctxt ^ "unsupported feature: this form of pattern cannot be used in a let:\n" 
             ^ printPattern ms_pat)
     
op term2expression_record (ms_fields : List (Id * MSTerm), 
                           _         : MSTerm, 
                           ctxt      : S2I_Context) 
 : I_Expr = 
 if numbered? ms_fields then
   let i_exprs = map (fn (_, ms_tm) -> term2expression (ms_tm, ctxt)) ms_fields in
   I_TupleExpr i_exprs
 else
   let i_fields = map (fn (id, ms_tm) -> (id, term2expression (ms_tm, ctxt))) ms_fields in
   I_StructExpr i_fields
   
op arrowType? (ms_type : MSType, ctxt : S2I_Context) : Bool =
 case unfoldToArrow (ctxt.ms_spec, ms_type) of
   | Arrow _ -> true
   | _ -> false
     
op getEqOpQid (Qualified (q, id) : QualifiedId) : QualifiedId =
 Qualified (q, "eq_" ^ id)

op equalsExpression (ms_t1 : MSTerm, ms_t2 : MSTerm, ctxt : S2I_Context) 
 : I_Expr =
 let

   def t2e ms_tm = 
     term2expression (ms_tm, ctxt)

   def primEq () =
     I_Builtin (I_Equals (t2e ms_t1, t2e ms_t2))

 in

 % analyse, which equal we need; let's hope type checking
 % already made sure, that the types fit, so just look at one
 % of the terms

 let ms_type = inferType (ctxt.ms_spec, ms_t1) in

 %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
 let ms_utype = stripSubtypesAndBaseDefs ctxt.ms_spec ms_type in

 case ms_utype of
   | Boolean                                    _  -> primEq ()
   | Base (Qualified ("Bool",    "Bool"),   [], _) -> primEq ()
   | Base (Qualified ("Nat",     "Nat"),    [], _) -> primEq ()  % TODO: is this possible?
   | Base (Qualified ("Integer", "Int"),    [], _) -> primEq ()
   | Base (Qualified ("Char",    "Char"),   [], _) -> primEq ()
   | Base (Qualified ("Float",   "Float"),  [], _) -> primEq ()
   | Base (Qualified ("String",  "String"), [], _) -> I_Builtin (I_StrEquals (t2e ms_t1, t2e ms_t2))
   | _ ->
     let ms_type = foldType (termType ms_t1, ctxt) in
     let 
       def errmsg () = 
         "sorry, the current version of the code generator doesn't support the equality check for\ntype = "
         ^ printType ms_type ^ "\n t1 = " ^ printTerm ms_t1 ^ "\n t2 = " ^ printTerm ms_t2
     in
     case ms_type of
       
       | Base (qid, _, _) ->
         let eqid as Qualified (eq, eid) = getEqOpQid qid in
         let i_eq_fname = qid2OpName (eqid, ctxt) in
         (case AnnSpec.findTheOp (ctxt.ms_spec, eqid) of
            | Some _ ->
              I_FunCall (i_eq_fname, [], [t2e ms_t1, t2e ms_t2])
            | _ ->
              % let _ = appOpInfos (fn info -> writeLine (anyToString info.names)) spc.ops in
              let _ = writeLine ("eq-op not found for " ^ anyToString qid ^ " via " ^ anyToString eqid) in
              I_FunCall (i_eq_fname, [], [t2e ms_t1, t2e ms_t2]))
     
       | Product (ms_fields, _) ->
         let ms_eq_tm     = getEqTermFromProductFields (ms_fields, ms_type, ms_t1, ms_t2) in
         let i_typed_expr = t2e ms_eq_tm in
         i_typed_expr.expr
     
       | _ -> 
         fail (errmsg () ^ "\n[term type must be a base or product type]") % primEq ()

op getEqTermFromProductFields (ms_fields : List (Id * MSType),
                               ms_otyp   : MSType,
                               ms_varx   : MSTerm,
                               ms_vary   : MSTerm)
 : MSTerm =
 let b          = typeAnn ms_otyp in
 let ms_default = mkTrue ()    in
 foldr (fn ((fid, ms_ftyp), ms_eq_all) ->
          let ms_projtyp  = Arrow (ms_otyp,                                        ms_ftyp,   b) in
          let ms_eqtyp    = Arrow (Product ([("1", ms_ftyp), ("2", ms_ftyp)], b),  Boolean b, b) in
          let ms_proj     = Fun   (Project fid, ms_projtyp,                                   b) in
          let ms_t1       = Apply (ms_proj,                ms_varx,                           b) in
          let ms_t2       = Apply (ms_proj,                ms_vary,                           b) in
          let ms_eq_field = Apply (Fun (Equals, ms_eqtyp, b), 
                                   Record ([("1", ms_t1), ("2", ms_t2)], b),  
                                   b)
          in
          if ms_eq_all = ms_default then
            ms_eq_field
          else
            Apply (mkAndOp b, Record ([("1", ms_eq_field), ("2", ms_eq_all)], b), b))
       ms_default
       ms_fields

op getBuiltinExpr (ms_term : MSTerm, 
                   ms_args : MSTerms,
                   ctxt    : S2I_Context)
 : Option I_Expr =
 let
   def t2e tm = term2expression (tm, ctxt)
 in
 case (ms_term, ms_args) of
   | (Fun (Equals,    _, _),                                          [t1,t2]) -> Some (equalsExpression (t1, t2, ctxt))
     
   | (Fun (Not,       _, _),                                          [t1])    -> Some (I_Builtin (I_BoolNot             (t2e t1)))
   | (Fun (And,       _, _),                                          [t1,t2]) -> Some (I_Builtin (I_BoolAnd             (t2e t1, t2e t2)))
   | (Fun (Or,        _, _),                                          [t1,t2]) -> Some (I_Builtin (I_BoolOr              (t2e t1, t2e t2)))
   | (Fun (Implies,   _, _),                                          [t1,t2]) -> Some (I_Builtin (I_BoolImplies         (t2e t1, t2e t2)))
   | (Fun (Iff,       _, _),                                          [t1,t2]) -> Some (I_Builtin (I_BoolEquiv           (t2e t1, t2e t2)))
   | (Fun (NotEquals, _, _),                                          [t1,t2]) -> let eq_tm = 
                                                                                        I_Builtin (I_Equals              (t2e t1, t2e t2))
                                                                                  in
                                                                                  Some (I_Builtin (I_BoolNot             {expr  = eq_tm, 
                                                                                                                          typ   = I_Primitive I_Bool,
                                                                                                                          cast? = false}))
                                                                                  
   | (Fun (Op (Qualified ("Integer",    "+"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntPlus             (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "-"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntMinus            (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("IntegerAux", "-"),             _), _, _),  [t1])    -> Some (I_Builtin (I_IntUnaryMinus       (t2e t1)))
   | (Fun (Op (Qualified ("Integer",    "*"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntMult             (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "div"),           _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntDiv              (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "rem"),           _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntRem              (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "<"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntLess             (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "<="),            _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntLessOrEqual      (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    ">"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntGreater          (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    ">="),            _), _, _),  [t1,t2]) -> Some (I_Builtin (I_IntGreaterOrEqual   (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Integer",    "isucc"),         _), _, _),  [t1])    -> Some (I_Builtin (I_IntPlus             (t2e t1, I_One)))
   | (Fun (Op (Qualified ("Integer",    "ipred"),         _), _, _),  [t1])    -> Some (I_Builtin (I_IntMinus            (t2e t1, I_One)))
   | (Fun (Op (Qualified ("Nat",        "succ"),          _), _, _),  [t1])    -> Some (I_Builtin (I_IntPlus             (t2e t1, I_One)))
   | (Fun (Op (Qualified ("Nat",        "pred"),          _), _, _),  [t1])    -> Some (I_Builtin (I_IntMinus            (t2e t1, I_One)))
     
   | (Fun (Op (Qualified ("Float",      "toFloat"),       _), _, _),  [t1])    -> Some (I_Builtin (I_IntToFloat          (t2e t1)))
   | (Fun (Op (Qualified ("Float",      "stringToFloat"), _), _, _),  [t1])    -> Some (I_Builtin (I_StringToFloat       (t2e t1)))
     
   | (Fun (Op (Qualified ("Float",      "+"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatPlus           (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "-"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatMinus          (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "~"),             _), _, _),  [t1])    -> Some (I_Builtin (I_FloatUnaryMinus     (t2e t1)))
   | (Fun (Op (Qualified ("Float",      "*"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatMult           (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "div"),           _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatDiv            (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "<"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatLess           (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      ">"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatGreater        (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "<="),            _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatLessOrEqual    (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      ">="),            _), _, _),  [t1,t2]) -> Some (I_Builtin (I_FloatGreaterOrEqual (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("Float",      "toInt"),         _), _, _),  [t1])    -> Some (I_Builtin (I_FloatToInt          (t2e t1)))
     
   | (Fun (Op (Qualified ("String",     "<"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_StrLess             (t2e t1, t2e t2)))
   | (Fun (Op (Qualified ("String",     ">"),             _), _, _),  [t1,t2]) -> Some (I_Builtin (I_StrGreater          (t2e t1, t2e t2)))

  % var refs:
  %      | (Fun (Op (Qualified ("ESpecPrimitives", "ref"), _), _, _), [t1])
  %        -> let def qid2varname qid =
  %                 case qid of
  %                   | Qualified (spcname, name) -> (spcname,name)
  %                  %| Local name -> (spc.name,name)
  %           in
  %           (case t1 of
  %              | Fun (Op (qid, _), _, _)
  %                -> %if member (qid,ctxt.vars) then Some (VarRef (qid2varname qid))
  %                   %else 
  %                       fail ("\"ref\" can only be used for vars, but \""^
  %                             (qidstr qid)^"\" is not declared as a var.")
  %              | _ -> fail ("\"ref\" can only be used for vars, not for:\n"^
  %                           printTerm t1)
  %           )
  
   | _ -> None

op isVariable (_ : S2I_Context, _ : QualifiedId) : Bool = 
 % In vanilla metaslang, as opposed to ESpecs, there are no variables,
 % but they might appear at a future date.
 false % member (qid, ctxt. vars)
 
(*
 *  simpleCoProductCase checks for a special case of lambda term that represents one of the most
 *  common uses of case expression:
 *  case term of
 *    | Constr1 (x1,x2)
 *    | Constr2 (y1)
 *    ....
 *  i.e. where the term's type is a coproduct and the cases are the constructors of the coproduct.
 *  In the args of the constructors (x1,x2,y1 above) only var pattern are supported.
 *)

op simpleCoProductCase (ms_term : MSTerm, ctxt : S2I_Context) : Option I_Expr =
 let ms_outer_tm = ms_term in
 case ms_term of
   
   | Apply (embedfun as Lambda (ms_rules, _), ms_arg, _) ->
     (case ms_rules of
        | [(ms_pat as VarPat ((v,ty), b), _, ms_body)] ->
          % that's a very simple case: "case tm of v -> body" (no other case)
          % we transform it to "let v = tm in body"
          let i_typed_expr = term2expression (Let ([(ms_pat, ms_arg)], ms_body, b), ctxt) in
          Some i_typed_expr.expr
        | _ -> 
          let
            def getTypeForConstructorArgs (ms_type, id) =
              %let ms_type = unfoldBase (spc, ms_type) in
              let ms_type = stripSubtypesAndBaseDefs ctxt.ms_spec ms_type in
              case ms_type of
                | CoProduct (ms_fields, _) ->
                  (case findLeftmost (fn (id0, _) -> id0 = id) ms_fields of
                     | Some (_, opt_ms_type) -> 
                       (case opt_ms_type of
                          | Some ms_type -> Some (type2itype ([], ms_type, unsetToplevel ctxt))
                          | _ -> None)
                     | _ -> fail ("internal error: constructor id " ^ id ^ " of term " ^
                                    printTerm ms_arg ^ " cannot be found."))
                | _ -> 
                  let ms_utype = unfoldBase (ctxt.ms_spec, ms_type) in
                  if ms_utype = ms_type then
                    fail ("internal error: type of term is no coproduct: " ^
                            printTerm ms_arg ^ ":" ^ printType ms_type)
                  else 
                    getTypeForConstructorArgs (ms_utype, id)
                    
          in
          % check whether the pattern have the supported format, i.e.
          % (constructor name followed by var patterns) or (wildpat)
          let
          
            def getUnionCase (ms_pat, ms_cond, ms_tm) =
              let i_exp = term2expression (ms_tm, ctxt) in
              case ms_pat of
                
                | EmbedPat (constructorId, opt_ms_pat, parent_ms_type, _) ->
                  % let opttype = getTypeForConstructorArgs (parent_type, constructorId) in
                  let vars =
                      case opt_ms_pat of
                    
                        | None                       -> []
                        | Some (VarPat ((id, _), _)) -> [Some id]
                        | Some (WildPat _)           -> [None]
                          
                        | Some (ms_pat as RecordPat (ms_fields, _)) ->
                          % pattern must be a recordpat consisting of var or wildpattern
                          if numbered? ms_fields then
                            map (fn | (_, WildPat _)           -> None
                                    | (_, VarPat ((id, _), _)) -> Some id
                                    | (_, ms_pat) -> 
                                      fail (mkInOpStr ctxt ^ "unsupported feature: you can only use var patterns or _ here, not:\n" 
                                              ^ printPattern ms_pat))
                                ms_fields
                          else
                            fail (mkInOpStr ctxt ^ "unsupported feature: record pattern not supported:\n" 
                                    ^ printPattern ms_pat)
                        | Some ms_pat -> 
                          fail (mkInOpStr ctxt ^ "unsupported feature: you can only use "^
                                  "var patterns, tuples of these, or \"_\" here, "^
                                  "not:\n"^printPattern ms_pat)
                  in
                  let selector = {name  = constructorId, 
                                  index = alt_index (constructorId, parent_ms_type, ctxt)} 
                  in
                  I_ConstrCase (Some selector, vars, i_exp)
                  
                | WildPat _              -> I_ConstrCase (None, [], i_exp)
                | NatPat  (n, _)         -> I_NatCase    (n,        i_exp)
                | CharPat (c, _)         -> I_CharCase   (c,        i_exp)
                | VarPat  ((id, typ), _) -> let ityp = type2itype ([], typ, unsetToplevel ctxt) in
                  I_VarCase (id, ityp, i_exp)
                | RestrictedPat (ms_pat, _, _) -> getUnionCase (ms_pat, ms_cond, ms_tm) % cond will be ignored, is just a filler 
                | _ -> 
                  fail (mkInOpStr ctxt ^ "unsupported feature: pattern not supported, use embed or wildcard pattern instead:\n"
                          ^ " pattern = " ^ printPattern ms_pat ^ " = " ^ anyToString ms_pat 
                          ^ "\n inside term = " ^ printTerm ms_outer_tm ^ " = " ^ anyToString ms_outer_tm 
                          ^ "\n")
          in
          let i_unioncases = map getUnionCase ms_rules      in
          let i_expr       = term2expression (ms_arg, ctxt) in
          Some (I_UnionCaseExpr (i_expr, i_unioncases)))
     
   | _ -> 
     let _ = writeLine (mkInOpStr ctxt ^ "fail in simpleCoProductCase (wrong term format)") in
     None


% --------------------------------------------------------------------------------

op foldType (ms_type : MSType, ctxt : S2I_Context) : MSType =
 let opt_ms_type =
     foldriAQualifierMap (fn (q, id, ms_info, opt_ms_type) ->
                            case opt_ms_type of
                              | Some _ -> opt_ms_type
                              | _ -> 
                                if definedTypeInfo? ms_info then
                                  let (ms_tvs, ms_typ0) = unpackFirstTypeDef ms_info in
                                  %let ms_utyp  = unfoldBase (spc, ms_type)  in
                                  %let ms_utyp0 = unfoldBase (spc, ms_typ0) in
                                  if equivType? ctxt.ms_spec (ms_type, ms_typ0) then
                                    let b      = typeAnn ms_typ0                     in
                                    let qid    = Qualified (q, id)                   in
                                    let ms_tvs = map (fn tv -> TyVar (tv, b)) ms_tvs in
                                    Some (Base (qid, ms_tvs, b))
                                  else 
                                    None
                                else
                                  None)
                         None 
                         ctxt.ms_spec.types
 in
 case opt_ms_type of
   | Some new_ms_type -> new_ms_type
   | _ -> ms_type

end-spec
