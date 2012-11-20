(**
 Stand-alone C-code generation for specs
*)


SpecsToI2L qualifying spec
{

  import /Library/Legacy/DataStructures/ListPair

  import /Languages/MetaSlang/Specs/StandardSpec
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/MetaSlang/Specs/Environment
% import /Languages/MetaSlang/CodeGen/CodeGenTransforms  % stripSubtypesAndBaseDefs

  import /Languages/I2L/I2L

  op CUtils.cString (id : String) : String  % TODO: defined in CUtils.sw

  type S2I_Context = {
                      specname       : String,             % not (yet) used
                      isToplevel     : Bool,               % not used
                      useRefTypes    : Bool,               % always true
                      constrOps      : List   QualifiedId, % not used, constrOps are distinguished by their name (contain "__")
                      currentOpType  : Option QualifiedId
                      }

  op default_S2I_Context : S2I_Context =
    {
     specname      = "",
     isToplevel    = false,
     useRefTypes   = true,
     constrOps     = [],
     currentOpType = None
     }

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

      | Some (qid as Qualified(q,id)) -> %~(member(qid,ctxt.constrOps))
        let expl = explode q ++ explode id in
        let (indl,_) = foldl (fn((indl,n),c) -> if c = #_ then (n::indl,n+1) else (indl,n+1)) ([],0) expl in
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


  op generateI2LCodeSpec (spc          : Spec,
                          useRefTypes? : Bool, 
                          constrOps    : List QualifiedId)
    : I_ImpUnit =
    generateI2LCodeSpecFilter (spc, useRefTypes?, constrOps, fn(_) -> true)

  op generateI2LCodeSpecFilter (spc          : Spec, 
                                useRefTypes? : Bool,
                                constrOps    : List QualifiedId, 
                                filter       : QualifiedId -> Bool)
    : I_ImpUnit =
    let ctxt = {specname      = "", 
                isToplevel    = true, 
                useRefTypes   = useRefTypes?,
                constrOps     = constrOps,
                currentOpType = None}
    in
    %let spc = normalizeArrowTypesInSpec spc in
    let transformedOps = 
        foldriAQualifierMap (fn (q, id, opinfo, l1) ->
                               if filter (Qualified (q, id)) then
                                 let trOp = opinfo2declOrDefn (Qualified (q, id), opinfo, None, ctxt, spc) in
                                 l1 ++ [trOp]
                               else
                                 l1)
                            []
                            spc.ops
    in
    let res : I_ImpUnit = 
        {
         name     = "",%s pc.name:String,
         includes = [],
         decls    = {
                     typedefs = foldriAQualifierMap (fn (qid, name, typeinfo, l2) ->
                                                       if filter (Qualified (qid, name)) then
                                                         case typeinfo2typedef (Qualified (qid, name), typeinfo, ctxt, spc) of
                                                           | Some typedef -> l2 ++ [typedef]
                                                           | _            -> l2
                                                       else 
                                                         l2)
                                                    []
                                                    spc.types,
                     opdecls  = foldl (fn | (l3,OpDecl d) -> l3++[d] 
                                          | (l4,_)        -> l4)
                                      []
                                      transformedOps,

                     funDecls = foldl (fn | (l5,FunDecl d)              -> l5++[d]
                                          | (l6,FunDefn{decl=d,body=_}) -> l6++[d]
                                          | (l7,_)                      -> l7)
                                      [] 
                                      transformedOps,

                     funDefns = foldl (fn | (l8,FunDefn d) -> l8++[d] 
                                          | (l9,_)         -> l9)
                                      []
                                      transformedOps,

                     varDecls = foldl (fn | (l10,VarDecl d) -> l10++[d] 
                                          | (l11,_)         -> l11)
                                      [] 
                                      transformedOps,

                     mapDecls = foldl (fn | (l12,MapDecl d) -> l12++[d] 
                                          | (l13,_)         -> l13)
                                      [] 
                                      transformedOps
                    }
        }
    in
    res

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                    %
  %                       TYPES -> I2L.TYPES                           %
  %                                                                    %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (**
   transforms a typeinfo into a type definition; the name of the type
   is the unqualified name, the qualifier is ignored.
   *)
  op typeinfo2typedef (Qualified (q, id) : QualifiedId,
                       info              : TypeInfo,
                       ctxt              : S2I_Context,
                       spc               : Spec)
    : Option I_TypeDefinition =
    if definedTypeInfo? info then
      let (tvs, typ) = unpackFirstTypeDef info in
      let typename = (q, id) in
      Some (typename, type2itype (tvs, typ, ctxt, spc))
    else
      None 

  type LeLt   = | LE | LT
  type MinMax = | Min | Max

  op find_simple_constant_bounds (tm : MSTerm) : Option (Int * Int) =
    %% returns Some (m, n) if the type directly expresses the inclusive range [m, n], otherwise None
    let 

      def eval_const tm =
        %% todo: could be smarter, but for now just recognizes constant terms such as 10 or -10, but not 3+4 or 2**8, etc.
        case tm of
          | Fun   (Nat m,_,_)                                                      -> Some m
          | Apply (Fun(Op(Qualified("IntegerAux","-"),_),_,_), Fun(Nat m,_,_), _) -> Some (-m)
          | _ -> None

      def find_min_bound vid tm1 tm2 =
        %% look for simple constant lower bounds such as '-10 < x', 'x >= 100', etc. 
        let maybe_min =
            case (vid, tm1, tm2) of
              | ("<",  bound,        Var ((v,_),_)) -> Some (bound, LT, v)
              | ("<=", bound,        Var ((v,_),_)) -> Some (bound, LE, v)
              | (">",  Var((v,_),_), bound        ) -> Some (bound, LT, v)
              | (">=", Var((v,_),_), bound        ) -> Some (bound, LE, v)
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
              | ("<",  Var((v,_),_), bound         ) -> Some (v, LT, bound)
              | ("<=", Var((v,_),_), bound         ) -> Some (v, LE, bound)
              | (">",  bound,        Var ((v,_),_) ) -> Some (v, LT, bound)
              | (">=", bound,        Var ((v,_),_) ) -> Some (v, LE, bound)
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
          | Apply (Fun(Op(Qualified("Integer",id),_),_,_),
                   Record ([("1",tm1),("2",tm2)],_),
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
    case tm of
      | Lambda([(VarPat ((vid,_),_),
                 Fun (Bool true, _, _),
                 Apply  (Fun(And,_,_), Record ([("1",tm1), ("2",tm2)], _), _))],
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
      | _ -> None

  op type2itype (tvs  : TyVars,
                 typ  : MSType,
                 ctxt : S2I_Context,
                 spc  : Spec)
    : I_Type =
    let utyp = unfoldToSpecials (typ, spc) in
    %let utyp = unfoldBaseVP(spc,typ,false,true) in
    case utyp of

      % ----------------------------------------------------------------------
      % primitives
      % ----------------------------------------------------------------------

      | Boolean _                                    -> I_Primitive I_Bool
      | Base(Qualified("Nat",       "Nat"),    [],_) -> I_Primitive I_Nat
      | Base(Qualified("Integer",   "Int"),    [],_) -> I_Primitive I_Int
      | Base(Qualified("Character", "Char"),   [],_) -> I_Primitive I_Char
      | Base(Qualified("String",    "String"), [],_) -> I_Primitive I_String
     %| Base(Qualified("Float",     "Float"),  [],_) -> I_Primitive I_Float

      % ----------------------------------------------------------------------

     % reference type
     %| Base(Qualified("ESpecPrimitives","Ref"),[typ],_) -> Ref(type2itype(ctxt,spc,tvs,typ))

     %| Base(Qualified(_,"List"),[ptyp],_) ->
     %    let ptype = type2itype(ctxt,spc,tvs,ptyp) in
     %    List(ptype)

     %| Base(Qualified(_,"List"),[ptyp],_) ->
     %  System.fail("sorry, this version of the code generator doesn't support lists.")
     %         
     %     System.fail("if using List type, please add a term restricting "^
     %     "the length of the list\n       "^
     %     "(e.g. \"{l:List("^printType(ptyp)^")| length(l) <= 32}\")")
     % ----------------------------------------------------------------------

      | Subtype (Base (Qualified ("Nat", "Nat"), [], _),
                 %% {x : Nat -> x < n} where n is a Nat
                 Lambda([(VarPat((X,_),_),
                          Fun (Bool true, _, _),
                          Apply(Fun(Op(Qualified(_,pred),_),_,_),
                                Record([(_,Var((X0,_),_)),
                                        (_,Fun(Nat(n),_,_))],
                                       _),
                                _)
                        )],_),_) 
        -> 
        if X = X0 then 
          (case pred of
             | "<=" ->  I_BoundedNat n
             | "<"  ->  I_BoundedNat (n - 1)
             | _    ->  I_Primitive  I_Nat)
        else 
          I_Primitive I_Nat

      | Subtype (Base (Qualified ("Integer", "Int"), [], _), pred, _) ->
        (case find_simple_constant_bounds pred of
           | Some (m, n) ->
             if m = 0 then
               I_BoundedNat n
             else
               I_BoundedInt (m, n)
           | _ ->
             I_Primitive I_Int)

      % ----------------------------------------------------------------------
      % special form for list types, term must restrict length of list
      % the form of the term must be {X:List(T)| length(X) < N}
      % where N must be a constant term evaluating to a positive Nat
      % lenght(X) <= N, N > length(X), N >= length(X), N = length(X) can also be used
      % ----------------------------------------------------------------------

      | Subtype (Base (Qualified ("List", "List"), [ptyp], _), tm, _) ->
        let ptype = type2itype (tvs, ptyp, unsetToplevel ctxt, spc) in
        let err = "wrong form of restriction term for list length" in
        (case tm of
           | Lambda ([(VarPat((X,_),_),
                       Fun (Bool true, _, _),
                       t2)],
                     _)
             -> 
             (case t2 of
                | Apply(Fun(cmp,_,_),
                        Record([arg1,arg2],_),_) ->
                  let
                    def checklengthterm((_,lengthop),(_,constantterm),minconst) =
                      let _ = 
                          case lengthop of
                            | Apply (Fun (Op (Qualified (_, "length"), _), _, _),
                                     V, 
                                     _)
                              ->
                              (case V of
                                 | Var ((X0, _), _) -> if X = X0 then () else fail err
                                 | _ -> fail err)
                            | _ -> fail err
                      in
                      let const = constantTermIntValue (constantterm, spc) in
                      if const < minconst then fail err else const
                  in
                  (case cmp of
                     | Op (Qualified (_, comparesym), _) ->
                       (case comparesym of
                          | ">"  -> let const = checklengthterm (arg2, arg1, 2) in I_BoundedList (ptype, const - 1)
                          | "<"  -> let const = checklengthterm (arg1, arg2, 2) in I_BoundedList (ptype, const - 1)
                          | "<=" -> let const = checklengthterm (arg1, arg2, 1) in I_BoundedList (ptype, const)
                          | ">=" -> let const = checklengthterm (arg2, arg1, 1) in I_BoundedList (ptype, const)
                          | _ -> fail err)
                     | Eq -> let const = checklengthterm(arg1,arg2,1) in
                       I_BoundedList (ptype, const))
                | _ -> fail err)
           | _ -> fail err)

      % ----------------------------------------------------------------------
      % for arrow types make a distinction between products and argument lists:
      % op foo(n:Nat,m:Nat) -> Nat must be called with two Nats
      % ----------------------------------------------------------------------

      | Arrow (typ1, typ2, _) ->
        let typ1 = unfoldToSpecials (typ1, spc) in
        %let typ1 = unfoldToProduct(spc,typ1) in
        (case typ1 of
           | Product (fields, _) ->
             let types = map (fn (_, typ) -> 
                                let typ = unfoldToSpecials (typ, spc) in
                                type2itype (tvs, typ, unsetToplevel ctxt, spc)) 
                             fields
             in
             let typ = type2itype (tvs, typ2, unsetToplevel ctxt, spc) in
             I_FunOrMap (types, typ)
           | _ -> 
             let dom_type =
                 case type2itype (tvs, typ1, unsetToplevel ctxt, spc) of
                   | I_Tuple types -> types
                   | typ -> [typ]
             in
             I_FunOrMap (dom_type, 
                         type2itype (tvs, typ2, unsetToplevel ctxt, spc)))

      % ----------------------------------------------------------------------

      | Product (fields, _) ->
        if numbered? fields then
          let types = 
              map (fn (_,typ) -> 
                     type2itype (tvs, typ, unsetToplevel ctxt, spc)) 
                  fields 
          in
          if types = [] then I_Void else I_Tuple types
        else
          let structfields = 
              map (fn (id, typ) -> 
                     (id, type2itype (tvs, typ, unsetToplevel ctxt, spc)))
                  fields
          in
          if structfields = [] then I_Void else I_Struct structfields

      % ----------------------------------------------------------------------

      | CoProduct(fields,_) ->
        let unionfields = map (fn | (id,None)     -> (id, I_Void)
                                  | (id,Some typ) -> (id, type2itype (tvs, typ, unsetToplevel ctxt, spc)))
                              fields
        in
        I_Union unionfields

      % ----------------------------------------------------------------------

      | TyVar _ -> 
        if ctxt.useRefTypes then 
          I_Any
        else
          fail("sorry, this version of the code generator doesn't support polymorphic types.")

      % ----------------------------------------------------------------------
      % use the base types as given, assume that the original definition has been checked
      % ----------------------------------------------------------------------

      | Base (Qualified (q, id), _, _) -> I_Base (q, id)

      | Subtype (typ, trm, _) -> % ignore the term...
        type2itype (tvs, typ, ctxt, spc)

      | Quotient (typ, trm, _) -> % ignore the term...
        type2itype (tvs, typ, ctxt, spc)

      | _ ->
        fail ("sorry, code generation doesn't support the use of this type:\n       "
                ^ printType typ)

  op constantTermIntValue (tm : MSTerm, spc : Spec) : Int =
    let 
      def err () = 
        let _ = print tm in
        fail ("cannot evaluate the constant value of term " ^ printTerm tm)
    in
    case tm of
      | Fun (Nat n, _, _) -> n
      | Fun (Op (qid, _), _, _) -> 
        (case getOpDefinition (qid, spc) of
           | None -> err()
           | Some tm -> constantTermIntValue (tm, spc))
      | _ -> err()


  (**
   returns the definition term of the given op, if it exists in the given spec.
   *)
  op getOpDefinition (Qualified (q, id) : QualifiedId, spc : Spec) : Option MSTerm =
    case findAQualifierMap (spc.ops, q, id) of
      | Some info ->
        if definedOpInfo? info then
          Some (firstOpDefInnerTerm info)
        else
          None
      | _ -> None

  (**
    unfolds a type, only if it is an alias for a Product, otherwise it's left unchanged;
    this is used to "normalize" the arrow types, i.e. to detect, whether the first argument of
    an arrow type is a product or not. Only "real" products are unfolded, i.e. type of the
    form (A1 * A2 * ... * An) are unfolded, not those of the form {x1:A1,x2:A2,...,xn:An}
  *)
  op  unfoldToProduct (typ : MSType, spc : Spec) : MSType =
    let
      def unfoldRec typ =
        let utyp = unfoldBaseKeepPrimitives (typ, spc) in
        if utyp = typ then typ else unfoldRec utyp

    in
    let utyp = unfoldRec typ in
    case utyp of
      | Product (fields, _) -> if numbered? fields then utyp else typ
      | _ -> typ


  op unfoldToCoProduct (typ : MSType, spc : Spec) : MSType =
    let
      def unfoldRec typ =
        let utyp = unfoldBase (spc, typ) in
        if utyp = typ then typ else unfoldRec utyp

    in
    let utyp = unfoldRec typ in
    case utyp of
      | CoProduct (fields, _) -> utyp
      | _ -> typ

  % unfold to special type in order to get the necessary information to generate code
  % e.g. unfold to type of the form {n:Nat|n<C} which is needed to generate arrays

  op unfoldToSpecials (typ : MSType, _ : Spec) : MSType = 
    typ

  op unfoldToSpecials1 (typ : MSType, spc : Spec) : MSType =
    let
      def unfoldToSpecials0 typ =
        let
          def unfoldRec typ =
            let utyp = unfoldBaseKeepPrimitives (typ, spc) in
            if utyp = typ then typ else unfoldRec utyp
        in
        let utyp = unfoldRec typ in
        case utyp of
          % this corresponds to a term of the form {x:Nat|x<C} where C must be a Integer const
          | Subtype (Base (Qualified (_, "Nat"), [], _),
                     Lambda ([(VarPat((X,_), _), 
                               Fun (Bool true, _, _),
                               Apply (Fun (Op (Qualified(_,"<"), _), _, _),
                                      Record([(_, Var ((X0,_), _)),
                                              (_, Fun (Nat(n), _, _))],
                                             _),
                                      _))],
                             _),
                     _) 
            -> 
            if X = X0 then utyp else typ
        | _ -> typ
    in
    mapType (fn tm -> tm, unfoldToSpecials0, fn pat -> pat) typ
  
  op normalizeArrowTypesInSpec (spc : Spec) : Spec =
    mapSpec (fn tm -> tm,
             fn | Arrow (typ1, typ2, X) -> 
                  Arrow (unfoldToProduct (typ1, spc), typ2, X)
                | typ -> typ,
             fn pat -> pat) 
            spc

 op unfoldBaseKeepPrimitives (typ : MSType, spc : Spec) : MSType =
   case typ of
     | Base (qid, typs, a) ->
       (case AnnSpec.findTheType (spc, qid) of
          | Some info ->
            (if ~ (definedTypeInfo? info) then
               typ
             else
               let (tvs, typ2) = unpackFirstTypeDef info in
               let
                 def continue () =
                   let styp = substType (zip (tvs, typs), typ2) in
                   unfoldBaseKeepPrimitives (styp, spc)
               in
               case typ of
                 | Boolean                                         _  -> typ
                 | Base (Qualified ("Nat",     "Nat"),    [],      _) -> typ
                 | Base (Qualified ("Integer", "Int"),    [],      _) -> typ
                 | Base (Qualified ("Char",    "Char"),   [],      _) -> typ
                 | Base (Qualified ("String",  "String"), [],      _) -> typ

                 | Base (Qualified ("List",    "List"),   [ptyp],  X) ->
                   Base (Qualified ("List",    "List"),   
                         [unfoldBaseKeepPrimitives (ptyp, spc)], 
                         X)

                 | Base (Qualified ("Option",  "Option"), [ptyp],  X) ->
                   Base (Qualified ("Option",  "Option"), 
                         [unfoldBaseKeepPrimitives (ptyp, spc)],
                         X)

                 | _ -> continue ())
          | _ -> typ)
     | _ -> typ


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
                        info        : OpInfo,
                        optParNames : Option (List String),
                        ctxt        : S2I_Context, 
                        spc         : Spec)
    : opInfoResult =
    let Qualified(q,id) = qid in
    let (tvs, typ, _) = unpackFirstOpDef info in
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

                  | VarPat ((id,_), _) -> 
                    [cString id]

                  | RecordPat (plist, _) -> 
                    map (fn | (_,VarPat((id,_),_)) -> cString id
                            | _ -> fail (err ()))
                        plist

                  | RestrictedPat (VarPat((id,_),_), _, _) -> 
                    [cString id]

                  | RestrictedPat (RecordPat(plist,_), _, _) -> 
                    map (fn | (_,VarPat((id,_),_)) -> cString id
                            | _ -> fail (err ()))
                        plist

                  | _ -> 
                    fail (err ())
            in
            (plist,body)
          | _ -> fail (err())

      def alignTypes pnames types =
        %% given one var and a list of types, convert list of types to a tuple type
        case (pnames, types) of
          | ([_], [_])   -> types
          | ([_], _)     -> [I_Tuple types]
          | (_,   [typ]) -> map (fn _ -> I_Void) pnames  % TODO: fix this
          | _            -> types

    in
    let Qualified (q, lid) = qid in
    let id   = (q, lid)                                       in
    let id0  = (q, "__" ^ lid ^ "__")                         in
    let typ  = unfoldToArrow (spc, typ)                       in
    let typ  = type2itype (tvs, typ, unsetToplevel ctxt, spc) in
    let ctxt = setCurrentOpType (qid, ctxt)                   in
    case typ of 
      | I_FunOrMap (types, rtype) ->
        if definedOpInfo? info then
          let tm = firstOpDefInnerTerm info           in
          % let tm = liftUnsupportedPattern (tm, spc) in  % must do this in prior pass before pattern match compilation
          let (pnames,body) = getParamNames(ctxt,tm) in
          let types = alignTypes pnames types in
          let decl = {name       = id,
                      params     = zip (pnames, types),
                      returntype = rtype}
          in
          let expr = term2expression (body, ctxt, spc) in
          FunDefn {decl = decl,
                   body = I_Exp expr} % functional function body
        else
          let params = 
              case optParNames of
                | Some pnames -> 
                  let types = alignTypes pnames types in
                  zip (pnames, types)
                | _ -> 
                  map (fn t -> ("", t)) types
          in
          FunDecl {name       = id,
                   params     = params,
                   returntype = rtype}
      | _ -> 
        let opt_exp = 
            if definedOpInfo? info then
              let tm = firstOpDefInnerTerm info in
              Some (term2expression (tm, ctxt, spc))
            else
              None
        in
        OpDecl (id, typ, opt_exp)

  % --------------------------------------------------------------------------------

  op qid2varid (Qualified (q, id) : QualifiedId) : I_VarName = (q, id)

  op term2expression (tm : MSTerm, ctxt : S2I_Context, spc : Spec) : I_TypedExpr =
    let typ  = inferType (spc, tm)                            in
    let typ  = unfoldBaseKeepPrimitives (typ, spc)            in
    let exp  = term2expression_internal (tm, typ, ctxt, spc)  in
    let ityp = type2itype ([], typ, unsetToplevel ctxt, spc)  in
    let cast? = 
        case exp of
          | I_FunCall(("TranslationBuiltIn", "failWith"), _, _) -> true
          | _ -> false
    in
    {expr = exp, typ = ityp, cast? = cast?}

  op term2expression_internal (tm : MSTerm, typ : MSType, ctxt : S2I_Context, spc : Spec) : I_Expr =

    % Accord hack:
    % checks, whether the given id is an outputop of the espec; if yes is has to be
    % replaced by a VarDeref/FunCallDeref, as done below
    %    let def isOutputOp(varid as (spcname,lid)) =
    %          let outputops = ctxt.espc.interface.outputops in
    %    (spcname = ctxt.espc.spc.name) && lid in? outputops)
    %    in

    case tm of
      | Apply      (t1,            t2,  _) -> term2expression_apply  (t1,  t2,    tm, typ, ctxt, spc)
      | Record     (fields,             _) -> term2expression_record (fields,     tm,      ctxt, spc)
      | Let        ([(pat,deftm)], tm,  _) -> term2expression_let    (pat, deftm, tm,      ctxt, spc)
      | Var        ((id, _),            _) -> I_Var ("", id)
      | Fun        (fun,           typ, _) -> term2expression_fun    (fun, typ,   tm,      ctxt, spc)
      | IfThenElse (t1, t2, t3,         _) -> I_IfExpr (term2expression (t1, ctxt, spc),
                                                        term2expression (t2, ctxt, spc),
                                                        term2expression (t3, ctxt, spc))
      | Seq        (tms,                _) -> I_Comma (map (fn tm -> term2expression (tm, ctxt, spc)) tms)
      | TypedTerm  (tm, typ,            _) -> let typed_expr = term2expression (tm, ctxt, spc) in typed_expr.expr  % TODO: add cast? ??
      | _ -> 
        % Bind, The, LetRec, Lambda, Transform, Pi, And, Any 
        let s = "Unrecognized term in term2expression: " ^ printTerm tm in
        let _ = writeLine s in
        I_Str s

  op alt_index (x : Id, typ : MSType, spc : Spec) : Nat =
    let 
      def aux (n, alts) =
        case alts of
          | [] -> 0
          | (alt,_) :: alts ->
            if alt = x then 
              n
            else
              aux (n + 1, alts)
    in
    case unfoldToCoProduct (typ, spc) of
      | CoProduct (alts,_) -> aux (1, alts)
      | _ -> 
        let _ = writeLine ("Type is not a coproduct, so index is 0: " ^ printType typ) in
        0

  op term2expression_fun (fun : Fun, typ : MSType, tm : MSTerm, ctxt : S2I_Context, spc : Spec) : I_Expr =

    % This is called when a Fun occurs "standalone", i.e. not in the context of an apply.
    % We restrict the possible forms to those not having an arrow type, 
    % i.e. we don't support functions as objects
    % Not, And, Or, etc,. should never occur "standalone", so we don't look for them here
    % See process_t1 below for case where Fun is applied.

    if arrowType? (typ, spc) then
      case fun of
        | Op (qid,_) -> I_VarRef (qid2varid qid)
        | _ -> 
          fail("sorry, functions as objects (higher-order functions) are not yet supported:\n" ^ printTerm tm)
    else
      case fun of
        | Nat    n -> I_Int  n
        | String s -> I_Str  s
        | Char   c -> I_Char c
        | Bool   b -> I_Bool b

        | Op (qid, _) -> 
          let varname = qid2varid qid in
          %if isOutputOp varname then VarDeref varname else 
          I_Var varname

        | Embed (id,_) -> 
          let selector = {name = id, index = alt_index (id, typ, spc)} in
          if useConstrCalls? ctxt then
            case typ of
              
              | Base (qid, _, _) ->
                let vname = qid2varid qid in
                I_ConstrCall (vname, selector, [])

              | Boolean _ -> 
                I_ConstrCall (("Boolean", "Boolean"), selector, [])

              | _ -> 
                I_AssignUnion (selector, None)
          else
            I_AssignUnion (selector, None)

        | _ -> 
          fail (mkInOpStr ctxt ^ "unsupported Fun: " ^ printTerm tm)

  op getExprs4Args (args : MSTerms, ctxt : S2I_Context, spc : Spec) : List I_TypedExpr = 
    map (fn tm -> term2expression (tm, ctxt, spc)) args

  op term2expression_apply (t1 : MSTerm, t2 : MSTerm, tm : MSTerm, typ : MSType, ctxt : S2I_Context, spc : Spec) : I_Expr =
    let args = 
        % extract the list of argument terms from a record term given
        % as second argument of an Apply term
        case t2 of
          | Record (fields, _) ->
            if numbered? fields then
              map (fn (_,t) -> t) fields
            else
              [t2]
          | _ -> [t2]

    in
    case getBuiltinExpr (t1, args, ctxt, spc) of
      | Some expr -> expr
      | _ ->
        let origlhs = t1 in
        let

          def getProjectionList (tm, projids) =
            case tm of
              | Apply (Fun (Project id, _, _), t2, _) -> getProjectionList (t2, id::projids)
              | _ -> (projids, tm)

          % this is a sub-def, because we collect and skip projections
          def process_t1 (t1, projections) =
            case t1 of

              | Var ((id, _), _) ->
                let exprs = getExprs4Args (args, ctxt, spc) in
                let varname = ("", id) in
                % infer the type of the original lhs to get the real type of the map
                % taking all the projections into account
                let lhstype = inferType (spc, origlhs)                          in
                let lhstype = unfoldToSpecials (lhstype, spc)                   in
                let lhstype = type2itype ([], lhstype, unsetToplevel ctxt, spc) in
                I_FunCall(varname,projections,exprs)
                
              | Fun (fun, _, _) -> term2expression_apply_fun (fun, origlhs, projections, t2, args, tm, typ, ctxt, spc)
              | _ ->
                case getProjectionList (t1, []) of
                  | (prjs as (_::_), t1) -> process_t1 (t1, prjs)
                  | _ -> 
                    % handle special cases:
                    case simpleCoProductCase (tm, ctxt, spc) of
                      | Some expr -> expr
                      | _ ->
                        let msg = mkInOpStr ctxt ^ "cannot yet handle: " ^ printTerm t1 in
                        let _ = writeLine msg in
                        I_Str msg
                        
        in
        process_t1 (t1, [])

  op term2expression_apply_fun (fun         : Fun, 
                                origlhs     : MSTerm,
                                projections : List Id, 
                                t2          : MSTerm,
                                args        : MSTerms,
                                tm          : MSTerm, 
                                typ         : MSType, 
                                ctxt        : S2I_Context, 
                                spc         : Spec) 
    : I_Expr =
    case fun of
      | Op (qid, _) ->
        let exprs   = getExprs4Args (args, ctxt, spc)                   in
        let varname = qid2varid qid                                     in
        % infer the type of the original lhs to get the real type of the map
        % taking all the projections into account
        let lhstype = inferType (spc, origlhs)                          in
        let lhstype = unfoldToSpecials (lhstype, spc)                   in
        let lhstype = type2itype ([], lhstype, unsetToplevel ctxt, spc) in
        %if isOutputOp varname then MapAccessDeref (varname,lhstype,projections,exprs) else 
        if isVariable (ctxt, qid) then
          I_MapAccess (varname, lhstype, projections, exprs)
        else
          I_FunCall (varname, projections, exprs)
                  
      | Embed (id, _) ->
        let 
          def mkExpr2() = term2expression (t2, ctxt, spc)
        in
        if projections = [] then
          % let typ = foldType (typ, spc) in
          let selector = {name = id, index = alt_index (id, typ, spc)} in
          if useConstrCalls? ctxt then
            case typ of
              
              | Base (qid, _, _) ->
                let vname = qid2varid qid in
                let exprs = case t2 of
                              | Record (fields, b) ->
                                if numbered? fields then
                                  map (fn (_,tm) -> term2expression (tm, ctxt, spc)) fields
                                else 
                                  [mkExpr2()]
                              | _ -> 
                                [mkExpr2()]
                in
                I_ConstrCall (vname, selector, exprs)
                        
              | Boolean _ -> 
                let exprs = case t2 of
                              | Record (fields, b) ->
                                if numbered? fields then
                                  map (fn(_,tm) -> term2expression (tm, ctxt, spc)) fields
                                else 
                                  [mkExpr2()]
                              | _ -> 
                                [mkExpr2()]
                in
                I_ConstrCall (("Boolean", "Boolean"), selector, exprs)

              | _ -> 
                I_AssignUnion (selector, Some (mkExpr2()))
          else 
            I_AssignUnion (selector, Some (mkExpr2()))

        else 
          fail (mkInOpStr ctxt ^ "not handled as fun to be applied: " ^ anyToString fun)

      | Embedded id -> 
        let lhstype = inferType (spc, origlhs)        in
        let index =
            case unfoldToArrow (spc, lhstype) of
              | Arrow (super_type, Bool, _) ->
                %% type of a predicate used to test for variants among a coproduct
                alt_index (id, super_type, spc) 
              | _ ->
                let _ = writeLine ("Expected arrow type: " ^ printType lhstype) in
                0
        in
        let selector = {name = id, index = index} in
        I_Embedded (selector, term2expression (t2, ctxt, spc))

      | Select id ->
        let expr2 = term2expression (t2, ctxt, spc) in
        if projections = [] then 
          % let union = I_Project(expr2,"alt") in
          % let (_,ityp2) = expr2 in
          % I_Select ((union, ityp2), id)
          I_Select (expr2, id)
        else 
          fail (mkInOpStr ctxt ^ "not handled as selection: " ^ anyToString id ^ " given projections " ^ anyToString projections)

      | Project id ->
        let expr2 = term2expression (t2, ctxt, spc) in
        if projections = [] then 
          I_Project(expr2,id)
        else 
          fail (mkInOpStr ctxt ^ "not handled as projection: " ^ anyToString id ^ " given projections " ^ anyToString projections)

      | _ ->
        fail (mkInOpStr ctxt ^ "not handled as fun to be applied: " ^ anyToString fun)

  op term2expression_let (pat : MSPattern, deftm : MSTerm, tm : MSTerm, ctxt : S2I_Context, spc : Spec) : I_Expr =
    % let's can only contain one pattern/term entry (see parser)
    case pat of

      | VarPat ((id, typ), _) ->
        let defexp = term2expression (deftm, ctxt, spc)            in
        let exp    = term2expression (tm,    ctxt, spc)            in
        let typ    = type2itype ([], typ, unsetToplevel ctxt, spc) in
        I_Let (id, typ, defexp, exp)

      | WildPat _ ->
        let defexp = term2expression (deftm, ctxt, spc) in
        let exp    = term2expression (tm,    ctxt, spc) in
        I_Comma [defexp, exp]

      | _ -> 
        fail (mkInOpStr ctxt ^ "unsupported feature: this form of pattern cannot be used in a let:\n" ^ printPattern pat)

  op term2expression_record (fields : List (Id * MSTerm), tm : MSTerm, ctxt : S2I_Context, spc : Spec) : I_Expr = 
    if numbered? fields then
      let exps = map (fn (_, tm) -> term2expression (tm, ctxt, spc)) fields in
      I_TupleExpr exps
    else
      let fields = map (fn (id, tm) -> (id, term2expression (tm, ctxt, spc))) fields in
      I_StructExpr fields

  op arrowType? (typ : MSType, spc : Spec) : Bool =
    case unfoldToArrow (spc, typ) of
      | Arrow _ -> true
      | _ -> false

  op getEqOpQid (Qualified (q, id) : QualifiedId) : QualifiedId =
    Qualified (q, "eq_" ^ id)

  op equalsExpression (t1 : MSTerm, t2 : MSTerm, ctxt : S2I_Context, spc : Spec) 
    : I_Expr =
    let

      def t2e tm = 
        term2expression (tm, ctxt, spc)

      def primEq () =
        I_Builtin (I_Equals (t2e t1, t2e t2))

    in

    % analyse, which equal we need; let's hope type checking
    % already made sure, that the types fit, so just look at one
    % of the terms
    let typ = inferType (spc, t1) in
    %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
    let utyp = stripSubtypesAndBaseDefs spc typ in
    case utyp of
      | Boolean                         _  -> primEq ()
      | Base (Qualified ("Bool",    "Bool"),   [],_) -> primEq ()
      | Base (Qualified ("Nat",     "Nat"),    [],_) -> primEq ()  % TODO: is this possible?
      | Base (Qualified ("Integer", "Int"),    [],_) -> primEq ()
      | Base (Qualified ("Char",    "Char"),   [],_) -> primEq ()
      | Base (Qualified ("Float",   "Float"),  [],_) -> primEq ()
      | Base (Qualified ("String",  "String"), [],_) -> I_Builtin (I_StrEquals (t2e t1,t2e t2))
      | _ ->
        let typ = foldType (termType t1, spc) in
        let 
          def errmsg () = 
            "sorry, the current version of the code generator doesn't support the equality check for\ntype = "
            ^ printType typ ^ "\n t1 = " ^ printTerm t1 ^ "\n t2 = " ^ printTerm t2
        in
        case typ of

          | Base(qid,_,_) ->
            let eqid as Qualified (eq, eid) = getEqOpQid qid in
            (case AnnSpec.findTheOp(spc,eqid) of
               | Some _ ->
                 let eqfname = (eq, eid) in
                 I_FunCall (eqfname, [], [t2e t1, t2e t2])
               | _ ->
                 % let _ = appOpInfos (fn info -> writeLine (anyToString info.names)) spc.ops in
                 let _ = writeLine ("eq-op not found for " ^ anyToString qid ^ " via " ^ anyToString eqid) in
                 let eqfname = (eq, eid) in
                 I_FunCall (eqfname, [], [t2e t1, t2e t2]))

          | Product (fields, _) ->
            let eqtm       = getEqTermFromProductFields (fields, typ, t1, t2) in
            let typed_expr = t2e eqtm in
            typed_expr.expr

          | _ -> 
            fail (errmsg() ^ "\n[term type must be a base or product type]") %primEq()

  op getEqTermFromProductFields (fields : List (Id * MSType),
                                 otyp   : MSType,
                                 varx   : MSTerm,
                                 vary   : MSTerm)
    : MSTerm =
    let b       = typeAnn otyp in
    let default = mkTrue()     in
    foldr (fn ((fid, ftyp), eq_all) ->
           let projtyp  = Arrow (otyp,                                 ftyp,          b) in
           let eqtyp    = Arrow (Product([("1",ftyp), ("2",ftyp)], b), Boolean b,     b) in
           let proj     = Fun   (Project fid, projtyp,                                b) in
           let t1       = Apply (proj,                varx,                           b) in
           let t2       = Apply (proj,                vary,                           b) in
           let eq_field = Apply (Fun(Equals,eqtyp,b), Record([("1",t1),("2",t2)],b),  b) in
           if eq_all = default then
             eq_field
           else
             Apply (mkAndOp b, Record ([("1",eq_field), ("2",eq_all)], b), b))
          default
          fields

  op getBuiltinExpr (tm   : MSTerm, 
                     args : MSTerms,
                     ctxt : S2I_Context,
                     spc  : Spec)
    : Option I_Expr =
    let
      def t2e tm = term2expression (tm, ctxt, spc)
    in
    let I_one : I_TypedExpr = {expr = I_Int 1, typ = I_Primitive I_Nat, cast? = false} in
    case (tm, args) of
      | (Fun (Equals,    _, _),                                          [t1,t2]) -> Some (equalsExpression (t1, t2, ctxt, spc))

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
      | (Fun (Op (Qualified ("Integer",    "isucc"),         _), _, _),  [t1])    -> Some (I_Builtin (I_IntPlus             (t2e t1, I_one)))
      | (Fun (Op (Qualified ("Integer",    "ipred"),         _), _, _),  [t1])    -> Some (I_Builtin (I_IntMinus            (t2e t1, I_one)))
      | (Fun (Op (Qualified ("Nat",        "succ"),          _), _, _),  [t1])    -> Some (I_Builtin (I_IntPlus             (t2e t1, I_one)))
      | (Fun (Op (Qualified ("Nat",        "pred"),          _), _, _),  [t1])    -> Some (I_Builtin (I_IntMinus            (t2e t1, I_one)))

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
      %      | (Fun(Op(Qualified("ESpecPrimitives","ref"),_),_,_),[t1])
      %        -> let def qid2varname(qid) =
      %                 case qid of
      %                   | Qualified(spcname,name) -> (spcname,name)
      %                  %| Local(name) -> (spc.name,name)
      %           in
      %           (case t1 of
      %              | Fun(Op(qid,_),_,_)
      %                -> %if member(qid,ctxt.vars) then Some(VarRef(qid2varname qid))
      %                   %else 
      %                       fail("\"ref\" can only be used for vars, but \""^
      %                            (qidstr qid)^"\" is not declared as a var.")
      %              | _ -> fail("\"ref\" can only be used for vars, not for:\n"^
      %                          printTerm(t1))
      %           )

      | _ -> None

  op isVariable (_ : S2I_Context, _ : QualifiedId) : Bool = 
    % In vanilla metaslang, as opposed to ESpecs, there are no variables,
    % but they might appear at a future date.
    false % member(qid, ctxt.vars)

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

  op simpleCoProductCase (tm : MSTerm, ctxt : S2I_Context, spc : Spec) : Option I_Expr =
    let outer_tm = tm in
    case tm of

      | Apply(embedfun as Lambda (rules,_), tm, _) ->
        (case rules of
           | [(p as VarPat ((v,ty), b), _, body)] ->
             % that's a very simple case: "case tm of v -> body" (no other case)
             % we transform it to "let v = tm in body"
             let typed_expr = term2expression (Let ([(p,tm)], body, b), ctxt, spc) in
             Some typed_expr.expr
           | _ -> 
             let

               def getTypeForConstructorArgs (typ, id) =
                 %let typ = unfoldBase(spc,typ) in
                 let typ = stripSubtypesAndBaseDefs spc typ in
                 case typ of
                   | CoProduct (fields,_) ->
                     (case findLeftmost (fn (id0, _) -> id0 = id) fields of
                        | Some(_,opttype) -> (case opttype of
                                                | Some typ -> Some (type2itype ([], typ, unsetToplevel ctxt, spc))
                                                | None -> None)
                        | _ -> fail("internal error: constructor id " ^ id ^ " of term " ^
                                      printTerm tm ^ " cannot be found."))
                   | _ -> 
                     let utyp = unfoldBase (spc, typ) in
                     if utyp = typ then
                       fail ("internal error: type of term is no coproduct: " ^
                               printTerm tm ^ ":" ^ printType typ)
                     else 
                       getTypeForConstructorArgs (utyp, id)

             in
             % check whether the pattern have the supported format, i.e.
             % (constructor name followed by var patterns) or (wildpat)
             let

               def getUnionCase (pat, cond, tm) =
                 let exp = term2expression (tm, ctxt, spc) in
                 case pat of

                   | EmbedPat (constructorId, optpat, parent_type, _) ->
                     % let opttype = getTypeForConstructorArgs (parent_type, constructorId) in
                     let vars =
                         case optpat of
                        
                           | None                       -> []
                           | Some (VarPat ((id, _), _)) -> [Some id]
                           | Some (WildPat _)           -> [None]
                          
                           | Some (pat as RecordPat (fields, _)) ->
                             % pattern must be a recordpat consisting of var or wildpattern
                             if numbered? fields then
                               map (fn | (_,WildPat _) -> None
                                       | (_,VarPat((id,_),_)) -> Some id
                                       | (_,pat) -> 
                                         fail (mkInOpStr ctxt ^ "unsupported feature: you can only use var patterns or _ here, not:\n" 
                                                 ^ printPattern pat))
                                   fields
                             else
                               fail (mkInOpStr ctxt ^ "unsupported feature: record pattern not supported:\n" 
                                       ^ printPattern pat)
                           | Some pat -> 
                             fail (mkInOpStr ctxt ^ "unsupported feature: you can only use "^
                                     "var patterns, tuples of these, or \"_\" here, "^
                                     "not:\n"^printPattern pat)
                     in
                     let selector = {name = constructorId, index = alt_index (constructorId, parent_type, spc)} in
                     I_ConstrCase (Some selector, vars, exp)

                   | WildPat _            -> I_ConstrCase (None, [], exp)
                   | NatPat  (n,_)        -> I_NatCase    (n,        exp)
                   | CharPat (c,_)        -> I_CharCase   (c,        exp)
                   | VarPat  ((id,typ),_) -> let ityp = type2itype([], typ, unsetToplevel ctxt, spc) in
                                             I_VarCase    (id, ityp, exp)
                   | RestrictedPat (pat, _, _) -> getUnionCase (pat, cond, tm) % cond will be ignored, is just a filler 
                   | _ -> 
                     fail (mkInOpStr ctxt ^ "unsupported feature: pattern not supported, use embed or wildcard pattern instead:\n"
                             ^ " pattern = " ^ printPattern pat ^ " = " ^ anyToString pat ^ "\n inside term = " ^ printTerm outer_tm ^ " = " ^ anyToString outer_tm ^ "\n")
             in
             let unioncases = map getUnionCase rules          in
             let expr       = term2expression (tm, ctxt, spc) in
             Some (I_UnionCaseExpr (expr, unioncases)))

      | _ -> 
        let _ = writeLine (mkInOpStr ctxt ^ "fail in simpleCoProductCase (wrong term format)") in
        None


% --------------------------------------------------------------------------------

 op foldType (typ : MSType, spc : Spec) : MSType =
   let opt_typ =
       foldriAQualifierMap (fn (q, id, info, opt_typ) ->
                              case opt_typ of
                                | Some _ -> opt_typ
                                | _ -> 
                                  if definedTypeInfo? info then
                                    let (tvs, typ0) = unpackFirstTypeDef info in
                                    %let utyp = unfoldBase(spc,typ) in
                                    %let utyp0 = unfoldBase(spc,typ0) in
                                    if equivType? spc (typ, typ0) then
                                      let b   = typeAnn typ0                     in
                                      let qid = Qualified (q, id)                in
                                      let tvs = map (fn tv -> TyVar (tv, b)) tvs in
                                      Some (Base (qid, tvs, b))
                                    else 
                                      None
                                  else
                                    None)
                           None 
                           spc.types
   in
   case opt_typ of
     | Some new_typ -> new_typ
     | _ -> typ


}
