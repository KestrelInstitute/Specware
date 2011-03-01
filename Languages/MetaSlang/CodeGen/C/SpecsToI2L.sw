(**
 Stand-alone C-code generation for specs
*)


SpecsToI2L qualifying spec
{

  % import ElaborateESpecs
  import I2L

  import /Library/Legacy/DataStructures/ListPair
  %import MergeSort

  %import SpecEnvironment
  %import MetaSlangPrint
  %import PrintESpecs

  import /Languages/MetaSlang/Specs/StandardSpec
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/MetaSlang/Specs/Environment

  type Term = MS.Term

  type CgContext = {
		    specname       : String,             % not (yet) used
		    isToplevel     : Bool,            % not used
		    useRefTypes    : Bool,            % always true
		    constrOps      : List   QualifiedId, % not used, constrOps are distinguished by their name (contain "__")
		    currentOpSort  : Option QualifiedId
		   }

  op defaultCgContext : CgContext =
    {
     specname      = "",
     isToplevel    = false,
     useRefTypes   = true,
     constrOps     = [],
     currentOpSort = None
     }

  op unsetToplevel (ctxt : CgContext) : CgContext =
    ctxt << {isToplevel = false}

  op setCurrentOpSort (ctxt : CgContext, qid : QualifiedId) : CgContext = 
    ctxt << {currentOpSort = Some qid}

  op mkInOpStr (ctxt : CgContext) : String =
    case ctxt.currentOpSort of
      | Some qid -> "in op \"" ^ (printQualifiedId qid) ^ "\": "
      | _ -> ""

  op useConstrCalls? (ctxt : CgContext) : Bool =
    case ctxt.currentOpSort of

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
    : IImpUnit =
    generateI2LCodeSpecFilter (spc, useRefTypes?, constrOps, fn(_) -> true)

  op generateI2LCodeSpecFilter (spc          : Spec, 
                                useRefTypes? : Bool,
                                constrOps    : List QualifiedId, 
                                filter       : QualifiedId -> Bool)
    : IImpUnit =
    let ctxt = {specname      = "", 
                isToplevel    = true, 
                useRefTypes   = useRefTypes?,
                constrOps     = constrOps,
                currentOpSort = None}
    in
    %let spc = normalizeArrowSortsInSpec(spc) in
    let transformedOps = 
        foldriAQualifierMap (fn (qid, name, opinfo, l1) ->
                               if filter (Qualified (qid, name)) then
                                 let trOp = opinfo2declOrDefn (ctxt, spc, Qualified (qid, name), opinfo, None) in
                                 l1 ++ [trOp]
                               else
                                 l1)
                            []
                            spc.ops
    in

    %let _ = writeLine("ops transformed.") in
    %let len = length transformedOps in
    %let _ = writeLine(";;            "^Integer.toString(len)^" ops have been transformed.") in
    %let _ = foldriAQualifierMap 
    %(fn(qid,name,(aliases,tvs,defs),l) -> 
    % let _ = writeLine("sort "^printQualifiedId(Qualified(qid,name))) in
    % let _ = writeLine("  typeVars: "^(foldl(fn(s,tv)->s^tv^" ") "" tvs)) in
    % let _ = writeLine("  aliases:     "^(foldl (fn(s,qid0) -> s^(printQualifiedId(qid0))^" ") "" aliases)) in
    % let _ = writeLine("  defs: ") in
    % let _ = app(fn(tvs,typ) -> 
    %    let _ = writeLine("   typeVars: "^(foldl(fn(s,tv)->s^tv^" ") "" tvs)) in
    %    writeLine("   "^printSort(typ))) defs in
    % l)
    %[] spc.sorts
    %in

    let res : IImpUnit = 
        {
         name     = "",%s pc.name:String,
         includes = [],
         decls    = {
                     typedefs = foldriAQualifierMap (fn (qid, name, sortinfo, l2) ->
                                                       if filter (Qualified (qid, name)) then
                                                         case sortinfo2typedef (ctxt, spc, Qualified (qid, name), sortinfo) of
                                                           | Some typedef -> l2 ++ [typedef]
                                                           | _            -> l2
                                                       else 
                                                         l2)
                                                    []
                                                    spc.sorts,
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
  %                       SORTS -> I2L.TYPES                           %
  %                                                                    %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (**
   transforms a sortinfo into a type definition; the name of the type
   is the unqualified name, the qualifier is ignored.
   *)
  op sortinfo2typedef (ctxt              : CgContext,
                       spc               : Spec,
                       Qualified (q, id) : QualifiedId,
                       info              : SortInfo)
    : Option ITypeDefinition =
    if definedSortInfo? info then
      let (tvs, typ) = unpackFirstSortDef info in
      let typename = (q, id) in
      Some (typename, type2itype (ctxt, spc, tvs, typ))
    else
      None 

  op type2itype (ctxt : CgContext,
                 spc  : Spec,
                 tvs  : TyVars,
                 typ  : Sort) 
    : IType =
    let utyp = unfoldToSpecials (spc, typ) in
    %let utyp = unfoldBaseVP(spc,typ,false,true) in
    case utyp of

      % ----------------------------------------------------------------------
      % primitives
      % ----------------------------------------------------------------------

      | Boolean _                         -> IPrimitive IBool
      | Base(Qualified(_,"Nat"),    [],_) -> IPrimitive INat
      | Base(Qualified(_,"Int"),    [],_) -> IPrimitive IInt
      | Base(Qualified(_,"Char"),   [],_) -> IPrimitive IChar
      | Base(Qualified(_,"String"), [],_) -> IPrimitive IString
     %| Base(Qualified(_,"Float"),  [],_) -> IPrimitive IFloat

      % ----------------------------------------------------------------------

     % reference type
     %| Base(Qualified("ESpecPrimitives","Ref"),[typ],_) -> Ref(type2itype(ctxt,spc,tvs,typ))

     %| Base(Qualified(_,"List"),[ptyp],_) ->
     %    let ptype = type2itype(ctxt,spc,tvs,ptyp) in
     %	  List(ptype)

     %| Base(Qualified(_,"List"),[ptyp],_) ->
     %  System.fail("sorry, this version of the code generator doesn't support lists.")
     %         
     %     System.fail("if using List sort, please add a term restricting "^
     %	   "the length of the list\n       "^
     %	   "(e.g. \"{l:List("^printSort(ptyp)^")| length(l) <= 32}\")")
		
      % ----------------------------------------------------------------------

      | Subsort (Base (Qualified (_, "Nat"), [], _),
                 Lambda([(VarPat((X,_),_),_,
                          Apply(Fun(Op(Qualified(_,"<"),_),_,_),
                                Record([(_,Var((X0,_),_)),
                                        (_,Fun(Nat(n),_,_))],
                                       _),
                                _)
			)],_),_) 
        -> 
        if X = X0 then 
          IRestrictedNat n
        else 
          IPrimitive INat


      % ----------------------------------------------------------------------
      % special form for list sorts, term must restrict length of list
      % the form of the term must be {X:List(T)| length(X) < N}
      % where N must be a constant term evaluating to a positive Nat
      % lenght(X) <= N, N > length(X), N >= length(X), N = length(X) can also be used
      % ----------------------------------------------------------------------

      | Subsort (Base (Qualified (_, "List"), [ptyp], _), tm, _) ->
        let ptype = type2itype (unsetToplevel ctxt, spc, tvs, ptyp) in
        let err = "wrong form of restriction term for list length" in
        (case tm of
           | Lambda ([(VarPat((X,_),_),t1,t2)],_) -> 
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
                      let const = constantTermIntValue (spc, constantterm) in
                      if const < minconst then fail err else const
                  in
                  (case cmp of
                     | Op (Qualified (_, comparesym), _) ->
                       (case comparesym of
                          | ">"  -> let const = checklengthterm (arg2, arg1, 2) in IBoundList (ptype, const - 1)
                          | "<"  -> let const = checklengthterm (arg1, arg2, 2) in IBoundList (ptype, const - 1)
                          | "<=" -> let const = checklengthterm (arg1, arg2, 1) in IBoundList (ptype, const)
                          | ">=" -> let const = checklengthterm (arg2, arg1, 1) in IBoundList (ptype, const)
                          | _ -> fail err)
                     | Eq -> let const = checklengthterm(arg1,arg2,1) in
                       IBoundList (ptype, const))
                | _ -> fail err)
           | _ -> fail err)

      % ----------------------------------------------------------------------
      % for arrow sorts make a distinction between products and argument lists:
      % op foo(n:Nat,m:Nat) -> Nat must be called with two Nats
      % ----------------------------------------------------------------------

      | Arrow (typ1, typ2, _) ->
        let typ1 = unfoldToSpecials (spc, typ1) in
        %let typ1 = unfoldToProduct(spc,typ1) in
        (case typ1 of
           | Product (fields, _) ->
             let types = map (fn (_, typ) -> 
                                let typ = unfoldToSpecials (spc, typ) in
                                type2itype (unsetToplevel ctxt, spc, tvs, typ)) 
                             fields
             in
             let typ = type2itype (unsetToplevel ctxt, spc, tvs, typ2) in
             IFunOrMap (types, typ)
           | _ -> 
             let dom_type =
                 case type2itype (unsetToplevel ctxt, spc, tvs, typ1) of
                   | ITuple types -> types
                   | typ -> [typ]
             in
             IFunOrMap (dom_type, 
                        type2itype (unsetToplevel ctxt, spc, tvs, typ2)))

      % ----------------------------------------------------------------------

      | Product (fields, _) ->
        if numbered? fields then
          let types = 
              map (fn (_,typ) -> 
                     type2itype (unsetToplevel ctxt, spc, tvs, typ)) 
                  fields 
          in
          if types = [] then IVoid else ITuple types
        else
          let structfields = 
              map (fn (id, typ) -> 
                     (id, type2itype (unsetToplevel ctxt, spc, tvs, typ)))
                  fields
          in
          if structfields = [] then IVoid else IStruct structfields

      % ----------------------------------------------------------------------

      | CoProduct(fields,_) ->
        let unionfields = map (fn | (id,None)     -> (id, IVoid)
                                  | (id,Some typ) -> (id, type2itype (unsetToplevel ctxt, spc, tvs, typ)))
			      fields
        in
        IUnion unionfields

      % ----------------------------------------------------------------------


      | TyVar _ -> 
        if ctxt.useRefTypes then 
          IAny
        else
          fail("sorry, this version of the code generator doesn't support polymorphic types.")

      % ----------------------------------------------------------------------
      % use the base sorts as given, assume that the original definition has been checked
      % ----------------------------------------------------------------------

      | Base (Qualified (q, id), _, _) -> IBase (q, id)

      | Subsort (typ, trm, _) -> % ignore the term...
	type2itype (ctxt, spc, tvs, typ)

      | _ ->
        fail ("sorry, code generation doesn't support the use of this sort:\n       "
                ^ printSort typ)

  op constantTermIntValue (spc : Spec, tm : Term) : Int =
    let 
      def err () = 
        let _ = print tm in
        fail ("cannot evaluate the constant value of term " ^ printTerm tm)
    in
    case tm of
      | Fun (Nat n, _, _) -> n
      | Fun (Op (qid, _), _, _) -> 
        (case getOpDefinition (spc, qid) of
           | None -> err()
           | Some t -> constantTermIntValue (spc, t))
      | _ -> err()


  (**
   returns the definition term of the given op, if it exists in the given spec.
   *)
  op getOpDefinition (spc : Spec, Qualified (q, id) : QualifiedId) : Option Term =
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
  op  unfoldToProduct (spc : Spec, typ : Sort) : Sort =
    let
      def unfoldRec typ =
	let utyp = unfoldBaseKeepPrimitives (spc, typ) in
	if utyp = typ then typ else unfoldRec utyp

    in
    let utyp = unfoldRec typ in
    case utyp of
      | Product (fields, _) -> if numbered? fields then utyp else typ
      | _ -> typ


  op unfoldToCoProduct (spc : Spec, typ : Sort) : Sort =
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

  op unfoldToSpecials (_ : Spec, typ : Sort) : Sort = 
    typ

  op unfoldToSpecials1 (spc : Spec, typ : Sort) : Sort =
    let
      def unfoldToSpecials0 typ =
        let
          def unfoldRec typ =
            let utyp = unfoldBaseKeepPrimitives (spc, typ) in
            if utyp = typ then typ else unfoldRec utyp
        in
        let utyp = unfoldRec typ in
        case utyp of
          % this corresponds to a term of the form {x:Nat|x<C} where C must be a Integer const
          | Subsort (Base (Qualified (_, "Nat"), [], _),
                     Lambda ([(VarPat((X,_), _), 
                               _,
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
    mapSort (fn tm -> tm, unfoldToSpecials0, fn pat -> pat) typ
  
  op normalizeArrowSortsInSpec (spc : Spec) : Spec =
    mapSpec (fn tm -> tm,
	     fn | Arrow (typ1, typ2, X) -> 
	          Arrow (unfoldToProduct (spc, typ1), typ2, X)
	        | typ -> typ,
             fn pat -> pat) 
            spc

 op unfoldBaseKeepPrimitives (spc : Spec, typ : Sort) : Sort =
   case typ of
     | Base (qid, typs, a) ->
       (case findTheSort (spc, qid) of
	  | Some info ->
	    (if ~ (definedSortInfo? info) then
               typ
             else
               let (tvs, typ2) = unpackFirstSortDef info in
               let
                 def continue () =
                   let styp = substSort (zip (tvs, typs), typ2) in
                   unfoldBaseKeepPrimitives (spc, styp)
               in
               case typ of
                 | Boolean                                         _  -> typ
                 | Base (Qualified ("Nat",     "Nat"),    [],      _) -> typ
                 | Base (Qualified ("Integer", "Int"),    [],      _) -> typ
                 | Base (Qualified ("Char",    "Char"),   [],      _) -> typ
                 | Base (Qualified ("String",  "String"), [],      _) -> typ

                 | Base (Qualified ("List",    "List"),   [ptyp],  X) ->
                   Base (Qualified ("List",    "List"),   
                         [unfoldBaseKeepPrimitives (spc, ptyp)], 
                         X)

                 | Base (Qualified ("Option",  "Option"), [ptyp],  X) ->
                   Base (Qualified ("Option",  "Option"), 
                         [unfoldBaseKeepPrimitives (spc, ptyp)],
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

  sort opInfoResult = | OpDecl  IDeclaration 
                      | FunDecl IFunDeclaration
                      | FunDefn IFunDefinition
                      | VarDecl IDeclaration
                      | MapDecl IFunDeclaration
                      | Skip


  op opinfo2declOrDefn (ctxt        : CgContext, 
                        spc         : Spec,
                        qid         : QualifiedId,
                        info        : OpInfo,
                        optParNames : Option (List String))
    : opInfoResult =
    let (tvs, typ, _) = unpackFirstOpDef info in
    let 

      def qid2str (Qualified (q, id)) =
        if q = UnQualified then id else q ^ "." ^ id

      def getParamNames (ctxt, tm) =
        let 
          def err () = 
            let prefix = case ctxt.currentOpSort of 
                           | Some qid -> "in op "^ qid2str qid ^ ":\n" 
                           | _ -> ""
            in
            prefix ^ "unsupported operator definition format:\n       " ^ printTerm tm
        in
        case tm of
          | Lambda ([(pat, _, body)], _) ->
            let plist =
                case pat of

                  | VarPat ((id,_), _) -> 
                    [substGlyphInIdent id]

                  | RecordPat (plist, _) -> 
                    map (fn | (_,VarPat((id,_),_)) -> substGlyphInIdent id
                            | _ -> fail (err ()))
                        plist

                  | RestrictedPat (VarPat((id,_),_), _, _) -> 
                    [substGlyphInIdent id]

                  | RestrictedPat (RecordPat(plist,_), _, _) -> 
                    map (fn | (_,VarPat((id,_),_)) -> substGlyphInIdent id
                            | _ -> fail (err ()))
                        plist

                  | _ -> 
                    fail (err ())
            in
            (plist,body)
          | _ -> fail (err())
    in
    let Qualified (q, lid) = qid in
    let id   = (q, lid)                                       in
    let id0  = (q, "__" ^ lid ^ "__")                         in
    let typ  = unfoldToArrow (spc, typ)                       in
    let typ  = type2itype (unsetToplevel ctxt, spc, tvs, typ) in
    let ctxt = setCurrentOpSort (ctxt, qid)                   in
    case typ of 
      | IFunOrMap (types, rtype) ->
        if definedOpInfo? info then
          let tm = firstOpDefInnerTerm info          in
          let tm = liftUnsupportedPattern (spc, tm)  in
          let (pnames,body) = getParamNames(ctxt,tm) in
          let decl = {name       = id,
                      params     = zip (pnames, types),
                      returntype = rtype}
          in
          let expr = term2expression (ctxt, spc, body) in
          FunDefn {decl = decl,
                   body = IExp expr} % functional function body
        else
          let params = 
              case optParNames of
                | Some pnames -> zip (pnames, types)
                | _ -> map (fn t -> ("", t)) types
          in
          FunDecl {name       = id,
                   params     = params,
                   returntype = rtype}
      | _ -> 
        let opt_exp = 
            if definedOpInfo? info then
              let tm = firstOpDefInnerTerm info in
              Some (term2expression (ctxt, spc, tm))
            else
              None
        in
        OpDecl (id, typ, opt_exp)

  op liftUnsupportedPattern (spc : Spec, tm : Term) : Term =
    let b = termAnn tm in
    case tm of
      | Lambda ([(pat, _, body)], _) ->
        (case pat of
	   | VarPat _ -> tm
	   | RecordPat (plist, _) -> 
	     if forall? (fn | (_, VarPat _) -> true | _ -> false) plist then 
               tm
	     else
	       %let _ = writeLine("unsupported pattern in operator definition: "^(printPattern pat)) in
	       let typ = inferType (spc, tm) in
	       let varx    = Var    (("x", typ),                  b) in
	       let appl    = Apply  (tm, varx,                    b) in
	       let varpatx = VarPat (("x", typ),                  b) in
	       let tm      = Lambda ([(varpatx, mkTrue(), appl)], b) in
	       tm
	   | _ -> tm)
      | _ -> tm

  % --------------------------------------------------------------------------------


  op term2expression (ctxt : CgContext, spc : Spec, tm : Term) : ITypedExpr =
    let typ = inferType (spc, tm)                           in
    let typ = unfoldBaseKeepPrimitives (spc, typ)           in
    let exp = term2expression_internal (ctxt,spc, tm, typ)  in
    let typ = type2itype (unsetToplevel ctxt, spc, [], typ) in
    (exp, typ)

  op term2expression_internal (ctxt : CgContext,
                               spc  : Spec, 
                               tm   : Term, 
                               typ  : Sort)
    : IExpr =
    let 

      def qid2varid (Qualified (q, id)) = 
        (q, id)

      % extract the list of argument terms from a record term given
      % as second argument of an Apply term

      def getArgs argtm = 
        case argtm of
          | Record (fields, _) ->
            if numbered? fields then
              map (fn (_,t) -> t) fields
            else
              [argtm]
	  | _ -> [argtm]

    in
    let errmsg = 
        mkInOpStr ctxt ^ "unsupported feature: this format cannot be used for terms:\n"
        ^ printTerm tm
    in

    % checks, whether the given id is an outputop of the espec; if yes is has to be
    % replaced by a VarDeref/FunCallDeref, as done below
    %    let def isOutputOp(varid as (spcname,lid)) =
    %          let outputops = ctxt.espc.interface.outputops in
    %	  (spcname = ctxt.espc.spc.name) && lid in? outputops)
    %    in

    case tm of

      % this is active, when a Fun occurs "standalone", i.e. not in the context of an apply.
      % we restrict the possible forms to those not having an arrow sort, i.e. we don't support
      % functions as objects
      % Not, And, Or, etc,. should never occur "standalone", so we don't look for them here

      | Fun (fun, typ, _) ->
        if arrowSort? (spc, typ) then
          case fun of
            | Op (qid,_) -> IVarRef (qid2varid qid)
            | _ -> 
              fail("sorry, functions as objects (higher-order functions) are not yet supported:\n       "
                     ^ printTerm tm)
        else
          (case fun of
             | Nat    n -> IInt  n
             | String s -> IStr  s
             | Char   c -> IChar c
             | Bool   b -> IBool b

             | Op (qid, _) -> 
               let varname = qid2varid qid in
               %if isOutputOp varname
               %then VarDeref varname
               %else 
               IVar varname

             | Embed (id,_) -> 
               let typ = foldSort (spc, typ) in
               if useConstrCalls? ctxt then
                 case typ of

		   | Base (qid, _, _) ->
		     let vname = qid2varid qid in
		     IConstrCall (vname, id, [])

		   | Boolean _ -> 
                     IConstrCall (("Boolean", "Boolean"), id, [])

		   | _ -> 
                     IAssignUnion (id, None)
               else
                 IAssignUnion (id, None)

             | _ -> fail errmsg)

      | Apply (t1, t2, _) ->
        let
          def getProjectionList (tm, projids) =
            case tm of
              | Apply (Fun (Project id, _, _), t2, _) -> getProjectionList (t2, id::projids)
              | _ -> (projids, tm)
        in
        let args = getArgs t2 in
        let 
          def getExprs4Args () = map (fn tm -> term2expression (ctxt, spc, tm)) args
        in
        (case getBuiltinExpr (ctxt, spc, t1, args) of
           | Some expr -> expr
           | _ ->
	    let origlhs = t1 in
	    let
              % this is a sub-def, because we collect and skip projections
              def process_t1 (t1, projections) =
		case t1 of

                  | Var ((id, _), _) ->
                    let exprs = getExprs4Args () in
                    let varname = ("", id) in
                    % infer the type of the original lhs to get the real type of the map
                    % taking all the projections into account
                    let lhssort = inferType (spc, origlhs)                          in
                    let lhssort = unfoldToSpecials (spc, lhssort)                   in
                    let lhstype = type2itype (unsetToplevel ctxt, spc, [], lhssort) in
                    IFunCall(varname,projections,exprs)

		   | Fun(Op(qid,_),_,_) ->
                     let exprs = getExprs4Args ()                                    in
                     let varname = qid2varid qid                                     in
                     % infer the type of the original lhs to get the real type of the map
                     % taking all the projections into account
                     let lhssort = inferType (spc, origlhs)                          in
                     let lhssort = unfoldToSpecials (spc, lhssort)                   in
                     let lhstype = type2itype (unsetToplevel ctxt, spc, [], lhssort) in
                     %if isOutputOp varname
                     %then MapAccessDeref (varname,lhstype,projections,exprs)
                     %else 
                     if isVariable (ctxt, qid) then
                       IMapAccess (varname, lhstype, projections, exprs)
                     else
                       IFunCall (varname, projections, exprs)

		   | Fun (Embed (id, _), _, _) ->
		     let 
                       def mkExpr2() = term2expression (ctxt, spc, t2)
                     in
                     if projections = [] then
                       let typ = foldSort (spc, typ) in
                       if useConstrCalls? ctxt then
                         case typ of

                           | Base (qid, _, _) ->
                             let vname = qid2varid qid in
                             let exprs = case t2 of
                                           | Record (fields, b) ->
                                             if numbered? fields then
                                               map (fn (_,t) -> term2expression (ctxt, spc, t)) fields
                                             else 
                                               [mkExpr2()]
                                           | _ -> 
                                             [mkExpr2()]
                             in
                             IConstrCall(vname,id,exprs)

                           | Boolean _ -> 
                             let exprs = case t2 of
                                           | Record (fields, b) ->
                                             if numbered? fields then
                                               map (fn(_,t) -> term2expression(ctxt,spc,t)) fields
                                             else 
                                               [mkExpr2()]
                                           | _ -> 
                                             [mkExpr2()]
                             in
                             IConstrCall (("Boolean", "Boolean"), id, exprs)

                           | _ -> 
                             IAssignUnion (id, Some (mkExpr2()))
                       else 
                         IAssignUnion (id, Some (mkExpr2()))

                     else 
                       fail (mkInOpStr ctxt ^ "unsupported feature: this term can not be used as an lhs-term of an application:\n"
                               ^ printTerm t1)

                   | Fun (Project id, _, _) ->
		     let expr2 = term2expression (ctxt, spc, t2) in
                     if projections = [] then 
                       IProject(expr2,id)
                     else 
                       fail (mkInOpStr ctxt ^ "unsupported feature: this term can not be used as an lhs-term of an application:\n"
                               ^ printTerm t1)
	           | _ ->
                     case getProjectionList (t1, []) of
                       | (prjs as (_::_), t1) -> process_t1 (t1, prjs)
                       | _ -> 
                         % handle special cases:
                         case simpleCoProductCase (ctxt, spc, tm) of
                           | Some expr -> expr
                           | _ ->
                             fail (mkInOpStr ctxt ^ "unsupported feature: this term can not be used as an lhs-term of an application:\n"
                                     ^ printTerm t1)
	    in
	      process_t1 (t1, []))

      % ----------------------------------------------------------------------

      | Let ([(pat,deftm)], tm, _) -> % let's can only contain one pattern/term entry (see parser)
	(case pat of

           | VarPat ((id, typ), _) ->
             let defexp = term2expression (ctxt, spc, deftm)            in
             let exp    = term2expression (ctxt, spc, tm)               in
             let typ    = type2itype (unsetToplevel ctxt, spc, [], typ) in
             ILet (id, typ, defexp, exp)

           | WildPat _ ->
             let defexp = term2expression (ctxt, spc, deftm) in
             let exp    = term2expression (ctxt, spc, tm)    in
             IComma [defexp, exp]

           | _ -> 
             fail (mkInOpStr ctxt ^ "unsupported feature: this form of pattern cannot be used:\n"
                     ^ printPattern pat))

      % ----------------------------------------------------------------------

      | Record (fields,_) ->
        if numbered? fields then
          let exps = map (fn (_, tm) -> term2expression (ctxt, spc, tm)) fields in
          ITupleExpr exps
        else
          let fields = map (fn (id, tm) -> (id, term2expression (ctxt, spc, tm))) fields in
          IStructExpr fields

      % ----------------------------------------------------------------------

      | Var ((id, _), _) -> IVar ("", id)

      | Seq (tms, _) -> 
        let exps = map (fn tm -> term2expression (ctxt, spc, tm)) tms in
        IComma exps

      | IfThenElse(t1,t2,t3,_) ->
	let e1 = term2expression (ctxt, spc, t1) in
	let e2 = term2expression (ctxt, spc, t2) in
	let e3 = term2expression (ctxt, spc, t3) in
	IIfExpr (e1, e2, e3)

      | SortedTerm (tm, _, _) -> 
        let (exp, _) = term2expression (ctxt, spc, tm) in 
        exp

      | _ -> fail errmsg

  op arrowSort? (spc : Spec, typ : Sort) : Bool =
    case unfoldToArrow (spc, typ) of
      | Arrow _ -> true
      | _ -> false

  op getEqOpQid (Qualified (q, id) : QualifiedId) : QualifiedId =
    Qualified (q, "eq_" ^ id)

  op equalsExpression (ctxt : CgContext, spc : Spec, t1 : Term, t2 : Term) 
    : IExpr =
    let

      def t2e tm = 
        term2expression (ctxt, spc, tm)

      def primEq () =
	IBuiltin (IEquals (t2e t1, t2e t2))

    in

    % analyse, which equal we need; let's hope type checking
    % already made sure, that the types fit, so just look at one
    % of the terms
    let typ = inferType (spc, t1) in
    %% Was unfoldStripSort which is unnecessary and dangerous because of recursive types
    let utyp = stripSubsorts (spc, typ) in
    case utyp of
      | Boolean                         _  -> primEq ()
      | Base (Qualified(_,"Bool"),   [],_) -> primEq ()
      | Base (Qualified(_,"Nat"),    [],_) -> primEq ()
      | Base (Qualified(_,"Int"),    [],_) -> primEq ()
      | Base (Qualified(_,"Int"),    [],_) -> primEq ()
      | Base (Qualified(_,"Char"),   [],_) -> primEq ()
     %| Base (Qualified(_,"Float"),  [],_) -> primEq ()
      | Base (Qualified(_,"String"), [],_) -> IBuiltin (IStrEquals (t2e t1,t2e t2))
      | _ ->
        let typ = foldSort (spc, termSort t1) in
	let errmsg = "sorry, the current version of the code generator doesn't support the equality check for sort\n"
	             ^ printSort typ
	in
        case typ of

	  | Base(qid,_,_) ->
	    let eqid as Qualified (eq, eid) = getEqOpQid qid in
	    (case findTheOp(spc,eqid) of
	       | Some _ ->
	         let eqfname = (eq, eid) in
		 IFunCall (eqfname, [], [t2e t1, t2e t2])
	       | _ ->
	         fail (errmsg ^ "\nReason: eq-op not found in extended spec:\n" ^ printSpec spc))

          | Product (fields, _) ->
	    let eqtm    = getEqTermFromProductFields (fields, typ, t1, t2) in
	    let (exp,_) = t2e eqtm in
	    exp

	  | _ -> 
            fail (errmsg ^ "\n[term sort must be a base or product sort]") %primEq()

  op getEqTermFromProductFields (fields : List (Id * Sort),
                                 otyp   : Sort,
                                 varx   : Term,
                                 vary   : Term)
    : Term =
    let b       = sortAnn otyp in
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

  op getBuiltinExpr (ctxt : CgContext,
                     spc  : Spec,
                     tm   : Term, 
                     args : List Term) 
    : Option IExpr =
    let
      def t2e tm = term2expression (ctxt, spc, tm)
    in
    case (tm, args) of
      | (Fun (Equals,    _, _),                                       [t1,t2]) -> Some (equalsExpression (ctxt, spc, t1, t2))

      | (Fun (Not,       _, _),                                       [t1])    -> Some (IBuiltin (IBoolNot             (t2e t1)))
      | (Fun (And,       _, _),                                       [t1,t2]) -> Some (IBuiltin (IBoolAnd             (t2e t1, t2e t2)))
      | (Fun (Or,        _, _),                                       [t1,t2]) -> Some (IBuiltin (IBoolOr              (t2e t1, t2e t2)))
      | (Fun (Implies,   _, _),                                       [t1,t2]) -> Some (IBuiltin (IBoolImplies         (t2e t1, t2e t2)))
      | (Fun (Iff,       _, _),                                       [t1,t2]) -> Some (IBuiltin (IBoolEquiv           (t2e t1, t2e t2)))
      | (Fun (NotEquals, _, _),                                       [t1,t2]) -> let eq_tm = 
                                                                                        IBuiltin (IEquals              (t2e t1, t2e t2))
                                                                                  in
                                                                                  Some (IBuiltin (IBoolNot             (eq_tm, IPrimitive IBool)))

      | (Fun (Op (Qualified ("Integer", "+"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntPlus             (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "-"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntMinus            (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "~"),             _), _, _),  [t1])    -> Some (IBuiltin (IIntUnaryMinus       (t2e t1)))
      | (Fun (Op (Qualified ("Integer", "*"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntMult             (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "div"),           _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntDiv              (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "rem"),           _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntRem              (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "<"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntLess             (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", "<="),            _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntLessOrEqual      (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", ">"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntGreater          (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Integer", ">="),            _), _, _),  [t1,t2]) -> Some (IBuiltin (IIntGreaterOrEqual   (t2e t1, t2e t2)))

      | (Fun (Op (Qualified ("Float",   "toFloat"),       _), _, _),  [t1])    -> Some (IBuiltin (IIntToFloat          (t2e t1)))
      | (Fun (Op (Qualified ("Float",   "stringToFloat"), _), _, _),  [t1])    -> Some (IBuiltin (IStringToFloat       (t2e t1)))
      | (Fun (Op (Qualified ("Float",   "+"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatPlus           (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "-"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatMinus          (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "~"),             _), _, _),  [t1])    -> Some (IBuiltin (IFloatUnaryMinus     (t2e t1)))
      | (Fun (Op (Qualified ("Float",   "*"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatMult           (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "div"),           _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatDiv            (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "<"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatLess           (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   ">"),             _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatGreater        (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "<="),            _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatLessOrEqual    (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   ">="),            _), _, _),  [t1,t2]) -> Some (IBuiltin (IFloatGreaterOrEqual (t2e t1, t2e t2)))
      | (Fun (Op (Qualified ("Float",   "toInt"),         _), _, _),  [t1])    -> Some (IBuiltin (IFloatToInt          (t2e t1)))

      | (Fun (Op (Qualified ("Nat",     "succ"),          _), _, _),  [t1])    -> Some (IBuiltin (IIntPlus             (t2e t1, (IInt 1, IPrimitive INat))))
      | (Fun (Op (Qualified ("Nat",     "pred"),          _), _, _),  [t1])    -> Some (IBuiltin (IIntMinus            (t2e t1, (IInt 1, IPrimitive INat))))
      | (Fun (Op (Qualified ("Integer", "isucc"),         _), _, _),  [t1])    -> Some (IBuiltin (IIntPlus             (t2e t1, (IInt 1, IPrimitive INat))))
      | (Fun (Op (Qualified ("Integer", "ipred"),         _), _, _),  [t1])    -> Some (IBuiltin (IIntMinus            (t2e t1, (IInt 1, IPrimitive INat))))

      % var refs:
      %      | (Fun(Op(Qualified("ESpecPrimitives","ref"),_),_,_),[t1])
      %	-> let def qid2varname(qid) =
      %                 case qid of
      %	           | Qualified(spcname,name) -> (spcname,name)
      %		   %| Local(name) -> (spc.name,name)
      %	   in
      %	   (case t1 of
      %	      | Fun(Op(qid,_),_,_)
      %	        -> %if member(qid,ctxt.vars) then Some(VarRef(qid2varname qid))
      %		   %else 
      %		       fail("\"ref\" can only be used for vars, but \""^
      %				    (qidstr qid)^"\" is not declared as a var.")
      %	      | _ -> fail("\"ref\" can only be used for vars, not for:\n"^
      %				 printTerm(t1))
      %	   )

      | _ -> None

  op isVariable (_ : CgContext, _ : QualifiedId) : Bool = 
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
  *  i.e. where the term's sort is a coproduct and the cases are the constructors of the coproduct.
  *  In the args of the constructors (x1,x2,y1 above) only var pattern are supported.
  *)

  op simpleCoProductCase (ctxt : CgContext, spc : Spec, tm : Term) : Option IExpr =
    case tm of

      | Apply(embedfun as Lambda (rules,_), tm, _) ->
        (case rules of
	   | [(p as VarPat ((v,ty), b), _, body)] ->
	     % that's a very simple case: "case tm of v -> body" (no other case)
	     % we transform it to "let v = tm in body"
	     let (exp,_) = term2expression (ctxt, spc, Let ([(p,tm)], body, b)) in
	     Some exp
	   | _ -> 
             let

               def getTypeForConstructorArgs (typ, id) =
                 %let typ = unfoldBase(spc,typ) in
                 let typ = stripSubsorts (spc, typ) in
                 case typ of
                   | CoProduct (fields,_) ->
                     (case findLeftmost (fn (id0, _) -> id0 = id) fields of
                        | Some(_,optsort) -> (case optsort of
                                                | Some typ -> Some(type2itype(unsetToplevel ctxt,spc,[],typ))
                                                | None -> None)
                        | _ -> fail("internal error: constructor id " ^ id ^ " of term " ^
                                      printTerm tm ^ " cannot be found."))
                   | _ -> 
                     let utyp = unfoldBase (spc, typ) in
		     if utyp = typ then
		       fail ("internal error: sort of term is no coproduct: " ^
                               printTerm tm ^ ":" ^ printSort typ)
		     else 
                       getTypeForConstructorArgs (utyp, id)

             in
             % check whether the pattern have the supported format, i.e.
             % (constructor name followed by var patterns) or (wildpat)
             let

               def getUnionCase (pat, _, tm) =
                 let exp = term2expression (ctxt, spc, tm) in
                 case pat of

                   | EmbedPat (constructorId, optpat, typ, _) ->
                     let opttype = getTypeForConstructorArgs (typ, constructorId) in
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
                     IConstrCase (Some constructorId, opttype, vars, exp)

                   | WildPat _     -> IConstrCase (None,None,[], exp)
                   | NatPat  (n,_) -> INatCase    (n,            exp)
                   | CharPat (c,_) -> ICharCase   (c,            exp)
                   | _ -> 
                     fail (mkInOpStr ctxt ^ "unsupported feature: pattern not supported, use embed or wildcard pattern instead:\n"
                             ^ printPattern pat)
             in
             let unioncases = map getUnionCase rules          in
             let expr       = term2expression (ctxt, spc, tm) in
             Some (IUnionCaseExpr (expr, unioncases)))

      | _ -> 
        let _ = writeLine (mkInOpStr ctxt ^ "fail in simpleCoProductCase (wrong term format)") in
        None


% --------------------------------------------------------------------------------

 op foldSort (spc : Spec, typ : Sort) : Sort =
   let opt_typ =
       foldriAQualifierMap (fn (q, id, info, opt_typ) ->
                              case opt_typ of
                                | Some _ -> opt_typ
                                | _ -> 
                                  if definedSortInfo? info then
                                    let (tvs, typ0) = unpackFirstSortDef info in
                                    %let utyp = unfoldBase(spc,typ) in
                                    %let utyp0 = unfoldBase(spc,typ0) in
                                    if equivType? spc (typ, typ0) then
                                      let b   = sortAnn typ0                     in
                                      let qid = Qualified (q, id)                in
                                      let tvs = map (fn tv -> TyVar (tv, b)) tvs in
                                      Some (Base (qid, tvs, b))
                                    else 
                                      None
                                  else
                                    None)
                           None 
                           spc.sorts
   in
   case opt_typ of
     | Some new_typ -> new_typ
     | _ -> typ


}
