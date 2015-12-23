(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

snark qualifying spec

  import SpecToSnarkProperties
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec
  
  type SnarkSpec =
    {
     name: String,
     sortDecls: List LispCell,
     opDecls: List LispCell,
     assertions: List LispCell
%     conjectures: List LispCell
    }

  op snarkSpec: Spec -> SnarkSpec

  def snarkSpec(spc) =
    {name = snarkName(spc),
     sortDecls = snarkSorts(spc),
     opDecls = snarkOpDecls(spc),
     assertions = snarkProperties(spc)
%     conjectures = []
     }


  op snarkName: Spec -> String
  def snarkName(spc) =
    let packages = map mkLPackageId (qualifiers spc.ops) in
    let (defPkgName,extraPackages) =
        case packages
          of x::r -> (x,r)
           | [] -> (defaultSpecwarePackage,[]) in
    defPkgName



  op declare_sort: LispCell
  def declare_sort = Lisp.symbol("SNARK","DECLARE-SORT")

  op declare_subsorts: LispCell
  def declare_subsorts = Lisp.symbol("SNARK","DECLARE-SUBSORTS")

  op declare_function: LispCell
  def declare_function = Lisp.symbol("SNARK","DECLARE-FUNCTION-SYMBOL")

  op declare_constant: LispCell
  def declare_constant = Lisp.symbol("SNARK","DECLARE-CONSTANT-SYMBOL")

  op declare_predicate: LispCell
  def declare_predicate = Lisp.symbol("SNARK","DECLARE-PREDICATE-SYMBOL")

  op declare_proposition_symbol: LispCell
  def declare_proposition_symbol = Lisp.symbol("SNARK","DECLARE-PROPOSITION-SYMBOL")

%  op snark_assert: LispCell
%  def snark_assert = Lisp.symbol("SNARK","ASSERT")

  op arithmeticSorts: List LispCell
  def arithmeticSorts = 
      [ 
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Integer")), Lisp.symbol("KEYWORD", "IFF"), Lisp.quote(Lisp.symbol("SNARK", "NUMBER"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Int")), Lisp.symbol("KEYWORD", "IFF"), Lisp.quote(Lisp.symbol("SNARK", "NUMBER"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Nat")), Lisp.symbol("KEYWORD", "IFF"), Lisp.quote(Lisp.symbol("SNARK", "NATURAL"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "PosNat"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Int0"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "LOGICAL"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "BOOLEAN"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Char"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "String"))],
	Lisp.list [declare_subsorts, Lisp.quote(Lisp.symbol("SNARK", "Integer")),
                                     Lisp.quote(Lisp.symbol("SNARK", "Nat")),
                                     Lisp.quote(Lisp.symbol("SNARK", "PosNat")),
                                     Lisp.quote(Lisp.symbol("SNARK", "Int0"))],
	Lisp.list [declare_subsorts, Lisp.quote(Lisp.symbol("SNARK", "Nat")),
				     Lisp.quote(Lisp.symbol("SNARK", "PosNat"))]
      ]
  op baseSorts: List LispCell
  def baseSorts = 
      [ 
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Option"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "List"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "logical"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Comparison"))]
      ]

  op snarkBaseDecls: List LispCell
  def snarkBaseDecls =
    [
	Lisp.list[declare_predicate,
		  Lisp.quote(Lisp.symbol("SNARK", "embed?")), Lisp.nat(2)],
	Lisp.list[declare_constant,
		  Lisp.quote(Lisp.symbol("SNARK", "embed__Nil")), Lisp.symbol("KEYWORD","SORT"),  Lisp.quote(Lisp.symbol("SNARK","List"))],
	Lisp.list[declare_constant,
		  Lisp.quote(Lisp.symbol("SNARK", "nil")), Lisp.symbol("KEYWORD","SORT"),  Lisp.quote(Lisp.symbol("SNARK","List"))],
%	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "length")), Lisp.nat(1),
%		   Lisp.symbol("KEYWORD","SORT"),
%		   Lisp.quote(Lisp.list [Lisp.symbol("SNARK", "NUMBER"),
%					 Lisp.symbol("SNARK", "List")])],
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "embed__Cons")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [Lisp.symbol("SNARK", "List"),
					 Lisp.symbol("SNARK", "TRUE"),
					 Lisp.symbol("SNARK", "List")])],

	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "embed__Some")), Lisp.nat(1),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [Lisp.symbol("SNARK", "Option"),
					 Lisp.symbol("SNARK", "TRUE")])],

	Lisp.list[declare_constant,
		  Lisp.quote(Lisp.symbol("SNARK", "embed__None")), Lisp.symbol("KEYWORD","SORT"),  Lisp.quote(Lisp.symbol("SNARK","Option"))],

	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "embed__Some")), Lisp.nat(1),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [Lisp.symbol("SNARK", "Option"),
					 Lisp.symbol("SNARK", "TRUE")])],

	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "HOLDS")), Lisp.nat(1),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [Lisp.symbol("SNARK", "BOOLEAN"),
					 Lisp.symbol("SNARK", "logical")])]

       ] %++ arithmeticFunctions
						    
%(SNARK:DECLARE-CONSTANT-SYMBOL 'SNARK::|switchLamAux| :SORT 'SNARK::|Arrow_Nat_Nat|)
  op baseAxioms: List LispCell
  def baseAxioms =
    [
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK","ALL"),
			    Lisp.list[
				      Lisp.list [Lisp.symbol("SNARK","?X"),
						 Lisp.symbol("KEYWORD","SORT"),
						 Lisp.symbol("SNARK","Option")]
				     ],
			    Lisp.list [Lisp.symbol("SNARK","OR"),
				       Lisp.list[Lisp.symbol("SNARK","embed?"),
						 Lisp.symbol("SNARK","Some"),
						 Lisp.symbol("SNARK","?X")],
				       Lisp.list[Lisp.symbol("SNARK","embed?"),
						 Lisp.symbol("SNARK","None"),
						 Lisp.symbol("SNARK","?X")]
				       ]
			    ]
		)],
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK","ALL"),
			    Lisp.list[
				      Lisp.list [Lisp.symbol("SNARK","?X"),
						 Lisp.symbol("KEYWORD","SORT"),
						 Lisp.symbol("SNARK","List")]
				     ],
			    Lisp.list [Lisp.symbol("SNARK","OR"),
				       Lisp.list[Lisp.symbol("SNARK","embed?"),
						 Lisp.symbol("SNARK","Cons"),
						 Lisp.symbol("SNARK","?X")],
				       Lisp.list[Lisp.symbol("SNARK","embed?"),
						 Lisp.symbol("SNARK","Nil"),
						 Lisp.symbol("SNARK","?X")]
				       ]
			    ]
		)],
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK",">="), Lisp.nat(1), Lisp.nat(0)]
		)
	       ],		
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK",">"), Lisp.nat(1), Lisp.nat(0)]
		)
	       ],		
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK",">="), Lisp.nat(0), Lisp.nat(0)]
		)
	       ],
     Lisp.list [snark_assert,
		Lisp.quote
		(Lisp.list [Lisp.symbol("SNARK","NOT"), (Lisp.list [Lisp.symbol("SNARK","="), Lisp.nat(1), Lisp.nat(0)])]
		)
	       ]

    ]

  op arithmeticFunctions: List LispCell
  def arithmeticFunctions =
      [
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "+")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)]
%	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "*")), Lisp.nat(2),
%		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
%		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)]

%	"(snark::declare-function-symbol
%                'snark::+ 2 
%                :associative t
%                :commutative t)",
%        "(snark::declare-function-symbol
%                'snark::* 2 
%                :associative t
%                :commutative t)",
%        "(snark::declare-subsorts 'snark::integer 'snark::natural)"
%        "(snark::declare-function-symbol
%                'snark::- 2 
%                :sort '(snark::integer snark::natural snark::natural))",
%,
%        "(snark::assert 
%               '(snark::all ((x INTEGER)) 
%                      ( => (|Integer.>= | x 0) (snark::exists ((y NATURAL)) ( = x y))))
%               :documentation \"Nonnegative integers are naturals\")"
      ]

  
  op LogicalSorts: List LispCell
  def logicalSorts = 
      [
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "logical-&")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [ Lisp.symbol("SNARK", "logical"),
					 Lisp.symbol("SNARK", "logical"),
					 Lisp.symbol("SNARK", "logical")]),
		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)],
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "logical-or")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","SORT"),
		   Lisp.quote(Lisp.list [ Lisp.symbol("SNARK", "logical"),
					 Lisp.symbol("SNARK", "logical"),
					 Lisp.symbol("SNARK", "logical")]),
		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)]
       ]

%"(snark::declare-function-symbol 'snark::logical-& 2
%                  :sort '(snark::logical snark::logical snark::logical)
%                  :associative t
%                  :commutative t)",
%	 "(snark::declare-function-symbol 'snark::logical-or 2
%                  :sort '(snark::logical snark::logical snark::logical)
%                  :associative t
%                  :commutative t)"

  
  op snarkBuiltInSorts: Bool -> List LispCell
  
  def snarkBuiltInSorts(useLogicalSorts) = 
      (if useLogicalSorts then logicalSorts else [])
      ++
      arithmeticSorts 
      ++
      baseSorts

  op snarkSorts: Spec -> List LispCell

  def snarkSorts(spc) =
      let types = typesAsList(spc) in
      let snarkSorts =
             map(fn (qual, id, info) ->
	            Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", snarkSortId(id)))])	%
                 types in
      let snarkSubSorts = mapPartial(fn (qual, id, info) ->
			      typeInfoToSnarkSubsort(spc, id, info))
                              types in
         snarkBuiltInSorts(false) ++ snarkSorts ++ snarkSubSorts

 op  typeInfoToSnarkSubsort: Spec * Id * TypeInfo -> Option LispCell
 def typeInfoToSnarkSubsort(spc, id, info) =
   if ~ (definedTypeInfo? info) then
     None
   else
     case firstTypeDefInnerType info of
       | Subtype (supSrt, pred, _) ->
         Some (Lisp.list [declare_subsorts, 
			  Lisp.quote (snarkBaseSort (spc, supSrt, false)), 
			  Lisp.quote (Lisp.symbol ("SNARK", snarkSortId id))])
       | _ -> None

 op  snarkFunctionNoArityDecl: Spec * String * MSType -> LispCell
 def snarkFunctionNoArityDecl (spc, name, srt) =
   case srt of
     | Boolean _ -> snarkPropositionSymbolDecl(name)
     | Base (Qualified(qual, id), srts, _) ->
       Lisp.list [declare_constant, Lisp.quote(Lisp.symbol("SNARK", name)),
		  Lisp.symbol("KEYWORD","SORT"),
		  Lisp.quote(snarkBaseSort(spc, srt, true))]
     | Arrow(dom, rng, _) ->
       (case rng of
	  | Boolean _ -> snarkPredicateDecl(spc, name, dom, 1)
	  | _ -> 
	    let snarkDomSrt = snarkBaseSort(spc, dom, false) in
	    Lisp.list[declare_function,
		      Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(1),
		      Lisp.symbol("KEYWORD","SORT"),
		      Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))])
     | _ -> Lisp.list [declare_constant, Lisp.quote(Lisp.symbol("SNARK", name)),
		       Lisp.symbol("KEYWORD","SORT"),
		       Lisp.quote(snarkBaseSort(spc, srt, true))]

  def snarkPropositionSymbolDecl name =
    Lisp.list [declare_proposition_symbol,
	       Lisp.quote(Lisp.symbol("SNARK", name))]

  def snarkBaseSort (spc, s:MSType, rng?) : LispCell = 
    let s = unfoldBaseUnInterp(spc, s) in
    case s of
     %| Base (Qualified ("Nat",     "Nat"),     _,_) -> Lisp.symbol ("SNARK", "NUMBER")
     %| Base (Qualified ("Nat",     "PosNat"),  _,_) -> Lisp.symbol ("SNARK", "NUMBER")
      | Base (Qualified ("Integer", "Int"), _,_) -> Lisp.symbol ("SNARK", "NUMBER")
      | Boolean _ -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE")
     %| Base(Qualified(qual,id),_,_) -> let res = findBuiltInSort(spc, Qualified(qual,id), rng?) in
     %let _ = if specwareDebug? then toScreen("findBuiltInSort: "^printSort(s)^" returns ") else () in
     %let _ = if specwareDebug? then  LISP.PPRINT(res) else Lisp.list [] in
     %let _ = if specwareDebug? then  writeLine("") else () in
     %res   %findBuiltInSort(spc, Qualified(qual,id), rng?)
      | Base(Qualified( _,id),_,_) -> (if rng? then 
					 Lisp.symbol ("SNARK", snarkSortId id)
				      else 
					 Lisp.symbol ("SNARK", snarkSortId id))
      | Subtype(supSrt, _, _) -> snarkBaseSort(spc, supSrt, rng?)
      | Quotient(supSrt, _, _) -> snarkBaseSort(spc, supSrt, rng?)
      | Product _ -> Lisp.symbol("SNARK", "TRUE")
      | Arrow   _ -> Lisp.symbol("SNARK", "TRUE")
      | TyVar   _ -> Lisp.symbol("SNARK", "TRUE")
      | _         -> Lisp.symbol("SNARK", "TRUE")

  def findBuiltInSort(spc, qid as Qualified(qual,id), rng?) =
    let optSrt = AnnSpec.findTheType(spc, qid) in
    case optSrt of
      | Some info ->
      (let
        def builtinType?(s) =
	  case s of 
	    | Base(Qualified("Nat",    "Nat"),_,_) -> true
	    | Base(Qualified("Integer","Int"),_,_) -> true
	    | Boolean _ -> true
            | _ -> false in
      let
	def builtinSnarkSort(s) =
	  case s of 
	    | Base(Qualified("Nat",    "Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
	    | Base(Qualified("Integer","Int"),_,_) -> Lisp.symbol("SNARK","NUMBER")
	    | Boolean _ -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE") in
      let defs = typeInfoDefs info in
      let builtinSort = findLeftmost builtinType? defs in
        (case builtinSort of
	  | Some srt -> builtinSnarkSort srt
	  | _ -> case defs of
	           | [dfn] -> 
	             (let (_, typ) = unpackType dfn in
	              case typ of
			| Subtype(supSrt, _, _) -> Lisp.symbol("SNARK",snarkSortId(id))
			| Quotient (supSrt, _, _) -> Lisp.symbol("SNARK",snarkSortId(id))
			| _ -> snarkBaseSort(spc, typ, rng?))
	           | _ -> Lisp.symbol("SNARK",snarkSortId(id))))
      | _ -> Lisp.symbol("SNARK",snarkSortId(id))
    
  
  def snarkPredicateDecl(spc, name, dom, arity) =
    case productOpt(spc, dom) of
      | Some fields -> 
	let domSortList = map(fn (id: Id, srt:MSType) -> snarkBaseSort(spc, srt, false))
	fields in
	Lisp.list[declare_predicate,
		  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
		  Lisp.symbol("KEYWORD","SORT"),
		  Lisp.quote(Lisp.cons(Lisp.symbol("SNARK","BOOLEAN"), Lisp.list(domSortList)))]
      | _ ->
	let domSortList = [snarkBaseSort(spc, dom, false)] in
	Lisp.list[declare_predicate,
		  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
		  Lisp.symbol("KEYWORD","SORT"),
		  Lisp.quote(Lisp.cons(Lisp.symbol("SNARK","BOOLEAN"), Lisp.list(domSortList)))]
  

  op substringp: String * String -> Bool
  def substringp(s1, s2) =
    length(s1) <= length(s2) &&
    subFromTo(s2, 0, length(s1)) = s1

  op snarkFunctionNoCurryDecl: Spec * String * MSType * Nat -> LispCell

  def snarkFunctionNoCurryDecl(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	%let _ = if name = "remove" then debug("found it") else () in
	case rng of
	  | Boolean _ -> snarkPredicateDecl(spc, name, dom, arity)
	  | _ ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    if substringp("project", name) || substringp("embed", name) then
	      %let _ = if true || name = "remove" then debug("found it 1") else () in
	      if fields = [] then
		Lisp.list[declare_constant,
			  Lisp.quote(Lisp.symbol("SNARK", name)),
			  Lisp.symbol("KEYWORD","SORT"), Lisp.quote(snarkBaseSort(spc, rng, true))]
		else
		  let snarkDomSrt = snarkBaseSort(spc, dom, false) in
		  Lisp.list[declare_function,
			    Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(1),
			    Lisp.symbol("KEYWORD","SORT"),
			    Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))]
	    else
	      (case dom of
		| Base(domQid, _, _) -> 
		  let snarkDomSrt = snarkBaseSort(spc, dom, false) in
		  Lisp.list[declare_function,
			    Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(1),
			    Lisp.symbol("KEYWORD","SORT"),
			    Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))]
		| _ ->
	    let domSortList = map(fn (id: Id, srt:MSType) -> snarkBaseSort(spc, srt, false))
	                          fields in
	    %let _ = if true || name = "remove" then debug("found it 2") else () in
	      Lisp.list[declare_function,
			Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			Lisp.symbol("KEYWORD","SORT"),
			Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list(domSortList)))])
	  | _ ->
	      let snarkDomSrt = snarkBaseSort(spc, dom, false) in
	        Lisp.list[declare_function,
			  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			  Lisp.symbol("KEYWORD","SORT"),
			  Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))]

  def snarkFunctionCurryNoArityDecl(spc, name, srt) =
    snarkFunctionNoArityDecl(spc, name, srt)

  def snarkFunctionCurryDecl() =
    Lisp.nil() %Lisp.symbol("","Curry")

  op snarkFunctionDecl: Spec * String * MSType -> LispCell

  def snarkFunctionDecl(spc, name, srt) =
    %let _ = toScreen("Generating snark decl for "^name^" with sort: ") in
    %let _ = printSortToTerminal srt in
    %let _ = if name = "remove" then debug("remove") else () in
    (case (curryShapeNum(spc, srt), typeArity(spc, srt))
       of (1,None) ->     %let _ = debug("noArity") in 
	 snarkFunctionNoArityDecl(spc, name, srt)
	| (1, Some(_,arity)) -> %let _ = debug("noCurry") in 
	 snarkFunctionNoCurryDecl(spc, name, srt, arity)
	| (curryN, None) -> %let _ = debug("CurryNoArity") in 
	 snarkFunctionCurryNoArityDecl(spc, name, srt)
	| (curryN, Some (_, arity)) -> %let _ = debug("Curry") in 
	 snarkFunctionCurryDecl()
	| _ -> %let _ = debug("Last") in
	 snarkFunctionNoArityDecl(spc, name, srt))

  op snarkOpDeclPartial: Spec * String * MSType -> Option LispCell

  def snarkOpDeclPartial(spc, name, srt) =
    let decl = snarkOpDecl(spc, name, srt) in
       if null(decl) then None else Some decl

%      case decl of
%	Const _ -> None
%        | _ -> Some decl
  
  op snarkOpDecl: Spec * String * MSType -> LispCell

  def snarkOpDecl(spc, name, srt) =
    case name of
      | "+" -> Lisp.nil()
      | "-" -> Lisp.nil()
      | "*" -> Lisp.nil()
      | _ ->
    if Prover.functionType?(spc, srt)
      then snarkFunctionDecl(spc, name, srt)
      else snarkFunctionDecl(spc, name, srt)

  op snarkBuiltInOps: List LispCell

  def snarkBuiltInOps = arithmeticFunctions
  
   op snarkOpDecls : Spec -> List LispCell
  def snarkOpDecls spc =
    let snarkOpDecls =
        foldOpInfos (fn (info, decls) ->
		     let Qualified (q, id) = primaryOpName info in
		     let (tvs, srt, _) = unpackFirstOpDef info in
		     case snarkOpDeclPartial (spc, mkSnarkName (q, id), srt) of
		       | None -> decls
		       | Some snark_decl -> decls ++ [snark_decl])
	            []
	            spc.ops
    in
  % snarkBuiltInOps ++ snarkOpDecls
    snarkBaseDecls ++
    snarkOpDecls

  def ppLispCell(t:LispCell) =
%    string (toString(LISP.PPRINT(t)))
    string (anyToString(t))
  

  def ppSpec (s : SnarkSpec) : PrettyPrint.Pretty =
      let sortDecls = s.sortDecls 	in
      let opDecls = s.opDecls 	in
      let name = s.name 		in
      let assertions = s.assertions in
%      let conjectures = s.conjectures in
%      let ppSortTerms = map ppTerm sortDecls in
%      let ppOpTerms = map ppTerm opDecls in
      prettysAll
     (
     (section (";;; Snark spec: " ^ name,
	       [string ("(in-package \"" ^ "SNARK" ^ "\")")]))
     ++ 
     (section (";;; Sorts",     List.map ppLispCell     sortDecls))
     ++ 
     (section (";;; Ops",     List.map ppLispCell     opDecls))
     ++ 
     (section (";;; Assertions",     List.map ppLispCell     assertions))
%     List.++ [string "#||"] 
%     List.++ section (";;; Axioms",             List.map ppTerm       s.axioms)
%     List.++ [string "||#", emptyPretty ()]
    )

  op ppSpecToFile : SnarkSpec * String * Text -> ()

  def ppSpecToFile (spc, file, preamble) =
    let p = ppSpec spc in
    let t = format (80, p) in
    toFile (file, t ++ preamble)

  op ppSpecToTerminal : SnarkSpec -> ()

  def ppSpecToTerminal spc =
    let p = ppSpec spc in
    let t = format (80, p) in
    toTerminal t

  op ppSpecsToFile : List SnarkSpec * String * Text -> ()

  def ppSpecsToFile (specs, file, preamble) =
    let ps = List.map ppSpec specs in
    let p  = prettysAll ps in
    let t  = format (80, p) in
    toFile (file, t ++ preamble)

  op toSnark        : Spec -> SnarkSpec
  op toSnarkEnv     : Spec -> SnarkSpec
  op toSnarkFile    : Spec * String * Text -> ()
  op toSnarkFileEnv : Spec * String * Text -> ()

  def toSnark spc =
      toSnarkEnv(spc)

(*
  def toSnarkEnv (spc) =
      let _   = writeLine "toSnark"                             in
      let spc = System.time(translateMatch(spc))          in
      let spc = System.time(arityNormalize(spc)) in
      let spc = System.time(lisp(spc))                             in
      spc 
*)

  def toSnarkEnv (spc) =
%      let _   = writeLine ("Translating " ^ spc.name ^ " to Snark.") in
%      let spc = translateMatch(spc)          in
%      let spc = arityNormalize(spc) in
      let spc = snarkSpec(spc)                          in
%      let _ = ppSpecToTerminal spc         in
      spc 
             
  def toSnarkFile (spc, file, preamble) =  
      toSnarkFileEnv (spc, file, preamble) 

  def toSnarkFileEnv (spc, file, preamble) =
      let _ = writeLine("Writing Snark file "^file) in
      let spc = toSnarkEnv (spc) in
      ppSpecToFile (spc, file, preamble)

end-spec
