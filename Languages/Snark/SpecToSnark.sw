spec {

  import SpecToSnarkProperties
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec
  
  sort SnarkSpec =
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

  op declare_sub_sorts: LispCell
  def declare_subsorts = Lisp.symbol("SNARK","DECLARE-SUBSORTS")

  op declare_function: LispCell
  def declare_function = Lisp.symbol("SNARK","DECLARE-FUNCTION-SYMBOL")

  op declare_constant: LispCell
  def declare_constant = Lisp.symbol("SNARK","DECLARE-CONSTANT-SYMBOL")

  op declare_predicate: LispCell
  def declare_predicate = Lisp.symbol("SNARK","DECLARE-PREDICATE-SYMBOL")

%  op snark_assert: LispCell
%  def snark_assert = Lisp.symbol("SNARK","ASSERT")

  op arithmeticSorts: List LispCell
  def arithmeticSorts = 
      [ 
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Integer")), Lisp.symbol("KEYWORD", "IFF"), Lisp.quote(Lisp.symbol("SNARK", "INTEGER"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Nat")), Lisp.symbol("KEYWORD", "IFF"), Lisp.quote(Lisp.symbol("SNARK", "NATURAL"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "PosNat"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "LOGICAL"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Char"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "String"))],
	Lisp.list [declare_subsorts, Lisp.quote(Lisp.symbol("SNARK", "Integer")),
                                    Lisp.quote(Lisp.symbol("SNARK", "Nat")),
                                    Lisp.quote(Lisp.symbol("SNARK", "PosNat"))],
	Lisp.list [declare_subsorts, Lisp.quote(Lisp.symbol("SNARK", "Nat")),
				     Lisp.quote(Lisp.symbol("SNARK", "PosNat"))]
      ]

  op arithmeticFunctions: List LispCell
  def arithmeticFunctions =
      [
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "+")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)],
	Lisp.list [declare_function, Lisp.quote(Lisp.symbol("SNARK", "*")), Lisp.nat(2),
		   Lisp.symbol("KEYWORD","ASSOCIATIVE"), Lisp.bool(true),
		   Lisp.symbol("KEYWORD","COMMUTATIVE"), Lisp.bool(true)]

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

  
  op snarkBuiltInSorts: Boolean -> List LispCell
  
  def snarkBuiltInSorts(useLogicalSorts) = 
      (if useLogicalSorts then logicalSorts else [])
      ++
      arithmeticSorts 

  op snarkSorts: Spec -> List LispCell

  def snarkSorts(spc) =
      let sorts = sortsAsList(spc) in
      let snarkSorts =
             map(fn (qual, id, info) ->
	            Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", id))])	%
                 sorts in
         snarkBuiltInSorts(false) ++ snarkSorts

  op snarkFunctionNoArityDecl: Spec * String * Sort -> LispCell

  def snarkFunctionNoArityDecl(spc, name, srt) =
    (case srt of
       Base (Qualified(qual, id), srts, _) ->
	 Lisp.list [declare_constant, Lisp.quote(Lisp.symbol("SNARK", name)),
		    Lisp.symbol("KEYWORD","SORT"),
		    Lisp.quote(Lisp.symbol("SNARK", id))]
	| _ -> Lisp.nil()) %Lisp.symbol("","FD1")

  def snarkBaseSort(s:Sort, rng?):LispCell = 
	          case s of
		    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NATURAL")
		    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","INTEGER")
		    | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
                                                       else Lisp.symbol("SNARK",id)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar _ -> Lisp.symbol("SNARK","TRUE")
  
  def snarkPredicateDecl(spc, name, srt, dom, arity) =
    case productOpt(spc, dom) of
      Some fields -> 
	let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(srt, false))
	fields in
	Lisp.list[declare_predicate,
		  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
		  Lisp.symbol("KEYWORD","SORT"),
		  Lisp.quote(Lisp.cons(Lisp.symbol("SNARK","BOOLEAN"), Lisp.list(domSortList)))]
  
  op snarkFunctionNoCurryDecl: Spec * String * Sort * Nat -> LispCell

  def snarkFunctionNoCurryDecl(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case rng of
	  | Base(Qualified( _,"Boolean"),_,_) -> snarkPredicateDecl(spc, name, srt, dom, arity)
	  | _ ->
	case productOpt(spc, dom) of
	  Some fields -> 
	    let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(srt, false))
	                          fields in
	      Lisp.list[declare_function,
			Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			Lisp.symbol("KEYWORD","SORT"),
			Lisp.quote(Lisp.cons(snarkBaseSort(rng, true), Lisp.list(domSortList)))]

  def snarkFunctionCurryNoArityDecl(spc, name, srt) =
    snarkFunctionNoArityDecl(spc, name, srt)

  def snarkFunctionCurryDecl(spc, name, srt, arity) =
    Lisp.nil() %Lisp.symbol("","Curry")

  op snarkFunctionDecl: Spec * String * Sort -> LispCell

  def snarkFunctionDecl(spc, name, srt) =
%    let _ = toScreen("Generating snark decl for "^name^" with sort: ") in
%    let _ = printSortToTerminal srt in
    (case (curryShapeNum(spc, srt), sortArity(spc, srt))
       of (1,None) -> snarkFunctionNoArityDecl(spc, name, srt)
	| (1, Some(_,arity)) -> snarkFunctionNoCurryDecl(spc, name, srt, arity)
	| (curryN, None) -> snarkFunctionCurryNoArityDecl(spc, name, srt)
	| (curryN, Some (_, arity)) -> snarkFunctionCurryDecl(spc, name, srt, arity)
	| _ -> snarkFunctionNoArityDecl(spc, name, srt))

  op snarkOpDeclPartial: Spec * String * Sort -> Option LispCell

  def snarkOpDeclPartial(spc, name, srt) =
    let decl = snarkOpDecl(spc, name, srt) in
       if null(decl) then None else Some decl

%      case decl of
%	Const _ -> None
%        | _ -> Some decl
  
  op snarkOpDecl: Spec * String * Sort -> LispCell

  def snarkOpDecl(spc, name, srt) =
    if functionSort?(spc, srt)
      then snarkFunctionDecl(spc, name, srt)
      else snarkFunctionDecl(spc, name, srt)

  op snarkBuiltInOps: List LispCell

  def snarkBuiltInOps = arithmeticFunctions
  
  op snarkOpDecls: Spec -> List LispCell

  def snarkOpDecls(spc) =
    let opsigs = specOps(spc) in
    let snarkOpDecls =
          mapPartial(fn (qname, name, _, srt) -> 
		           snarkOpDeclPartial(spc, mkSnarkName(qname,name), srt))
                    opsigs in
%      snarkBuiltInOps ++ snarkOpDecls
       snarkOpDecls


  op LISP.PPRINT: LispCell -> LispCell

  def ppLispCell(t:LispCell) =
%    string (toString(LISP.PPRINT(t)))
    string (toString(t))
  
  def ppSpec (s : SnarkSpec) : Pretty =
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



  }
