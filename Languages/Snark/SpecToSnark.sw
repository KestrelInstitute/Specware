spec {

  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec
  
  sort SnarkSpec =
    {
     name: String,
     sortDecls: LispTerms,
     opDecls: LispTerms,
     assertions: LispTerms,
     conjectures: LispTerms
    }

  op snarkSpec: Spec -> SnarkSpec

  def snarkSpec(spc) =
    {name = snarkName(spc),
     sortDecls = snarkSorts(spc),
     opDecls = snarkOpDecls(spc),
     assertions = [],
     conjectures = []
     }


  op snarkName: Spec -> String
  def snarkName(spc) =
    let packages = map mkLPackageId (qualifiers spc.ops) in
    let (defPkgName,extraPackages) =
        case packages
          of x::r -> (x,r)
           | [] -> (defaultSpecwarePackage,[]) in
    defPkgName



  op declare_sort: LispTerm
  def declare_sort = Op "DECLARE-SORT"

  op declare_sub_sort: LispTerm
  def declare_subsort = Op "DECLARE-SUBSORT"

  op declare_function: LispTerm
  def declare_function = Op "DECLARE-FUNCTION-SYMBOL"

  op declare_predicate: LispTerm
  def declare_predicate = Op "DECLARE-PREDICATE-SYMBOL"

  op arithmeticSorts: LispTerms
  def arithmeticSorts = 
      [ 
	Apply (declare_sort, [Const (Symbol("SNARK", "integer"))]),
	Apply (declare_sort, [Const (Symbol("SNARK", "natural"))]),
	Apply (declare_sort, [Const (Symbol("SNARK", "logical"))]),
	Apply (declare_sort, [Const (Symbol("SNARK", "char"))]),
	Apply (declare_sort, [Const (Symbol("SNARK", "string"))]),
	Apply (declare_subsort, [Const (Symbol("SNARK", "integer")),
				 Const (Symbol("SNARK", "natural"))])
      ]

  op arithmeticFunctions: LispTerms
  def arithmeticFunctions =
      [
	Apply (declare_function, 
	       [Const (Symbol("SNARK", "+")), Const (Nat 2),
		Const (Parameter(":associative")), Const (Boolean true),
		Const (Parameter(":commutative")), Const (Boolean true)]),
	Apply (declare_function, 
	       [Const (Symbol("SNARK", "*")), Const (Nat 2),
		Const (Parameter(":associative")), Const (Boolean true), 
		Const (Parameter(":commutative")), Const (Boolean true)])

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

  
  op LogicalSorts: LispTerms
  def logicalSorts = 
      [
	Apply (declare_function, 
	       [Const (Symbol("SNARK", "logical-&")), Const (Nat 2),
		Const (Parameter(":sort")),
		Apply ((Op "QUOTE"), 
		       [Apply ((Op "SNARK::logical"), 
			       [Const (Parameter("SNARK::logical")),
				Const (Parameter("SNARK::logical"))])]),
		Const (Parameter(":associative")), Const (Boolean true),
		Const (Parameter(":commutative")), Const (Boolean true)]),
	Apply (declare_function, 
	       [Const (Symbol("SNARK", "logical-or")), Const (Nat 2),
		Const (Parameter(":sort")),
		Apply ((Op "QUOTE"), 
		       [Apply ((Op "SNARK::logical"), 
			       [Const (Parameter("SNARK::logical")),
				Const (Parameter("SNARK::logical"))])]),
		Const (Parameter(":associative")), Const (Boolean true),
		Const (Parameter(":commutative")), Const (Boolean true)])
       ]

%"(snark::declare-function-symbol 'snark::logical-& 2
%                  :sort '(snark::logical snark::logical snark::logical)
%                  :associative t
%                  :commutative t)",
%	 "(snark::declare-function-symbol 'snark::logical-or 2
%                  :sort '(snark::logical snark::logical snark::logical)
%                  :associative t
%                  :commutative t)"

  
  op snarkBuiltInSorts: Boolean -> LispTerms
  
  def snarkBuiltInSorts(useLogicalSorts) = 
      (if useLogicalSorts then logicalSorts else [])
      ++
      arithmeticSorts 

  op snarkSorts: Spec -> LispTerms

  def snarkSorts(spc) =
      let sorts = sortsAsList(spc) in
      let snarkSorts =
             map(fn (qual, id, info) ->
	            Apply (declare_sort, [Const (Symbol("SNARK", id))]))
	     sorts in
         snarkBuiltInSorts(true) ++ snarkSorts

  op snarkFunctionNoArityDecl: Spec * String * Sort -> LispTerm

  def snarkFunctionNoArityDecl(spc, name, srt) =
    (case srt of
       Base (Qualified(qual, id), srts, _) ->
	 Apply (declare_function, 
		[Const (Symbol("SNARK", name)), Const (Nat 0),
		 Const (Parameter(":sort")),
		 Const (Symbol("SNARK", id))])
	| _ -> Const (Parameter "FD1"))

  op snarkFunctionNoCurryDecl: Spec * String * Sort * Nat -> LispTerm

  def snarkFunctionNoCurryDecl(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case productOpt(spc, dom) of
	  Some fields -> 
	    let def snarkBaseSort(s:Sort, rng?):LispTerm = 
	          case s of
		     Base(Qualified( _,id),_,_) -> if rng? then Op ("SNARK::"^id)
                                                     else Const (Parameter ("SNARK::"^id))
		    | Product _ -> Const (Boolean true)
		    | Arrow _ -> Const (Boolean true)
		    | TyVar _ -> Const (Boolean true) in
	    let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(srt, false))
	                          fields in
	      Apply(declare_function, 
		    [Const (Symbol("SNARK", name)), Const (Nat arity),
		     Const (Parameter(":sort")),
		     Apply ((Op "Quote"),
			    [Apply (snarkBaseSort(rng, true),
				    domSortList)])])

  def snarkFunctionCurryNoArityDecl(spc, name, srt) =
    snarkFunctionNoArityDecl(spc, name, srt)

  def snarkFunctionCurryDecl(spc, name, srt, arity) =
    Const (Parameter "Curry")

  op snarkFunctionDecl: Spec * String * Sort -> LispTerm

  def snarkFunctionDecl(spc, name, srt) =
%    let _ = toScreen("Generating snark decl for "^name^" with sort: ") in
%    let _ = printSortToTerminal srt in
    (case (curryShapeNum(spc, srt), sortArity(spc, srt))
       of (1,None) -> snarkFunctionNoArityDecl(spc, name, srt)
	| (1, Some(_,arity)) -> snarkFunctionNoCurryDecl(spc, name, srt, arity)
	| (curryN, None) -> snarkFunctionCurryNoArityDecl(spc, name, srt)
	| (curryN, Some (_, arity)) -> snarkFunctionCurryDecl(spc, name, srt, arity)
	| _ -> snarkFunctionNoArityDecl(spc, name, srt))

  op snarkOpDeclPartial: Spec * String * Sort -> Option LispTerm

  def snarkOpDeclPartial(spc, name, srt) =
    let decl = snarkOpDecl(spc, name, srt) in
      case decl of
	Const _ -> None
        | _ -> Some decl
  
  op snarkOpDecl: Spec * String * Sort -> LispTerm

  def snarkOpDecl(spc, name, srt) =
    if functionSort?(spc, srt)
      then snarkFunctionDecl(spc, name, srt)
      else snarkFunctionDecl(spc, name, srt)

  op snarkOpDecls: Spec -> LispTerms

  def snarkOpDecls(spc) =
    let opsigs = specOps(spc) in
    let snarkOpDecls =
          mapPartial(fn (qname, name, _, srt) -> snarkOpDeclPartial(spc, name, srt))
	  opsigs in
      snarkOpDecls


  def ppSpec (s : SnarkSpec) : Pretty =
      let sortDecls = s.sortDecls 	in
      let opDecls = s.opDecls 	in
      let name = s.name 		in
%      let assertions = s.assertions in
%      let conjectures = s.conjectures in
%      let ppSortTerms = map ppTerm sortDecls in
%      let ppOpTerms = map ppTerm opDecls in
      prettysAll
     (
     (section (";;; Snark spec: " ^ name,
	       [string ("(in-package \"" ^ "SNARK" ^ "\")")]))
     ++ 
     (section (";;; Sorts",     List.map ppTerm     sortDecls))
     ++ 
     (section (";;; Ops",     List.map ppTerm     opDecls))
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
