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

  op declare_proposition_symbol: LispCell
  def declare_proposition_symbol = Lisp.symbol("SNARK","DECLARE-PROPOSITION-SYMBOL")

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
  op baseSorts: List LispCell
  def baseSorts = 
      [ 
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "Option"))],
	Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", "List"))]
      ]

  op snarkBaseDecls: List LispCell
  def snarkBaseDecls =
    [
	Lisp.list[declare_predicate,
		  Lisp.quote(Lisp.symbol("SNARK", "embed?")), Lisp.nat(2)]
       ]
						    

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
		 )
		]
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
      ++
      baseSorts

  op snarkSorts: Spec -> List LispCell

  def snarkSorts(spc) =
      let sorts = sortsAsList(spc) in
      let snarkSorts =
             map(fn (qual, id, info) ->
	            Lisp.list [declare_sort, Lisp.quote(Lisp.symbol("SNARK", id))])	%
                 sorts in
      let snarkSubSorts = mapPartial(fn (qual, id, info) ->
			      sortInfoToSnarkSubsort(spc, id, info))
                              sorts in
         snarkBuiltInSorts(false) ++ snarkSorts ++ snarkSubSorts

  op sortInfoToSnarkSubsort: Spec * Id * SortInfo -> Option LispCell
  def sortInfoToSnarkSubsort(spc, id, info) =
    let (_, _, srtScheme) = info in
    case srtScheme of
      | Nil -> None
      | [(_, srt)] ->
        case srt of
	  | Subsort (supSrt, pred, _) ->
	     Some (Lisp.list [declare_subsorts, Lisp.quote(snarkBaseSort(spc, supSrt, false)), Lisp.quote(Lisp.symbol("SNARK", id))])
	  | _ -> None

  op snarkFunctionNoArityDecl: Spec * String * Sort -> LispCell

  def snarkFunctionNoArityDecl(spc, name, srt) =
    (case srt of
       | Base(Qualified( _,"Boolean"),_,_) -> snarkPropositionSymbolDecl(name)
       | Base (Qualified(qual, id), srts, _) ->
          Lisp.list [declare_constant, Lisp.quote(Lisp.symbol("SNARK", name)),
		     Lisp.symbol("KEYWORD","SORT"),
		     Lisp.quote(snarkBaseSort(spc, srt, true))]
       | Arrow(dom, rng, _) ->
	  case rng of
	  | Base(Qualified( _,"Boolean"),_,_) -> snarkPredicateDecl(spc, name, dom, 1)
	  | _ -> 
	    let snarkDomSrt = snarkBaseSort(spc, dom, false) in
	        Lisp.list[declare_function,
			  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(1),
			  Lisp.symbol("KEYWORD","SORT"),
			  Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))]
       )

  def snarkPropositionSymbolDecl(name) =
    Lisp.list[declare_proposition_symbol,
	      Lisp.quote(Lisp.symbol("SNARK", name))]

  def snarkBaseSort(spc, s:Sort, rng?):LispCell = 
	          case s of
		    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NATURAL")
		    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","INTEGER")
		    | Base(Qualified("Boolean","Boolean"),_,_) -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE")
		    | Base(Qualified(qual,id),_,_) -> let res = findBuiltInSort(spc, Qualified(qual,id), rng?) in
                      %let _ = if specwareDebug? then toScreen("findBuiltInSort: "^printSort(s)^" returns ") else () in
                      %let _ = if specwareDebug? then  LISP.PPRINT(res) else Lisp.list [] in
		      %let _ = if specwareDebug? then  writeLine("") else () in
		      res   %findBuiltInSort(spc, Qualified(qual,id), rng?)
		    | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
                                                       else Lisp.symbol("SNARK",id)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar _ -> Lisp.symbol("SNARK","TRUE")
		    | _ -> Lisp.symbol("SNARK", "TRUE")

  def findBuiltInSort(spc, qid as Qualified(qual,id), rng?) =
    let optSrt = findTheSort(spc, qid) in
    case optSrt of
      | Some (names, _, schemes) ->
      (let
        def builtinSort?(s) =
	  case s of 
	    | Base(Qualified("Nat","Nat"),_,_) -> true
	    | Base(Qualified("Integer","Integer"),_,_) -> true
	    | Base(Qualified("Boolean","Boolean"),_,_) -> true 
            | _ -> false in
      let
	def builtinSnarkSort(s) =
	  case s of 
	    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NATURAL")
	    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","INTEGER")
	    | Base(Qualified("Boolean","Boolean"),_,_) -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE") in
      let builtinScheme = find (fn (_, srt) -> builtinSort?(srt)) schemes in
        (case builtinScheme of
	  | Some (_, srt) -> builtinSnarkSort(srt)
	  | _ -> case schemes of
	           | [(_, srt)] -> 
	              (case srt of
			| Subsort (supSrt, _, _) -> Lisp.symbol("SNARK",id)
			| _ -> snarkBaseSort(spc, srt, rng?))
	           | _ -> Lisp.symbol("SNARK",id)))
      | _ -> Lisp.symbol("SNARK",id)
    
  
  def snarkPredicateDecl(spc, name, dom, arity) =
    case productOpt(spc, dom) of
      | Some fields -> 
	let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(spc, srt, false))
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
  
  op snarkFunctionNoCurryDecl: Spec * String * Sort * Nat -> LispCell

  def snarkFunctionNoCurryDecl(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case rng of
	  | Base(Qualified( _,"Boolean"),_,_) -> snarkPredicateDecl(spc, name, dom, arity)
	  | _ ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(spc, srt, false))
	                          fields in
	      Lisp.list[declare_function,
			Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			Lisp.symbol("KEYWORD","SORT"),
			Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list(domSortList)))]
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

  op snarkFunctionDecl: Spec * String * Sort -> LispCell

  def snarkFunctionDecl(spc, name, srt) =
    %let _ = toScreen("Generating snark decl for "^name^" with sort: ") in
    %let _ = printSortToTerminal srt in
    (case (curryShapeNum(spc, srt), sortArity(spc, srt))
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
       snarkBaseDecls ++
       snarkOpDecls

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
