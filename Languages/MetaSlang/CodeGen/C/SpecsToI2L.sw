(**
 Stand-alone C-code generation for specs
*)


SpecsToI2L qualifying spec {

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

  sort Term = MS.Term

  sort CgContext = {
		    specname       : String, % not (yet) used
		    isToplevel     : Boolean, % not used
		    useRefTypes    : Boolean, % always true
		    constrOps      : List(QualifiedId), % not used, constrOps are distinguished by their name (contain "$$")
		    currentOpSort  : Option(QualifiedId)
		   }

  op defaultCgContext: CgContext
  def defaultCgContext = {
			 specname = "",
			 isToplevel = false,
			 useRefTypes = true,
			 constrOps = [],
			 currentOpSort = None
			}

  op unsetToplevel: CgContext -> CgContext
  def unsetToplevel(ctxt) =
    {specname=ctxt.specname,isToplevel=false,useRefTypes=ctxt.useRefTypes,constrOps=ctxt.constrOps,currentOpSort=ctxt.currentOpSort}

  op setCurrentOpSort: CgContext * QualifiedId -> CgContext
  def setCurrentOpSort(ctxt,qid) =
    {specname=ctxt.specname,isToplevel=ctxt.isToplevel,
     useRefTypes=ctxt.useRefTypes,constrOps=ctxt.constrOps,currentOpSort=Some(qid)}

  op mkInOpStr: CgContext -> String
  def mkInOpStr(ctxt) =
    case ctxt.currentOpSort of
      | Some qid -> "in op \""^(printQualifiedId qid)^"\": "
      | None -> ""

  op useConstrCalls : CgContext -> Boolean
  def useConstrCalls(ctxt) =
    case ctxt.currentOpSort of
      | None -> true
      | Some (qid as Qualified(q,id)) -> %~(member(qid,ctxt.constrOps))
        %let _ = writeLine("useConstrCalls, id="^id) in
        let expl = concat(String.explode q, String.explode id) in
	let (indl,_) = List.foldl (fn(c,(indl,n)) -> if c = #$ then (cons(n,indl),n+1) else (indl,n+1)) ([],0) expl in
	case indl of
	  | [n,m] ->
	      if n = m+1 then
		%let _ = writeLine("constructor op: \""^(printQualifiedId qid)^"\"") in
		false
	      else false
          | _ -> true



  op generateI2LCodeSpec: AnnSpec.Spec * Boolean * List(QualifiedId) -> ImpUnit
  def generateI2LCodeSpec(spc, useRefTypes, constrOps) =
    generateI2LCodeSpecFilter(spc,useRefTypes,constrOps,(fn(_) -> true))

  op generateI2LCodeSpecFilter: AnnSpec.Spec * Boolean * List(QualifiedId) * (QualifiedId -> Boolean) -> ImpUnit
  def generateI2LCodeSpecFilter(spc, useRefTypes, constrOps, filter) =
    %let _ = writeLine(";;   phase 1: Generating i2l...") in
    let ctxt = {specname="", isToplevel=true, useRefTypes=useRefTypes, constrOps=constrOps, currentOpSort=None} in
    %let spc = normalizeArrowSortsInSpec(spc) in
    let transformedOps = foldriAQualifierMap
                          (fn(qid,name,opinfo,l1) ->
			   if filter(Qualified(qid,name)) then
			     let trOp = opinfo2declOrDefn(ctxt,spc,Qualified(qid,name),opinfo,None) in
			     List.concat(l1,[trOp])
			   else
			     %let _ = writeLine("skipping "^(printQualifiedId(Qualified(qid,name)))) in
			     l1
			   )
			   [] spc.ops
    in
    %let _ = writeLine("ops transformed.") in
    let len = List.length(transformedOps) in
    %let _ = writeLine(";;            "^Integer.toString(len)^" ops have been transformed.") in
%    let _ = foldriAQualifierMap 
%	   (fn(qid,name,(aliases,tvs,defs),l) -> 
%	    let _ = writeLine("sort "^printQualifiedId(Qualified(qid,name))) in
%	    let _ = writeLine("  typeVars: "^(List.foldl(fn(tv,s)->s^tv^" ") "" tvs)) in
%	    let _ = writeLine("  aliases:     "^(List.foldl (fn(qid0,s) -> s^(printQualifiedId(qid0))^" ") "" aliases)) in
%	    let _ = writeLine("  defs: ") in
%	    let _ = List.app(fn(tvs,srt) -> 
%			     let _ = writeLine("   typeVars: "^(List.foldl(fn(tv,s)->s^tv^" ") "" tvs)) in
%			     writeLine("   "^printSort(srt))) defs in
%	    l)
%	   [] spc.sorts
%    in

    let res = {
	       name = "",%spc.name:String,
	       includes = [],
	       decls = {
			typedefs = foldriAQualifierMap 
	                           (fn(qid,name,sortinfo,l2) ->
				    if filter(Qualified(qid,name)) then
				      (case sortinfo2typedef(ctxt,spc,Qualified(qid,name),sortinfo) of
					 | Some typedef -> concat(l2,[typedef])
					 | None -> l2)
				    else 
				      %let _ = writeLine("skipping "^(printQualifiedId(Qualified(qid,name)))) in
				      l2
					)
			           [] spc.sorts,
			opdecls  = List.foldl (fn | (OpDecl d,l3) -> concat(l3,[d]) | (_,l4) -> l4)
	                           [] transformedOps,
			funDecls = List.foldl (fn | (FunDecl d,l5) -> concat(l5,[d])
					          | (FunDefn{decl=d,body=_},l6) -> concat(l6,[d])
		                                  | (_,l7) -> l7)
	                           [] transformedOps,
			funDefns = List.foldl (fn | (FunDefn d,l8) -> concat(l8,[d]) | (_,l9) -> l9)
	                           [] transformedOps,
			varDecls = List.foldl (fn | (VarDecl d,l10) -> concat(l10,[d]) | (_,l11) -> l11)
	                           [] transformedOps,
			mapDecls = List.foldl (fn | (MapDecl d,l12) -> concat(l12,[d]) | (_,l13) -> l13)
	                           [] transformedOps
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
  op sortinfo2typedef: CgContext * Spec * QualifiedId * SortInfo -> Option TypeDefinition
  def sortinfo2typedef(ctxt,spc,qid,(aliases,tvs,defs)) =
    let def qid2typedefId(qid) =
          case qid of
	    | Qualified(spcname,name) -> (spcname,name)
%	    | Local(name) -> ("",name)
    in
    let typename = qid2typedefId(qid) in
    let res = case defs of
                 | [] -> None % Some (typename,Any) %None 
                 | (tvs,srt)::_ -> Some (typename,sort2type(ctxt,spc,tvs,srt))
    in
    res

  def sort2type(ctxt,spc,tvs,srt) =
    let def qid2typedefId(qid) =
    case qid of
      | Qualified(spcname,name) -> (spcname,name)
    in
    let usrt = unfoldToSpecials(spc,srt) in
    %let usrt = unfoldBaseVP(spc,srt,false,true) in
    %let _ = String.writeLine(printSort(srt)^"-[unfold]->"^printSort(usrt)) in
    case usrt of
      % primitives ----------------------------------------------
      | Boolean _  -> Primitive "Boolean"
      | Base(Qualified(_,"Nat"),    [],_) -> Primitive "Nat"
      | Base(Qualified(_,"Integer"),[],_) -> Primitive "Integer"
      | Base(Qualified(_,"Char"),   [],_) -> Primitive "Char"
      | Base(Qualified(_,"String"), [],_) -> Primitive "String"
     %| Base(Qualified(_,"Float"),[],_) -> Primitive "Float"

     % reference type
     %| Base(Qualified("ESpecPrimitives","Ref"),[srt],_) -> Ref(sort2type(ctxt,spc,tvs,srt))

     %| Base(Qualified(_,"List"),[psrt],_) ->
     %    let ptype = sort2type(ctxt,spc,tvs,psrt) in
     %	  List(ptype)

     %| Base(Qualified(_,"List"),[psrt],_) ->
     %  System.fail("sorry, this version of the code generator doesn't support lists.")
     %         
     %     System.fail("if using List sort, please add a term restricting "^
     %	   "the length of the list\n       "^
     %	   "(e.g. \"{l:List("^printSort(psrt)^")| length(l) <= 32}\")")
		

      | Subsort(Base(Qualified(_,"Nat"),[],_),
		Lambda([(VarPat((X,_),_),_,
			 Apply(Fun(Op(Qualified(_,"<"),_),_,_),
			       Record([(_,Var((X0,_),_)),(_,Fun(Nat(n),_,_))],_),_)
			)],_),_) -> if X = X0 then RestrictedNat n
				    else Primitive "Nat"


      % ----------------------------------------------------------------------
      % special form for list sorts, term must restrict length of list
      % the form of the term must be {X:List(T)| length(X) < N}
      % where N must be a constant term evaluating to a positive Nat
      % lenght(X) <= N, N > length(X), N >= length(X), N = length(X) can also be used
      | Subsort(Base(Qualified(_,"List"),[psrt],_),term,_) ->
	       let ptype = sort2type(unsetToplevel(ctxt),spc,tvs,psrt) in
	       (let err = ("wrong form of restriction term for list length") in
		case term of
		  | Lambda ([(VarPat((X,_),_),t1,t2)],_) -> 
		    (case t2 of
		       | Apply(Fun(cmp,_,_),
			       Record([arg1,arg2],_),_) ->
		               let
			         def checklengthterm((_,lengthop),(_,constantterm),minconst) =
				   let _ = 
				   case lengthop of
				     | Apply(Fun(Op(Qualified(_,"length"),_),_,_),V,_) ->
				       (case V of
					  | Var((X0,_),_) -> if X = X0 then () else System.fail(err)
					  | _ -> System.fail(err))
				     | _ -> System.fail(err)
				   in
				   let const = constantTermIntegerValue(spc,constantterm) in
				   if const<minconst then System.fail(err) else const
			       in
		               (case cmp of
				  | Op(Qualified(_,comparesym),_) ->
				    (case comparesym of
				       | ">" -> let const = checklengthterm(arg2,arg1,2) in
				                BoundList(ptype,const-1)
				       | "<" -> let const = checklengthterm(arg1,arg2,2) in
						BoundList(ptype,const-1)
				       | "<=" -> let const = checklengthterm(arg1,arg2,1) in
						BoundList(ptype,const)
				       | ">=" -> let const = checklengthterm(arg2,arg1,1) in
						BoundList(ptype,const)
				       | _ -> System.fail(err)
					       )
				   | Eq -> let const = checklengthterm(arg1,arg2,1) in
				           BoundList(ptype,const)
					  )
		       | _ -> System.fail(err)
		      )
		  | _ -> System.fail(err)
		  )
      % ----------------------------------------------------------------------


      % for arrow sorts make a distinction between products and argument lists:
      % op foo(n:Nat,m:Nat) -> Nat must be called with two Nats
      | Arrow(srt1,srt2,_) ->
	  let srt1 = unfoldToSpecials(spc,srt1) in
	  %let srt1 = unfoldToProduct(spc,srt1) in
	  %let _ = writeLine("domsort: "^printSort(srt1)) in
	  (case srt1 of
	     | Product(fields,_) ->
	        let types = List.map (fn(_,srt) -> 
				      let srt = unfoldToSpecials(spc,srt) in
				      sort2type(unsetToplevel ctxt,spc,tvs,srt)) fields in
		let typ = sort2type(unsetToplevel ctxt,spc,tvs,srt2) in
		FunOrMap(types,typ)
	     | _ -> FunOrMap([sort2type(unsetToplevel ctxt,spc,tvs,srt1)],
			     sort2type(unsetToplevel ctxt,spc,tvs,srt2))
	  )

      % ----------------------------------------------------------------------

      | Product(fields,_) ->
	  if fieldsAreNumbered(fields) then
	    let types = List.map (fn(_,srt) -> sort2type(unsetToplevel ctxt,spc,tvs,srt)) fields in
	    if types = nil then Void else Tuple(types)
	  else
	    let structfields = List.map 
	                       (fn(id,srt) -> (id,sort2type(unsetToplevel ctxt,spc,tvs,srt))) fields
	    in
	    if structfields = nil then Void else Struct(structfields)

      % ----------------------------------------------------------------------

      | CoProduct(fields,_) ->
	    let unionfields = List.map
	                      (fn |(id,None) -> (id,Void)
			          |(id,Some srt) -> (id,sort2type(unsetToplevel ctxt,spc,tvs,srt)))
			      fields
	    in
	    Union unionfields

      % ----------------------------------------------------------------------


      | TyVar _ -> 
	    if ctxt.useRefTypes then Any
	    else
	      System.fail("sorry, this version of the code generator doesn't support "^
			  "polymorphic types.")

      % use the base sorts as given, assume that the original definition has been checked
      | Base(qid,_,_) -> Base (qid2typedefId qid)

      | Subsort(srt,trm,_) -> % ignore the term...
	sort2type(ctxt,spc,tvs,srt)

      | _ -> %let _ = System.print(usrt) in
	       System.fail("sorry, code generation doesn't support the use of this sort:\n       "
			   ^printSort(srt))

  op constantTermIntegerValue : Spec * Term -> Integer
  def constantTermIntegerValue(spc,t) =
    let def err() = (System.print(t);
             System.fail("cannot evaluate the constant value of term "^
			 printTerm(t)))
    in
    case t of
      | Fun(Nat(n),_,_) -> n
      | Fun(Op(qid,_),_,_) -> 
      (case getOpDefinition(spc,qid) of
	 | None -> err()
	 | Some t -> constantTermIntegerValue(spc,t)
	)
      | _ -> err()



  (**
   returns the definition term of the given op, if it exists in the given spec.
   *)
  op getOpDefinition: Spec * QualifiedId -> Option Term
  def getOpDefinition(spc,qid as Qualified(q,id)) =
    let opmap = spc.ops in
    case findAQualifierMap(opmap,q,id) of
      | None -> None
      | Some (_,_,_,termschemes) -> 
      (case termschemes of
	 | [] -> None
	 | (tvs,term)::_ -> Some term
	)


  (**
    unfolds a sort, only if it is an alias for a Product, otherwise it's left unchanged;
    this is used to "normalize" the arrow sorts, i.e. to detect, whether the first argument of
    an arrow sort is a product or not. Only "real" products are unfolded, i.e. sort of the
    form (A1 * A2 * ... * An) are unfolded, not those of the form {x1:A1,x2:A2,...,xn:An}
  *)
  op unfoldToProduct: Spec * Sort -> Sort
  def unfoldToProduct(spc,srt) =
    let
      def unfoldRec(srt) =
	let usrt = unfoldBaseKeepPrimitives(spc,srt) in
	if usrt = srt then srt else unfoldRec(usrt)

    in
    let usrt = unfoldRec(srt) in
    case usrt of
      | Product (fields,_) -> if fieldsAreNumbered(fields) then usrt else srt
      | _ -> srt


  op unfoldToCoProduct: Spec * Sort -> Sort
  def unfoldToCoProduct(spc,srt) =
    let
      def unfoldRec(srt) =
	let usrt = unfoldBase(spc,srt) in
	if usrt = srt then srt else unfoldRec(usrt)

    in
    let usrt = unfoldRec(srt) in
    case usrt of
      | CoProduct (fields,_) -> usrt
      | _ -> srt

  % unfold to special sort in order to get the necessary information to generate code
  % e.g. unfold to sort of the form {n:Nat|n<C} which is needed to generate arrays
  op unfoldToSpecials: Spec * Sort -> Sort
  def unfoldToSpecials(_(*spc*),srt) = srt
  def unfoldToSpecials_(spc,srt) =
  let
    def unfoldToSpecials0(srt) =
      let
        def unfoldRec(srt) =
	  %let _ = String.writeLine("unfoldRec: "^MetaSlangPrint.printSort(srt)) in
	  let usrt = unfoldBaseKeepPrimitives(spc,srt) in
	  if usrt = srt then srt else unfoldRec(usrt)
      in
      let usrt = unfoldRec(srt) in
      case usrt of
	% this corresponds to a term of the form {x:Nat|x<C} where C must be a Integer const
        | Subsort(Base(Qualified(_,"Nat"),[],_),
		  Lambda([(VarPat((X,_),_),_,
			   Apply(Fun(Op(Qualified(_,"<"),_),_,_),
				 Record([(_,Var((X0,_),_)),(_,Fun(Nat(n),_,_))],_),_)
			  )],_),_) -> if X = X0 then usrt else srt
	| _ -> srt
  in
  mapSort((fn(t)->t),unfoldToSpecials0,(fn(p)->p)) srt
  




  op normalizeArrowSortsInSpec: Spec -> Spec
  def normalizeArrowSortsInSpec(spc) =
    mapSpec ((fn(x) -> x),
	     (fn | Arrow(srt1,srt2,X) -> 
	           Arrow(unfoldToProduct(spc,srt1),srt2,X)
	         | srt -> srt),
	     (fn(x) -> x)) spc

 op unfoldBaseKeepPrimitives  : Spec * Sort -> Sort 
 def unfoldBaseKeepPrimitives (sp:Spec, srt) = 
  case srt of
    | Base (qid, srts, a) ->
       (case findTheSort(sp,qid)
          of None -> srt
           | Some(_, _, []) -> srt
           | Some(_, _, (tvs, srt2)::_) ->
             let
               def continue() =
		 let ssrt = substSort (zip (tvs, srts), srt2) in
		 unfoldBaseKeepPrimitives (sp, ssrt)
	     in
	       (case srt of
		 | Boolean _ -> srt
		 | Base(Qualified("Nat","Nat"),[],_) -> srt
		 | Base(Qualified("Integer","Integer"),[],_) -> srt
		 | Base(Qualified("Char","Char"),[],_) -> srt
		 | Base(Qualified("String","String"),[],_) -> srt
		 | Base(Qualified("List","List"),[psrt],X) ->
		   let upsrt = unfoldBaseKeepPrimitives(sp,psrt) in
		   Base(Qualified("List","List"),[upsrt],X)
		 | Base(Qualified("Option","Option"),[psrt],X) ->
		   let upsrt = unfoldBaseKeepPrimitives(sp,psrt) in
		   Base(Qualified("Option","Option"),[upsrt],X)
		 | _ -> continue()
	       )
	  )
     | _ -> srt


  % this is used to distinguish "real" product from "record-products"
  op fieldsAreNumbered: fa(a) List(String * a) -> Boolean
  def fieldsAreNumbered(fields) =
    let
      def fieldsAreNumbered0(i,fields) =
	case fields of
          | [] -> true
	  | (id,_)::fields -> id = Nat.toString(i) & fieldsAreNumbered0(i+1,fields)
    in
    fieldsAreNumbered0(1,fields)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                    %
  %                       TERMS -> I2L.EXPRESSIONS                     %
  %                                                                    %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort opInfoResult = | OpDecl  Declaration 
		     | FunDecl FunDeclaration
		     | FunDefn FunDefinition
                     | VarDecl Declaration
                     | MapDecl FunDeclaration
                     | Skip


  op opinfo2declOrDefn: CgContext * Spec * QualifiedId * OpInfo * Option(List String) -> opInfoResult
  
  def opinfo2declOrDefn(ctxt,spc,qid,(opnames,fixity,(tvs,srt),opterms),optParNames) =
    let def qid2declid(qid) =
          case qid of
            | Qualified(spcname,name) -> (spcname,name)
        def qid2str(Qualified(q,id)) =
	  if q = UnQualified then id else q^"."^id
        def getParamNames(ctxt,t) =
	  %let _ = System.print(t) in
	  let def errmsg ctxt = (case ctxt.currentOpSort of Some qid -> "in op "^(qid2str qid)^":\n" | _ -> "")^
	               "unsupported operator definition format:\n"^
	               "       "^printTerm(t)
	  in
	  case t of
	    | Lambda ([(pat,_,bodyterm)],_) ->
	      let plist =
	      (case pat of
		 | VarPat((id,_),_) -> [id]
		 | RecordPat(plist,_) -> List.map (fn | (_,VarPat((id,_),_)) -> id
						      | _ -> System.fail(errmsg ctxt)) plist
		 | _ -> System.fail (errmsg ctxt)
		)
	      in
	      (plist,bodyterm)
	    | _ -> System.fail(errmsg ctxt)
    in
    let id as (spcname,lid) = qid2declid(qid) in
    let id0 = (spcname,"__"^lid^"__") in
    %let _ = writeLine("translating op "^lid^"...") in
    let srt = unfoldToArrow(spc,srt) in
    %let _ = writeLine("srt: "^printSort(srt)) in
    let typ = sort2type(unsetToplevel ctxt,spc,tvs,srt) in
    let ctxt = setCurrentOpSort(ctxt,qid) in
    let res = 
      case typ of 
        | FunOrMap(types,rtype) ->
	  (case opterms of
             | [] -> let params = (case optParNames of
					    | None -> List.map (fn(t) -> ("",t)) types
					    | Some pnames -> zip(pnames,types)
				    )
		       in
	               FunDecl {
				name=id,
				params = params,
				returntype = rtype
			       }
	     | (tvs,term)::_ ->
		            let term = liftUnsupportedPattern(spc,term) in
		            let (pnames,bodyterm) = getParamNames(ctxt,term) in
	                    let decl = {
					name = id,
					params = zip(pnames,types),
					returntype = rtype
				       }
			    in
			    let expr = term2expression(ctxt,spc,bodyterm) in
			    FunDefn {
				     decl = decl,
				     body = Exp expr % functional function body
				    }
	    )
        | _ -> (case opterms of
		| [] -> OpDecl(id,typ,None)
		| (tvs,term)::_ -> OpDecl(id,typ,Some(term2expression(ctxt,spc,term)))
	       )
    in

    res

  op liftUnsupportedPattern: Spec * Term -> Term
  def liftUnsupportedPattern(spc,t) =
    let b = termAnn(t) in
    case t of
      | Lambda([(pat,_,bodyterm)],_) ->
        (case pat of
	   | VarPat _ -> t
	   | RecordPat(plist,_) -> 
	     if all (fn | (_,VarPat _) -> true | _ -> false) plist then t
	     else
	       %let _ = writeLine("unsupported pattern in operator definition: "^(printPattern pat)) in
	       let ty = inferType(spc,t) in
	       let varx:Term = Var(("x",ty),b) in
	       let appl = Apply(t,varx,b) in
	       let varpatx = VarPat(("x",ty),b) in
	       let newt = Lambda([(varpatx,mkTrue(),appl)],b) in
	       let _ = writeLine("new term: "^(printTerm newt)) in
	       newt
	   | _ -> t
	       )
      | _ -> t

  % --------------------------------------------------------------------------------


  op term2expression: CgContext * Spec * Term -> Expression
  def term2expression(ctxt,spc,term) =
    let srt = inferType(spc,term) in
    let srt = unfoldBaseKeepPrimitives(spc,srt) in
    let expr = term2expression_internal(ctxt,spc,term,srt) in
    let typ = sort2type(unsetToplevel ctxt,spc,[],srt) in
    (expr,typ)

  op term2expression_internal: CgContext * Spec * Term * Sort -> Expr
  def term2expression_internal(ctxt,spc,term,termsrt) =
    %let _ = System.print(term) in
    let def qid2varid(qid) =
          case qid of
	    | Qualified(spcname,name) -> (spcname,name)
	    %| Local(name) -> (spc.name,name)

        % extract the list of argument terms from a record term given
        % as second argument of an Apply term
	def getArgs(argterm) = 
	  case argterm of
	    | Record(fields,_) ->
	      if fieldsAreNumbered fields then
		List.map (fn(_,t) -> t) fields
	      else
		[argterm]
	    | _ -> [argterm]
    in
    let errmsg = (mkInOpStr(ctxt))^"unsupported feature: this format cannot be used for terms:\n"
                 ^printTerm(term)
    in
    % checks, whether the given id is an outputop of the espec; if yes is has to be
    % replaced by a VarDeref/FunCallDeref, as done below
%    let def isOutputOp(varid as (spcname,lid)) =
%          let outputops = ctxt.espc.interface.outputops in
%          %let _ = String.writeLine("outputops: "^(List.foldl (fn(id,s) -> s^id^" ") "" outputops)) in
%	  (spcname = ctxt.espc.spc.name) & (List.member(lid,outputops))
%    in
    case term of

      % this is active, when a Fun occurs "standalone", i.e. not in the context of an apply.
      % we restrict the possible forms to those not having an arrow sort, i.e. we don't support
      % functions as objects
      % Not, And, Or, etc,. should never occur "standalone", so we don't look for them here
      | Fun(fun,srt,_) ->
         if arrowSort?(spc,srt) then
	   case fun of
	     | Op(qid,_) -> let varid = qid2varid qid in
	                    VarRef varid
	     | _ -> 
	     System.fail("sorry, functions as objects (higher-order functions) "^
			 "are not yet supported:\n       "^
			 printTerm(term))
	 else
         (case fun of
	    | Nat n -> Int n
	    | String s -> Str s
	    | Char c -> Char c
	    | Bool b -> Bool b
	    | Op(qid,_) -> 
	      let varname = qid2varid qid in
	      %if isOutputOp varname
		%then VarDeref varname
	      %else 
	      Var varname
	    | Embed (id,_) -> 
	      let termsrt = foldSort(spc,termsrt) in
	      %let _ = writeLine("processing 0-ary constructor "^id^", srt="^printSort(termsrt)) in
	      if useConstrCalls(ctxt) then
		(case termsrt of
		   | Base(qid,_,_) ->
		     let vname = qid2varid qid in
		     ConstrCall(vname,id,[])
		   | Boolean _ -> ConstrCall(("Boolean", "Boolean"), id, [])
		   | _ -> AssignUnion(id,None)
		    )
	      else AssignUnion(id,None)
	    | _ -> System.fail errmsg
	   )

      | Apply(t1,t2,_) ->
	 let
	   def getProjectionList(t,projids) =
	     case t of
	       | Apply(Fun(Project(id),_,_),t2,_) -> getProjectionList(t2,cons(id,projids))
	       | _ -> (projids,t)
	 in
	 let args = getArgs t2 in
	 let def getExprs4Args() = List.map (fn(t) -> term2expression(ctxt,spc,t)) args in
	 (case getBuiltinExpr(ctxt,spc,t1,args) of
	    | Some expr -> expr
	    | None ->
	    let origlhs = t1 in
	    let
              % this is a sub-def, because we collect and skip projections
	      def process_t1(t1,projections) =
		(case t1 of
		   | Var((id,_),_)
		     -> let exprs = getExprs4Args() in
		        let varname = ("",id) in
			% infer the type of the original lhs to get the real type of the map
			% taking all the projections into account
			let lhssort = inferType(spc,origlhs) in
			let lhssort = unfoldToSpecials(spc,lhssort) in
			let lhstype = sort2type(unsetToplevel ctxt,spc,[],lhssort) in
			FunCall(varname,projections,exprs)
		   | Fun(Op(qid,_),_,_)
		   -> let exprs = getExprs4Args() in
		      let varname = qid2varid qid in
		      % infer the type of the original lhs to get the real type of the map
		      % taking all the projections into account
		      let lhssort = inferType(spc,origlhs) in
		      let lhssort = unfoldToSpecials(spc,lhssort) in
		      %let _ = String.writeLine("sort for "^varname.2^": "^
		      %			       MetaSlangPrint.printSort(t1sort)) in
		      let lhstype = sort2type(unsetToplevel ctxt,spc,[],lhssort) in
		      %if isOutputOp varname
		        %then MapAccessDeref (varname,lhstype,projections,exprs)
		      %else 
		        if isVariable(ctxt,qid) then
		          MapAccess(varname,lhstype,projections,exprs)
		        else
			  FunCall(varname,projections,exprs)
		   | Fun(Embed(id,_),_,_) 
		     -> let def mkExpr2() = term2expression(ctxt,spc,t2) in
		        if projections = [] then
			  let termsrt = foldSort(spc,termsrt) in
			  %let _ = writeLine("processing 0-ary constructor "^id^", srt="^printSort(termsrt)) in
			  if useConstrCalls(ctxt) then
			    (case termsrt of
			       | Base(qid,_,_) ->
			         let vname = qid2varid qid in
				 let exprs = 
				     (case t2 of
					| Record(fields,b) ->
					  if fieldsAreNumbered fields then
					    %let _ = writeLine("t2="^printTerm(t2)) in
					    map (fn(_,t) -> term2expression(ctxt,spc,t)) fields
					  else [mkExpr2()]
					| _ -> [mkExpr2()]
					   )
				 in
				 ConstrCall(vname,id,exprs)
			       | Boolean _ -> 
				 let exprs = 
				     (case t2 of
					| Record(fields,b) ->
					  if fieldsAreNumbered fields then
					    %let _ = writeLine("t2="^printTerm(t2)) in
					    map (fn(_,t) -> term2expression(ctxt,spc,t)) fields
					  else [mkExpr2()]
					| _ -> [mkExpr2()]
					   )
				 in
				 ConstrCall(("Boolean", "Boolean"), id, exprs)
			       | _ -> AssignUnion(id,Some(mkExpr2()))
			      )
			  else AssignUnion(id,Some(mkExpr2()))

			else System.fail(mkInOpStr(ctxt)^"unsupported feature: "^
					 "this term can not be used as an lhs-term of "^
					 "an application:\n"^printTerm(t1))
		   | Fun(Project(id),_,_)
		     -> let expr2 = term2expression(ctxt,spc,t2) in
		        if projections = [] then Project(expr2,id)
			else System.fail(mkInOpStr(ctxt)^"unsupported feature: "^
					 "this term can not be used as an lhs-term of "^
					 "an application:\n"^printTerm(t1))
	           | _ ->
			(case getProjectionList(t1,[]) of
		           | (prjs as (_::_),t1) -> process_t1(t1,prjs)
			   | _ -> 
			   % handle special cases:
			   (case simpleCoProductCase(ctxt,spc,term) of
			     | Some expr -> expr
			     | None ->
			       System.fail(mkInOpStr(ctxt)^"unsupported feature: "^
					   "this term can not be used as an lhs-term of "^
					   "an application:\n"^printTerm(t1))
			     )))
	    in
	      process_t1(t1,[])
	   )

      % ----------------------------------------------------------------------

      | Let([(pat,defterm)],term,_) % let's can only contain one pattern/term entry (see parser)
	-> (case pat of
	      | VarPat((id,srt),_)
                -> let defexpr = term2expression(ctxt,spc,defterm) in
		   let expr = term2expression(ctxt,spc,term) in
		   let typ = sort2type(unsetToplevel ctxt,spc,[],srt) in
		   Let(id,typ,defexpr,expr)
	      | WildPat _
                -> let defexpr = term2expression(ctxt,spc,defterm) in
		   let expr = term2expression(ctxt,spc,term) in
		   Comma [defexpr,expr]
	      | _ -> System.fail(mkInOpStr(ctxt)^"unsupported feature: this form of pattern cannot be used:\n"
				 ^printPattern(pat))
		  )

      % ----------------------------------------------------------------------

      | Record (fields,_) ->
	  if fieldsAreNumbered(fields) then
	    let exprs = List.map (fn(_,t) -> term2expression(ctxt,spc,t)) fields in
	    TupleExpr exprs
	  else
	    let fields = List.map (fn(id,t) -> (id,term2expression(ctxt,spc,t))) fields in
	    StructExpr fields

      % ----------------------------------------------------------------------

      | Var((id,_),_) -> Var ("",id)

      | Seq(terms,_) -> let exprs = List.map (fn(t) -> term2expression(ctxt,spc,t)) terms in
	                Comma(exprs)

      | IfThenElse(t1,t2,t3,_) ->
	let e1 = term2expression(ctxt,spc,t1) in
	let e2 = term2expression(ctxt,spc,t2) in
	let e3 = term2expression(ctxt,spc,t3) in
	IfExpr(e1,e2,e3)

      | SortedTerm(t,_,_) -> let (expr,_) = term2expression(ctxt,spc,t) in expr

      | _ -> (%System.print(term);
	      System.fail errmsg)



  op arrowSort?: Spec * Sort -> Boolean
  def arrowSort?(spc,srt) =
    case unfoldToArrow(spc,srt) of
      | Arrow _ -> true
      | _ -> false

  op getEqOpQid: QualifiedId -> QualifiedId
  def getEqOpQid(qid as Qualified(q,id)) =
    Qualified(q,"eq$"^id)

  op equalsExpression: CgContext * Spec * Term * Term -> Expr
  def equalsExpression(ctxt,spc,t1,t2) =
    %let _ = writeLine("t1="^printTermWithSorts(t1)) in
    let
      def t2e(t) = term2expression(ctxt,spc,t)
    in
    let
      def primEq() =
	let (e1,e2) = (t2e t1,t2e t2) in
	Builtin(Equals(e1,e2))
    in
    % analyse, which equal we need; let's hope type checking
    % already made sure, that the types fit, so just look at one
    % of the terms
    let srt = inferType(spc,t1) in
    let usrt = unfoldStripSort(spc,srt,false) in
    case usrt of
      | Boolean                            _  -> primEq()
      | Base    (Qualified(_,"Nat"),    [],_) -> primEq()
      | Base    (Qualified(_,"Integer"),[],_) -> primEq()
      | Base    (Qualified(_,"Char"),   [],_) -> primEq()
     %| Base    (Qualified(_,"Float"),  [],_) -> primEq()
      | Base    (Qualified(_,"String"), [],_) -> Builtin(StrEquals(t2e t1,t2e t2))
      | _ ->
        let srt = foldSort(spc,termSort t1) in
	let errmsg = "sorry, the current version of the code generator doesn't "
	             ^"support the equality check for sort\n"
	             ^printSort(srt)
	in
	%let _ = writeLine("found srt in Eq: "^printSort(srt)) in
        case srt of
	  | Base(qid,_,_) ->
	    let eqid as Qualified(eq,eid) = getEqOpQid qid in
	    (case findTheOp(spc,eqid) of
	       | None -> 
	         fail(errmsg^"\nReason: eq-op not found in extended spec:\n"^(printSpec spc))
	       | Some _ ->
	         let eqfname = (eq,eid) in
		 FunCall(eqfname,[],[t2e t1,t2e t2])
		)
          | Product(fields,_) ->
	    let eqterm = getEqTermFromProductFields(fields,srt,t1,t2) in
	    let (exp,_) = t2e(eqterm) in
	    exp
	  | _ -> fail(errmsg^"\n[term sort must be a base or product sort]") %primEq()

  op getEqTermFromProductFields: List(Id * Sort) * Sort * Term * Term -> Term
  def getEqTermFromProductFields(fields,osrt,varx,vary) =
    foldr (fn((fid,fsrt),body) ->
	   let b = sortAnn(osrt) in
	   let projsrt = Arrow(osrt,fsrt,b) in
	   let eqsort  = Arrow(Product([("1",fsrt),("2",fsrt)],b),Boolean b,b) in
	   let proj = Fun(Project(fid),projsrt,b) in
	   let t1 = Apply(proj,varx,b) in
	   let t2 = Apply(proj,vary,b) in
	   let t = Apply(Fun(Equals,eqsort,b),Record([("1",t1),("2",t2)],b),b) in
	   if body = mkTrue() then t
	   else
	     Apply(mkAndOp b,
		   Record([("1",t),("2",body)],b),b)
	     %IfThenElse(t,body,mkFalse(),b)
	    )
    (mkTrue()) fields


  op getBuiltinExpr: CgContext * Spec * Term * List(Term) -> Option Expr
  def getBuiltinExpr(ctxt,spc,term,args) =
    let
      def t2e(t) = term2expression(ctxt,spc,t)
    in
    case (term,args) of
      | (Fun(Equals,_,_),[t1,t2]) 
        -> let e = equalsExpression(ctxt,spc,t1,t2) in
	   Some e
      | (Fun(Op(Qualified("Integer","+"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntPlus(e1,e2)))
      | (Fun(Op(Qualified("Integer","-"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntMinus(e1,e2)))
      | (Fun(Op(Qualified("Integer","*"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntMult(e1,e2)))
      | (Fun(Op(Qualified("Integer","div"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntDiv(e1,e2)))
      | (Fun(Op(Qualified("Integer","rem"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntRem(e1,e2)))
      | (Fun(Op(Qualified("Integer","<"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntLess(e1,e2)))
      | (Fun(Op(Qualified("Integer","<="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntLessOrEqual(e1,e2)))
      | (Fun(Op(Qualified("Integer",">"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntGreater(e1,e2)))
      | (Fun(Op(Qualified("Integer",">="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntGreaterOrEqual(e1,e2)))
      | (Fun(Op(Qualified("Integer","~"),_),_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(IntUnaryMinus(e1)))

      | (Fun(Op(Qualified("Float","+"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatPlus(e1,e2)))
      | (Fun(Op(Qualified("Float","-"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatMinus(e1,e2)))
      | (Fun(Op(Qualified("Float","*"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatMult(e1,e2)))
      | (Fun(Op(Qualified("Float","div"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatDiv(e1,e2)))
      | (Fun(Op(Qualified("Float","<"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatLess(e1,e2)))
      | (Fun(Op(Qualified("Float","<="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatLessOrEqual(e1,e2)))
      | (Fun(Op(Qualified("Float",">"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatGreater(e1,e2)))
      | (Fun(Op(Qualified("Float",">="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(FloatGreaterOrEqual(e1,e2)))
      | (Fun(Op(Qualified("Float","~"),_),_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(FloatUnaryMinus(e1)))
      | (Fun(Op(Qualified("Float","toInt"),_),_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(FloatToInt(e1)))
      | (Fun(Op(Qualified("Float","toFloat"),_),_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(IntToFloat(e1)))

      | (Fun(Op(Qualified("Float","stringToFloat"),_),_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(StringToFloat(e1)))

      | (Fun(Op(Qualified("Nat","+"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntPlus(e1,e2)))
      | (Fun(Op(Qualified("Nat","-"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntMinus(e1,e2)))
      | (Fun(Op(Qualified("Nat","*"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntMult(e1,e2)))
      | (Fun(Op(Qualified("Nat","div"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntDiv(e1,e2)))
      | (Fun(Op(Qualified("Nat","rem"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntRem(e1,e2)))
      | (Fun(Op(Qualified("Nat","<"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntLess(e1,e2)))
      | (Fun(Op(Qualified("Nat","<="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntLessOrEqual(e1,e2)))
      | (Fun(Op(Qualified("Nat",">"),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntGreater(e1,e2)))
      | (Fun(Op(Qualified("Nat",">="),_),_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(IntGreaterOrEqual(e1,e2)))

      | (Fun(Not,_,_),[t1])
        -> let e1 = t2e t1 in
	   Some(Builtin(BoolNot(e1)))
      | (Fun(And,_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(BoolAnd(e1,e2)))
      | (Fun(Or,_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(BoolOr(e1,e2)))
      | (Fun(Implies,_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(BoolImplies(e1,e2)))
      | (Fun(Iff,_,_),[t1,t2])
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   Some(Builtin(BoolEquiv(e1,e2)))
      | (Fun(NotEquals, _,_),[t1,t2]) 
        -> let (e1,e2) = (t2e t1,t2e t2) in
	   let eqterm = (Builtin(Equals(e1,e2)),Primitive "Boolean") in
	   Some(Builtin(BoolNot(eqterm)))

      % var refs:
%      | (Fun(Op(Qualified("ESpecPrimitives","ref"),_),_,_),[t1])
%	-> let def qid2varname(qid) =
%                 case qid of
%	           | Qualified(spcname,name) -> (spcname,name)
%		   %| Local(name) -> (spc.name,name)
%	   in
%	   (case t1 of
%	      | Fun(Op(qid,_),_,_)
%	        -> %if List.member(qid,ctxt.vars) then Some(VarRef(qid2varname qid))
%		   %else 
%		       System.fail("\"ref\" can only be used for vars, but \""^
%				    (qidstr qid)^"\" is not declared as a var.")
%	      | _ -> System.fail("\"ref\" can only be used for vars, not for:\n"^
%				 printTerm(t1))
%	   )

      | _ -> None

  op isVariable: CgContext * QualifiedId -> Boolean
  %% In vanilla metaslang, as opposed to ESpecs, there are no variables,
  %% but they might appear at a future date.
  def isVariable(_(* ctxt *), _(* qid *)) = false % List.member(qid,ctxt.vars)


  (**

   simpleCoProductCase checks for a special case of lambda term that represents one of the most
   common uses of case expression:
   case term of
     | Constr1 (x1,x2)
     | Constr2 (y1)
     ....
   i.e. where the term's sort is a coproduct and the cases are the constructors of the coproduct.
   In the args of the constructors (x1,x2,y1 above) only var pattern are supported.
   *)

  op simpleCoProductCase: CgContext * Spec * Term -> Option Expr
  def simpleCoProductCase(ctxt,spc,term) =
    case term of
      | Apply(embedfun as Lambda(rules,_),term,_) ->
        (case rules of
	   | [(p as VarPat((v,ty),b),_,bodyterm)] ->
	     % that's a very simple case: "case term of v -> bodyterm" (no other case)
	     % we transform it to "let v = term in bodyterm"
	     let (t,_) = term2expression(ctxt,spc,Let([(p,term)],bodyterm,b)) in
	     Some t
	   | _ -> 
	%let _ = String.writeLine(MetaSlangPrint.printSort(srt))	in
	let
          def getTypeForConstructorArgs(srt,id) =
	    %let srt = unfoldBase(spc,srt) in
	    let srt = stripSubsorts(spc,srt) in
	    case srt of
	      | CoProduct (fields,_) ->
	        (case List.find (fn(id0,_) -> id0 = id) fields of
		   | Some(_,optsort) -> (case optsort of
					   | Some srt -> Some(sort2type(unsetToplevel ctxt,spc,[],srt))
					   | None -> None
					)
		   | None -> System.fail("internal error: constructor id "^id^" of term "^
					 printTerm(term)^" cannot be found.")
		  )
	      | _ -> let usrt = unfoldBase(spc,srt) in
		     if usrt = srt then
		       System.fail("internal error: sort of term is no coproduct: "^
				   printTerm(term)^":"^printSort(srt))
		     else getTypeForConstructorArgs(usrt,id)
	in
        % check whether the pattern have the supported format, i.e.
	% (constructor name followed by var patterns) or (wildpat)
        let
          def getUnionCase(pat,_,term) =
	    let def t2e(t) = term2expression(ctxt,spc,t) in
	    let cc = 
	    case pat of
	      | EmbedPat(constructorId,optpat,srt,_)
                -> let opttype = getTypeForConstructorArgs(srt,constructorId) in
	           (case optpat of
		      % case for nullary constructor
	              | None -> ConstrCase(Some constructorId,opttype,[],t2e term)
		      % cases for unary constructors:
		      | Some (VarPat((id,_),_)) -> ConstrCase(Some constructorId,opttype,[Some id],t2e term)
		      | Some (WildPat _) -> ConstrCase(Some constructorId,opttype,[None],t2e term)
		      % case for 2-and-more ary constructors,
		      % pattern must be a recordpat consisting of var or wildpattern
		      | Some(p as RecordPat(fields,_))
		        -> if fieldsAreNumbered(fields) then
			    let varlist =
			          List.map
				  (fn | (_,WildPat _) -> None
				      | (_,VarPat((id,_),_)) -> Some id
				      | (_,p) -> System.fail(mkInOpStr(ctxt)^"unsupported feature: you can "^
							     "only use var patterns or _ here, "^
							     "not:\n"^printPattern(p))
				  ) fields
			    in
			    ConstrCase(Some constructorId,opttype,varlist,t2e term)
			   else
			     System.fail(mkInOpStr(ctxt)^"unsupported feature: record pattern not "^
					 "supported:\n"^printPattern(p))
			     
		      | Some p -> System.fail(mkInOpStr(ctxt)^"unsupported feature: you can only use "^
					      "var patterns, tuples of these, or \"_\" here, "^
					      "not:\n"^printPattern(p))
			    )
	      | WildPat _ -> ConstrCase(None,None,[],t2e term)

	      | NatPat (n,_) -> NatCase(n,t2e term)
	      | CharPat (c,_) -> CharCase(c,t2e term)

	      | _ -> System.fail(mkInOpStr(ctxt)^"unsupported feature: pattern not supported, "^
				 "use embed or wildcard pattern instead:\n"
				 ^printPattern(pat)
				)
	    in
	      cc
	in
	let unioncases = List.map getUnionCase rules in
	let expr = term2expression(ctxt,spc,term) in
	Some(UnionCaseExpr(expr,unioncases))
        )
      | _ -> (String.writeLine(mkInOpStr(ctxt)^"fail in simpleCoProductCase (wrong term format)");
	      None)


% --------------------------------------------------------------------------------

op foldSort : Spec * Sort -> Sort
def foldSort(spc,srt) =
  let optsrt =
    foldriAQualifierMap
    (fn(q,id,sortinfo as (aliases,tvs,defs),optsrt) ->
     case optsrt of
       | Some srt -> Some srt
       | None -> (case defs of
		    | [] -> None
		    | (tvs,srt0)::_ ->
		      %let usrt = unfoldBase(spc,srt) in
		      %let usrt0 = unfoldBase(spc,srt0) in
		      if equalSort?(srt,srt0) then
			let b = sortAnn srt0 in
			let qid = Qualified(q,id) in
			let tvs = map (fn(tv) -> TyVar(tv,b)) tvs in
			Some(Base(qid,tvs,b))
		      else None
		       )
    )
    None spc.sorts
  in
  case optsrt of
    | Some srt -> srt
    | None -> srt


}
