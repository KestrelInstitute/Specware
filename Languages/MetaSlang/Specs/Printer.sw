(*
 * This works but it's a mess. This will be refactored and perhaps
 * rewritten.
 *
 * MetaSlang pretty printer.
 * This module contains utilities for printing terms, sorts, and patterns to 
 * strings, files, or standard out.
 *
 * Formats supported are:
 *
 *  - Ascii
 *  - HTML
 *  - LaTeX
 *  - pdfLaTeX

 *  - highligthable Ascii
 *)

%% 
%% General comment.
%% This pretty printer targets different format (HTML, LaTeX, Pdf,Ascii)
%% At the same time it is possible to pretty print with path information
%% stored in a markTable variable in a context that is passed down.
%% This adds a lot of clutter to the code. Alternative ways for separating
%% concerns are speculated upon in the file "pretty-printing.sl", and
%% assembled in the document ../doc/deforestation/main.ps.
%% 

ASpecPrinter qualifying spec { 
  import ../AbstractSyntax/Printer
  import AnnSpec
  import /Library/Legacy/DataStructures/IntegerSet  % for indicesToDisable
  import /Library/Legacy/DataStructures/NatMap      % for markTable's

  %% ========================================================================

  sort Path = List Nat

  sort ParentSort = | Top | ArrowLeft | ArrowRight | Product | CoProduct | Quotient | Subsort 

  sort ParentTerm = | Top | Nonfix | Infix Associativity * Nat

  sort context = {
        	  pp                 : ATermPrinter,
        	  printSort          : Boolean,
        	  markSubterm        : Boolean,
        	  markNumber         : Ref Nat,
        	  markTable          : Ref (NatMap.Map (List Nat)),
        	  indicesToDisable   : IntegerSet.Set,
        	  sosIndicesToEnable : IntegerSet.Set
        	}


  %% ========================================================================

  op printTerm                    : fa(a) ATerm       a -> String
  op printSort                    : fa(a) ASort       a -> String 
  op printPattern                 : fa(a) APattern    a -> String
  op printSortScheme              : fa(a) ASortScheme a -> String 
  op printTermWithSorts           : fa(a) ATerm       a -> String
  op printSpec                    : fa(a) ASpec       a -> String
  op latexSpec                    : fa(a) ASpec       a -> String

  op printSpecToFile              : fa(a) String * ASpec a -> ()
  op latexSpecToFile              : fa(a) String * ASpec a -> ()
  op printSpecToTerminal          : fa(a)          ASpec a -> ()
  op printSpecWithSortsToTerminal : fa(a)          ASpec a -> ()

  op isShortTuple                 : fa(A) Nat * List (Id * A) -> Boolean
  op ppTerm                       : fa(a) context -> Path * ParentTerm -> ATerm    a -> Pretty
  op ppSort                       : fa(a) context -> Path * ParentSort -> ASort    a -> Pretty
  op ppPattern                    : fa(a) context -> Path * Boolean    -> APattern a -> Pretty
  op termToPretty                 : fa(a) ATerm a -> Pretty
  op printTermToTerminal          : fa(a) ATerm a -> ()
  op printSort                    : fa(a) ASort a -> String
  op printSortToTerminal          : fa(a) ASort a -> ()
  op printSortScheme              : fa(a) ASortScheme a -> String
  op printPattern                 : fa(a) APattern a -> String
  op printTermWithSorts           : fa(a) ATerm a -> String
  op ppProperty                   : fa(a) context -> Nat * AProperty a -> Line
  op ppSpec                       : fa(a) context -> ASpec a -> Pretty  
  op ppSpecR                      : fa(a) context -> ASpec a -> Pretty
  op ppSpecAll                    : fa(a) context -> ASpec a -> Pretty
  op ppSortDecls                  : fa(a) context -> ASortMap a -> Lines
  op ppOpDecls                    : fa(a) context -> AOpMap a -> Lines
  op specToPrettyVerbose          : fa(a) ASpec a -> Pretty
  op specToPretty                 : fa(a) ASpec a -> Pretty
  op specToPrettyR                : fa(a) ASpec a -> Pretty
  op printSpec                    : fa(a) ASpec a -> String
  op printSpecVerbose             : fa(a) ASpec a -> String
  op printSpecToTerminal          : fa(a) ASpec a -> ()
  op printSpecToFile              : fa(a) String * ASpec a -> ()
  op printMarkedSpecToFile        : fa(a) String * String * IntegerSet.Set * IntegerSet.Set * ASpec a -> NatMap.Map(List(Nat))
  op printMarkedSpecToString      : fa(a) IntegerSet.Set * IntegerSet.Set * ASpec a -> String * NatMap.Map(List(Nat))
  op printSpecWithSortsToTerminal : fa(a) ASpec(a) -> ()
  op latexSpecToPretty            : fa(a) ASpec(a) -> Pretty
  op latexSpec                    : fa(a) ASpec(a) -> String
  op latexSpecToFile              : fa(a) String * ASpec(a) -> ()
  op htmlSpecToPretty             : fa(a) ASpec(a) -> Pretty
  op htmlSpecToFile               : fa(a) String * ASpec(a) -> ()

  %% ========================================================================

  def toString = PrettyPrint.toString

  def isShortTuple (i, row) = 
   case row of
    | []           -> true
    | (lbl,r)::row -> lbl = Nat.toString i & isShortTuple (i + 1, row)
      

  def fa(a) isFiniteList (term : ATerm a) : Option (List (ATerm a)) =  
   case term of
    | Fun    (Embed ("Nil", false), _, _) -> Some []
    | Apply  (Fun (Embed("Cons", true), _, _),  Record ([(_, t1), (_, t2)], _), _) -> 
      (case isFiniteList t2 of
        | Some terms -> Some (cons (t1, terms))
        | None ->  None)
    | ApplyN ([Fun (Embed ("Cons", true), _, _), _, Record ([(_, t1), (_, t2)], _), _], _) -> 
      (case isFiniteList t2 of
        | Some terms -> Some (cons (t1, terms))
        | None ->  None)
    | _ -> None


  def initialize (pp, printSort?) : context = 
   {pp                 = pp,
    printSort          = printSort?,
    markSubterm        = false,
    markNumber         = ref 0,
    markTable          = ref NatMap.empty,
    indicesToDisable   = IntegerSet.empty,
    sosIndicesToEnable = IntegerSet.empty}
 
  def initializeMark (pp, indicesToDisable, sosIndicesToEnable) : context = 
    {pp                 = pp,
     printSort          = false,
     markSubterm        = true, 
     markNumber         = ref 0,
     markTable          = ref NatMap.empty,
     indicesToDisable   = indicesToDisable,
     sosIndicesToEnable = sosIndicesToEnable}
 
  def printSort?   (c:context) = c.printSort
  def markSubterm? (c:context) = c.markSubterm
 
  def fa(a) termFixity(term:ATerm a):Fixity = 
   case term of
    | Fun (termOp, srt, _) -> 
      (case termOp of
        | Op (_, fixity) -> fixity
        | Equals         -> Infix (Left, 20) % was 10 ??
        | _              -> Nonfix)
    | _ -> Nonfix
 
  def fa(a) printOp (context, 
        	     pp     : ATermPrinter, 
        	     termOp : AFun  a, 
        	     srt    : ASort a, 
        	     a      : a) 
   : Pretty = 
   case termOp of
    | Op        (idInfo, _) -> pp.ppOpId (idInfo)
    | Bool      b           -> pp.fromString (Boolean.toString b)
    | Nat       n           -> pp.fromString (Nat.toString n)
    | String    s           -> pp.fromString ("\""^s^"\"")              % "abc"
    | Char      c           -> pp.fromString ("#" ^ (Char.toString c))  % #A
    | Embed     (s,_)       -> pp.fromString (s)  %"embed("^s^")"
    | Project   s           -> pp.fromString ("project("^s^")")
    | Embedded  s           -> pp.fromString ("embed?("^s^")")
    | Quotient              -> pp.fromString ("quotient")
    | Choose                -> pp.fromString ("choose")
    | PQuotient _           -> pp.fromString ("quotient")
    | PChoose   _           -> pp.fromString ("choose")
    | Equals                -> pp.Equals
    | OneName   (x, _)      -> pp.fromString x
    | TwoNames  (x, y, _)   -> pp.fromString (x ^"."^ y)
 
    | Relax                 -> let p = case srt of Arrow (Subsort (_, p, _), _, _) -> p | _ -> mkTrueA a in
                               prettysFill [pp.fromString "relax", 
        				    string "(",
        				    ppTerm context ([], Top : ParentTerm) p, 
        				    string ")"]
    | Restrict              -> let p = case srt of Arrow (_, Subsort (_, p, _), _) -> p | _ -> mkTrueA a in
         	              prettysFill [pp.fromString "restrict", 
         				   string "(",
         				   ppTerm context ([], Top : ParentTerm) p,
         				   string ")"]
    | PRelax    t           -> %let p = case srt of Arrow (Subsort (_, p, _), _, _) -> p | _ -> mkTrueA a in
                               prettysFill [pp.fromString "relax", 
        				    string "(",
        				    ppTerm context ([], Top : ParentTerm) t,
        				    string ")"]
    | PRestrict t           -> %let p = case srt of Arrow (_, Subsort (_, p, _), _) -> p | _ -> mkTrueA a in
                               prettysFill [pp.fromString "restrict", 
        				    string "(",
        				    ppTerm context ([], Top : ParentTerm) t,
        				    string ")"]


  def fa(a) singletonPattern (pat : APattern a) = 
   case pat of
    | AliasPat    _ -> false
    | RelaxPat    _ -> false
    | QuotientPat _ -> false
    | _             -> true


  def printLambda (context, path, marker, match) = 
   let pp : ATermPrinter = context.pp in
   let def prRule marker (i,(pat,cond,trm)) = 
        case cond of
         | Fun(Bool true,_,_) -> 
            blockFill (0,
        	      [(0, prettysNone [marker,
        				ppPattern context ([0,i] ++ path,true) pat,
        				pp.Arrow]),
        	       (3, ppTerm context ([2,i] ++ path, Top : ParentTerm) trm)])
         | _ -> 
           blockFill (0,
        	      [(0, prettysNone [marker,
        				ppPattern context ([0,i] ++ path,true) pat,
        				string " ",
        				pp.Where,
        				string " ",
        				ppTerm context ([1,i] ++ path,Top:ParentTerm) cond,
        				pp.Arrow]),
        	       (3, ppTerm context ([3,i] ++ path, Top : ParentTerm) trm)])
   in
   prettysAll (case match of
                | [] -> []
        	| rule::rules -> 
                    [prRule marker (0,rule)] ++
        	  (ListUtilities.mapWithIndex (fn(i,rule) -> prRule pp.Bar (i + 1,rule)) 
        	                              rules))
 
  def ppTerm context (path, parentTerm) term =
   let pretty = ppTerm1 context (path,parentTerm) term in
   if markSubterm? context then
     let num = State.! context.markNumber in
     let table = State.! context.markTable in
     (context.markTable State.:= NatMap.insert(table,num,path);
      context.markNumber State.:= num + 1;
      PrettyPrint.markPretty(num,pretty))
   else 
     pretty

  def fa(a) ppTerm1 context (path,parentTerm) (term:ATerm a):Pretty =
   let pp : ATermPrinter = context.pp in
   let % Function application is printed taking special cases into account
       def prApply(t1,t2) = 
         case (t1,t2)
               of (Lambda (rules as (_ :: _),_),_) ->
 % Print lambda abstraction as
 % case pattern matching
        	  blockAll(0,
        	   [(0,prettysNone [pp.LP,pp.Case,ppTerm context ([1] ++ path,Top:ParentTerm) t2]),
        	    (3,prettysNone 
        		[printLambda(context,[0] ++ path,pp.Of,rules),
        		 pp.RP])])
 % Print tuple projection using
 % dot notation.
        	| (Fun(Project p,srt1,_),Var((id,srt2),_)) ->
        	  if printSort?(context)
        	     then prettysNone [	pp.fromString id,
        				string ":",
        				ppSort context ([0,1] ++ path,Top:ParentSort) srt2,
        			       	string ".",
        				string p,
        				string ":",
        				ppSort context ([0,0] ++ path,Top:ParentSort) srt1]
        	  else
        	  prettysNone [pp.fromString id,string ".",pp.fromString p]
        	| _ -> 
             blockFill(0,
        	[(0,ppTerm context ([0] ++ path,Top:ParentTerm) t1),
        	 (1,blockNone(0,
        		(case t2
        		   of Record(row,_) ->
        		       if isShortTuple(1,row)
        			 then %% We want the application to be mouse-sensitive not
        			      %% just the argument list--otherwise there is no way to
        			      %% select the application which is what you normally want
        			     [(0,ppTerm1 context ([1] ++ path,Top:ParentTerm) t2)]
        			else [(0,ppTerm context ([1] ++ path,Top:ParentTerm) t2)]
        		    | Var _ -> [(0,string " "),(0,ppTerm context ([1] ++ path,Top:ParentTerm) t2)(*,(0,string " ")*)]
        		    | _ -> [(0,pp.LP),
        		 	    (0,ppTerm context ([1] ++ path,Top:ParentTerm) t2),
        		 	    (0,pp.RP)])))])
   in

   case isFiniteList term of
    | Some terms -> ATermPrinter.ppListPath path
           (fn (path,term) -> 
        	ppTerm context (path,Top:ParentTerm) term) 
        	   (pp.LBrack,pp.Comma,pp.RBrack)  terms
    | None -> 

   case term of
    | Fun(top,srt,a) -> 
           if printSort?(context)
              then blockFill(0,
        	   [(0,printOp(context,pp,top,srt,a)),(0,string " : "),
        		(0,ppSort context ([0] ++ path,Top:ParentSort) srt)])
           else printOp(context,pp,top,srt,a)
    | Var((id,srt),_) -> 
           if printSort?(context)
              then blockFill(0,
        	   [(0,pp.fromString id),(0,string " : "),
        		(0,ppSort context ([0] ++ path,Top:ParentSort) srt)])
           else pp.fromString id
    | Let(decls,body,_) -> 
      let def ppD(index,separatorLength,separator,pat,trm) = 
           case (pat,trm) of
            | (VarPat _,Lambda([(pat2,Fun(Bool true,_,_),body)],_)) ->
        	  (0,blockLinear(0,
        	     [(0,prettysNone
        		 [separator,
        		  ppPattern context ([0,index]++ path,false) pat,
        		  string " ",
        		  ppPattern context ([0,1,index]++ path,false) pat2,
        		  string " ",
        		  pp.Equals,
        		  string " "]),
        	       (separatorLength,
        		 prettysNone [ppTerm context ([2,1,index]++ path,Top:ParentTerm) body,string " "])])) 
            | _ -> 
        	  (0,blockLinear(0,
        	     [(0,prettysNone 
        		  [separator,
        	           ppPattern context ([0,index]++ path,true) pat,
        		   string " ",
        	      	   pp.Equals,
        		   string " "]),
        	      (separatorLength,
        		  prettysNone
        		     [ppTerm context ([1,index]++ path,Top:ParentTerm) trm,string " "])]))
      in
      let def ppDs(index,l,separator,decls) = 
           case decls of
            | [] -> []
            | (pat,trm)::decls -> cons(ppD(index,l,separator,pat,trm),ppDs(index + 1,5,pp.And,decls))
      in

      blockAll (0,
        	[(0, blockFill (0,
        			[(0,blockLinear(0,ppDs(0,4,pp.Let,decls))),
        			 (0,pp.In)])),
        	 (0,ppTerm context ([length decls]++ path,parentTerm) body)])
    | LetRec(decls,body,_) -> 
      let
        	def ppD(path,((id,_),trm)) =
        	    case trm
        	      of Lambda([(pat,Fun(Bool true,_,_),body)],_) -> 
        		 blockLinear(0,
        		   [(0,prettysNone
        			[pp.Def,
        			 pp.fromString id,
        			 string " ",
        			 ppPattern context ([1,0] ++ path,false) pat,
        			 pp.Equals]),
        		     (4,ppTerm context ([2,0] ++ path,Top:ParentTerm) body)])
        	       | _ -> 
        		 blockLinear(0,
        		   [(0,prettysNone
        			 [pp.Def,
        		 	  pp.fromString id,
        			  pp.Equals]),
        	            (4,ppTerm context (path,Top:ParentTerm) trm)])
            in
        	blockAll(0,
        	   [(0,blockNone(0,
        	       [(0,pp.Let),
        	    	(0,ATermPrinter.ppListPath path ppD (pp.Empty,pp.Def,pp.In) decls)])),
        	    (0,ppTerm context ([length decls]++ path,parentTerm) body)])
    | Record(row,_) ->
              if isShortTuple(1,row)
        	 then 
        	 ATermPrinter.ppListPath path (fn (path,(_,t)) -> ppTerm context (path,Top:ParentTerm) t) (pp.LP,pp.Comma,pp.RP) row
              else
              let
        	  def ppEntry  (path,(id,t)) = 
        	      blockLinear(0,
        		[(0,pp.fromString  id),
        		 (0,string  " = "),
        	         (0,ppTerm context (path,Top:ParentTerm) t)])
              in
        	 ATermPrinter.ppListPath path ppEntry (pp.LCurly,string ", ",pp.RCurly) row
    | IfThenElse(t1,t2,t3,_) -> 
              blockLinear(0,
        	[(0,prettys [pp.If,ppTerm context ([0]++ path,Top:ParentTerm) t1]),
        	 (3,blockLinear(0,
        		[(0,pp.Then),
        		 (0,ppTerm context ([1]++ path,Top:ParentTerm) t2),
        		 (0,string " ")])),
        	 (0,blockFill(0,
                  [(0,pp.Else),
                   (0,ppTerm context ([2]++ path,Top:ParentTerm) t3)]))])
            | Lambda(match,_) -> 
              prettysNone 
        	[pp.LP,
        	 printLambda(context,path,pp.Lambda,match),
        	 pp.RP]
    | Bind(binder,bound,body,_) ->
               let b = case binder 
        	        of Forall -> pp.Fa
        	         | Exists -> pp.Ex
              in
              let 
        	def ppBound(index,(id,srt)) =
        	    (prettys 
        	      [
        	       pp.fromString id,
        	       string " : ",
        	       ppSort context ([index]++ path,Top:ParentSort) srt
        	      ])
              in
                blockFill(0,[
        	  (0,prettysNone 
        	    [b,pp.LP,
        	     prettysFill (addSeparator (string ", ") 
        		(ListUtilities.mapWithIndex ppBound bound)),
        	     pp.RP,
        	     string " "]),
        	  (1,ppTerm context ([length bound]++ path,parentTerm) body)])
         
    | Seq(ts,_) -> ATermPrinter.ppListPath path
              (fn(path,trm) -> ppTerm context (path,Top:ParentTerm) trm) 
        	(pp.LP,string ";",pp.RP)  ts
    | Apply(trm1,trm2 as Record([(_,t1),(_,t2)],_),_) ->
              let
        	 def prInfix(f1,f2,l,t1,oper,t2,r) =
        	     prettysFill
        	       [l,
        		ppTerm context ([0,1]++ path,f1) t1,
        	 	string " ",
        	 	ppTerm context ([0]++ path,Top:ParentTerm) oper,
        	 	string " ",
        	 	ppTerm context ([1,1]++ path,f2) t2,
        		r]
              in
  %
  % Infix printing is to be completed.
  %
              (case (parentTerm,termFixity(trm1))
                 of (_,Nonfix) -> prApply(trm1,trm2)
        	  | (Nonfix,Infix(a,p)) ->
        	    prInfix(Nonfix,Nonfix,pp.LP,t1,trm1,t2,pp.RP)
        	  | (Top,Infix(a,p))  ->
        	    prInfix(Nonfix,Nonfix,pp.Empty,t1,trm1,t2,pp.Empty) 
        	  | (Infix(a1,p1),Infix(a2,p2)) ->
        	    prInfix(Nonfix,Nonfix,pp.LP,t1,trm1,t2,pp.RP))
    | Apply(t1,t2,_) -> prApply(t1,t2)
    | ApplyN([t],_) -> ppTerm context (path,parentTerm) t
    | ApplyN([trm1,trm2 as Record([(_,t1),(_,t2)],_)],_) ->
              let
        	 def prInfix(f1,f2,l,t1,oper,t2,r) =
        	     prettysFill
        	       [l,
        		ppTerm context ([0,1]++ path,f1) t1,
        	 	string " ",
        	 	ppTerm context ([0]++ path,Top:ParentTerm) oper,
        	 	string " ",
        	 	ppTerm context ([1,1]++ path,f2) t2,
        		r]
              in
  %
  % Infix printing is to be completed.
  %
              (case (parentTerm,termFixity(trm1):Fixity)
        	 of (_,Nonfix) -> prApply(trm1,trm2)
        	  | (Nonfix,Infix(a,p)) ->
        	    prInfix(Nonfix,Nonfix,pp.LP,t1,trm1,t2,pp.RP)
        	  | (Top,Infix(a,p))  ->
        	    prInfix(Nonfix,Nonfix,pp.Empty,t1,trm1,t2,pp.Empty) 
        	  | (Infix(a1,p1),Infix(a2,p2)) ->
        	    prInfix(Nonfix,Nonfix,pp.LP,t1,trm1,t2,pp.RP))
    | ApplyN([t1,t2],_) -> prApply(t1,t2)
    | ApplyN(t1::t2::ts,a) -> prApply(ApplyN([t1,t2],a),ApplyN(ts,a))
    | SortedTerm(t,s,_) -> prettysNone
        	                     [ppTerm context ([0]++ path,Top:ParentTerm) t,
        			      string ":", string " ",
        	                      ppSort context ([1]++ path,Top:ParentSort) s]
    | _ -> System.fail "Uncovered case for term"
      
   
 def ppSortScheme context parent (tyVars,srt) = 
     let pp2 = ppSort context parent srt in
     let pp1 = ppForallTyVars context.pp tyVars in
     prettysNone [pp1,pp2]     


  def ppSort context (path,parent) srt = 
   let pp : ATermPrinter = context.pp in
   case srt of
     | CoProduct(row,_) -> 
          let
        	def ppEntry (path,(id,srtOption)) = 
        	    case srtOption
        	      of Some s -> 
        		 prettysNone
        		  [pp.Bar,
        	           pp.fromString  id,
        	           string  " ",
        	           ppSort context (path,CoProduct:ParentSort) s]
        		| None -> 
        		  prettysNone
        		   [pp.Bar, pp.fromString  id]
          in
          let (left,right) = 
               case parent
        	 of Product -> (pp.LP,pp.RP)
        	  | CoProduct -> (pp.LP,pp.RP)
        	  | _ -> (pp.Empty,pp.Empty)
        	    
           in
              ATermPrinter.ppListPath path ppEntry (pp.Empty,pp.Empty,pp.Empty) row
    | Product([],_) -> string  "()"
    | Product(row,_) -> 
           if isShortTuple(1,row)
                then 
        	let (left,right) = 
                    case parent
        	      of Product -> (pp.LP,pp.RP)
        	       | _ -> (pp.Empty,pp.Empty)
                in
        	     ATermPrinter.ppListPath path (fn(path,(lbl,t)) -> 
        		      ppSort context (path,Product:ParentSort) t) (left,pp.Product,right)  row
              else
              let		  
        	  def ppEntry  (path,(id,s)) = 
        	      blockFill(0,
        		[(0,pp.fromString  id),
        	         (0,string  ":"),
        	         (0,ppSort context (path,Top:ParentSort) s)])
              in
        	  ATermPrinter.ppListPath path ppEntry (pp.LCurly,string ", ",pp.RCurly)  row
              
    | Arrow(dom,rng,_) -> 
           let (left,right) = 
               case parent
        	 of Product -> (pp.LP,pp.RP)
        	  | ArrowLeft -> (pp.LP,pp.RP)
        	  | _ -> (pp.Empty,pp.Empty)
           in
           blockFill(0,
             [(0,prettysNone
        	[left,
        	 ppSort context ([0]++ path,ArrowLeft:ParentSort) dom,
        	 pp.Arrow]),
              (3,prettysNone
        	[ppSort context ([1]++ path,ArrowRight:ParentSort) rng,
        	 right])])
    | Subsort(s,Lambda([(pat,Fun(Bool true,_,_),t)],_),_) -> 
              blockFill(0,
        	[(0,pp.LCurly),
        	 (0,ppPattern context ([0,0,1]++ path,true) pat),
        	 (0,string " : "),
                 (0,ppSort context  ([0]++ path,Top:ParentSort) s),
                 (0,pp.Bar),
                 (0,ppTerm context ([2,0,1]++ path,Top:ParentTerm) t),
                 (0,pp.RCurly)])
    | Subsort(s,t,_) -> 
              blockFill(0,
        	[(0,pp.LP),
                 (0,ppSort context  ([0]++ path,Top:ParentSort) s),
                 (0,pp.Bar),
                 (0,ppTerm context ([1]++ path,Top:ParentTerm) t),
                 (0,pp.RP)])
    | Quotient(s,t,_) -> 
              blockFill(0,
        	[(0,pp.LP),
                 (0,ppSort context  ([0]++ path,Top:ParentSort) s),
                 (0,string  " / "),
                 (0,ppTerm context ([1]++ path,Top:ParentTerm) t),
                 (0,pp.RP)])

  % | Base (Qualified ("Boolean", "Boolean")) -> string "Boolean"
  % | Base (Qualified ("String",  "String"))  -> string "String"
  % | Base (Qualified ("Nat",     "Nat"))     -> string "Nat"

    | Base(idInfo,[],_) -> pp.ppSortId(idInfo)
    | Base(idInfo,ts,_) -> 
            blockFill(0,
        	[(0,pp.ppSortId(idInfo)),
        	 (0,ATermPrinter.ppListPath path
        	      (fn(path,srt) -> ppSort context (path,Top:ParentSort) srt)
        	      (pp.LP,pp.Comma,pp.RP) ts)])
    | PBase(idInfo,[],_) -> pp.ppPSortId(idInfo)
    | PBase(idInfo,ts,_) -> 
            blockFill(0,
        	[(0,pp.ppPSortId(idInfo)),
        	 (0,ATermPrinter.ppListPath path
        	      (fn(path,srt) -> ppSort context (path,Top:ParentSort) srt)
        	      (pp.LP,pp.Comma,pp.RP) ts)])
    | TyVar(id,_) -> string id
    | MetaTyVar(mtv,_) -> string (TyVarString mtv)
    | _ -> string "ignoring bad case for sort"
      

  def fa(a) TyVarString(mtv: AMetaTyVar a) : String =
   let {link,uniqueId,name} = State.! mtv in
   case link of
    | None -> "mtv%"^Nat.toString uniqueId
    | Some srt -> printSort srt

  %% More elaborate version
  %     let linkr =
  %       case link
  %         of None  -> ""
  %          | Some srt -> "["^printSort srt^"]"
  %     in "mtv%"^Nat.toString uniqueId^linkr

  def enclose(enclosed,pretty) = 
   if enclosed then
     pretty 
   else
     prettysFill [string "(",pretty,string ")"]
        
  def ppPattern context (path,enclosed) pattern = 
   let pp : ATermPrinter = context.pp in
   case pattern of
    | WildPat   (_(* srt *), _) -> pp.Underscore
    | BoolPat   (b, _) -> string  (Boolean.toString b)
    | NatPat    (n, _) -> string  (Nat.toString     n)                
    | StringPat (s, _) -> pp.fromString  ("\""^s^"\"")               % "abc"
    | CharPat   (c, _) -> pp.fromString  ("#" ^ (Char.toString c))   % #A
    | VarPat    ((id, srt), _) -> 
     if printSort?(context) then
       blockFill (0,
        	  [(0, pp.fromString id),
        	   (0, string " : "),
        	   (0, ppSort context ([0] ++ path, Top : ParentSort) srt)])
     else 
       pp.fromString id
    | EmbedPat  ("Nil", None, Base (Qualified   ("List",      "List"), [_], _), _) -> string "[]"
    | EmbedPat  ("Nil", None, Base (Qualified   (UnQualified, "List"), [_], _), _) -> string "[]" % ???
    | EmbedPat  (id, None, _(* srt *),_) -> pp.fromString id
    | RecordPat (row, _) ->
     if isShortTuple (1, row) then
       ATermPrinter.ppListPath path (fn (path,(id, pat)) -> 
        			     ppPattern context (path,true) pat) 
                                    (pp.LP, pp.Comma, pp.RP) 
                               row
     else
       let def ppEntry (path, (id, pat)) = 
             blockFill (0,
        		[(0,prettysNone [pp.fromString id, pp.Equals]),
        		 (2 + String.length id,
        		  prettysFill [ppPattern context (path, true) pat])])
       in
         ATermPrinter.ppListPath path ppEntry (pp.LCurly, pp.Comma, pp.RCurly) row
    | EmbedPat ("Cons", 
               Some (RecordPat ([("1",p1), ("2",p2)], _)),
               Base (_(* Qualified("List","List") *), [_], _), _) -> 
     enclose(enclosed,
             prettysFill [ppPattern context ([0]++ path,false) p1,
        		  string " :: ",
        		  ppPattern context ([1]++ path,false) p2])
    | EmbedPat ("Cons",
               Some  (RecordPat ([("1",p1),("2",p2)], _)),
               PBase (_(* Qualified("List","List") *),[_],_), _) -> 
     enclose(enclosed,
             prettysFill [ppPattern context ([0]++ path,false) p1,
        		  string " :: ",
        		  ppPattern context ([1]++ path,false) p2])
    | EmbedPat (id, Some pat,_(* srt *),_) -> 
     enclose(enclosed,
             prettysFill (cons (pp.fromString id,
        			if singletonPattern pat then
        			  [string " ",
        			   ppPattern context ([0]++ path,false) pat]
        			else
        			  [pp.LP,
        			   ppPattern context ([0]++ path,true) pat,
        			   pp.RP])))
    | SortedPat (pat, srt, _) -> 
     enclose(enclosed,
             blockFill(0,
        	       [(0, ppPattern context ([0]++ path, false) pat),
        		(0, string  " : "),
        		(0, ppSort context ([1]++ path, Top : ParentSort) srt)]))
    | AliasPat (pat1, pat2, _) -> 
     enclose(enclosed,
             blockFill(0,
        	       [(0, ppPattern context ([0]++ path, false) pat1),
        		(0, string  " as "),
        		(0, ppPattern context ([1]++ path, false) pat2)]))
    | RelaxPat (pat, trm, _) -> 
     let _(* srt *) = patternSort(pat) in
     enclose(enclosed,
             blockFill(0,
        	       [(0, string "relax ("),
        		(0, ppTerm context ([1]++ path,Top:ParentTerm) trm),
        		(0, pp.RP),
        		(0, ppPattern context ([0]++ path,false) pat)
        	       ]))
    | QuotientPat (pat, term, _) -> 
     enclose(enclosed,
             blockFill(0,
        	       [(0, string "quotient("),
        		(0, ppTerm context ([1]++ path,Top:ParentTerm) term),
        		(0, string " ?)" ),
        		(0, ppPattern context ([0]++ path,false) pat)]))

    | _ -> System.fail "Uncovered case for pattern"
      

  def printTerm term = 
   toString(format(60,ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term))

  def termToPretty term =
   ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term

  def printTermToTerminal term =
   toTerminal(format(60,ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term))
 
  def printSort srt = 
   toString (format (60, ppSort (initialize (asciiPrinter, false))
        	     ([], Top : ParentSort) srt))

  def printSortToTerminal srt = 
   toTerminal (format (60, ppSort (initialize (asciiPrinter, false))
        		([],Top : ParentSort) srt))
 
  def printSortScheme scheme = 
   toString (format (60, ppSortScheme (initialize(asciiPrinter,false))
        	     ([],Top:ParentSort) scheme))

  def printPattern pat = 
   toString(format(60,ppPattern (initialize(asciiPrinter,false))
        				     ([],true) pat))

  def printTermWithSorts term = 
   toString(format(60,ppTerm (initialize(asciiPrinter,true))
        				     ([],Top:ParentTerm) term))

  def ppForallTyVars (pp:ATermPrinter) tyVars = 
   (case tyVars
        of [] -> string ""
         | _ -> ATermPrinter.ppList string
                  (prettysNone [string " ",pp.Fa,pp.LP],pp.Comma,pp.RP) tyVars)
  def ppTyVars (pp:ATermPrinter) tyVars = 
   (case tyVars
        of [] -> string ""
         | _ -> ATermPrinter.ppList string (pp.LP,pp.Comma,pp.RP) tyVars)

  def sortIndex     = 0
  def opIndex       = 1
  def defIndex      = 2
  def propertyIndex = 3

  def ppProperty context (index,(pt,name,tyVars,term)) = 
    let pp : ATermPrinter = context.pp in
    let button1 = if markSubterm?(context) 
        	   then PrettyPrint.buttonPretty
        	          (~(IntegerSet.member(context.indicesToDisable,index)),
        		   index,string " ",false) 
        	   else string "" in
    let button2 = if markSubterm?(context) 
        	   then PrettyPrint.buttonPretty
        	          (IntegerSet.member(context.sosIndicesToEnable,index),
        		   index,string " ",true) 
        	   else string "" in

    (1,blockFill(0,
        [(0,button1),
         (0,button2),
         (0,case (pt:PropertyType) 
              of Theorem -> pp.Theorem | Axiom -> pp.Axiom | Conjecture -> pp.Conjecture),
         (0,pp.ppFormulaDesc (" "^name)),
         (0,string " "),
         (0,pp.Is),
         (0,if null tyVars then string "" else string " sort"),
         (0,ppForallTyVars pp tyVars),
         (0,string " "),
         (3,ppTerm context ([index,propertyIndex],Top:ParentTerm) term)]))

  %op ppOp: fa(a) context -> String * AOpInfo a * Line -> Nat * Lines
  def fa(a) ppOpDecl (context : context)
                     (qualifier, id, 
        	      (op_names, fixity, (tyVars, srt), optDefn) : AOpInfo a, 
        	      (index, lines)) = 
     let pp : ATermPrinter = context.pp in
     % let def ppOpNm() = pp.ppOpId(Qualified(qualifier,id)) in
     % let def ppOpNm() = (if spName = qualifier then pp.ppOp id
     %         	 else pp.ppOpId(Qualified(qualifier,id))) in
     let def ppOpNm() =
      (if qualifier = "" then
         pp.ppOp id
       else
         pp.ppOpId (Qualified(qualifier,id))) in
     let index1 = Integer.~(index + 1) in
     let button1 = if markSubterm?(context) & some? optDefn
        	    then PrettyPrint.buttonPretty
        	           (~(IntegerSet.member(context.indicesToDisable,index1)),
        		    index1,string " ",false)
        	  else string "" in
     let button2 = if markSubterm?(context) & some? optDefn
        	    then PrettyPrint.buttonPretty
        	           (IntegerSet.member(context.sosIndicesToEnable,index1),
        		    index1,string " ",true)
        	  else string "" in
     (index + 1,
      cons((1,blockFill
                (0, [(0, pp.Op),
        	     (0, string " "),
        	     (0, ppOpNm()),
        	     (0, case fixity 
        		   of Nonfix -> string ""
        		    | Infix(Left,i)  -> string (" infixl "^Nat.toString i)
        		    | Infix(Right,i) -> string (" infixr "^Nat.toString i)),
        	     (0, string " :"),
        	     (0, ppForallTyVars pp tyVars),
        	     (0, string " "),
        	     (3, ppSort context ([index,opIndex],Top:ParentSort) srt)])),
           (case optDefn
              of None -> lines
               | Some term ->
                 let def ppDefn(path,term) = 
        	     case term
        	       of Lambda([(pat,Fun(Bool true,_,_),body)],_) ->
        		  let pat = ppPattern context ([0,0] ++ path,false) pat in 
        		  let body = ppDefn([2,0] ++ path,body) in
        		  let prettys = [(0,pat),(0,string " ")] ++ body in
        		  if markSubterm?(context) then
        		    let num = State.! context.markNumber in
        		    let table = State.! context.markTable in
        		    (context.markTable State.:= NatMap.insert(table,num,path);
        		     context.markNumber State.:= num + 1;
        		     PrettyPrint.markLines(num,prettys))
        		  else prettys
        		| _ -> 
        		    let pretty = ppTerm context (path,Top:ParentTerm) term in
        		    let prettys = [(0,pp.DefEquals),(0,string " "),(4,pretty)] in
        		    prettys
        	 in
        	 let prettys = ppDefn([index,defIndex],term) in
                 cons((1, blockFill (0,
        			     [(0, blockFill (0,
        					     [(0, button1),
        					      (0, button2),
        					      (0, pp.Def),
        					      (if printSort?(context) 
        						 then (0,ppForallTyVars pp tyVars) 
        					       else (0,string "")),
        					      (0, ppOpNm()),
        					      (0, string " ")]
        					    ))]
        			     ++ prettys)),
        	      lines))))

  def fa(a) ppSortDecl (context : context)
                       (qualifier, id, (sort_names, tyVars, optSort) : ASortInfo a, 
                       (index, lines)) = 
   let pp : ATermPrinter = context.pp in
   let pretty_name_or_names = 
      (if qualifier = "" then
         pp.ppSort id
       else
         pp.ppSortId (Qualified (qualifier, id))) in
   (index + 1,
    cons(case optSort
           of None -> 
              (1,blockFill(0,[(0, pp.Sort),
        		      (0, string " "),
        		      (0, pretty_name_or_names),
        		      (0, ppTyVars pp tyVars)]))
            | Some srt -> 
              (1,blockFill(0,[(0, pp.Sort),
        		      (0, string " "),
        		      (0, pretty_name_or_names),
        		      (0, ppTyVars pp tyVars),
        		      (0, string " "),
        		      (0, pp.DefEquals),
        		      (0, string " "),
        		      (3, ppSort context ([index,sortIndex],Top:ParentSort) srt)])),
         lines))

  op isBuiltIn? : Import -> Boolean
  def isBuiltIn? (spec_ref, _ (* spc *)) =
   %% Regard "List" and "General" as built-in.
   spec_ref = "String"  or spec_ref = "Nat"  or 
   spec_ref = "Boolean" or spec_ref = "Char" or
   spec_ref = "Integer" or spec_ref = "List" or 
   spec_ref = "General"

  %% Top-level print module; lower-level print spec
  def ppSpec context  {imports, importedSpec=_, sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      blockAll(0,
               [(0,blockFill(0,
                             [(0, pp.Module),
                              (0, string " "),
        		      (0, pp.Equals)]))]
               ++
               (map (fn (spec_ref, spc) -> (1,prettysFill [pp.Import, string spec_ref])) imports) 
               ++
               (ppSortDecls context sorts)
               ++
               (ppOpDecls   context ops)
               ++
               (ListUtilities.mapWithIndex (ppProperty context) properties)
               ++
               [(0, pp.EndModule),
        	(0, string "")])

  def ppSpecR context  {imports, importedSpec=_, sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      blockAll(0,
               [(0, blockFill(0,
        		      [(0, pp.Spec),
        		       (0, string " "),
        		       (0, pp.Equals)]))]
               ++
               (map (fn (spec_ref, spc) -> (1,prettysFill [pp.Import, string spec_ref])) imports) 
               ++
               (ppSortDecls context sorts)
               ++
               (ppOpDecls context ops)
               ++
               (ListUtilities.mapWithIndex (ppProperty context) properties)
               ++
               [(0, pp.EndSpec),
        	(0, string "")])

  def ppSpecAll context  {imports, importedSpec=_,sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      let ppImports = map (fn (spec_ref, spc) ->
        		   (2, blockFill (0,
        				  [(0,string "import "),
        				   (0,string spec_ref),
        				   (0,string " |-> "),
        				   (0,ppSpecAll context spc)])))
                          imports in
      blockAll(0,
               [(0, blockFill(0,
        		      [(0, pp.Spec),
        		       (0, string " ")
        		      ]))]
               ++
               ppImports 
               ++
               (ppSortDecls context sorts)
               ++
               (ppOpDecls context ops)
               ++
               (ListUtilities.mapWithIndex (ppProperty context) properties)
               ++
               [(0, pp.EndSpec),
        	(0, string "")])
  def ppSortDecls context sorts =  
      let (index,pps) = foldriDouble (ppSortDecl context) (0,[]) sorts in
      pps

  def ppOpDecls context ops =  
      let (index,pps) = foldriDouble (ppOpDecl context) (0,[]) ops in
      pps

  def specToPrettyVerbose spc = 
      ppSpecAll(initialize(asciiPrinter,false)) spc
      
  def specToPretty spc = 
      ppSpecR(initialize(asciiPrinter,false)) spc
      
  def specToPrettyR spc = 
      ppSpecR(initialize(asciiPrinter,false)) spc
      
  def printSpec spc =
      toString(format(60,specToPretty spc))

  def printSpecVerbose spc =
      toString(format(60,specToPrettyVerbose spc))

  def printSpecToTerminal spc =
      (toTerminal(format(60,specToPretty spc));
       String.writeLine "")

  def printSpecToFile(fileName,spc) = 
      toFile(fileName,format(90,specToPretty spc))

  def printMarkedSpecToFile
        (fileName,pathFileName,indicesToDisable,sosIndicesToEnable,spc) = 
      let context = initializeMark(asciiPrinter,indicesToDisable,sosIndicesToEnable) in
      let specToPretty = ppSpec(context) in
      (PrettyPrint.toPathFiles
         (fileName,pathFileName,format(90,specToPretty spc));
       State.! context.markTable)

  def printMarkedSpecToString(indicesToDisable,sosIndicesToEnable,spc) = 
      let context = initializeMark(asciiPrinter,indicesToDisable,sosIndicesToEnable) in
      let specToPretty = ppSpec(context) in
      let spcAndMarking = PrettyPrint.toStringWithPathIndexing
                            (format(90,specToPretty spc)) in
      (spcAndMarking,State.! context.markTable)


  def printSpecWithSortsToTerminal spc =
      toTerminal(format(60,ppSpec(initialize(asciiPrinter,true)) spc))

  def latexSpecToPretty spc = 
      let pSpec = ppSpec(initialize(latexPrinter,false)) spc in
      makeSpecListing pSpec

  def makeSpecListing pSpec = 
       blockAll(0,
        [(0,string "\\specListing{"),
         (0,pSpec),
         (0,string "}")]) 

  def latexSpec spc = 
      PrettyPrint.toLatexString(format(90,latexSpecToPretty spc))

  def latexSpecToFile(fileName,spc) = 
      PrettyPrint.toLatexFile(fileName,format(90,latexSpecToPretty spc))

  def htmlSpecToPretty spc = 
      let pSpec = ppSpec(initialize(htmlPrinter(),false)) spc in
      prettysAll
        [string "<html><body BGCOLOR = \"#EEFFFA\"><pre>",
         pSpec,
         string "</pre></body></html>"]      


  def htmlSpecToFile(fileName,spc) = 
      PrettyPrint.toFile(fileName,format(90,htmlSpecToPretty spc))

  def boolToNat(b) = if b then 1 else 0
  def positive?(n) = if n > 0 then 1 else 0

  def pdfMenu(spc) = 
     let sorts = 
        foldriDouble 
          (fn (qualifier,id,_,sorts) -> 
              cons(
        	prettysNone
        	 [string ("  \\pdfoutline goto name {"^"???"^":Sort:"
        		  ^(if qualifier = UnQualified then "" else qualifier^".")^id^"} {"),
        	  string (if qualifier = UnQualified then "" else qualifier^"."),
        	  string id,
        	 string "}"],
        	sorts))
          [] 
          spc.sorts	
     in
     let ops = 
        foldriDouble 
          (fn (qualifier,id,_,ops) -> 
              cons(
        	prettysNone
        	 [string ("  \\pdfoutline goto name {"^"???"^":Op:"
        		  ^(if qualifier = UnQualified then "" else qualifier^".")^id^"} {"),
        	  string (if qualifier = UnQualified then "" else qualifier^"."),
        	  string id,
        	 string "}"],
        	ops))
          [] 
          spc.ops
     in
     let (counter,properties) = 
         foldl 
         (fn ((pt,desc,tvs,_),(counter,list)) -> 
             (counter + 1,
              cons(
        	string ("  \\pdfoutline goto num "^Nat.toString counter^
        		"  {"^desc^"}"),
        	list))) (1,[]) spc.properties
     in
     let properties = rev properties in
     let sortCount  = length sorts        	in
     let opCount    = length ops        	in
     let pCount     = length properties         in

     let menuCount = positive? sortCount + 
        	     positive? opCount +
        	     positive? pCount	
     in
     prettysAll(
     [
        string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
        	Nat.toString menuCount^"  {"^"???"^"}")
     ]
     ++
     (if sortCount > 0
        then 
        [string ("\\pdfoutline goto name {Spec:"^"???"^
        	"} count -"^Nat.toString sortCount^
        	" {Sorts}"
        	)]
        else [])
     ++
     sorts
     ++
     (if opCount > 0
         then 
             [
        	string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
        	Nat.toString opCount^
        	" {Ops}"
        	)
                  ]
      else [])
     ++
     ops
     ++
     (if pCount > 0
         then 
         [string ("\\pdfoutline goto name {Spec:"^"???"^"} count-"^
        	  Nat.toString pCount^" {Properties}")]
      else [])
     ++
     properties)          

  def fa(a) pdfSpecsToPretty specs0 = 
     let counter = ref 0 : Ref(Nat) in
     let specs = 
         map 
           (fn (sp:ASpec a) -> 
        	ppSpec (initialize(pdfPrinter(counter,"???"),false)) sp) specs0 
     in
     let menues = map pdfMenu specs0         	 in
     prettysAll
        ([string "\\documentclass{article}",
         string ("\\input{" ^ (System.getenv "SPECWARE2000") ^ "/doc/pdf-sources/megamacros}"),
         % string "\\input{/specware/doc/macros/macros}",
         string "\\begin{document}",
         string "\\pdfthread num 1"]
         ++
         (map (fn s -> string(PrettyPrint.toLatexString(
        	format(90,makeSpecListing s)))) specs)
         ++
         [string "\\pdfendthread"]
         ++
         menues
         ++
         [string "\\pdfcatalog{ /PageMode /UseOutlines }",
          string "\\end{document}"])	
        		
  def fa (a) pdfSpecsToFile (fileName, spcs : List(ASpec a)) = 
      PrettyPrint.toFile(fileName,format(90,pdfSpecsToPretty spcs))

 % Separate output in three portions:
 % 1. pretty print the prelude erasing older versions
 % 2. pretty print append each spec with LaTeX line breaks.
 % 3. pretty print append the postlude.

  def pdfPreludeToFile(fileName) =
      PrettyPrint.toFile(fileName,format(90,
        prettysAll
        ([string "\\documentclass{article}",
         string ("\\input{" ^ (System.getenv "SPECWARE2000") ^ "/doc/pdf-sources/megamacros}"),
         string "\\begin{document}",
         string "\\pdfthread num 1"])))

  def fa(a) pdfOneSpecToFile(counter,fileName,spc:ASpec a) = 
      let spc1 = ppSpec (initialize(pdfPrinter(counter,"???"),false)) spc         in
      let menu = pdfMenu spc         						in
      (PrettyPrint.appendFile(fileName,
        	format(90,string "\\newpage"));
       PrettyPrint.appendLatexFile(fileName,PrettyPrint.format(90,makeSpecListing spc1));
       menu)

  def pdfPostLudeToFile(fileName,menues) = 
      PrettyPrint.appendFile(fileName,
       PrettyPrint.format(90,
        prettysAll
        ([string "\\pdfendthread"]
          ++ menues
          ++ [string "\\pdfcatalog{ /PageMode /UseOutlines }",
              string "\\end{document}"])))
}
