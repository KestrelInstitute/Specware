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

AnnSpecPrinter qualifying spec { 
  import ../AbstractSyntax/Printer
  import AnnSpec
  % import /Library/IO/Primitive/IO                    % for getEnv
  import /Library/Legacy/DataStructures/IntSetSplay  % for indicesToDisable
  import /Library/Legacy/DataStructures/NatMapSplay  % for markTable's

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
  op printTermScheme              : fa(a) ATermScheme a -> String 
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
  % op printSort                    : fa(a) ASort a -> String
  op printSortToTerminal          : fa(a) ASort a -> ()
  % op printSortScheme              : fa(a) ASortScheme a -> String
  % op printPattern                 : fa(a) APattern a -> String
  % op printTermWithSorts           : fa(a) ATerm a -> String
  op ppProperty                   : fa(a) context -> Nat * AProperty a -> Line
  op ppSpec                       : fa(a) context -> ASpec a -> Pretty  
  op ppSpecR                      : fa(a) context -> ASpec a -> Pretty
  op ppSpecHidingImportedStuff    : fa(a) context -> Spec -> ASpec a -> Pretty
  op ppSpecAll                    : fa(a) context -> ASpec a -> Pretty
  op ppSortDecls                  : fa(a) context -> ASortMap a -> Lines
  op ppOpDecls                    : fa(a) context -> AOpMap a -> Lines
  op specToPrettyVerbose          : fa(a) ASpec a -> Pretty
  op specToPretty                 : fa(a) ASpec a -> Pretty
  op specToPrettyR                : fa(a) ASpec a -> Pretty
  % op printSpec                    : fa(a) ASpec a -> String
  op printSpecVerbose             : fa(a) ASpec a -> String
  % op printSpecToTerminal          : fa(a) ASpec a -> ()
  % op printSpecToFile              : fa(a) String * ASpec a -> ()
  op printMarkedSpecToFile        : fa(a) String * String * IntegerSet.Set * IntegerSet.Set * ASpec a -> NatMap.Map(List(Nat))
  op printMarkedSpecToString      : fa(a) IntegerSet.Set * IntegerSet.Set * ASpec a -> String * NatMap.Map(List(Nat))
  % op printSpecWithSortsToTerminal : fa(a) ASpec(a) -> ()
  op latexSpecToPretty            : fa(a) ASpec(a) -> Pretty
  % op latexSpec                    : fa(a) ASpec(a) -> String
  % op latexSpecToFile              : fa(a) String * ASpec(a) -> ()
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
    | Fun (Embed ("Nil", false), _, _) -> Some []
    | Apply (Fun (Embed("Cons", true), _, _),  Record ([(_, t1), (_, t2)], _), _) -> 
      (case isFiniteList t2 of
        | Some terms -> Some (cons (t1, terms))
        | _ ->  None)
    | ApplyN ([Fun (Embed ("Cons", true), _, _), _,
	       Record ([(_, t1), (_, t2)], _),
	       _], _) -> 
      (case isFiniteList t2 of
        | Some terms -> Some (cons (t1, terms))
        | _  ->  None)
    | _ -> None

  def initialize (pp, printSort?) : context = 
   {pp                 = pp,
    printSort          = printSort?,
    markSubterm        = false,
    markNumber         = Ref 0,
    markTable          = Ref NatMap.empty,
    indicesToDisable   = IntegerSet.empty,
    sosIndicesToEnable = IntegerSet.empty}
 
  def initializeMark (pp, indicesToDisable, sosIndicesToEnable) : context = 
    {pp                 = pp,
     printSort          = false,
     markSubterm        = true, 
     markNumber         = (Ref 0),
     markTable          = Ref NatMap.empty,
     indicesToDisable   = indicesToDisable,
     sosIndicesToEnable = sosIndicesToEnable}
 
  def printSort?   (c:context) = c.printSort
  def markSubterm? (c:context) = c.markSubterm
 
  def fa(a) termFixity(term:ATerm a):Fixity = 
   case term of
    | Fun (termOp, srt, _) -> 
      (case termOp of
        | Op (_, fixity) -> (case fixity of
                               | Unspecified -> Nonfix
                               | _ -> fixity)
        | And            -> Infix (Right, 15) 
        | Or             -> Infix (Right, 14) 
        | Implies        -> Infix (Right, 13) 
        | Iff            -> Infix (Right, 12) 
        | Equals         -> Infix (Left, 20) % was 10 ??
        | NotEquals      -> Infix (Left, 20) 
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
    | Not                   -> pp.Not
    | And                   -> pp.And
    | Or                    -> pp.Or
    | Implies               -> pp.Implies
    | Iff                   -> pp.Iff
    | Equals                -> pp.Equals
    | NotEquals             -> pp.NotEquals
    | OneName   (x, _)      -> pp.fromString x
    | TwoNames  (x, y, _)   -> pp.fromString (if x = UnQualified then y else x^"."^ y)
 
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
    %% Only used internally at present
    | Select s              -> pp.fromString ("select("^s^")")


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
 
  def ppTermScheme context parent (type_vars, term) = 
     let pp1 = ppForallTyVars context.pp type_vars in
     let pp2 = ppTerm context parent term in
     prettysNone [pp1,pp2]     

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
         case (t1,t2) of
           | (Lambda (rules as (_ :: _),_),_) ->
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
                     then prettysNone [ pp.fromString id,
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
                 (2,blockNone(0,
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
    | Some terms -> AnnTermPrinter.ppListPath path
                      (fn (path,term) -> 
		       ppTerm context (path,Top:ParentTerm) term) 
                      (pp.LBrack,pp.Comma,pp.RBrack)  terms
    | None -> 
        (case term of
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
                              prettysNone [ppTerm context
					     ([2,1,index]++ path,Top:ParentTerm)
					     body,string " "])])) 
                 | _ -> 
                   (0,blockLinear
		       (0,
		        [(0,prettysNone 
			     [separator,
			      ppPattern context ([0,index]++ path,true) pat,
			      string " ",
				    pp.Equals,
			      string " "]),
			 (separatorLength,
			     prettysNone
				[ppTerm context ([1,index]++ path,Top:ParentTerm) trm,
				 string " "])]))
           in
           let def ppDs(index,l,separator,decls) = 
                (case decls of
                 | [] -> []
                 | (pat,trm)::decls -> cons(ppD(index,l,separator,pat,trm),
					    ppDs(index + 1,5,pp.LetDeclsAnd,decls)))
           in
     
                blockAll (0,
                     [(0, blockLinear (0,
                                       [(0,blockLinear(0,ppDs(0,4,pp.Let,decls))),
					(0,pp.In)])),
                      (0,ppTerm context ([length decls]++ path,parentTerm) body)])
         | LetRec(decls,body,_) -> 
            let
              def ppD(path,((id,_),trm)) =
                (case trm of
                  | Lambda([(pat,Fun(Bool true,_,_),body)],_) -> 
		    blockLinear(0,
                                [(0,prettysNone
                                     [pp.Def,
                                      pp.fromString id,
                                      string " ",
                                      ppPattern context ([1,0] ++ path,false) pat,
				      string " ",
                                      pp.Equals,
				      string " "]),
                                  (2,ppTerm context ([2,0] ++ path,Top:ParentTerm)
				       body)])
                  | _ -> 
		    blockLinear(0,
                                [(0,prettysNone
                                  [pp.Def,
                                   pp.fromString id,
                                   pp.Equals]),
                                 (4,ppTerm context (path,Top:ParentTerm) trm)]))
            in
              blockAll(0,
                         [(0,blockNone(0,
                                [(0,pp.Let),
                                 (0,AnnTermPrinter.ppListPath path ppD
				      (pp.Empty,pp.Empty,pp.Empty) decls)])),
			  (0,pp.In),
			  (0,ppTerm context ([length decls]++ path,parentTerm) body)])
         | Record(row,_) ->
                   if isShortTuple(1,row)
                      then 
                      AnnTermPrinter.ppListPath path (fn (path,(_,t)) ->
						      ppTerm context
						        (path,Top:ParentTerm) t)
		        (pp.LP,pp.Comma,pp.RP) row
                   else
                   let
                       def ppEntry  (path,(id,t)) = 
                           blockFill(0,
                             [(0,prettysNone[pp.fromString  id,
					     string  " = "]),
                              (2,ppTerm context (path,Top:ParentTerm) t)])
                   in
                      AnnTermPrinter.ppListPath path ppEntry (pp.LCurly,string ", ",pp.RCurly) row
         | IfThenElse(t1,t2,t3,_) -> 
                   blockLinear(0,
                     [(0,prettys [pp.If,ppTerm context ([0]++ path,Top:ParentTerm) t1]),
                      (0,blockFill(0,
                             [(0,pp.Then),
                              (3,ppTerm context ([1]++ path,Top:ParentTerm) t2),
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
              
         | Seq(ts,_) -> AnnTermPrinter.ppListPath path
              (fn(path,trm) -> ppTerm context (path,Top:ParentTerm) trm) 
                (pp.LP,string ";",pp.RP)  ts
         | Apply(trm1,trm2 as Record([(_,t1),(_,t2)],_),_) ->
              let
                 def prInfix(f1,f2,l,t1,oper,t2,r) =
                     prettysFill
                       [prettysNone[l,
				    ppTerm context ([0,1]++ path,f1) t1,
				    string " "],
                        prettysNone[ppTerm context ([0]++ path,Top:ParentTerm) oper,
				    string " ",
				    ppTerm context ([1,1]++ path,f2) t2,
				    r]]
              in
  %
  % Infix printing is to be completed.
  %
              (case (parentTerm,termFixity(trm1))
                 of (_,Nonfix) -> prApply(trm1,trm2)
                  | (Nonfix,Infix(a,p)) ->
                    prInfix(Infix(Left,p),Infix(Right,p),pp.LP,t1,trm1,t2,pp.RP)
                  | (Top,Infix(a,p))  ->
                    prInfix(Infix(Left,p),Infix(Right,p),pp.Empty,t1,trm1,t2,pp.Empty) 
                  | (Infix(a1,p1),Infix(a2,p2)) ->
		    if p1 = p2
		      then (if a1 = a2
			     then prInfix(Infix(Left,p2),Infix(Right,p2),pp.Empty,t1,trm1,t2,pp.Empty)
			     else prInfix(Infix(Left,p2),Infix(Right,p2),pp.LP,t1,trm1,t2,pp.RP))
		      else (if p2 > p1
			     then %% Inner has higher precedence
			          prInfix(Infix(Left,p2),Infix(Right,p2),pp.Empty,t1,trm1,t2,pp.Empty)
			     else prInfix(Infix(Left,p2),Infix(Right,p2),pp.LP,t1,trm1,t2,pp.RP)))
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
              (case (parentTerm,(termFixity trm1):Fixity)
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
         | _ -> System.fail "Uncovered case for term")
      
   
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
                case srtOption of
                  | Some s -> 
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
               case parent of
                 | Product -> (pp.LP,pp.RP)
                 | CoProduct -> (pp.LP,pp.RP)
                 | _ -> (pp.Empty,pp.Empty)
                    
           in
              AnnTermPrinter.ppListPath path ppEntry (pp.Empty,pp.Empty,pp.Empty) row
    | Product ([],_) -> string  "()"
    | Product (row,_) -> 
           if isShortTuple(1,row)
                then 
                let (left,right) = 
                  case parent of
                    | Product -> (pp.LP,pp.RP)
                    | _ -> (pp.Empty,pp.Empty)
                in
                  AnnTermPrinter.ppListPath path (fn(path,(lbl,t)) -> 
                              ppSort context (path,Product:ParentSort) t) (left,pp.Product,right)  row
              else
              let                  
                 def ppEntry  (path,(id,s)) = 
                      blockFill(0,
                        [(0,pp.fromString  id),
                         (0,string  ":"),
                         (0,ppSort context (path,Top:ParentSort) s)])
              in
                  AnnTermPrinter.ppListPath path ppEntry (pp.LCurly,string ", ",pp.RCurly)  row
              
    | Arrow (dom,rng,_) -> 
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
                 (0,AnnTermPrinter.ppListPath path
                      (fn(path,srt) -> ppSort context (path,Top:ParentSort) srt)
                      (pp.LP,pp.Comma,pp.RP) ts)])
%    | PBase(idInfo,[],_) -> pp.ppPSortId(idInfo)
%    | PBase(idInfo,ts,_) -> 
%            blockFill(0,
%                [(0,pp.ppPSortId(idInfo)),
%                 (0,AnnTermPrinter.ppListPath path
%                      (fn(path,srt) -> ppSort context (path,Top:ParentSort) srt)
%                      (pp.LP,pp.Comma,pp.RP) ts)])
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
	AnnTermPrinter.ppListPath path (fn (path,(id, pat)) -> 
				      ppPattern context (path,true) pat) 
				     (pp.LP, pp.Comma, pp.RP) 
				row
      else
	let def ppEntry (path, (id, pat)) = 
	      blockFill (0,
			 [(0,prettysNone [pp.fromString id,string " ",pp.Equals,string " "]),
			  (2,
			   prettysFill [ppPattern context (path, true) pat])])
	in
	  AnnTermPrinter.ppListPath path ppEntry (pp.LCurly, pp.Comma, pp.RCurly) row
    | EmbedPat ("Cons", 
               Some (RecordPat ([("1",p1), ("2",p2)], _)),
               Base (_(* Qualified("List","List") *), [_], _), _) -> 
     enclose(enclosed,
             prettysFill [ppPattern context ([0]++ path,false) p1,
                          string " :: ",
                          ppPattern context ([1]++ path,false) p2])
%    | EmbedPat ("Cons",
%               Some  (RecordPat ([("1",p1),("2",p2)], _)),
%               PBase (_(* Qualified("List","List") *),[_],_), _) -> 
%     enclose(enclosed,
%             prettysFill [ppPattern context ([0]++ path,false) p1,
%                          string " :: ",
%                          ppPattern context ([1]++ path,false) p2])
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
   PrettyPrint.toString (format(80,ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term))

  def termToPretty term =
   ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term

  def printTermToTerminal term =
   toTerminal(format(80,ppTerm (initialize(asciiPrinter,false)) ([],Top:ParentTerm) term))
 
  def printSort srt = 
    PrettyPrint.toString (format (80, ppSort (initialize (asciiPrinter, false))
                     ([], Top : ParentSort) srt))

  def printSortToTerminal srt = 
   toTerminal (format (80, ppSort (initialize (asciiPrinter, false))
                        ([],Top : ParentSort) srt))
 
  def printSortScheme scheme = 
    PrettyPrint.toString (format (80, ppSortScheme (initialize(asciiPrinter,false))
				  ([],Top:ParentSort) scheme))

  def printTermScheme scheme = 
    PrettyPrint.toString (format (80, ppTermScheme (initialize(asciiPrinter,false))
				  ([],Top:ParentTerm) scheme))

  def printPattern pat = 
    PrettyPrint.toString(format(80,ppPattern (initialize(asciiPrinter,false))
                                             ([],true) pat))

  def printTermWithSorts term = 
    PrettyPrint.toString(format(80,ppTerm (initialize(asciiPrinter,true))
                                             ([],Top:ParentTerm) term))

  def ppForallTyVars (pp:ATermPrinter) tyVars = 
   (case tyVars
        of [] -> string ""
         | _ -> AnnTermPrinter.ppList string
                  (prettysNone [string " ",pp.Fa,pp.LP],pp.Comma,pp.RP) tyVars)
  def ppTyVars (pp:ATermPrinter) tyVars = 
   (case tyVars
        of [] -> string ""
         | _ -> AnnTermPrinter.ppList string (pp.LP,pp.Comma,pp.RP) tyVars)

  def sortIndex     = 0
  def opIndex       = 1
  def defIndex      = 2
  def propertyIndex = 3

  def ppProperty context (index,(pt,name,tyVars,term)) = 
    let pp : ATermPrinter = context.pp in
    let button1 = if markSubterm?(context) 
                   then PrettyPrint.buttonPretty
                          (~(IntegerSet.member (context.indicesToDisable, index)),
			   index,string " ",false) 
                   else string "" in
    let button2 = if markSubterm?(context) 
                   then PrettyPrint.buttonPretty
                          (IntegerSet.member(context.sosIndicesToEnable, index),
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

  %op ppOp: fa(a) context -> Qualifier * String * AOpInfo a * Line -> Nat * Lines
  % op ppOpDecl : fa(a) context -> Qualifier * String * (AOpInfo a) * (Nat * Lines) -> Lines
  def fa(a) ppOpDecl (context : context)
                     (ref_qualifier, ref_id,
		      (aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_,
		       fixity, 
		       (tyVars, srt), 
		       defs) : AOpInfo a, 
                      (index, lines)) = 
   if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
     (index, lines)
   else
     let pp : ATermPrinter = context.pp in
     % let def ppOpNm() = pp.ppOpId(Qualified(qualifier,id)) in
     % let def ppOpNm() = (if spName = qualifier then pp.ppOp id
     %                  else pp.ppOpId(Qualified(qualifier,id))) in
     let def ppOpName (qid as Qualified(qualifier, id)) =
      (if qualifier = UnQualified then
         pp.ppOp id
       else
         pp.ppOpId qid)
     in
     let def ppOpNames () =
       case aliases of
         | [name] -> ppOpName name
         | _      -> ppList ppOpName ("{", ",", "}") aliases
     in
     let index1 = Integer.~(index + 1) in
     let button1 = if markSubterm?(context) & ~ (null defs)
                    then PrettyPrint.buttonPretty
                           (~(IntegerSet.member(context.indicesToDisable,index1)),
                            index1,string " ",false)
                  else string "" in
     let button2 = if markSubterm?(context) & ~ (null defs)
                    then PrettyPrint.buttonPretty
                           (IntegerSet.member(context.sosIndicesToEnable,index1),
                            index1,string " ",true)
                  else string "" in
     (index + 1,
      cons((1,blockFill
                (0, [(0, pp.Op),
                     (0, string " "),
                     (0, ppOpNames()),
                     (0, case fixity 
                           of Nonfix         -> string ""
			    | Unspecified    -> string ""
                            | Infix(Left,i)  -> string (" infixl "^Nat.toString i)
                            | Infix(Right,i) -> string (" infixr "^Nat.toString i)),
                     (0, string " :"),
                     (0, ppForallTyVars pp tyVars),
                     (0, string " "),
                     (3, ppSort context ([index,opIndex],Top:ParentSort) srt)])),
           (foldl (fn ((defining_type_vars, defining_term), lines) ->
		   let def ppDefn (path,term) = 
		        case term of
			  | Lambda ([(pat,Fun(Bool true,_,_),body)],_) ->
                            let pat = ppPattern context ([0,0] ++ path,false) pat in 
			    let body = ppDefn([2,0] ++ path,body) in
			    let prettys = [(0,pat),(0,string " ")] ++ body in
			    if markSubterm? (context) then
			      let num = State.! context.markNumber in
			      let table = State.! context.markTable in
			      (context.markTable State.:= NatMap.insert(table,num,path);
			       context.markNumber State.:= num + 1;
			       PrettyPrint.markLines(num,prettys))
			    else 
			      prettys
			  | _ -> 
                            let pretty = ppTerm context (path,Top:ParentTerm) term in
                            let prettys = [(0,pp.DefEquals),(0,string " "),(2,pretty)] in
                            prettys
		   in
		   let prettys = ppDefn([index,defIndex],defining_term) in
		   cons((1, blockFill (0,
				       [(0, blockFill (0,
						       [(0, button1),
							(0, button2),
							(0, pp.Def),
							(if printSort? context then
							   (0,ppForallTyVars pp defining_type_vars) 
							 else 
							   (0,string "")),
							(0, ppOpName primary_name),
							(0, string " ")]
						      ))]
				       ++ prettys)),
			lines))
	          lines
		  defs)))


  def fa(a) ppSortDecl (context : context)
                       (ref_qualifier, ref_id,
			(aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_,
			 tyVars, 
			 defs) : ASortInfo a, 
			(index, lines)) = 
   if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
     (index, lines)
   else
     let pp : ATermPrinter = context.pp in
     let def ppSortName (qid as Qualified (qualifier, id)) =
      (if qualifier = UnQualified then
         pp.ppSort id
       else
         pp.ppSortId qid)
     in
     let def ppSortNames () =
       case aliases of
         | [qid] -> ppSortName qid
         | _     -> ppList ppSortName ("{", ",", "}") aliases
     in
     (index + 1,
      case defs of
	| [] -> 
	  cons ((1,blockFill(0,[(0, pp.Sort),
				(0, string " "),
				(0, ppSortNames ()),
				(0, ppTyVars pp tyVars)])),
		lines)
	| _ ->
	  foldl (fn ((defining_type_vars, defining_sort), lines) ->
		 cons ((1,blockFill(0,[(0, pp.Sort),
				       (0, string " "),
				       (0, ppSortNames()),
				       (0, ppTyVars pp defining_type_vars),
				       (0, string " "),
				       (0, pp.DefEquals),
				       (0, string " "),
				       (3, ppSort context ([index,sortIndex],Top:ParentSort) defining_sort)])),
		       lines))
	        lines
		defs)

   % op isBuiltIn? : Import -> Boolean
   % def isBuiltIn? (specCalcTerm, _ (* spc *)) = false
   % spec_ref = "String"  or spec_ref = "Nat"  or 
   % spec_ref = "Boolean" or spec_ref = "Char" or
   % spec_ref = "Integer" or spec_ref = "List" or 
   % spec_ref = "General"

  %% Top-level print module; lower-level print spec
  def ppSpec context  {importInfo = {imports, importedSpec=_,localOps=_,localSorts=_},
                       sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      % let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      blockAll(0,
               [(0,blockFill(0,
                             [(0, pp.Spec),
                              (0, string " ")]))]
               ++
               (map (fn (specCalcTerm, spc) -> (1,prettysFill [pp.Import, string (showTerm specCalcTerm)])) imports) 
               ++
               (ppSortDecls context sorts)
               ++
               (ppOpDecls   context ops)
               ++
               (ListUtilities.mapWithIndex (ppProperty context) properties)
               ++
               [(0, pp.EndSpec),
                (0, string "")])

  def ppSpecR context  {importInfo = {imports, importedSpec=_,localOps=_,localSorts=_},
                        sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      % let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      blockAll(0,
               [(0, blockFill(0,
                              [(0, pp.Spec),
                               (0, string " ")]))]
               ++
               (map (fn (specCalcTerm, spc) -> (1,prettysFill [pp.Import, string (showTerm specCalcTerm)])) imports) 
               ++
               (ppSortDecls context sorts)
               ++
               (ppOpDecls context ops)
               ++
               (ListUtilities.mapWithIndex (ppProperty context) properties)
               ++
               [(0, pp.EndSpec),
                (0, string "")])


  def ppSpecHidingImportedStuff context base_spec
                                {importInfo = {imports, importedSpec,localOps,localSorts},
				 sorts, ops, properties} =
      %% Also suppress printing import of base specs
      let pp : ATermPrinter = context.pp in
      let imported_sorts  = Cons (base_spec.sorts,      map (fn (_,spc) -> spc.sorts)        imports) in
      let imported_ops    = Cons (base_spec.ops,        map (fn (_,spc) -> spc.ops)          imports) in
      let imported_props  = Cons (base_spec.properties, map (fn (_,spc) -> spc.properties)   imports) in
      let def imported_sort? (qualifier, id) =
  	    exists (fn sorts -> case findAQualifierMap (sorts, qualifier, id) of 
				  | Some _ -> true 
				  | _ -> false)
	           imported_sorts
      in
      let def imported_op? (qualifier, id) =
  	    exists (fn ops -> case findAQualifierMap (ops, qualifier, id) of
				  | Some _ -> true 
				  | _ -> false)
	           imported_ops
      in
      let def imported_prop? (typ, name, _, _) =
  	    exists (fn imp_props -> exists (fn (imp_type, imp_name, _, _) -> 
                                            %% can't quite do prop = imported_prop 
					    %% because imported_prop has type  Property
					    %%     but prop          has type  Aproperty a
					    typ = imp_type & name = imp_name)
		                           imp_props)
	           imported_props % list of lists of properties
      in
      blockAll(0,
               [(0, blockFill(0,
                              [(0, pp.Spec),
                               (0, string " ")]))]
               ++
               (let {importInfo = {imports=base_imports, importedSpec=_, localOps=_, localSorts=_},
		     sorts=_, ops=_, properties=_} = base_spec
		in
		let non_base_imports = filter (fn (_,imp_spec) -> 
					       if imp_spec = base_spec then
						 false % not not imported, i.e. imported
					       else
						 List.foldl (fn ((_,base_imp_spec), not_imported?) ->
							     if imp_spec = base_imp_spec then
							       false % not not imported, i.e. imported
							     else
							       not_imported?)
					                   true % begin assuming not imported
							   base_imports)
		                              imports
		in
		let pps : Lines =
		  List.map (fn (specCalcTerm, _) -> (1,prettysFill [pp.Import, string (showTerm specCalcTerm)])) 
		           non_base_imports
		in
		  pps)
               ++
	       (let (index,pps : Lines) = foldriAQualifierMap (fn (qualifier, id, sort_info, index_and_pps) ->
							  if imported_sort? (qualifier, id) then
							    index_and_pps
							  else
							    ppSortDecl context (qualifier, id, sort_info, index_and_pps))
		                                         (0,[])   
                                                         sorts
		in
		  pps)
   	       ++
	       (let (index,pps : Lines) = foldriAQualifierMap (fn (qualifier, id, op_info, index_and_pps) ->
							  if imported_op? (qualifier, id) then
							    index_and_pps
							  else
							    ppOpDecl context (qualifier, id, op_info, index_and_pps))
                                                         (0,[])   
                                                         ops
		in
		  pps)
               ++
	       (let pps : Lines =
		List.foldl (fn (prop, pps) ->
			    if imported_prop? prop then
			      pps
			    else
			      Cons (ppProperty context (0, prop), pps)) % Ok to keep index at 0?
		           []   
			   properties
		in
		  pps)
               ++
               [(0, pp.EndSpec),
                (0, string "")])

  def ppSpecAll context  {importInfo = {imports, importedSpec=_,localOps=_,localSorts=_},
                          sorts, ops, properties} = 
      let pp : ATermPrinter = context.pp in
      % let imports = filter (fn imp -> ~(isBuiltIn? imp)) imports in
      let ppImports = map (fn (specCalcTerm, spc) ->
                           (2, blockFill (0,
                                          [(0,string "import "),
                                           (0,string (showTerm specCalcTerm)),
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
      let (index,pps) = foldriAQualifierMap (ppSortDecl context) (0,[]) sorts in
      pps

  def ppOpDecls context ops =  
      let (index,pps) = foldriAQualifierMap (ppOpDecl context) (0,[]) ops in
      pps

  def specToPrettyVerbose spc = 
      ppSpecAll (initialize(asciiPrinter,false)) spc
      
  def specToPretty spc = 
      ppSpecR (initialize(asciiPrinter,false)) spc
      
  def specToPrettyR spc = 
      ppSpecR (initialize(asciiPrinter,false)) spc
      
  def printSpec spc =
      PrettyPrint.toString (format(80,specToPretty spc))

  def printSpecVerbose spc =
      PrettyPrint.toString (format(80,specToPrettyVerbose spc))

  def printSpecToTerminal spc =
     (toTerminal (format(80,specToPretty spc)); String.writeLine "")

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
      toTerminal(format(80,ppSpec(initialize(asciiPrinter,true)) spc))

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
        foldriAQualifierMap 
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
        foldriAQualifierMap 
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
     let sortCount  = length sorts                in
     let opCount    = length ops                in
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
     let counter = (Ref 0) : Ref(Nat) in
     let specs = 
         map 
           (fn (sp:ASpec a) -> 
                ppSpec (initialize(pdfPrinter(counter,"???"),false)) sp) specs0 
     in
     let menues = map pdfMenu specs0                  in
     let sw2000 = case getEnv "SPECWARE2000" of
                    | None            -> "??SPECWARE2000??" 
                    | Some dir_string -> dir_string
     in
     prettysAll
        ([string "\\documentclass{article}",
         string ("\\input{" ^ sw2000 ^ "/doc/pdf-sources/megamacros}"),
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
     let sw2000 = case getEnv "SPECWARE2000" of
                    | None            -> "??SPECWARE2000??" 
                    | Some dir_string -> dir_string
     in
     PrettyPrint.toFile(fileName,format(90,
        prettysAll
        ([string "\\documentclass{article}",
         string ("\\input{" ^ sw2000 ^ "/doc/pdf-sources/megamacros}"),
         string "\\begin{document}",
         string "\\pdfthread num 1"])))

  def fa(a) pdfOneSpecToFile(counter,fileName,spc:ASpec a) = 
      let spc1 = ppSpec (initialize(pdfPrinter(counter,"???"),false)) spc         in
      let menu = pdfMenu spc                                                         in
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
