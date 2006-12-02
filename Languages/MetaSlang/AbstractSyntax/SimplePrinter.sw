\section{Simple MetaSlang Pretty Printer}

A simple pretty printer for MetaSlang.

\begin{spec}
SpecCalc qualifying spec {
  import AnnTerm
  import /Library/PrettyPrinter/WadlerLindig

  op isSimpleTerm? : fa (a) ATerm a -> Boolean
  def isSimpleTerm? trm =
    case trm of
      | Var _ -> true
      | Fun _ -> true
      | _ -> false

  def ppGrConcat x = ppGroup (ppConcat x)

  op ppATerm : fa (a) ATerm a -> Pretty
  def ppATerm term =
    case (isFiniteList term) of
        Some terms ->
          ppGrConcat [
            ppString "[",
            ppSep (ppString ",") (map ppATerm terms),
            ppString "]"
          ]
      | None ->
\end{spec}

When we see an infix operator applied to a product, then we print it
infix with brackets. And similarly when we see an \verb+Equals+.

\begin{spec}
        (case term of
          | Apply (Fun (Op (qid,Infix (assoc,prec)),srt,_),
		   Record ([("1",left),("2",right)],_), _) ->
              if (isSimpleTerm? left) or (isSimpleTerm? right) then
                ppGroup (ppConcat [
                  ppString "(",
                  ppATerm left,
                  ppString " ",
                  ppQualifiedId qid,
                  ppString " ",
                  ppATerm right,
                  ppString ")"
                ])
              else
                ppGrConcat [
                  ppString "(",
                  ppATerm left,
                  ppGroup (ppIndent (ppConcat [
                    ppString " ",
                    ppQualifiedId qid,
                    ppBreak,
                    ppAppend (ppATerm right) (ppString ")")
                  ]))
                ]
          | Apply (term1 as Fun(fun, srt, _), 
		   term2 as Record ([("1",left),("2",right)],_),
		   _)
	     ->
	     %% Having all these cases seems awful -- is there a simpler dispatch?
	     (let opt_infix_string =
	          case fun of
		    | And       -> Some " &&"
		    | Or        -> Some " ||"
		    | Implies   -> Some " =>"
		    | Iff       -> Some " <=>"
		    | Equals    -> Some " ="
		    | NotEquals -> Some " ~="
		    | _ -> None
	      in
		case opt_infix_string of
		  | Some infix_string ->
		    if (isSimpleTerm? left) or (isSimpleTerm? right) then
		      ppGroup (ppConcat [
			ppString "(",
			ppATerm left,
			ppString infix_string,
			ppString " ",
			ppATerm right,
                        ppString ")"
					])
		    else
		      ppGrConcat [
		        ppString "(",
			ppATerm left,
			ppGroup (ppIndent (ppConcat [
			  ppString infix_string,
                          ppBreak,
                          ppAppend (ppATerm right) (ppString ")")
                        ]))
                      ]
		  | _ ->
		    %% same as Apply (term1, term2, _) below
		    if (isSimpleTerm? term1) or (isSimpleTerm? term2) then
		      ppGroup (ppConcat [
			ppString "(",
			ppATerm term1,
                        ppString " ",
                        ppATerm term2,
                        ppString ")"
                      ])
                    else
                      ppGrConcat [
                        ppString "(",
                        ppGroup (ppIndent (ppConcat [
                          ppATerm term1,
                          ppBreak,
                          (ppAppend (ppATerm term2) (ppString ")"))
                        ]))
                      ])
          | Apply (Lambda (match as (_ :: _ :: _), _), term,_) ->
              ppIndent (ppGrConcat [
                ppString "case ",
                ppATerm term,
                ppString " of",
                ppIndent (ppAppend ppBreak (ppAMatch match))
              ])
          | Apply (term1,term2,_) ->
              if (isSimpleTerm? term1) or (isSimpleTerm? term2) then
                ppGroup (ppConcat [
                  ppString "(",
                  ppATerm term1,
                  ppString " ",
                  ppATerm term2,
                  ppString ")"
                ])
              else
                ppGrConcat [
                  ppString "(",
                  ppGroup (ppIndent (ppConcat [
                    ppATerm term1,
                    ppBreak,
                    (ppAppend (ppATerm term2) (ppString ")"))
                  ]))
                ]
          | ApplyN (terms,_) ->
              let def ppTerms l =
                case l of
                  | [] -> ppNil
                  | [t] -> ppATerm t
                  | t::rest -> ppGroup (ppIndent 
                     (ppCons (ppATerm t) 
                             (ppCons ppBreak (ppTerms rest)))) in
              ppTerms terms
          | Record (fields,_) ->      
              (case fields of
                | [] -> ppString "()"
                | ("1",_) :: _ ->
                    let def ppField (_,y) = ppATerm y in
                    ppConcat [
                      ppString "(",
                      ppSep (ppString ",") (map ppField fields),
                      ppString ")"
                    ]
                | _ ->
                    let def ppField (x,y) =
                      ppConcat [
                        ppString x,
                        ppString "=",
                        ppATerm y
                      ] in
                    ppConcat [
                      ppString "{",
                      ppSep (ppString ",") (map ppField fields),
                      ppString "}"
                    ])
          | The (var,term,_) ->
              ppGrConcat [
                ppString "the (",
                ppAVarWithoutSort var,
                ppString ") ",
                ppATerm term
              ]
          | Bind (binder,vars,term,_) ->
              ppGrConcat [
                ppBinder binder,
                ppString " (",
                ppSep (ppString ",") (map ppAVarWithoutSort vars),
                ppString ") ",
                ppATerm term
              ]
          | Let (decls,term,_) ->
              let def ppDecl (pattern,term) =
                ppConcat [
                  ppAPattern pattern,
                  ppString "=",
                  ppATerm term
                ] in
              ppGrConcat [
                ppString "let ",
                ppIndent (ppSep ppNewline (map ppDecl decls)),
                ppString "in",
                ppNewline,
                ppIndent (ppATerm term)
             ]
          | LetRec (decls,term,_) ->
              let def ppDecl (v,term) =
                ppGrConcat [
                  ppString "def ",
                  ppAVarWithoutSort v,
                  ppString " = ",
                  ppATerm term
                ] in
              ppGrConcat [
                ppString "let",
                ppNewline,
                ppString "  ",
                ppIndent (ppSep ppNewline (map ppDecl decls)),
                ppNewline,
                ppString "in",
                ppNewline,
                ppATerm term
             ]
          | Var (v,_) -> ppAVarWithoutSort v
          | Fun (fun,srt,_) -> ppAFun fun
          | Lambda ([(pattern,_,term)],_) ->
              ppGrConcat [
                ppString "(fn ",
                ppAPattern pattern,
                ppGroup (ppIndent (ppConcat [
                  ppString " ->",
                  ppBreak,
                  ppAppend (ppATerm term) (ppString ")")
                ]))
              ]
          | Lambda (match,_) -> ppAMatch match
          | IfThenElse (pred,term1,term2,_) -> 
              ppGrConcat [
                ppString "if ",
                ppATerm pred,
                ppString " then",
                ppBreak,
                ppString "  ",
                ppIndent (ppATerm term1),
                ppBreak,
                ppString "else",
                ppBreak,
                ppString "  ",
                ppIndent (ppATerm term2)
              ]
          | Seq (terms,_) ->
              ppSep (ppString "; ") (map ppATerm terms)
	  | SortedTerm (tm,srt,_) ->
	      ppGrConcat [ppATerm tm, ppString": ",ppBreak,ppASort srt]
          | mystery -> fail ("No match in ppATerm with: '" ^ (anyToString mystery) ^ "'"))

  op ppBinder : Binder -> Pretty
  def ppBinder binder =
    case binder of
      | Forall -> ppString "fa"
      | Exists -> ppString "ex"
      | Exists1 -> ppString "ex1"

  op ppAVarWithoutSort : fa (a) AVar a -> Pretty
  def ppAVarWithoutSort (id, _(* srt *)) = ppString id

  op ppAVar : fa (a) AVar a -> Pretty
  def ppAVar (id,srt) =
    ppConcat [
      ppString id,
      ppString ":",
      ppASort srt
    ]

  op ppAMatch : fa (a) AMatch a -> Pretty
  def ppAMatch cases =
    let def ppCase (pattern,_,term) =
       ppGrConcat [
         ppString "| ",
         ppAPattern pattern,
         ppString " -> ",
         ppATerm term
       ]
    in
      ppGroup (ppSep ppNewline (map ppCase cases))

  op ppAPattern : fa (a) APattern a -> Pretty
  def ppAPattern pattern = 
    case pattern of
      | AliasPat (pat1,pat2,_) -> 
          ppGrConcat [
            ppAPattern pat1,
            ppString " as ",
            ppAPattern pat2
          ]
      | VarPat (v,_) -> ppAVarWithoutSort v
      | EmbedPat (constr,pat,srt,_) ->
          ppGrConcat [
            ppString constr,
            case pat of
              | None -> ppNil
              | Some pat -> ppAppend (ppString " ") (ppAPattern pat)
          ]
      | RecordPat (fields,_) ->
          (case fields of
            | [] -> ppString "()"
            | ("1",_)::_ ->
                let def ppField (_,pat) = ppAPattern pat in
                ppConcat [
                  ppString "(",
                  ppSep (ppString ",") (map ppField fields),
                  ppString ")"
                ]
            | _ ->
                let def ppField (x,pat) =
                  ppConcat [
                    ppString x,
                    ppString "=",
                    ppAPattern pat
                  ] in
                ppConcat [
                  ppString "{",
                  ppSep (ppString ",") (map ppField fields),
                  ppString "}"
                ])
      | WildPat (srt,_) -> ppString "_"
      | StringPat (str,_) -> ppString ("\"" ^ str ^ "\"")
      | BoolPat (b,_) -> ppBoolean b
      | CharPat (chr,_) -> ppString (Char.toString chr)
      | NatPat (int,_) -> ppString (Nat.toString int)      
      | QuotientPat (pat,qid,_) -> 
          ppGrConcat [ppString ("(quotient[" ^ toString qid ^ "] "),
                      ppAPattern pat,
                      ppString ")"]
      | RestrictedPat (pat,term,_) -> 
%        (case pat of
%	   | RecordPat (fields,_) ->
%	     (case fields of
%	       | [] -> ppGrConcat [ppString "() | ",ppATerm term]
%	       | ("1",_)::_ ->
%		   let def ppField (_,pat) = ppAPattern pat in
%		   ppConcat [
%		     ppString "(",
%		     ppSep (ppString ",") (map ppField fields),
%		     ppString " | ",
%		     ppATerm term,
%		     ppString ")"
%		   ]
%	       | _ ->
%		   let def ppField (x,pat) =
%		     ppConcat [
%		       ppString x,
%		       ppString "=",
%		       ppAPattern pat
%		     ] in
%		   ppConcat [
%		     ppString "{",
%		     ppSep (ppString ",") (map ppField fields),
%		     ppString " | ",
%		     ppATerm term,
%		     ppString "}"
%		   ])
%	       | _ ->
	    ppGrConcat [ppAPattern pat,
			ppString " | ",
			ppATerm term] %)
      | SortedPat (pat,srt,_) -> ppAPattern pat
      | mystery -> fail ("No match in ppAPattern with: '" ^ (anyToString mystery) ^ "'")


  op ppBoolean : Boolean -> Pretty
  def ppBoolean b =
    case b of
      | true -> ppString "true"
      | false -> ppString "false"

  op ppAFun : fa (a) AFun a -> Pretty
  def ppAFun fun =
    case fun of
      | Not           -> ppString "~"
      | And           -> ppString "&&"
      | Or            -> ppString "||"
      | Implies       -> ppString "=>"
      | Iff           -> ppString "<=>"
      | Equals        -> ppString "="
      | NotEquals     -> ppString "~="
      | Quotient  qid -> ppGrConcat [ppString "quotient[", ppQualifiedId qid, ppString "]"]
      | PQuotient _   -> ppString "quotient[??]" 
      | Choose    qid -> ppGrConcat [ppString "choose[",   ppQualifiedId qid, ppString "]"]
      | PChoose   _   -> ppString "choose"
      | Restrict      -> ppString "restrict"
      | Relax         -> ppString "relax"
      | Op (qid,Nonfix)      -> ppQualifiedId qid
      | Op (qid,Unspecified) -> ppQualifiedId qid
      | Op (qid,fix) -> 
          ppGrConcat [
            ppString "(",
            ppQualifiedId qid,
            ppString ",",
            ppFixity fix,
            ppString ")"
          ]
      | Project id ->
          ppConcat [
            ppString "project ",
            ppString id
          ]
      | RecordMerge ->
	  ppString "<<"
      | Embed (id,b) ->
          % ppConcat [
            % ppString "(embed ",
            ppString id
            % ppString " "
            % ppBoolean b,
            % ppString ")"
          % ]
      | Embedded id ->
          ppConcat [
            ppString "embedded ",
            ppString id
          ]
      | Select id ->
          ppConcat [
            ppString "select ",
            ppString id
          ]
      | Nat n -> ppString (Nat.toString n)
      | Char chr -> ppString (Char.toString chr)
      | String str -> ppString ("\"" ^ str ^ "\"")
      | Bool b -> ppBoolean b
      | OneName (id,fxty) -> ppString id
      | TwoNames (id1,id2,fxty) -> ppQualifiedId (Qualified (id1,id2))
      | mystery -> fail ("No match in ppAFun with: '" ^ (anyToString mystery) ^ "'")

  def omittedQualifiers = ["Integer","Nat","Double","List","String","Char"]  % "IntegerAux" "Option" ...?

  op ppQualifiedId : QualifiedId -> Pretty
  def ppQualifiedId (Qualified (qualifier,id)) =
    if (qualifier = UnQualified) or (member (qualifier,omittedQualifiers)) then
      ppString id
    else
      ppString (qualifier ^ "." ^ id)

  op ppFixity : Fixity -> Pretty
  def ppFixity fix =
    case fix of
      | Infix (Left,  n) -> ppConcat [
				      ppString "infixl ",
				      ppString (Nat.toString n)
				     ]
      | Infix (Right, n) -> ppConcat [
				      ppString "infixr ",
				      ppString (Nat.toString n)
				     ]
      | Nonfix           -> ppNil % ppString "Nonfix"
      | Unspecified      -> ppNil % ppString "Unspecified"
      | Error fixities   -> ppConcat [
				      ppString "conflicting fixities: [",
				      ppSep (ppString ",") (map ppFixity fixities),
				      ppString "]"
				     ]
      | mystery -> fail ("No match in ppFixity with: '" ^ (anyToString mystery) ^ "'")

  op isSimpleSort? : fa (a) ASort a -> Boolean
  def isSimpleSort? srt =
    case srt of
      | Base _ -> true
      | Boolean _ -> true
      | _ -> false

  op ppASort : fa (a) ASort a -> Pretty
  def ppASort srt =
    case srt of
      | Arrow (srt1,srt2,_) ->
          if (isSimpleSort? srt1) or (isSimpleSort? srt2) then
            ppGroup (ppConcat [
              ppString "(",
              ppASort srt1,
              ppString " -> ",
              ppASort srt2,
              ppString ")"
            ])
          else
            ppGrConcat [
              ppString "(",
              ppASort srt1,
              ppGroup (ppIndent (ppConcat [
                ppString " ->",
                ppBreak,             
                ppASort srt2,
                ppString ")"
              ]))
            ]
      | Product (fields,_) ->
          (case fields of
              [] -> ppString "()"
            | ("1",_)::_ ->
                let def ppField (_,y) = ppASort y in
                ppGrConcat [
                  ppString "(",
                  ppSep (ppString " * ") (map ppField fields),
                  ppString ")"
                ]
            | _ ->
                let def ppField (x,y) =
                  ppGroup (ppConcat [
                    ppString x,
                    ppString " : ",
                    ppASort y
                  ]) in
                ppIndent (ppGrConcat [
                  ppString "{",
                  ppSep (ppAppend (ppString ",") ppBreak) (map ppField fields),
                  ppString "}"
                ]))
      | CoProduct (taggedSorts,_) -> 
          let def ppTaggedSort (id,optSrt) =
            case optSrt of
              | None -> ppString id
              | Some srt ->
                  ppConcat [
                    ppString (id ^ " "),
                    ppASort srt
                  ]
          in ppGrConcat [
            ppString "(",
            ppGrConcat [
              ppString "|  ",
              ppSep (ppAppend ppBreak (ppString "| ")) (map ppTaggedSort taggedSorts)
            ],
            ppString ")"
          ]
      | Quotient (srt,term,_) ->
          ppGrConcat [
            ppString "(",
            ppASort srt,
            ppString " \\ ",
            ppATerm term,
            ppString ")"
          ]
      | Subsort (srt,term,_) ->
          ppGrConcat [
            ppString "(",
            ppASort srt,
            ppString " | ",
            ppATerm term,
            ppString ")"
          ]
      | Base (qid,[],_) -> ppQualifiedId qid
      | Base (qid,[srt],_) ->
           ppGrConcat [
             ppQualifiedId qid,
             ppString " ",
             ppASort srt
           ]
      | Base (qid,srts,_) ->
           ppGrConcat [
             ppQualifiedId qid,
             ppString " (",
             ppSep (ppString ",") (map ppASort srts),
             ppString ")"
           ]
      | Boolean _ -> ppString "Boolean"  
      | TyVar (tyVar,_) -> ppString tyVar
      | MetaTyVar (tyVar,_) -> 
         let ({link, uniqueId, name}) = ! tyVar in
             ppString (name ^ (Nat.toString uniqueId))

      | mystery -> fail ("No match in ppASort with: '" ^ (anyToString mystery) ^ "'")

  op isFiniteList : fa (a) ATerm a -> Option (List (ATerm a))
  def isFiniteList term =  
    case term of
      | Fun (Embed ("Nil", false), Base (Qualified("List", "List"), _, _), _) -> Some []
      | Apply (Fun(Embed("Cons",true), 
		   Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				   _),
			  Base (Qualified("List", "List"), _, _),
			  _),
		   _),
	       Record ([(_,t1),(_,t2)],_),
	       _) 
        -> 
	  (case isFiniteList t2 of
             | Some terms -> Some (Cons (t1,terms))
             | _ -> None)
      | ApplyN ([Fun (Embed ("Cons", true), 
		      Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				      _),
			     Base (Qualified("List", "List"), _, _),
			     _),
		      _),
		 Record ([(_, t1), (_, t2)], _),
		 _], 
		_)
	-> 
          (case isFiniteList t2 of
             | Some terms -> Some (Cons (t1,terms))
             | _ -> None)
     | _ -> None
}
\end{spec}
