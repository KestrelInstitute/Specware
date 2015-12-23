(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Simple MetaSlang Pretty Printer

A simple pretty printer for MetaSlang. *)

SpecCalc qualifying spec
  import AnnTerm
  import /Library/PrettyPrinter/WadlerLindig

  op isSimpleTerm? : [a] ATerm a -> Bool
  def isSimpleTerm? trm =
    case trm of
      | Var _ -> true
      | Fun _ -> true
      | _ -> false

  def ppGrConcat x = ppGroup (ppConcat x)

  op ppATerm : [a] ATerm a -> WLPretty
  def ppATerm term =
    case isFiniteList term of
        Some terms ->
          ppGrConcat [
            ppString "[",
            ppSep (ppString ",") (map ppATerm terms),
            ppString "]"
          ]
      | None ->
(*
When we see an infix operator applied to a product, then we print it
infix with brackets. And similarly when we see an \verb+Equals+.
*)
        (case term of
          | Apply (Fun (Op (qid,Infix (assoc,prec)),srt,_),
		   Record ([("1",left),("2",right)],_), _) ->
              if (isSimpleTerm? left) || (isSimpleTerm? right) then
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
                  ppBreak,
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
		    if (isSimpleTerm? left) || (isSimpleTerm? right) then
		      ppGroup (ppConcat [
			ppString "(",
			ppATerm left, ppBreak,
			ppString infix_string,
			ppString " ",
			ppATerm right,
                        ppString ")"
					])
		    else
		      ppGrConcat [
		        ppString "(",
			ppATerm left, ppBreak,
			ppGroup (ppIndent (ppConcat [
			  ppString infix_string,
                          ppBreak,
                          ppAppend (ppATerm right) (ppString ")")
                        ]))
                      ]
		  | _ ->
		    %% same as Apply (term1, term2, _) below
		    if (isSimpleTerm? term1) || (isSimpleTerm? term2) then
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
              if (isSimpleTerm? term1) || (isSimpleTerm? term2) then
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
                ppAVarWithoutType var,
                ppString ") ",
                ppATerm term
              ]
          | Bind (binder,vars,term,_) ->
              ppGrConcat [
                ppBinder binder,
                ppString " (",
                ppSep (ppString ",") (map ppAVarWithoutType vars),
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
                  ppAVarWithoutType v,
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
          | Var (v,_) -> ppAVarWithoutType v
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
	  | TypedTerm (tm,srt,_) ->
	      ppGrConcat [ppATerm tm, ppString": ",ppBreak,ppAType srt]
          | Transform (trfm, _) ->
            ppTransformExpr trfm
          | And (tms, _) ->
            ppGrConcat [ppString "<AndTerms", ppBreak, ppString "  ",
                        ppNest 0 (ppSep ppBreak (map ppATerm tms)),
                        ppString ">"]
          | Any _ -> ppString "<anyterm>"
          | mystery -> fail ("No match in ppATerm with: '" ^ (anyToString mystery) ^ "'"))

  op ppBinder : Binder -> WLPretty
  def ppBinder binder =
    case binder of
      | Forall -> ppString "fa"
      | Exists -> ppString "ex"
      | Exists1 -> ppString "ex1"

  op ppAVarWithoutType : [a] AVar a -> WLPretty
  def ppAVarWithoutType (id, _(* srt *)) = ppString id

  op ppAVar : [a] AVar a -> WLPretty
  def ppAVar (id,srt) =
    ppConcat [
      ppString id,
      ppString ":",
      ppAType srt
    ]

  op ppAMatch : [a] AMatch a -> WLPretty
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

  op ppAPattern : [a] APattern a -> WLPretty
  def ppAPattern pattern = 
    case pattern of
      | AliasPat (pat1,pat2,_) -> 
          ppGrConcat [
            ppAPattern pat1,
            ppString " as ",
            ppAPattern pat2
          ]
      | VarPat (v,_) -> ppAVarWithoutType v
      | EmbedPat (constr,pat,srt,_) ->
          ppGrConcat [
            ppQualifiedId constr,
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
      | BoolPat (b,_) -> ppBool b
      | CharPat (chr,_) -> ppString (Char.show chr)
      | NatPat (int,_) -> ppString (Nat.show int)      
      | QuotientPat (pat,qid,_,_) -> 
          ppGrConcat [ppString ("(quotient[" ^ show qid ^ "] "),
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
      | TypedPat (pat,srt,_) -> ppAPattern pat
      | mystery -> fail ("No match in ppAPattern with: '" ^ (anyToString mystery) ^ "'")


  op ppBool : Bool -> WLPretty
  def ppBool b =
    case b of
      | true -> ppString "true"
      | false -> ppString "false"

  op ppAFun : [a] AFun a -> WLPretty
  def ppAFun fun =
    case fun of
      | Not           -> ppString "~"
      | And           -> ppString "&&"
      | Or            -> ppString "||"
      | Implies       -> ppString "=>"
      | Iff           -> ppString "<=>"
      | Equals        -> ppString "="
      | NotEquals     -> ppString "~="
      | Quotient  qid -> ppGrConcat [ppString "quotient[", ppQualifiedId qid, ppString "] "]
      | PQuotient qid -> ppGrConcat [ppString "quotient[", ppQualifiedId qid, ppString "] "]
      | Choose    qid -> ppGrConcat [ppString "choose[",   ppQualifiedId qid, ppString "] "]
      | PChoose   qid -> ppGrConcat [ppString "choose[",   ppQualifiedId qid, ppString "] "]
      | Restrict      -> ppString "restrict"
      | Relax         -> ppString "relax"
      | Op (qid,Nonfix)       -> ppQualifiedId qid
      | Op (qid,Constructor0) -> ppQualifiedId qid
      | Op (qid,Constructor1) -> ppQualifiedId qid
      | Op (qid,Unspecified)  -> ppQualifiedId qid
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
      | Embed (qid,b) ->
          % ppConcat [
            % ppString "(embed ",
            ppQualifiedId qid
            % ppString " "
            % ppBool b,
            % ppString ")"
          % ]
      | Embedded qid ->
          ppConcat [
            ppString "embedded ",
            ppQualifiedId qid
          ]
      | Select qid ->
          ppConcat [
            ppString "select ",
            ppQualifiedId qid
          ]
      | Nat n -> ppString (Nat.show n)
      | Char chr -> ppString (Char.show chr)
      | String str -> ppString ("\"" ^ str ^ "\"")
      | Bool b -> ppBool b
      | OneName (id,fxty) -> ppString id
      | TwoNames (id1,id2,fxty) -> ppQualifiedId (Qualified (id1,id2))
      | mystery -> fail ("No match in ppAFun with: '" ^ (anyToString mystery) ^ "'")

  def omittedQualifiers = ["Integer","Nat","Double","List","String","Char"]  % "IntegerAux" "Option" ...?

  op ppQualifiedId : QualifiedId -> WLPretty
  def ppQualifiedId (Qualified (qualifier,id)) =
    if (qualifier = UnQualified) || (qualifier in? omittedQualifiers) then
      ppString id
    else
      ppString (qualifier ^ "." ^ id)

  op ppFixity : Fixity -> WLPretty
  def ppFixity fix =
    case fix of
      | Infix (Left,  n) -> ppConcat [
				      ppString "infixl ",
				      ppString (Nat.show n)
				     ]
      | Infix (Right, n) -> ppConcat [
				      ppString "infixr ",
				      ppString (Nat.show n)
				     ]
      | Nonfix           -> ppNil % ppString "Nonfix"
      | Constructor0     -> ppNil % ppString "Constructor0"
      | Constructor1     -> ppNil % ppString "Constructor1"
      | Unspecified      -> ppNil % ppString "Unspecified"
      | Error fixities   -> ppConcat [
				      ppString "conflicting fixities: [",
				      ppSep (ppString ",") (map ppFixity fixities),
				      ppString "]"
				     ]
      | mystery -> fail ("No match in ppFixity with: '" ^ (anyToString mystery) ^ "'")

  op isSimpleType? : [a] AType a -> Bool
  def isSimpleType? srt =
    case srt of
      | Base _ -> true
      | Boolean _ -> true
      | _ -> false

  op ppAType : [a] AType a -> WLPretty
  def ppAType srt =
    case srt of
      | Arrow (srt1,srt2,_) ->
          if (isSimpleType? srt1) || (isSimpleType? srt2) then
            ppGroup (ppConcat [
              ppString "(",
              ppAType srt1,
              ppString " -> ",
              ppAType srt2,
              ppString ")"
            ])
          else
            ppGrConcat [
              ppString "(",
              ppAType srt1,
              ppGroup (ppIndent (ppConcat [
                ppString " ->",
                ppBreak,             
                ppAType srt2,
                ppString ")"
              ]))
            ]
      | Product (fields,_) ->
          (case fields of
              [] -> ppString "()"
            | ("1",_)::_ ->
                let def ppField (_,y) = ppAType y in
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
                    ppAType y
                  ]) in
                ppIndent (ppGrConcat [
                  ppString "{",
                  ppSep (ppAppend (ppString ",") ppBreak) (map ppField fields),
                  ppString "}"
                ]))
      | CoProduct (taggedTypes,_) -> 
          let def ppTaggedType (qid,optSrt) =
            case optSrt of
              | None -> ppQualifiedId qid
              | Some srt ->
                  ppConcat [ppQualifiedId qid,
                            ppString  " ",
                            ppAType srt]
          in ppGrConcat [
            ppString "(",
            ppGrConcat [
              ppString "|  ",
              ppSep (ppAppend ppBreak (ppString "| ")) (map ppTaggedType taggedTypes)
            ],
            ppString ")"
          ]
      | Quotient (srt,term,_) ->
          ppGrConcat [
            ppString "(",
            ppAType srt,
            ppString " \\ ",
            ppATerm term,
            ppString ")"
          ]
      | Subtype (srt,term,_) ->
          ppGrConcat [
            ppString "(",
            ppAType srt,
            ppString " | ",
            ppATerm term,
            ppString ")"
          ]
      | Base (qid,[],_) -> ppQualifiedId qid
      | Base (qid,[srt],_) ->
           ppGrConcat [
             ppQualifiedId qid,
             ppString " ",
             ppAType srt
           ]
      | Base (qid,srts,_) ->
           ppGrConcat [
             ppQualifiedId qid,
             ppString " (",
             ppSep (ppString ",") (map ppAType srts),
             ppString ")"
           ]
      | Boolean _ -> ppString "Bool"  
      | TyVar (tyVar,_) -> ppString tyVar
      | MetaTyVar (tyVar,_) -> 
         let ({link, uniqueId, name}) = ! tyVar in
             ppString (name ^ (Nat.show uniqueId))

      | mystery -> fail ("No match in ppAType with: '" ^ (anyToString mystery) ^ "'")

 op [a] ppTransformExpr(tre: ATransformExpr a): WLPretty

endspec
