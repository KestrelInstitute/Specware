\section{SpecCalc pretty printer}

Synchronized with r1.8 SW4/Languages/SpecCalculus/AbstractSyntax/PrettyPrinter.sl

This is a pretty printer for the spec calculus. This is almost but
not quite throw away code. In my opinion, it should be separate from
the MetaSlang pretty printer. The problem is that the MetaSlang pretty
printer functions are parameterized on a context to handle HTML, PDF etc.
and all the Also the two pretty printers use different pretty printing
libraries. This one should be changed to use the original
pretty printer library. Alternatively, the original library should be
discarded.

We use \verb+show+ functions to render terms as strings. We
use \verb+pp+ functions to render terms as "Pretty".

\begin{spec}
SpecCalc qualifying spec {
  import Types
  import ../../MetaSlang/AbstractSyntax/Printer 
  import ../../MetaSlang/Specs/Printer
  import /Library/PrettyPrinter/WadlerLindig

  op showSpecFile : fa (a) SpecFile a -> String
  def showSpecFile specFile = ppFormat (ppSpecFile specFile)

  op showTerm : fa (a) SpecCalc.Term a -> String
  def showTerm term = ppFormat (ppTerm term)

  op showURI : URI -> String
  def showURI uri = ppFormat (ppURI uri)

  op ppURI : URI -> Doc
  def ppURI {path,hashSuffix}  = 
    let def ppElem elem =
      ppConcat [
          ppString "\"",
          ppString elem,
          ppString "\""
        ]
    in
      ppConcat [
          ppString "[",
          ppSep (ppString " ") (map ppElem path),
          (case hashSuffix of
            | None -> ppNil
            | Some suffix -> ppString (" # " ^ suffix))
        ]

  op showRelativeURI : RelativeURI -> String
  def showRelativeURI uri = ppFormat (ppRelativeURI uri)

  op ppSpecFile : fa (a) SpecFile a -> Doc
  def ppSpecFile (specFile as (term,position)) =
    case term of
      | Term term -> ppTerm term
      | Decls decls -> ppDecls decls

  op ppTerm : fa (a) SpecCalc.Term a -> Doc
  def ppTerm (term,position) =
    case term of
      | Print t ->
          ppConcat [
            ppString "print ",
            ppTerm t
          ]
      | URI uri -> ppRelativeURI uri
      | Spec specElems -> 
          ppConcat [
            ppString "spec {",
            %% case optName of None -> ppNil | Some name -> ppString name,
            ppNewline,
            ppString "  ",
            ppNest 2 (ppSpecElems specElems),
            ppNewline,
            ppString "}"
          ]
      | Qualify (term, qualifier) ->
          ppConcat [
            ppString qualifier,
            ppString " qualifying ",
            ppTerm term
          ]
      | Translate (term, (translation,_)) ->
          let def ppTranslatePair ((left,right),pos) =
            ppConcat [
              ppQualifier left,
              ppString " -> ",
              ppQualifier right
            ] in
          ppConcat [
            ppString "{",
            ppSep (ppString ", ") (map ppTranslatePair translation),
            ppString "}",
            ppString " translating ",
            ppTerm term
          ]
      | Let (decls, term) ->
          ppConcat [
            ppString "let {",
            ppNewline,
            ppString "  ",
            ppNest 2 (ppDecls decls),
            ppNewline,
            ppString "} in",
            ppNewline,
            ppNest 2 (ppTerm term)
          ]
      | Where (decls, term) ->
          ppConcat [
            ppTerm term,
            ppNewline,
            ppString "  ",
            ppString "where {",
            ppNewline,
            ppString "    ",
            ppNest 4 (ppDecls decls),
            ppNewline,
            ppString "}"
          ]
      | Diag elems ->
          ppConcat [
            ppString "diag {",    % with apologies to stephen
            ppNewline,
            ppString "  ",
            ppNest 2 (ppSep ppNewline (map ppDiagElem elems)),
            ppNewline,
            ppString "end"
          ]
(*
      | SpecMorph (dom,cod,elems) ->
          let def ppSpecMorphElem ((id,term),pos) =
            ppConcat [
              ppIdInfo id,
              ppString " |-> ",
              ppATerm term
            ] in
          ppConcat [
            ppString "morph {",
            ppNewline,
            ppString "  ",
            ppNest (Integer.fromNat 2) (ppSep ppNewline (map ppSpecMorphElem elems)),
            ppNewline,
            ppString "} : ",
            ppTerm dom,
            ppString " -> ",
            ppTerm cod
          ]
      | Hide (nameExpr,term) ->
          ppConcat [
            ppString "hide {",
            ppSep (ppString ",") (map ppIdInfo nameExpr),
            ppString "} in",
            ppTerm term
          ]
      | Export (nameExpr,term) ->
          ppConcat [
            ppString "export {",
            ppSep (ppString ",") (map ppIdInfo nameExpr),
            ppString "} from",
            ppTerm term
          ]
*)
      | Generate (target,term,optFileNm) ->
          ppConcat [
            ppString ("generate " ^ target ^ " "),
            ppTerm term,
            (case optFileNm of
	           | Some filNm -> ppString(" in " ^ filNm)
               | _ -> ppNil)
          ]

  def ppQualifier(Qualified(Qualifier,Id))  =
    if Qualifier = UnQualified then ppString Id
      else ppString(Qualifier^"."^Id)

  op ppDiagElem : fa (a) DiagElem a -> Doc
  def ppDiagElem (elem,position) =
    case elem of
      | Node (nodeId,term) ->
          ppConcat [
            ppString nodeId,
            ppString " |-> ",
            ppTerm term
          ]
      | Edge (edgeId,dom,cod,term) ->
          ppConcat [
            ppString edgeId,
            ppString " : ",
            ppString dom,
            ppString " -> ",
            ppString cod,
            ppString " |-> ",
            ppTerm term
          ]

  op ppRelativeURI : RelativeURI -> Doc
  def ppRelativeURI relURI =
    case relURI of
        | SpecPath_Relative uri -> ppAppend (ppString "/") (ppURI uri)
        | URI_Relative uri -> ppURI uri

  op ppDecls : fa (a) List (Decl a) -> Doc
  def ppDecls decls =
    let def ppDecl (name,term) =
      ppConcat [
        ppString name,
        ppString " = ",
        ppTerm term
      ]
    in
      ppSep ppNewline (map ppDecl decls)

  op ppSpecElems : fa (a) List (SpecElem a) -> Doc
  def ppSpecElems elems = ppSep ppNewline (map ppSpecElem elems)

  op ppSpecElem : fa(a) SpecElem a -> Doc
  def ppSpecElem (elem,_) = 
    case elem of
      | Import term ->
          ppConcat [
            ppString "import ",
            ppTerm term
          ]
(*
      | Sort (qid, sortInfo) -> 
          ppConcat [
            ppString "sort ",
            ppIdInfo qid,
            ppASortInfo sortInfo
          ]
      | Op (qid, opInfo) ->
          ppConcat [
            ppString "op ",
            ppIdInfo qid,
            ppAOpInfo opInfo
          ]
*)
      | Claim property -> ppAProperty property

  op ppIdInfo : List Id -> Doc
(*
  def ppIdInfo ids = ppSep (ppString ".") (map ppString ids)
*)
   
  op ppASortInfo : fa (a) TyVars * Option (ASort a) -> Doc
  def ppASortInfo sortInfo =
    case sortInfo of
       | ([],None) -> ppNil
       | ([],Some srt) -> ppAppend (ppString " = ") (ppASort srt)
       | (tyVars,Some srt) -> 
           ppConcat [
             ppString " (",
             ppSep (ppString ",") (map ppString tyVars),
             ppString ") = ",
             ppASort srt
           ]

  op ppAOpInfo : fa (a)  Fixity * ASortScheme a * Option (ATerm a) -> Doc
  def ppAOpInfo (fixity,(tyVars,srt),optTerm) =
    ppConcat [
      ppFixity fixity,
      ppString " : ",
      (case tyVars of
        | [] -> ppNil
        | _ -> 
           ppConcat [
             ppString "fa (",
             ppSep (ppString ",") (map ppString tyVars),
             ppString ") "
           ]),
      ppASort srt,
      (case optTerm of
        | None -> ppNil
        | Some term ->
            ppConcat [
              ppString " = ",
              ppATerm term
            ])
    ]

  op ppAProperty : fa (a) AProperty a -> Doc
  def ppAProperty (propType, name, tyVars, term) =
    ppConcat [
      ppPropertyType propType,
      ppString " ",
      ppString name,
      ppString " ",
      (case tyVars of
        | [] -> ppNil
        | _ -> 
           ppConcat [
             ppString "fa (",
             ppSep (ppString ",") (map ppString tyVars),
             ppString ") "
           ]),
      ppString " ",
      ppATerm term
    ]

  op ppPropertyType : PropertyType -> Doc
  def ppPropertyType propType =
    case propType of
      | Axiom -> ppString "axiom"
      | Theorem -> ppString "theorem"
      | Conjecture -> ppString "conjecture"
%       | any ->
%            fail ("No match in ppPropertyType with: '"
%               ^ (Lisp_toString any)
%               ^ "'")

  op ppFixity : Fixity -> Doc
  def ppFixity fix =
    case fix of
      | Infix (Left,n) ->
          ppConcat [
            ppString "infixl ",
            ppString (Nat.toString n)
          ]
      | Infix (Right,n) ->
          ppConcat [
            ppString "infixr ",
            ppString (Nat.toString n)
          ]
      | Nonfix -> ppNil % ppString "Nonfix"
%       | any ->
%            fail ("No match in ppFixity with: '"
%               ^ (Lisp_toString any)
%               ^ "'")

  op ppASort : fa (a) ASort a -> Doc
  def ppASort srt = ppString (printSort srt)

  op ppATerm : fa (a) ATerm a -> Doc
  def ppATerm term = ppString (printTerm term)
}
\end{spec}
