(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CodeGenUtilities qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Environment

import /Languages/MetaSlang/CodeGen/Generic/LanguageMorphism

% this is used to distinguish "real" product from "record-products"
 op productfieldsAreNumbered: [a] List (String * a) -> Bool
def productfieldsAreNumbered (fields) =
  let
    def fieldsAreNumbered0 (i, fields) =
      case fields of
	| [] -> true
	| (id, _)::fields -> id = Nat.show (i) && fieldsAreNumbered0 (i+1, fields)
  in
  fieldsAreNumbered0 (1, fields)

op getPatternAndTermFromType (typ : MSType) : MSPattern * MSTerm =
  %% Get pattern which decomposes an argument of the given type, 
  %% plus a term of the given type made by referencing vars from that pattern.
  let
    def mkVarPatAndTerm (id, typ) =
      (VarPat ((id, typ), noPos),
       Var    ((id, typ), noPos))
  in
  case typ of
    | Product (fields, _) ->
      if productfieldsAreNumbered fields then
        let pat  = RecordPat (map (fn (field_id, field_type) -> 
                                     let var       = ("x"^field_id, field_type) in
                                     let field_pat = VarPat (var, noPos) in
                                     (field_id, field_pat))
                                  fields, 
                              noPos)
        in
        let term = Record (map (fn (field_id, field_type) -> 
                                  let var      = ("x"^field_id, field_type) in
                                  let field_tm = Var (var, noPos) in
                                  (field_id, field_tm))
                               fields, 
                           noPos)
        in
        (pat, term)
      else 
        mkVarPatAndTerm ("x", typ)
    | _ -> 
      (mkVarPatAndTerm ("x", typ))

 op getAccessorOpName: String * QualifiedId * String -> QualifiedId
def getAccessorOpName (srtName, qid as Qualified (q, id), accid) =
  let sep = "_" in
  Qualified (q, "project"^sep^srtName^sep^accid)

op getRecordConstructorOpName: QualifiedId  -> QualifiedId
def getRecordConstructorOpName (qid as Qualified (q, id)) =
  let sep = "_" in
  Qualified (q, "mk_Record"^sep^id)


(**
 * looks in the spec for a user type matching the given type; if a matching
 * user type exists.
 *)
op findMatchingUserTypeOption: Spec * MSType -> Option MSType
def findMatchingUserTypeOption (spc, srtdef) =
  case srtdef of
    | Base    _ -> Some srtdef
    | Boolean _ -> Some srtdef
    | Product ([],_) -> Some srtdef
    | _ ->
      let srts = typesAsList spc in
      let srtPos = typeAnn srtdef in
      let foundSrt = findLeftmost (fn (q, id, info) ->
                                     case typeInfoDefs info of
                                       | [srt] -> 
                                         equalType? (srtdef, typeInnerType srt) %% also reasonable:  equivType? spc (srtdef, typeInnerType srt) 
                                       |_ -> false)
                          srts 
      in
	case foundSrt of
	  | Some (q, classId, _) -> 
            %let _ = writeLine("matching user type found: type "^classId^" = "^printType srtdef) in
            Some (Base (mkUnQualifiedId (classId), [], srtPos))
	  | None -> None
	    %let _ = writeLine ("no matching user type found for "^printType srtdef) in
	    %srtdef

(**
 * looks in the spec for a user type matching the given type; if a matching
 * user type exists, the corresponding type will be returned, otherwise the type
 * given as input itself will be returned
 *)
op findMatchingUserType: Spec * MSType -> MSType
def findMatchingUserType (spc, srt) =
  case findMatchingUserTypeOption (spc, srt) of
    | Some s -> 
      %let _ = writeLine("matching user type: "^(printType srt)^" ===> "^(printType s)) in 
      s
    | None -> srt

  (**
    unfolds a type, only if it is an alias for a Product, otherwise it's left unchanged;
    this is used to "normalize" the arrow types, i.e. to detect, whether the first argument of
    an arrow type is a product or not. Only "real" products are unfolded, i.e. type of the
    form (A1 * A2 * ... * An) are unfolded, not those of the form {x1:A1, x2:A2, ..., xn:An}
  *)
  op unfoldToProduct: Spec * MSType -> MSType
  def unfoldToProduct (spc, srt) =
    let
      def unfoldRec srt =
	let usrt = unfoldBase (spc, srt) in
	if usrt = srt then srt else unfoldRec (usrt)

    in
    let usrt = unfoldRec srt in
    case usrt of
      | Product (fields, _) -> if productfieldsAreNumbered (fields) then usrt else srt
      | _ -> srt

 op inferTypeFoldRecords: Spec * MSTerm -> MSType
 def inferTypeFoldRecords (spc, term) =
  let srt = inferType (spc, term) in
  %let _ = writeLine ("inferType ("^printTerm (term)^") = "^printType srt) in
  case srt of
    | Product _ -> 
      let srt0 = findMatchingUserType (spc, srt) in
      %let _ = writeLine ("findMatchingUserType ("^printType srt^") = "^printType (srt0)) in
      srt0
    | CoProduct _ -> 
      let srt0 = findMatchingUserType (spc, srt) in
      %let _ = writeLine ("findMatchingUserType ("^printType srt^") = "^printType (srt0)) in
      srt0
    | _ -> srt

end-spec
