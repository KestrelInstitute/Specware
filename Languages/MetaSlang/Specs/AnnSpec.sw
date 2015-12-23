(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AnnSpec qualifying spec

 import Position
 import MSTerm
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import QualifierMapAsSTHTable2
 import /Languages/MetaSlang/AbstractSyntax/Equalities

% NOTE: importing Proof creates a circular import
% import Proof
type Proof.Proof

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% StandardAnnotation is the annotation of fully resolved specs and terms
 %% i.e., types Spec, Term, Type etc. Currently it is just Position,
 %% conceivably it could be more interesting in the future.

 % type StandardAnnotation = Position	% was ()

 type Spec = ASpec StandardAnnotation

 type TypeInfo = ATypeInfo StandardAnnotation 
 type OpInfo   = AOpInfo   StandardAnnotation

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ASpec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ASpecs b = List (ASpec b)

 type ASpec b = {
		 types     : ATypeMap      b,
		 ops       : AOpMap        b,
		 elements  : ASpecElements b,
		 qualifier : Option Qualifier
		}

 type ATypeMap  b = AQualifierMap (ATypeInfo b) % i.e., Qualifier -> Id -> info
 type AOpMap    b = AQualifierMap (AOpInfo   b) % i.e., Qualifier -> Id -> info

 type ATypeInfo b = {
		     names : TypeNames, %When can there be more than one name?
		     dfn   : AType b
 		    }

 type AOpInfo   b = {
		     names           : OpNames,
		     fixity          : Fixity,
		     dfn             : ATerm b,
		     fullyQualified? : Bool  % true when no unqualified ops appear in body.  Make it false for new ops?
		    }

 type ASpecElements b  = List (ASpecElement b)
 type ASpecElement b =
    % For Import, the SpecElements argument has been filtered to
    % remove redundant imports (things imported before this import in
    % the over-arching spec that contains this import).  This helps
    % prevent imported specs from being printed over and over.
   | Import   SCTerm * Spec * SpecElements * b
   | Type     QualifiedId * b
   | TypeDef  QualifiedId * b
     % For Op, the Bool flag means def was supplied as part of decl
   | Op       QualifiedId * Bool * b
   % An OpDef gives one of the definitions of an op: multiple
   % definitions come from uses of "refine def"; the Nat gives the
   % ordering of the refined definitions, while the Proof ensures that
   % the given def is a refinement of the previous one
   | OpDef    QualifiedId * Nat  * Option Proof * b
   | Property (AProperty b)
   | Comment  String * b
   | Pragma   String * String * String * b

 type SpecElement  = ASpecElement  StandardAnnotation
 type SpecElements = ASpecElements StandardAnnotation

 op [a] propertyElement? (p : ASpecElement a) : Bool =
   case p of
     | Property _ -> true
     | _ -> false

 type AProperty    a = PropertyType * PropertyName * TyVars * ATerm a * a
 type PropertyType   = | Axiom | Theorem | Conjecture
 type AProperties  a = List (AProperty a)
 type Property       = AProperty   StandardAnnotation
 type Properties     = AProperties StandardAnnotation

 op [b] elementAnn(el: ASpecElement b): b =
   case el of
     | Import(_,_,_,a) -> a
     | Type(_,a) -> a
     | TypeDef(_,a) -> a
     | Op(_,_,a) -> a
     | OpDef(_,_,_,a) -> a
     | Property(_,_,_,_,a) -> a
     | Comment(_,a) -> a
     | Pragma(_,_,_,a) -> a



 op  primaryTypeName : [b] ATypeInfo b -> TypeName
 op  primaryOpName   : [b] AOpInfo   b -> OpName
 op  propertyName    : [b] AProperty b -> PropertyName

 def primaryTypeName info = head info.names
 def primaryOpName   info = head info.names
 def propertyName    p    = p.2

 type MetaTransform.TypedFun      % Defined in /Languages/MetaSlang/Transformations/MetaTransform
 type MetaTransform.AnnTypeValue  % Defined in /Languages/MetaSlang/Specs/Utilities

 type PathTerm.Path = List Nat

 % A RuleSpec records what transformation was used to refine an op
 % We introduce uninterpreted types for the various "proof representations" for transforms.
 type MergeRules.TraceTree
 op MergeRules.printMergeRulesProof(spc:Spec)(pr:MSTerm -> String)(boundVars:MSVars)(t:TraceTree)(q:List QualifiedId)(smtArgs:List QualifiedId):String
  op MergeRules.mergeRulesPredicate (t:TraceTree, orig_postCondn: MSTerm) : MSTerm

 type RuleSpec =
   | Unfold      QualifiedId % replace a name with its def
   | Fold        QualifiedId % replace a def with a name
   | Rewrite     QualifiedId % like unfold one step of a pattern-matching fun
   | LeftToRight QualifiedId % apply an equality theorem
   | RightToLeft QualifiedId % apply an the inverse of an equality theorem
   | Omit        QualifiedId % omit an automatically included rule
   | RLeibniz    QualifiedId % post-condition strengthening, replacing f x = f y by x = y
   | Strengthen  QualifiedId % strengthen with an implication: use x -> y to replace y with x
   | Weaken      QualifiedId % weaken with an implication: use x -> y to replace x with y
   | MetaRule    (QualifiedId * TypedFun * AnnTypeValue) % user-supplied transform
   | TermTransform (Id * TypedFun * AnnTypeValue) % user-supplied transform (overlaps MetaRule?)
   | SimpStandard % Isabelle's simplifier
   | RenameVars  (List(Id * Id)) % change bound variables in a term
   | AbstractCommonExpressions % replace repeated subexpressions with a let-binding
   | Eval % partial evaluation
   | Context % using context info in rewriting a term; e.g., p -> true in q of "if p then q else r"
   | AllDefs % ??? not used
   | MergeRulesTransform (TraceTree * List QualifiedId * List QualifiedId) % A mergerules proof

 type RuleSpecs = List RuleSpec


% FIXME emw4: remove this
 % op defaultRefinementProofLike(prf: RefinementProof): RefinementProof =
 %   case prf of
 %     | RefineEq _ -> RefineEq defaultEqProof
 %     | RefineStrengthen _ -> RefineStrengthen defaultImplProof
 %     | RefineDefOp _ -> RefineDefOp defaultPRedicateProof


% FIXME emw4: remove this
 % The following "smart constructors" for EqProofs implement a rewrite
 % system that transforms equality proofs into, hopefully, leading to
 % smaller proofs. The rewrite system is:
 %
 % Trans (Trans (pf1, ..., pfk), Trans (pf1', ..., pfn'))
 %   --> Trans (pf1, ..., pfk, pf1', ..., pfn')
 % Trans (Trans (pf1, ..., pfk), pf')  --> Trans (pf1, ..., pfk, pf')
 % Trans (pf, Trans (pf1, ..., pfk))  --> Trans (pf, pf1, ..., pfk)
 % Sym (Trans (pf1, ..., pfn)) --> Trans (Sym pf1, ..., Sym pfn)
 % Sym (Sym pf) --> pf
 % Sym (Subterm pf) --> Subterm (Sym pf)
 % Subterm (path1, Subterm (path2, pf)) --> Subterm (path1 ++ path2, pf)
 %
 % This essentially pushes Sym components to the leaves of the proof,
 % flattens Trans'es, and combines nested Subterm proofs. Note that
 % the smart constructors always assume that their arguments were
 % themselves built with smart constructors, i.e., that they already
 % been rewritten.


% FIXME emw4: remove the following two functions

% op optimizeEqProofSubterms (pf: EqProof): EqProof =
%    mappEqProof
%      (fn pfi -> case pfi of
%                   | EqProofTrans(pf_term_list, EqProofSubterm(last_path, last_pf))
%                       | forall? (fn (pf_term_i, _) -> embed? EqProofSubterm pf_term_i) pf_term_list ->
%                     let common_path = foldl (fn (r_path, (EqProofSubterm(i_path, _), _)) ->
%                                                longestCommonSuffix(r_path, i_path))
%                                         last_path pf_term_list
%                     in
%                     if common_path = [] then pfi
%                     else
%                     let common_path_len = length common_path in
%                     EqProofSubterm(common_path,
%                                    EqProofTrans(map (fn (EqProofSubterm(i_path, pf_i), tm_i) ->
%                                                        (mkEqProofSubterm(removeSuffix(i_path, common_path_len), pf_i),
%                                                         fromPathTerm(tm_i, common_path)))
%                                                   pf_term_list,
%                                                 mkEqProofSubterm(removeSuffix(last_path, common_path_len), last_pf)))
%                   | EqProofSubterm(path1, EqProofSubterm(path2, prf)) ->
%                     EqProofSubterm(path2 ++ path1, prf)
%                   | _ -> pfi)
%      pf

%  op mappEqProof : (EqProof -> EqProof) -> EqProof -> EqProof
%  def mappEqProof f pf =
%    let s_pf =
%        case pf of
%          | EqProofSubterm (path, sub_pf) -> EqProofSubterm (path, mappEqProof f sub_pf)
%          | EqProofSym pf -> EqProofSym (mappEqProof f pf)
%          | EqProofTrans (pf_term_list, last_pf) ->
%            EqProofTrans
%              (map (fn (pf,tm) -> (mappEqProof f pf, tm)) pf_term_list,
%               mappEqProof f last_pf)
%          | _ -> pf
%    in
%    f s_pf

 op contextRuleQualifier: Id = "-context-"
 op showQid(Qualified(q, nm): QualifiedId): String =
   if q = UnQualified then nm
     else if q = contextRuleQualifier then "\""^nm^"\""
     else q^"."^nm


 op metaRuleATV(rl: RuleSpec): AnnTypeValue =
   let MetaRule(_, _, atv) = rl in
   atv

 op showRuleSpec(rs: RuleSpec): String =
   case rs of
     | Unfold  qid     -> "unfold " ^ show qid
     | Fold    qid     -> "fold " ^ show qid
     | Rewrite qid     -> "rewr " ^ show qid
     | LeftToRight qid -> "lr " ^ showQid qid
     | RightToLeft qid -> "rl " ^ showQid qid
     | Omit qid        -> "omit " ^ showQid qid
     | RLeibniz    qid -> "revleibniz " ^ show qid
     | Strengthen  qid -> "strengthen " ^ show qid
     | Weaken      qid -> "weaken " ^ show qid
     | MetaRule   (qid, _, _) -> "meta-rule " ^ show qid
     | TermTransform (id, _, _) -> "transform " ^ id
     | RenameVars binds -> "rename [" ^ (foldr (fn ((id1, id2), r) -> "("^id1^", "^id2^")"^(if r = "" then r else ", "^r)) "" binds)
                                 ^ "]"
     | SimpStandard -> "simplify"
     | AbstractCommonExpressions -> "abstractCommonExpressions"
     | Eval -> "eval"
     | Context -> "context"
     | AllDefs -> "alldefs"

 op reverseRuleSpec(rs: RuleSpec): RuleSpec =
   case rs of
     | Unfold qid -> Fold qid
     | Fold qid -> Unfold qid
     | Rewrite qid -> Fold qid
     | LeftToRight qid -> RightToLeft qid
     | RightToLeft qid -> LeftToRight qid
     | _ -> (warn("Trying to reverse rule "^showRuleSpec rs))

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  definedTypeInfo? : [b] ATypeInfo b -> Bool
 def definedTypeInfo? info =
   definedType? info.dfn

 op  definedType? : [b] AType b -> Bool
 def definedType? srt =
   case srt of
     | Any _           -> false
     | Pi  (_, srt, _) -> definedType? srt
     | And (srts,   _) -> exists? definedType? srts
     | _               -> true

 op [b] definedOpInfo? (info : AOpInfo b) : Bool =
   definedTerm? info.dfn

 op [b] definedTerm? (tm : ATerm b) : Bool =
   case tm of
     | Any        _                  -> false               % op foo : Nat
     | Lambda     ([(_,_,body)],  _) -> definedTerm? body   % e.g., "op foo (n : Nat) : Nat" will see internal "fn n -> any" as undefined
     | TypedTerm  (tm, _,         _) -> definedTerm? tm
     | Pi         (_, tm,         _) -> definedTerm? tm
     | Apply      (f, _, _)          -> definedTerm? f
     | And        ([],            _) -> false
     | And        (tm1 :: _,      _) -> definedTerm? tm1
     | _                             -> true

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of typeInfo
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  typeInfoDefs : [b] ATypeInfo b -> List (AType b)
 def typeInfoDefs info =
   case info.dfn of
     | And (srts, _) -> filter definedType? srts
     | srt           -> filter definedType? [srt]

 op  typeInfoDeclsAndDefs : [b] ATypeInfo b -> List (AType b) * List (AType b)
 def typeInfoDeclsAndDefs info =
   let
     def segregate srts =
       foldl (fn ((decls, defs), srt) ->
	      if definedType? srt then
		(decls, defs ++ [srt])
	      else
		(decls ++ [srt], defs))
             ([], [])
             srts
   in
     case info.dfn of
       | And (srts, _) -> segregate srts
       | srt           -> segregate [srt]

 op  typeDefs : [b] AType b -> List (AType b)
 def typeDefs srt =
   case srt of
     | And (srts, _) -> filter definedType? srts
     | srt           -> filter definedType? [srt]

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of opInfo
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  opInfoAllDefs : [b] AOpInfo b -> List (ATerm b)
 def opInfoAllDefs info =
   % TODO What about intervening Pi's or TypedTerms ?
   case info.dfn of
     | And (tms, _) -> tms
     | tm           -> [tm]

 op  opInfoDefs : [b] AOpInfo b -> List (ATerm b)
 def opInfoDefs info =
   case info.dfn of
     | And (tms, _) -> filter definedTerm? tms
     | tm           -> filter definedTerm? [tm]

 % Will there always be exactly one decl?
 op [b] opInfoDeclsAndDefs (info : AOpInfo b) : List (ATerm b) * List (ATerm b) =
   termDeclsAndDefs info.dfn

 % Will there always be exactly one decl?
 op [b] termDeclsAndDefs (tm : ATerm b) : List (ATerm b) * List (ATerm b) =
   % let _ = writeLine("termDeclsAndDefs:\n"^printTerm tm) in
   let a = termAnn tm in
   let def segregate(tm, tvs, o_ty, tms) =
         case tm of
           | Pi (tvs, tm, _) -> segregate(tm, tvs, o_ty, tms)
           | And (a_tms,_) ->
             foldl (fn ((tvs, o_ty, tms), tm) -> segregate(tm, tvs, o_ty, tms)) (tvs, o_ty, tms) a_tms
           | TypedTerm (tm, ty, _) -> segregate(tm, tvs, if some? o_ty then o_ty else Some ty, tms)
           | Any _ -> (tvs, o_ty, tms)
           | _ -> (tvs, o_ty, (maybePiTypedTerm(tvs, o_ty, tm)) :: tms)
   in
   case segregate(tm, [], None, []) of
     | (tvs, Some ty, tms) -> ([maybePiTerm(tvs, TypedTerm(Any a, ty, a))], reverse tms)
     | (tvs, None, tms)    -> ([maybePiTerm(tvs, Any a)], reverse tms)

% op  termDeclsAndDefs : [b] ATerm b -> List (ATerm b) * List (ATerm b)
%  def termDeclsAndDefs tm =
%    let
%      def segregate tms =
%        foldl (fn ((decls, defs), tm) ->
% 	      if definedTerm? tm then
% 		(decls, defs ++ (andTerms [tm]))
% 	      else
% 		(decls ++ [tm], defs))
%              ([], [])
%              tms
%    in
%      case flattenAnds tm of
%        | And (tms, _) -> segregate tms
%        | tm           -> segregate [tm]

 op  termDefs : [b] ATerm b -> List (ATerm b)
 def termDefs tm =
   case tm of
     | And (tms, _) -> filter definedTerm? tms
     | tm           -> filter definedTerm? [tm]

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of primary type def
 %%%  Any uses of these simply ignore any definitions after the
 %%%  first one, which (IMHO) is probably not a good thing to do,
 %%%  but they are here for backwards compatibility
 %%%  Each use should be reviewed.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  firstTypeDef          : [b] ATypeInfo b -> AType b
 op  unpackFirstTypeDef    : [b] ATypeInfo b -> TyVars * AType b
 op  firstTypeDefTyVars    : [b] ATypeInfo b -> TyVars
 op  firstTypeDefInnerType : [b] ATypeInfo b -> AType b

 def firstTypeDef info =
   let (decls, defs)  = typeInfoDeclsAndDefs info in
   case defs ++ decls of
     | first_def :: _ -> first_def
     | _ -> (fail("No decls or defs for: "^anyToString info))

 def unpackFirstTypeDef info =
   unpackType (firstTypeDef info)

 def firstTypeDefTyVars info =
   case info.dfn of
     | And([], _) -> []
     | _ -> typeTyVars (firstTypeDef info)

 def firstTypeDefInnerType info =
   typeInnerType (head (typeInfoDefs info)) % fail if no decl but no def

 %%% Qualification flag
 op qualifiedSpec?  : [a] ASpec a -> Bool
 op markQualified   : [a] ASpec a -> Qualifier -> ASpec a
 op markUnQualified : [a] ASpec a              -> ASpec a

 def qualifiedSpec?  spc = case spc.qualifier of Some _ -> true | _ -> false
 def markQualified   spc q = spc << {qualifier = if q = UnQualified then None else Some q}
 def markUnQualified spc   = spc << {qualifier = None}

 %% A Spec with qualifier = Some dummyQualifier is fully qualified
 op dummyQualifier: Id = "<dummy qualifier>"
 op markQualifiedStatus(spc: Spec): Spec =
   if qualifiedSpec? spc then spc
     else if existsSpecElement? unQualifiedSpecElement? spc.elements
      then spc
      else markQualified spc dummyQualifier

 op unQualifiedSpecElement?(el: SpecElement): Bool =
   case el of
     % | Import (_, spc, _, _) ->
     %   ~(qualifiedSpec? spc) 
       % redundant?  && existsSpecElement? unQualifiedSpecElement? elts
     | Type(Qualified(q, _),_) -> q = UnQualified
     | TypeDef(Qualified(q, _),_) -> q = UnQualified
     | Op(Qualified(q, _),_,_) -> q = UnQualified
     | OpDef(Qualified(q, _),_,_,_) -> q = UnQualified
     | _ -> false

 op defaultQualifier(spc: Spec): Id =
    case spc.qualifier of
      | None -> UnQualified
      | Some qual -> qual

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of primary op def
 %%%  Any uses of these simply ignore any definitions after the
 %%%  first one, which (IMHO) is probably not a good thing to do,
 %%%  but they are here for backwards compatibility
 %%%  Each use should be reviewed.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  firstOpDef          : [b] AOpInfo b -> ATerm b
 op  unpackFirstOpDef    : [b] AOpInfo b -> TyVars * AType b * ATerm b
 op  firstOpDefTyVars    : [b] AOpInfo b -> TyVars
 op  firstOpDefInnerType : [b] AOpInfo b -> AType b
 op  firstOpDefInnerTerm : [b] AOpInfo b -> ATerm b

 def firstOpDef info =
   let (decls, defs)  = opInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   first_def

 def unpackFirstOpDef info =
   unpackFirstTerm (info.dfn)

 op [a] unpackNthOpDef(info: AOpInfo a, n: Nat): TyVars * AType a * ATerm a =
   unpackNthTerm(info.dfn, n)

 def firstOpDefTyVars info =
   termTyVars (firstOpDef info)

 def firstOpDefInnerType info =
   let (decls, defs)  = opInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   case first_def of
     | Pi (_, tm, _) -> termType tm % avoid returning Pi type
     | tm            -> termType tm

 def firstOpDefInnerTerm info =
   termInnerTerm (head (opInfoDefs info)) % fail if decl but no def

 %%% Support for multiple defs

 op [a] opDefInnerTerms(info: AOpInfo a): List(ATerm a) =
   innerTerms info.dfn

 op [a] numRefinedDefs (spc: ASpec a) (qid: QualifiedId): Nat =
   case findTheOp(spc, qid) of
     | None -> 0
     | Some opinfo ->
   %let (_, _, full_dfns) = unpackTerm opinfo.dfn in
   %% full_dfns will omit terms such as (fn x -> <any>) if alternatives such as (fn x -> f x) exist
   length (unpackTypedTerms opinfo.dfn)

op [a] polymorphic? (spc: ASpec a) (qid: QualifiedId): Bool =
  case findTheOp(spc, qid) of
    | None -> false
    | Some info -> (unpackFirstOpDef info).1 ~= []

op [a] typeOfOp (spc: ASpec a) (qid: QualifiedId): TyVars * AType a =
  let Some info = findTheOp(spc, qid) in
  let (tvs, ty, _) = unpackFirstOpDef info in
  (tvs, ty)

op addNewOp(new_op_qid as Qualified(new_op_qualifier, new_op_base_name): QualifiedId,
            new_op_fixity : Fixity,
            new_op_body : ATerm StandardAnnotation,
            spc : Spec) : Spec =

  %% Deconstruct the existing spec.  The ops and elements will be updated (but not the types or qualifier):
  let elements = spc.elements in
  let op_map = spc.ops in

  %% Build the new op:
  let new_op_names = [new_op_qid] in %% Only a single name is allowed.
  let fullyQualified? = false in %% TODO I don't understand this field.  Most ops seem to have false.
  let new_op_info = {names=new_op_names, fixity=new_op_fixity, dfn=new_op_body, fullyQualified?=fullyQualified?} in

  %% Assemble the new spec:
  let new_op_map = insertAQualifierMap(op_map, new_op_qualifier, new_op_base_name, new_op_info) in
  %% TODO This causes the element list to be reconsed, but I don't want to put the new stuff on the front (do I?)...
  let position = Internal "Created by Transformation" in %% TODO Do something better?  addNewOp could take the name of the transformation as an argument or even a descriptive strings (e.g., "From partially evaluating XXX.").
  let new_elements = elements ++ [Op(new_op_qid, true, position)] in
  spc << {ops = new_op_map, elements = new_elements}


op addDef(spc: Spec, op_info: OpInfo, new_dfn: MSTerm): Spec =
  let qid as Qualified(q, id) = primaryOpName op_info in
  let (new_tvs, new_ty, new_tm) = unpackTerm new_dfn in
  let (tvs, ty)
     = case unpackTypedTerms op_info.dfn of
         | (old_tvs, old_ty, _)::_ -> (old_tvs, old_ty)
         | [] -> (new_tvs, new_ty)
  in
  let new_defn =  maybePiTerm(tvs, TypedTerm(new_tm, ty, termAnn new_tm)) in
  let new_op_info = op_info << {dfn = new_dfn} in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, new_op_info),
          elements = spc.elements ++ [OpDef (qid, 0, None, noPos)]}


op addRefinedDefToOpinfo (info: OpInfo, new_dfn: MSTerm): OpInfo =
  let old_triples = unpackTypedTerms info.dfn in
  let qid as Qualified(q, id) = primaryOpName info in
  % let _ = writeLine("addRefinedDefToOpinfo: "^show qid^"\nOld:\n" ^printTerm info.dfn^"\nNew:\n"^printTerm new_dfn) in
  let new_triple = case new_dfn of
                     | TypedTerm (new_tm, new_ty, _) -> ([], new_ty, new_tm)
                     | _ -> 
                       let (old_tvs, old_ty, _) :: _ = old_triples in
                       (old_tvs, old_ty, new_dfn)
  in
  % let new_dfns = case curr_dfns of
  %                  | [] -> [new_dfn]
  %                  | last_def :: _ ->
  %                    if equalTerm?(new_dfn, last_def) then curr_dfns
  %                      else new_dfn :: curr_dfns
  % in
  let new_triples = new_triple :: old_triples in
  let new_dfn = maybePiAndTypedTerm new_triples in
  % let _ = writeLine("\naddRefinedDefToOpinfo "^show qid^":\n"^printTerm new_dfn) in
  info << {dfn = new_dfn}

op addRefinedDef(spc: Spec, info: OpInfo, new_dfn: MSTerm): Spec =
  addRefinedDefH(spc, info, new_dfn, None)

op addRefinedDefH(spc: Spec, info: OpInfo, new_dfn: MSTerm, pf: Option Proof): Spec =
  let qid as Qualified(q, id) = primaryOpName info in
  let new_opinfo = addRefinedDefToOpinfo(info, new_dfn) in
  % let _ = writeLine(show(numTerms new_opinfo.dfn)) in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, new_opinfo),
          elements = spc.elements ++ [OpDef (qid, max(0, numTerms new_opinfo.dfn - 1), pf, noPos)]}

op addRefinedTypeToOpinfo (info: OpInfo, new_ty: MSType, new_tm: Option MSTerm): OpInfo =
  let qid as Qualified(q, id) = primaryOpName info in
  let triples = unpackTypedTerms(info.dfn) in
  let def termDef (old_tm:MSTerm) = case new_tm of | Some t -> t | None -> old_tm in
  let new_full_dfn = case triples of
                       | [] -> TypedTerm (Any (typeAnn new_ty), new_ty, typeAnn new_ty)
                       | (tvs, _, old_tm) ::_ ->
                         % let _ = writeLine ("Adding refined type " ^ printType new_ty) in
                         maybePiAndTypedTerm (([], new_ty, termDef old_tm) :: triples)
  in
  % let _ = if show qid = "insertBlack"
  %          then writeLine("addRefinedType: "^show qid^"\n"^printTerm info.dfn^"\n"^printTerm new_full_dfn^"\n\n") else () in
  info << {dfn = new_full_dfn}

op addRefinedType(spc: Spec, info: OpInfo, new_ty: MSType): Spec =
  addRefinedTypeH(spc, info, new_ty, None, None)

%% addRefinedTypeH takes a new term, which is strange. However, it is
%% needed in the case where the precondition is changed. 
op addRefinedTypeH(spc: Spec, info: OpInfo, new_ty: MSType, new_tm: Option MSTerm, pf: Option Proof): Spec =
  let qid as Qualified(q, id) = primaryOpName info in
  let new_opinfo = addRefinedTypeToOpinfo(info, new_ty, new_tm) in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, new_opinfo),
          elements = spc.elements ++ [OpDef (qid, max(0, numTerms new_opinfo.dfn - 1), pf, noPos)]}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%                Recursive TSP map over Specs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "TSP" means "Term, Type, Pattern"

%%% Can't make mapSpec polymorphic because elements in imports have to be Standard

type TSP_Maps_St = TSP_Maps StandardAnnotation
op  mapSpec : TSP_Maps_St -> Spec -> Spec
def mapSpec tsp spc =
  spc << {
          types        = mapSpecTypes      tsp spc.types,
          ops          = mapSpecOps        tsp spc.ops,
          elements     = mapSpecProperties tsp spc.elements
         }

op  mapSpecTypes : [b] TSP_Maps b -> ATypeMap b -> ATypeMap b
def mapSpecTypes tsp types =
  mapTypeInfos (fn info -> info << {dfn = mapType tsp info.dfn})
               types

 op testing? : Bool = false
 op nnn : Nat = 0

 op fooincr () : () = ()

 op [a] foofoo (second? : Bool, msg : String, x : a) : () = 
   if testing? then 
     let _ = writeLine ("nnn = " ^ Nat.show nnn ^ ", " ^ Bool.show second?) in
     let _ = writeLine (msg ^ anyToString x)  in
     if second? then fooincr () else ()
   else 
     ()

 op  mapSpecOps : [b] TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOps tsp ops =
   mapOpInfos (fn info -> 
                 let _ = foofoo (false, "old info: ", info) in
                 let new_info = info << {dfn = mapTerm tsp info.dfn} in
                 let _ = foofoo (true, "new info: ", new_info) in
                 new_info)
              ops

op [a] mapSpecLocalOps (tsp: TSP_Maps a) (spc: ASpec a): ASpec a =
  let def mapOpDef(qid as Qualified(q, id), refine_num, ops) =
        case findTheOp(spc, qid) of
          | Some opinfo | primaryOpName?(q, id, opinfo) ->
            let trps = unpackTypedTerms (opinfo.dfn) in
            let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
            let new_tm = MetaSlang.mapTerm tsp tm in
            if equalTerm?(tm, new_tm) then ops
            else
              let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, new_tm))) in
              insertAQualifierMap(ops, q, id, opinfo << {dfn = new_dfn})                                       
          | _ -> ops
  in
  spc << {ops = foldl (fn (ops, el) ->
                       case el of
                         | Op(qid, true, _) -> mapOpDef(qid, 0, ops)
                         | OpDef(qid, refine_num, _, _) -> mapOpDef(qid, refine_num, ops)
                         | _ -> ops)
                  spc.ops spc.elements}

op [a] mapSpecLocals (tsp: TSP_Maps a) (spc: ASpec a): ASpec a =
  let def mapOpDef(qid as Qualified(q, id), refine_num, spc) =
        case findTheOp(spc, qid) of
          | Some opinfo | primaryOpName?(q, id, opinfo) ->
            let trps = unpackTypedTerms (opinfo.dfn) in
            let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
            let new_ty =  MetaSlang.mapType tsp ty in
            let new_tm = MetaSlang.mapTerm tsp tm in
            if tm = new_tm && ty = new_ty   %equalTerm?(tm, new_tm) && equalType?(ty, new_ty)
              then spc
            else
              let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, new_ty, new_tm))) in
              spc << {ops = insertAQualifierMap(spc.ops, q, id, opinfo << {dfn = new_dfn})}                                       
          | _ -> spc
      def mapTypeDef(qid as Qualified(q, id), spc) =
        case findTheType(spc, qid) of
          | Some typeinfo | primaryTypeName?(q, id, typeinfo) ->
            let (tvs, ty_dfn) = unpackType (typeinfo.dfn) in
            let new_ty_dfn = MetaSlang.mapType tsp ty_dfn in
            if equalType?(ty_dfn, new_ty_dfn) then spc
            else
              let new_ty_dfn = maybePiType(tvs, new_ty_dfn) in
              spc << {types = insertAQualifierMap(spc.types, q, id, typeinfo << {dfn = new_ty_dfn})}                                  
          | _ -> spc
  in
  let spc = setElements(spc, map (fn el ->
                                    case el of
                                      | Property (pt, nm, tvs, term, a) ->
                                        Property (pt, nm, tvs, mapTerm tsp term, a)
                                      | _ -> el)
                               spc.elements)
  in
  foldl (fn (spc, el) ->
          case el of
            | Op(qid, _, _) -> mapOpDef(qid, 0, spc)
            | OpDef(qid, refine_num, _, _) -> mapOpDef(qid, refine_num, spc)
            | TypeDef(qid, _) -> mapTypeDef(qid, spc)
            | _ -> spc)
    spc spc.elements


 %%% Only map over unqualified ops (for use in qualify)
 op  mapSpecUnqualified : TSP_Maps_St -> Spec -> Spec
 def mapSpecUnqualified tsp spc =
   spc << {
	   types        = mapSpecTypes          tsp spc.types,
	   ops          = mapSpecOpsUnqualified tsp spc.ops,
	   elements     = mapSpecProperties     tsp spc.elements
	  }

 op  mapSpecOpsUnqualified : [b] TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOpsUnqualified tsp ops =
   mapOpInfosUnqualified (fn info ->
			  info << {dfn = mapTerm tsp info.dfn,
				   fullyQualified? = true})
                         ops

 %% Useful if we know the defs from qualified specs won't be affected
 op  mapOpInfosUnqualified : [b] (AOpInfo b -> AOpInfo b) -> AOpMap b -> AOpMap b
 def mapOpInfosUnqualified opinfo_map ops =
   foldriAQualifierMap
     (fn (q, id, info, new_map) ->
      if primaryOpName? (q, id, info) && ~(info.fullyQualified?) then
	%% When access is via a primary alias, update the info and
	%% record that (identical) new value for all the aliases.
	let new_info = opinfo_map info
	in
	foldl (fn (new_map, Qualified (q, id)) ->
	       insertAQualifierMap (new_map, q, id, new_info))
	      new_map
	      info.names
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     ops
     ops

 %% mapTypeInfos and mapOpInfos apply the provided function
 %% just once to an info, even if it has multiple aliases,
 %% then arrange for each alias to index that same new info.

 op  primaryTypeName? : [a] Qualifier * Id * ATypeInfo a -> Bool
 op  primaryOpName?   : [a] Qualifier * Id * AOpInfo   a -> Bool

 def primaryTypeName? (q, id, info) =
   let Qualified (qq, ii) = primaryTypeName info in
   q = qq && id = ii

 def primaryOpName? (q, id, info) =
   let Qualified (qq, ii) = primaryOpName info in
   q = qq && id = ii

 op  mapTypeInfos : [b] (ATypeInfo b -> ATypeInfo b) -> ATypeMap b -> ATypeMap b
 def mapTypeInfos typeinfo_map types =
   foldriAQualifierMap
     (fn (q, id, info, new_map) ->
      if primaryTypeName? (q, id, info) then
	%% When access is via a primary alias, update the info and
	%% record that (identical) new value for all the aliases.
	let new_info = typeinfo_map info in
	foldl (fn (new_map, Qualified (q, id)) ->
	       insertAQualifierMap (new_map, q, id, new_info))
	      new_map
	      info.names
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     emptyAQualifierMap
     types

 op  mapOpInfos : [b] (AOpInfo b -> AOpInfo b) -> AOpMap b -> AOpMap b
 def mapOpInfos opinfo_map ops =
   let new_ops =
       mapiAQualifierMap
         (fn (q, id, info)->
          if primaryOpName? (q, id, info)
            then opinfo_map info
            else info)
         ops
   in
   foldriAQualifierMap
     (fn (q, id, info, new_ops)->
        if primaryOpName? (q, id, info)
          then new_ops
        else let Qualified (qq, ii) = primaryOpName info in
             let Some new_info = findAQualifierMap(new_ops, qq, ii) in
             insertAQualifierMap (new_ops, q, id, new_info))
     new_ops
     ops

%   foldriAQualifierMap
%     (fn (q, id, info, new_map) ->
%      if primaryOpName? (q, id, info) then
%	%% When access is via a primary alias, update the info and
%	%% ecord that (identical) new value for all the aliases.
%	let new_info = opinfo_map info in
%	foldl (fn (new_map, Qualified (q, id)) ->
%	       insertAQualifierMap (new_map, q, id, new_info))
%	      new_map
%	      info.names
%      else
%	%% For the non-primary aliases, do nothing,
%	%% since they are handled derivatively above.
%	new_map)
%     emptyAQualifierMap
%     ops

 op  filterTypeMap : [b] (ATypeInfo b -> Bool) -> ATypeMap b -> ATypeMap b
 def filterTypeMap keep? types =
   foldriAQualifierMap
     (fn (q, id, info, new_map) ->
      if primaryTypeName? (q, id, info) && keep? info then
	foldl (fn (new_map, Qualified(q, id)) ->
	       insertAQualifierMap (new_map, q, id, info))
	      new_map
	      info.names
      else
	new_map)
     emptyAQualifierMap
     types

 op  filterOpMap : [b] (AOpInfo b -> Bool) -> AOpMap b -> AOpMap b
 def filterOpMap keep? ops =
   foldriAQualifierMap
     (fn (q, id, info, new_map) ->
      if primaryOpName? (q, id, info) && keep? info then
	foldl (fn (new_map, Qualified(q, id)) ->
	       insertAQualifierMap (new_map, q, id, info))
	      new_map
	      info.names
      else
	new_map)
     emptyAQualifierMap
     ops

 op  foldTypeInfos : [a,b] (ATypeInfo a * b -> b) -> b -> ATypeMap a -> b
 def foldTypeInfos f init types =
   foldriAQualifierMap
     (fn (q, id, info, result) ->
      if primaryTypeName? (q, id, info) then
	f (info, result)
      else
	result)
     init
     types

 op [a,b] foldOpInfos (f : AOpInfo a * b -> b) (init:b) (ops : AOpMap a) : b =
   foldriAQualifierMap
     (fn (qq, idd, info, result) ->
      if primaryOpName? (qq, idd, info) then
	f (info, result)
      else
	result)
     init
     ops

 %% Check whether all opinfos satisfy the pred:
 op [a] forallOpInfos? (pred : AOpInfo a -> Bool) (ops : AOpMap a) : Bool =
   foldOpInfos (fn (x, result) -> result && pred x) true ops

 %% Check whether any opinfo satisfies the pred:
 op [a] existsOpInfo? (pred : AOpInfo a -> Bool) (ops : AOpMap a) : Bool =
   foldOpInfos (fn (x, result) -> result || pred x) false ops

 %% Count how many opinfos satisfy the pred:
 op [a] countOpInfos (pred? : AOpInfo a -> Bool) (ops : AOpMap a) : Nat =
   foldOpInfos (fn (x, result) -> result + (if pred? x then 1 else 0)) 0 ops

 %% Count how many typeinfos satisfy the pred:
 op [a] countTypeInfos (pred? : ATypeInfo a -> Bool) (types : ATypeMap a) : Nat =
   foldTypeInfos (fn (x, result) -> result + (if pred? x then 1 else 0)) 0 types


 op  appTypeInfos : [b] (ATypeInfo b -> ()) -> ATypeMap b -> ()
 def appTypeInfos f types =
   appiAQualifierMap
     (fn (q, id, info) ->
      if primaryTypeName? (q, id, info) then
	f info
      else
	())
     types

 op  appOpInfos : [b] (AOpInfo b -> ()) -> AOpMap b -> ()
 def appOpInfos f ops =
   appiAQualifierMap
     (fn (q, id, info) ->
      if primaryOpName? (q, id, info) then
	f info
      else
	())
     ops

 op  mapSpecProperties : TSP_Maps StandardAnnotation -> SpecElements -> SpecElements
 def mapSpecProperties tsp elements =
   map (fn el ->
	case el of
	  | Property (pt, nm, tvs, term, a) ->
            % let _ = writeLine("msp: "^printQualifiedId(nm)^"\n"^printTerm term) in
            Property (pt, nm, tvs, mapTerm tsp term, a)
	  | Import   (s_tm, i_sp, elts, a)  ->
            Import   (s_tm, i_sp, mapSpecProperties tsp elts, a)
	  | _ -> el)
       elements

 op  mapSpecElements: (SpecElement -> SpecElement) -> SpecElements -> SpecElements
 def mapSpecElements f elements =
   map (fn el ->
	case el of
	  | Import (s_tm, i_sp, elts, a) -> f (Import (s_tm, i_sp, mapSpecElements f elts, a))
	  | _ -> f el)
     elements

 op  mapPartialSpecElements: (SpecElement -> Option SpecElement) -> SpecElements -> SpecElements
 def mapPartialSpecElements f elements =
   mapPartial
     (fn el ->
      case f el of
	| Some (Import (s_tm, i_sp, elts, a)) ->
	  Some (Import (s_tm, i_sp, mapPartialSpecElements f elts, a))
	| new_el -> new_el)
     elements

 op  filterSpecElements: (SpecElement -> Bool) -> SpecElements -> SpecElements
 def filterSpecElements p elements =
   mapPartial
     (fn el ->
      if ~(p el) then
	None
      else
	Some(case el of
	       | Import (s_tm, i_sp, elts, a) ->
	         Import (s_tm, i_sp, filterSpecElements p elts, a)
	       | _ ->  el))
     elements

 %% Note that, for imports, this uses the list of elements with redundant imports removed.
 %% This seems to process the import element itself twice (once before processing the imported elements, and once after).
 op [a] foldlSpecElements (f: (a * SpecElement -> a)) (ini:a) (els:SpecElements) : a =
   foldl (fn (result, el) ->
	  case el of
	    | Import (_, _, elts, _) ->
	      let result1 = foldlSpecElements f (f (result, el)) elts in
	      f (result1, el)
	    | _ -> f (result, el))
         ini
	 els

 op  foldrSpecElements: [a] (SpecElement * a -> a) -> a -> SpecElements -> a
 def foldrSpecElements f ini els =
   foldr (fn (el, result) ->
	  case el of
	    | Import (s_tm, i_sp, elts, _) ->
	      let result1 = foldrSpecElements f result elts in
	      f (el, result1)
	    | _ -> f (el, result))
         ini
	 els

 op  mapFoldrSpecElements: [a] (SpecElement * a -> a) -> a -> SpecElements -> a
 def mapFoldrSpecElements f ini els =
   foldr (fn (el, result) ->
	  case el of
	    | Import (s_tm, i_sp, elts, _) ->
	      let result1 = mapFoldrSpecElements f result elts in
	      f (el, result1)
	    | _ -> f (el, result))
         ini
	 els

 op existsSpecElement? (p: SpecElement -> Bool) (els: SpecElements): Bool =
   exists? (fn el ->
              p el
                || (case el of
                      | Import (_, _, elts, _) ->
                        existsSpecElement? p elts
                      | _ -> false))
     els

 op existsSpecElementBefore? (p: SpecElement -> Bool) (limit_el: SpecElement) (els: SpecElements): Bool =
   case els of
     | []     -> false
     | hd::tl ->
       if hd = limit_el then false
        else if p hd then true
        else (case hd of
                | Import (_, _, elts, _) ->
                  existsSpecElementBefore? p limit_el elts
                | _ -> false)
           || existsSpecElementBefore? p limit_el tl

 op rdPos : Position = Internal "Remove Duplicates"


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Type, Pattern"

 type appTSP_St = appTSP StandardAnnotation

 op  appSpec : appTSP_St -> Spec -> ()
 def appSpec tsp spc =
   (
    appSpecOps      tsp spc.ops;
    appSpecTypes    tsp spc.types;
    appSpecElements tsp spc.elements
   )

 op  appSpecTypes : [a] appTSP a -> ATypeMap a -> ()
 def appSpecTypes tsp types =
   appAQualifierMap (fn info -> appType tsp info.dfn) types

 op  appSpecOps : [a] appTSP a -> AOpMap a -> ()
 def appSpecOps tsp ops =
   appAQualifierMap (fn info -> appTerm tsp info.dfn) ops

 op  appSpecElements :  appTSP_St -> SpecElements -> ()
 def appSpecElements tsp elements =
   app (fn  el ->
	case el of
	  | Property(_, _, _, term, a) -> appTerm tsp term
	  | Import (_, _, elts, a) -> appSpecElements tsp elts
	  | _ -> ())
       elements

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Types, Ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % return types/ops as list with entries of the form (qualifier, id, info)

 op typesAsList     : [b] ASpec b -> List (Qualifier * Id * ATypeInfo b)
 op opsAsList       : [b] ASpec b -> List (Qualifier * Id * AOpInfo   b)
 op typeInfosAsList : [b] ASpec b -> List (ATypeInfo b)
 op opInfosAsList   : [b] ASpec b -> List (AOpInfo   b)

 def typesAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) ->
			(q, id, info) :: new_list)
                       []
		       spc.types

 def typeInfosAsList spc =
   foldriAQualifierMap (fn (q, id, info, new_list) ->
			%% there could be multiple entries for the same typeInfo,
			%% so just consider the entry corresponding to the primary alias
			let Qualified (primary_q, primary_id) = primaryTypeName info in
			if q = primary_q && id = primary_id then
			  info :: new_list
			else
			  new_list)
                       []
		       spc.types

 def opsAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) ->
			(q, id, info) :: new_list)
                       []
		       spc.ops

 def opInfosAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) ->
			%% there could be multiple entries for the same opInfo,
			%% so just consider the entry corresponding to the primary alias
			let Qualified (primary_q, primary_id) = primaryOpName info in
			if q = primary_q && id = primary_id then
			  info :: new_list
			else
			  new_list)
                       []
		       spc.ops

 % Create a list of all the op, type, and prop names in a spec
 op allSpecNames (spc: Spec) : QualifiedIds =
    map (fn (q, id, _) -> Qualified (q, id)) (typesAsList spc)
    ++
    map (fn (q, id, _) -> Qualified (q, id)) (opsAsList spc)
    ++
    (allPropertyNames spc)


 % --------------------------------------------------------------------------------

 op  emptyTypeNames : TypeNames
 def emptyTypeNames = []

 op  emptyOpNames : OpNames
 def emptyOpNames = []

 op  emptyPropertyNames : PropertyNames
 def emptyPropertyNames = []

 op  memberNames : QualifiedId * List QualifiedId -> Bool
 def memberNames (qid, qids) = qid in? qids

 op  memberQualifiedId : Qualifier * Id * List QualifiedId -> Bool
 def memberQualifiedId (q, id, qids) =
   exists? (fn (Qualified (qq, ii)) -> q = qq && id = ii) qids

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op emptySpec         : [a] ASpec         a
 op emptyAElements    : [a] ASpecElements a
 op emptyATypeMap     : [a] AQualifierMap a
 op emptyAOpMap       : [a] AQualifierMap a
 op initialSpecInCat  : [a] ASpec         a

 %% Create new spec with altered name, imports, types, ops, elements, etc.

 op setLocalOps      : [a] ASpec a * OpNames          -> ASpec a
 op setLocalTypes    : [a] ASpec a * TypeNames        -> ASpec a
 op setLocalElements : [a] ASpec a * PropertyNames    -> ASpec a
 op setTypes         : [a] ASpec a * ATypeMap      a  -> ASpec a
 op setOps           : [a] ASpec a * AOpMap        a  -> ASpec a
 op setElements      : [a] ASpec a * ASpecElements a  -> ASpec a
 op appendElement    : [a] ASpec a * ASpecElement  a  -> ASpec a
 op prependElement   : [a] ASpec a * ASpecElement  a  -> ASpec a

 op someTypeAliasIsLocal? : [b] Aliases * ASpec b -> Bool
 op someOpAliasIsLocal?   : [b] Aliases * ASpec b -> Bool

 op getQIdIfOp: [a] ASpecElement a -> Option QualifiedId

 op localType?        : [a] QualifiedId * ASpec a -> Bool
 op localOp?          : [a] QualifiedId * ASpec a -> Bool
 op localProperty?    : [a] QualifiedId * ASpec a -> Bool
 op localProperties   : [a] ASpec a -> AProperties a
 op allProperties     : Spec -> Properties
 op allPropertyNames  : Spec -> QualifiedIds
 op localTypes        : [a] ASpec a -> List QualifiedId
 op localOps          : [a] ASpec a -> List QualifiedId
 op hasLocalType?     : [a] ASpec a -> Bool
 op hasLocalOp?       : [a] ASpec a -> Bool


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def [a] emptyAElements = []
 def emptyATypeMap      = emptyAQualifierMap
 def emptyAOpMap        = emptyAQualifierMap

 op emptySpec : Spec =
   {
    types     = emptyATypeMap,
    ops       = emptyAOpMap,
    elements  = emptyAElements,
    qualifier = None
   }

 op initialSpecInCat : Spec = emptySpec

 op copySpec (spc : Spec) : Spec =
  {types     = spc.types,
   ops       = spc.ops,
   elements  = spc.elements,
   qualifier = spc.qualifier}

 def setTypes    (spc, new_types)    = spc << {types    = new_types}
 def setOps      (spc, new_ops)      = spc << {ops      = new_ops}
 def setElements (spc, new_elements) = spc << {elements = new_elements}

 def appendElement  (spc, new_element) = spc << {elements = spc.elements ++ [new_element]}
 def prependElement (spc, new_element) = spc << {elements = new_element :: spc.elements}

 op [a] equalSpecElement?(el1: ASpecElement a, el2: ASpecElement a): Bool =
   case (el1, el2) of
     | (Import(tm1, spc1, _, _), Import(tm2, spc2, _, _)) -> tm1 = tm2 && spc1 = spc2 % ?
     | (Type(qid1, _), Type(qid2, _)) -> qid1 = qid2
     | (TypeDef(qid1, _), TypeDef(qid2, _)) -> qid1 = qid2
     | (Op(qid1, def1?,_), Op(qid2, def2?, _)) -> qid1 = qid2 && def1? = def2?
     | (OpDef(qid1, refine1?, _, _), OpDef(qid2, refine2?, _, _)) -> qid1 = qid2 && refine1? = refine2?
     | (Property(pty1, qid1, tvs1, bod1, _), Property(pty2, qid2,tvs2, bod2, _)) ->
       pty1 = pty2 && qid1 = qid2 && tvs1 = tvs2 && equalTerm?(bod1, bod2)
     | (Comment(str1, _), Comment(str2, _)) -> str1 = str2
     | (Pragma(stra1, strb1, strc1, _), Pragma(stra2, strb2, strc2, _)) ->
       stra1 = stra2 && strb1 = strb2 && strc1 = strc2
     | _ -> false

 op [a] addElementsAfter(spc: ASpec a, new_elements: ASpecElements a, old_element: ASpecElement a): ASpec a =
   spc << {elements = let elts = spc.elements in
	              let i = case findIndex (fn el -> equalSpecElement?(el, old_element)) elts of
                                | Some(i,_) -> i+1
                                | None -> length elts
                      in
		      take (i, elts) ++ new_elements ++ drop (i, elts)}

 op [a] addElementAfter(spc: ASpec a, new_element: ASpecElement a, old_element: ASpecElement a): ASpec a =
   addElementsAfter(spc, [new_element], old_element)

 op [a] addElementsBefore(spc: ASpec a, new_elements: ASpecElements a, old_element: ASpecElement a): ASpec a =
   spc << {elements = let elts = spc.elements in
	              let i = case findIndex (fn el -> equalSpecElement?(el, old_element)) elts of
                                | Some(i,_) -> i
                                | None -> length elts
                      in
		      take (i, elts) ++ new_elements ++ drop (i, elts)}

 op [a] addElementBefore(spc: ASpec a, new_element: ASpecElement a, old_element: ASpecElement a): ASpec a =
   addElementsBefore(spc, [new_element], old_element)

 op [a] deleteElement(spc: ASpec a, del_el: ASpecElement a): ASpec a =
   setElements(spc, filter (fn el -> ~(equalSpecElement?(el, del_el))) spc.elements)

 op [a] conjecture?(p: ASpecElement a): Bool =
   case p of
     | Property(Conjecture,_,_,_,_) -> true
     | _ -> false

 op [a] addElementsAfterConjecture(spc: ASpec a, new_elements: ASpecElements a, old_element: ASpecElement a): ASpec a =
   spc << {elements = let elts = spc.elements in
	              let i = case findIndex (fn el -> equalSpecElement?(el, old_element)) elts of
                                | Some(i,_) ->
                                  if i+1 < length elts && conjecture?(elts@(i+1))
                                    then i+2
                                    else i+1
                                | None -> length elts
                      in
		      take (i, elts) ++ new_elements ++ drop (i, elts)}


 def someTypeAliasIsLocal? (aliases, spc) =
   exists? (fn el ->
              case el of
                | Type (qid,_)    -> qid in? aliases
                | TypeDef (qid,_) -> qid in? aliases
                | _ -> false)
          spc.elements

 def someOpAliasIsLocal? (aliases, spc) =
   exists? (fn el ->
              case el of
                | Op    (qid,_,_) -> qid in? aliases
                | OpDef (qid,_,_,_) -> qid in? aliases
                | _ -> false)
          spc.elements

 def getQIdIfOp el =
   case el of
     | Op    (qid,_,_) -> Some qid
     | OpDef (qid,_,_,_) -> Some qid
     | _ -> None

 def localType? (qid, spc) = 
   exists? (fn el ->
              case el of
                | Type    (qid1,_) -> qid = qid1
                | TypeDef (qid1,_) -> qid = qid1
                | _ -> false)
          spc.elements

 def localOp? (qid, spc) = 
   exists? (fn el ->
              case el of
                | Op    (qid1,_,_) -> qid = qid1
                | OpDef (qid1,_,_,_) -> qid = qid1
                | _ -> false)
          spc.elements

 def localProperty? (qid, spc) = 
   exists? (fn el ->
              case el of
                | Property (_, qid1, _, _, _) -> qid = qid1
                | _ -> false)
          spc.elements

 def localTypes spc =
   removeDuplicates (mapPartial (fn el ->
				 case el of
				   | Type    (qid,_) -> Some qid
				   | TypeDef (qid,_) -> Some qid
				   | _ -> None)
		                spc.elements)


 def localOps spc =
   removeDuplicates (mapPartial (fn el ->
				 case el of
				   | Op    (qid,_,_) -> Some qid
				   | OpDef (qid,_,_,_) -> Some qid
				   | _ -> None)
		                spc.elements)

 def localProperties spc =
   mapPartial (fn el ->
	       case el of
		 | Property p -> Some p
		 | _ -> None)
              spc.elements

 def allProperties spc =
   foldrSpecElements (fn (el, result) ->
		      case el of
		       | Property p -> p :: result
		       | _ -> result)
                     []
		     spc.elements

 def allPropertyNames spc =
   removeDuplicates (mapPartial (fn el ->
				 case el of
				   | Property p -> Some (propertyName p)
				   | _ -> None)
		                spc.elements)

 op findPropertiesNamed(spc: Spec, qid: QualifiedId): List(Property) =
   foldrSpecElements (fn (el, result) ->
		      case el of
		       | Property(p as (_, qid1, _, _, _)) | qid = qid1 -> p :: result
		       | _ -> result)
                     []
		     spc.elements

 def hasLocalType? spc =
   exists? (fn el ->
              case el of
                | Type _    -> true
                | TypeDef _ -> true
                | _ -> false)
          spc.elements

 def hasLocalOp? spc =
   exists? (fn el ->
              case el of
                | Op _    -> true
                | OpDef _ -> true
                | _ -> false)
          spc.elements

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op findTheType  : [a] ASpec a * QualifiedId -> Option (ATypeInfo a)
 op findTheOp    : [a] ASpec a * QualifiedId -> Option (AOpInfo   a)

 op findAllTypes : [a] ASpec a * QualifiedId -> List (ATypeInfo a)
 op findAllOps   : [a] ASpec a * QualifiedId -> List (AOpInfo   a)

 def findTheType (spc, Qualified (q, id)) =
   %% We're looking for precisely one type,
   %% which we might have specified as being unqualified.
   %% (I.e., unqualified is not a wildcard here.)
   findAQualifierMap (spc.types, q, id)

 def findTheOp (spc, Qualified (q, id)) =
   %% We're looking for precisely one op,
   %% which we might have specified as being unqualified.
   %% (I.e., unqualified is not a wildcard here.)
   findAQualifierMap (spc.ops, q, id)

 %% Overloading is not particularly meaningful for types.
 %% (Would we ever want both  FOO.FOO x and FOO.FOO x y  as distinct types?)
 %% but we might have two or more types X.S, Y.S, etc.

 %% If the qualifier is UnQualified then we return unqualified answer first so as to
 %% give preference to it because there is no other way to refer to this entry.
 %% Note that checkType depends on this behavior.

 def findAllTypes (spc, Qualified (q, id)) =
   let found = (case findAQualifierMap (spc.types, q, id) of
		  | Some info -> [info]
		  | None           -> [])
   in
   if q = UnQualified then
     %% various other routines assume that any
     %% unqualified answer will be listed first
     found ++ filter (fn info -> info nin? found)
                     (wildFindUnQualified (spc.types, id))
   else
     found

 def findAllOps (spc, Qualified (q, id)) =
   let found = (case findAQualifierMap (spc.ops, q, id) of
		  | Some info -> [info]
		  | None           -> [])
   in
   if q = UnQualified then
     %% various other routines assume that any
     %% unqualified answer will be listed first
     found ++ filter (fn info -> info nin? found)
                     (wildFindUnQualified (spc.ops, id))
   else
     found

 % this next one is use only in substract spec. it cannot be defined inside
 % the scope of subtractSpec as there is no let-polymorphism in Specware
 op  mapDiffTypes : [a] ATypeMap a -> ATypeMap a -> ATypeMap a
 def mapDiffTypes xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of
                          | None ->
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)
			  | Some y_info ->
			    if definedTypeInfo? y_info then
			      %% omit the x_info, whether it is defined or not
			      newMap
			    else if definedTypeInfo? x_info then
			      insertAQualifierMap (newMap, q, id, x_info)
			    else
			      newMap)
                       emptyAQualifierMap
                       xMap

 op  mapDiffOps : [a] AOpMap a -> AOpMap a -> AOpMap a
 def mapDiffOps xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of
                          | None ->
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)
			  | Some y_info ->
			    if definedOpInfo? y_info then
			      %% omit the x_info, whether it is defined or not
			      newMap
			    else if definedOpInfo? x_info then
			      insertAQualifierMap (newMap, q, id, x_info)
			    else
			      newMap)
                       emptyAQualifierMap
                       xMap

op [a] showQ(el: ASpecElement a): String =
  case el of
    | Import _ -> "import ..."
    | Type(qid, _) -> "type "^show qid
    | TypeDef(qid, _) -> "type "^show qid^" = .."
    | Op(qid, def?, _) -> "op "^show qid^(if def? then " = .." else ": ...")
    | OpDef(qid, refine_num, _, _) -> (if refine_num > 0 then "refine " else "")^"def "^show qid^" = .."
    | Property _ -> "theorem ..."
    | Comment  _ -> "comment ..."
    | Pragma   _ -> "pragma ..."

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Testing
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Gather all of the Type (not TypeDef) spec elements for the given qualified Id.
 %% TODO use a filter function? (but here we don't want to preserve the import structure, unlike what filterSpecElements seems to do)
 op getTypeElements (qid : QualifiedId) (elts : SpecElements) : SpecElements =
   foldlSpecElements (fn (acc:SpecElements, elt:SpecElement) ->
                        (case elt of
                           | Type (qid2, _) -> if qid2 = qid then elt::acc else acc
                           | _ -> acc))
                     []
                     elts

 %% Gather all of the TypeDef (not Type) spec elements for the given qualified Id.
 %% TODO use a filter function? (but here we don't want to preserve the import structure, unlike what filterSpecElements seems to do)
 op getTypeDefElements (qid : QualifiedId) (elts : SpecElements) : SpecElements =
   foldlSpecElements (fn (acc:SpecElements, elt:SpecElement) ->
                        (case elt of
                           | TypeDef (qid2, _) -> if qid2 = qid then elt::acc else acc
                           | _ -> acc))
                     []
                     elts

 %% Gather all of the Op (not OpDef) spec elements for the given qualified Id.
 %% TODO use a filter function? (but here we don't want to preserve the import structure, unlike what filterSpecElements seems to do)
 op getOpElements (qid : QualifiedId) (elts : SpecElements) : SpecElements =
   foldlSpecElements (fn (acc:SpecElements, elt:SpecElement) ->
                        (case elt of
                           | Op (qid2, _, _) -> if qid2 = qid then elt::acc else acc
                           | _ -> acc))
                     []
                     elts

 %% Gather all of the OpDef (not Op) spec elements for the given qualified Id.
 %% TODO use a filter function? (but here we don't want to preserve the import structure, unlike what filterSpecElements seems to do)
 op getOpDefElements (qid : QualifiedId) (elts : SpecElements) : SpecElements =
   foldlSpecElements (fn (acc:SpecElements, elt:SpecElement) ->
                        (case elt of
                           | OpDef (qid2, _, _, _) -> if qid2 = qid then elt::acc else acc
                           | _ -> acc))
                     []
                     elts
   
 
 % TODO these are duplicated in PrintSpecAsC.sw
  op [a] intersperse (separator : a, vals : List a) : List a =
    (head vals)::(foldr (fn (elem, result) -> separator::elem::result) [] (tail vals))
 op showStrings (strings : List String) : String = (flatten (intersperse(" ", strings)))
 op showQIDs (qids : List QualifiedId) : String = showStrings (map printQualifiedId qids)

 %% debugging utility
 op SpecTransform.showImports (spc : Spec) (msg : String) (show_types? : Bool) (show_ops? : Bool) : () =
  let
    def spaces n =
      implode (repeat #\s n)

    def aux (n, elements) =
      app (fn x ->
             case x of
               | Import (tm, _, elts, _) ->
                 let _ = writeLine (spaces n ^ "Import  : " ^ showSCTerm tm) in
                 aux (n + 1, elts)
               | Type    (name, _)       -> if show_types? then writeLine (spaces n ^ "Type    : " ^ show name) else ()
               | TypeDef (name, _)       -> if show_types? then writeLine (spaces n ^ "TypeDef : " ^ show name) else ()
               | Op      (name, _, _)    -> if show_ops?   then writeLine (spaces n ^ "Op      : " ^ show name) else ()
               | OpDef   (name, _, _, _) -> if show_ops?   then writeLine (spaces n ^ "OpDef   : " ^ show name) else ()
               | _  -> ())
          elements
  in
  let _ = writeLine "====================" in
  let _ = writeLine msg in

  let _ = aux (0, spc.elements) in

  let _ = writeLine "====================" in
  ()

end-spec
