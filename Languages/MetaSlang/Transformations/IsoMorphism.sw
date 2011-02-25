
(* Takes isomorphism function iso_qid and its inverse osi_qid,
   Extracts State and State'
   Find all functions f that take State as an argument or returned value and create
   f' with State' instead of State. The body is a call to f with state parameters wrapped in
   osi_qid and result state wrapped in iso_qid.

   Simplify all
     Distributive rules
     fa(x': State') iso_qid(osi_qid x') = x'

   Simplify
*)

Isomorphism qualifying
spec
  import Script
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
  import /Languages/MetaSlang/Specs/AnalyzeRecursion

  op orderElements?: Boolean = true

(*
  op makeNewPrimedQid(Qualified(q,id): QualifiedId, exists?: QualifiedId -> Boolean): QualifiedId =
    let primed_qid = Qualified(q,id^"'") in
    if exists? primed_qid
      then makeNewPrimedQid(primed_qid, exists?)
      else primed_qid
*)

(*
  op makePrimedOpQid(qid: QualifiedId, spc: Spec): QualifiedId =
    makeNewPrimedQid(qid, fn nqid -> some?(findTheOp(spc, nqid)))

  op makePrimedTypeQid(qid: QualifiedId, spc: Spec): QualifiedId =
    makeNewPrimedQid(qid, fn nqid -> some?(findTheSort(spc, nqid)))
*)

 op Or (left : SpecCalc.Env Boolean) (right : SpecCalc.Env Boolean) : SpecCalc.Env Boolean = {
   b <- left;
   if b then
     right
   else
     return false
 }

 op [a] exists (f : a -> SpecCalc.Env Boolean) (l : List a) : SpecCalc.Env Boolean =
  case l of
    | [] -> return false
    | x::xs -> Or (f x) (exists f xs)
   
 op existsSubTerm : [b] (ATerm b -> SpecCalc.Env Boolean) -> ATerm b -> SpecCalc.Env Boolean
 def existsSubTerm pred? term =
   Or (pred? term) 
     (case term of
       | Apply (M, N, _) -> Or (existsSubTerm pred? M) (existsSubTerm pred? N)
       | ApplyN (Ms, _) -> exists (existsSubTerm pred?) Ms
       | Record (fields, _) -> exists (fn (_,M) -> existsSubTerm pred? M) fields
       | Bind (_,_,M, _) -> existsSubTerm pred? M
       | The (_,M, _) -> existsSubTerm pred? M
       | Let (decls, M, _) -> Or (existsSubTerm pred? M) (exists (fn (_,M) -> existsSubTerm pred? M) decls)
       | LetRec (decls, M, _) -> Or (existsSubTerm pred? M) (exists (fn (_,M) -> existsSubTerm pred? M) decls)
       | Var _ -> return false
       | Fun _ -> return false
       | Lambda (rules, _) ->
           exists (fn (p, c, M) ->
             Or (existsSubTermPat pred? p) 
            (Or (existsSubTerm pred? c) 
                (existsSubTerm pred? M))) rules
       | IfThenElse (M, N, P, _) ->
            Or (existsSubTerm pred? M)
           (Or (existsSubTerm pred? N) 
               (existsSubTerm pred? P))
       | Seq (Ms, _) -> exists (existsSubTerm pred?) Ms
       | SortedTerm (M, srt, _) -> existsSubTerm pred? M
       | Pi (tvs, t, _) -> existsSubTerm pred? t
       | And (tms, _) -> exists (existsSubTerm pred?) tms
       | Any _ -> return false)                 

 op existsSubTermPat : [b] (ATerm b -> SpecCalc.Env Boolean) -> APattern b -> SpecCalc.Env Boolean
 def existsSubTermPat pred? pat =
   case pat of
     | RestrictedPat(_,t,_) -> existsSubTerm pred? t
     | _ -> return false

  type IsoFnInfo = List(QualifiedId * QualifiedId)
  %% Look for fns of the form Bijection(a,a') -> Bijection(L a,L a')
  op findComplexIsoFns(spc: Spec): IsoFnInfo =
    foldOpInfos (fn (info, result) ->
                   case firstOpDefInnerSort info of
                     | Arrow(Base(Qualified("Function","Bijection"),_,_),
                             Base(Qualified("Function","Bijection"),
                                  [Base(qid1,_,_), Base(qid2,_,_)],
                                  _), _)
                         | qid1 = qid2 ->
                             Cons((qid1, primaryOpName info), result)
                     | _ -> result)
      []
      spc.ops

  % given
  % (fn_qid) : (dom_ty -> rng_ty) -> (ty_qid dom_ty -> ty_qid rng_ty)
  % and (fn_arg)
  % construct (fn_qid fn_arg)
  op mkHOIsoFn(ty_qid: QualifiedId, fn_qid: QualifiedId, fn_arg: MS.Term, dom_ty: Sort, rng_ty: Sort,
               spc: Spec): MS.Term =
    mkApply(mkOpFromDef (fn_qid,
                         mkArrow(mkArrow(dom_ty,rng_ty),
                                 mkArrow(mkBase(ty_qid, [dom_ty]),
                                         mkBase(ty_qid, [rng_ty]))),
                         spc),
            fn_arg)

  % given fn_arg and list_arg
  % construct (List.Map fn_arg list_arg)
  % List.Map : (dom_ty -> rng_ty) -> (List dom_ty -> List rng_ty)
  op mkMapApply(fn_arg: MS.Term, list_arg: MS.Term, dom_ty: Sort, rng_ty: Sort, spc: Spec): MS.Term =
    mkApply(mkApply(mkOpFromDef
                      (Qualified("List","map"),
                       mkArrow(mkArrow(dom_ty,rng_ty),
                               mkArrow(mkBase(Qualified("List","List"), [dom_ty]),
                                       mkBase(Qualified("List","List"), [rng_ty]))),
                       spc),
                    fn_arg),
            list_arg)

  op makeIsoTheorems(spc: Spec, iso_ref: MS.Term, osi_ref: MS.Term, tvs: TyVars,
                     src_ty: Sort, trg_ty: Sort, prev: List QualifiedId)
     : Spec * List QualifiedId =
    %% Thm inverse iso = osi
    let inv_thm1 = mkEquality(mkArrow(trg_ty,src_ty),
                              mkApply(mkOpFromDef(Qualified("Function","inverse"),
                                                  mkArrow(mkArrow(src_ty,trg_ty),
                                                          mkArrow(trg_ty,src_ty)),
                                                  spc),
                                      iso_ref),
                              osi_ref)
    in
    let inverse_iso_is_osi_qid = Qualified("generated","inverse_iso_is_osi") in
    let spc = addTheorem((inverse_iso_is_osi_qid, tvs, inv_thm1, noPos), spc) in

    let inv_thm2 = mkEquality(mkArrow(src_ty,trg_ty),
                              mkApply(mkOpFromDef(Qualified("Function","inverse"),
                                                  mkArrow(mkArrow(trg_ty,src_ty),
                                                          mkArrow(src_ty,trg_ty)),
                                                  spc),
                                      osi_ref),
                              iso_ref)
    in
    let inverse_osi_is_iso_qid = Qualified("generated","inverse_osi_is_iso") in
    let spc = addTheorem((inverse_osi_is_iso_qid, tvs, inv_thm2, noPos), spc) in

    %% Thm fa(x) iso(osi x) = x
     let x_pr_var = ("x'",trg_ty) in
     let inv_thm1 = mkBind(Forall,[x_pr_var],
                           mkEquality(trg_ty,
                                      mkApply(iso_ref,mkApply(osi_ref, mkVar x_pr_var)),
                                      mkVar x_pr_var))
     in
     let iso__osi_qid = Qualified("generated","iso__osi") in
     let spc = addTheorem((iso__osi_qid, tvs, inv_thm1, noPos), spc) in

     %% Thm fa(x) osi(iso x) = x
     let x_var = ("x",src_ty) in
     let inv_thm1 = mkBind(Forall,[x_var],
                           mkEquality(src_ty,
                                      mkApply(osi_ref,mkApply(iso_ref, mkVar x_var)),
                                      mkVar x_var))
     in
     %let _ = writeLine("osi__iso theorem:\n"^printTermWithSorts inv_thm1) in
     let osi__iso_qid = Qualified("generated","osi__iso") in
     let spc = addTheorem((osi__iso_qid, tvs, inv_thm1, noPos), spc) in

    %% Thm fa(x) map iso (map osi x) = x
 %    let x_pr_var = ("x'", mkBase(Qualified("List","List"), [trg_ty])) in
%     let inv_thm1 = mkBind(Forall,[x_pr_var],
%                           mkEquality(mkBase(Qualified("List","List"), [trg_ty]),
%                                      mkMapApply(iso_ref, mkMapApply(osi_ref, mkVar x_pr_var,
%                                                                     trg_ty, src_ty),
%                                                 src_ty, trg_ty),
%                                      mkVar x_pr_var))
%     in
%     let map__iso__osi_qid = Qualified("generated","map__iso__osi") in
%     let spc = addTheorem((iso__osi_qid, tvs, inv_thm1, noPos), spc) in

%     %% Thm fa(x) map osi(map iso x) = x
%     let x_var = ("x", mkBase(Qualified("List","List"), [src_ty])) in
%     let inv_thm1 = mkBind(Forall,[x_var],
%                           mkEquality(mkBase(Qualified("List","List"), [src_ty]),
%                                      mkMapApply(osi_ref, mkMapApply(iso_ref, mkVar x_var,
%                                                                         src_ty, trg_ty),
%                                                 trg_ty, src_ty),
%                                      mkVar x_var))
%     in
%     let map__osi__iso_qid = Qualified("generated","map__osi__iso") in
%     let spc = addTheorem((osi__iso_qid, tvs, inv_thm1, noPos), spc) in

    (spc, [inverse_iso_is_osi_qid, inverse_osi_is_iso_qid, iso__osi_qid, osi__iso_qid] ++ prev)

  %% fn x -> fn (x,y) -> \_dots  \_longrightarrow  fn x -> fn (x,y) -> f (x) (y,z)
  % ### LE I don't get this.
  op makeTrivialDef(spc: Spec, dfn: MS.Term, qid_pr_ref: MS.Term): MS.Term =
    let def constructDef(tm, new_bod) =
          case tm of
            | Lambda(binds,a) ->
              let new_binds = map (fn (p,condn,body) ->
                                     case patternToTerm p of
                                       | Some args ->
                                          (p,condn,
                                           constructDef(body, mkApply(new_bod, args)))
                                       | None -> (p,condn,body))
                             binds
              in
                Lambda(new_binds,a)
            | _ -> new_bod 
    in
    constructDef(dfn, qid_pr_ref)

  op printDef (spc: Spec, qid: QualifiedId): SpecCalc.Env () =
    case findTheOp(spc,qid) of
      | None -> escape ("Can't find op " ^ anyToString qid ^ "\n")
      | Some opinfo -> {
          (tvs, ty, dfn) <- return(unpackFirstTerm opinfo.dfn); 
          print (printQualifiedId qid^":");
          print (printTerm dfn)
        }

  op lookupIsoFnInfo(qid: QualifiedId, iso_fn_info: IsoFnInfo): Option QualifiedId =
    case iso_fn_info of
      | [] -> None
      | (qid1,qid2)::_ | qid = qid1 -> Some qid2
      | _::r -> lookupIsoFnInfo(qid,r)

  type IsoInfo = MS.Term * TyVars * Sort * Sort
  type IsoInfoList = List(IsoInfo * IsoInfo)

  op printIsoInfoList(iso_info: IsoInfoList): () =
    app (fn ((tma1, _, tya1, tya2), (tmb1, _, tyb1, tyb2)) ->
         (writeLine(printTerm tma1^": "^printSort tya1^" -> "^printSort tya2);
          writeLine(printTerm tmb1^": "^printSort tyb1^" -> "^printSort tyb2)))
      iso_info

  op lookupIsoInfo(qid: QualifiedId, iso_info: IsoInfoList): Option(IsoInfo * IsoInfo) =
    case iso_info of
      | [] -> None
      | (info as ((_,_,Base(ty_qid,_,_),_),_)) :: _ | qid = ty_qid ->
        Some info
      | _::rst -> lookupIsoInfo(qid,rst)

  op invertIsoInfo(iso_info: IsoInfoList): IsoInfoList =
    map (fn (x,y) -> (y,x)) iso_info

  op typeInIsoInfoList(qid: QualifiedId, iso_info: IsoInfoList): Boolean =
    case iso_info of
      | [] -> false
      | (info as ((_,_,Base(ty_qid,_,_),Base(ty'_qid,_,_)),_) :: _) | qid = ty_qid || qid = ty'_qid -> 
        true
      | _::rst -> typeInIsoInfoList(qid,rst)

%{{{  Env.mapOpInfos 
(*
 op  Env.mapOpInfos : [b] (AOpInfo b -> SpecCalc.Env (AOpInfo b)) -> AOpMap b -> SpecCalc.Env (AOpMap b)

 def Env.mapOpInfos f ops =
   foldM
     (fn newIdMap -> fn id -> {
       qualMap <- return (STHMap.eval (ops,id));
       newQualMap <-
         foldM (fn newQualMap -> fn q ->
           let info = Map.eval (qualMap,id) in {
           new_info <- f info; 
           return (Map.update (newQualMap,q,new_info))
         }) Map.emptyMap (domainToList qualMap);
       return (STHMap.update(newIdMap,id,newQualMap))
      }) STHMap.emptyMap (domainToList ops)
*)

 op  Env.mapOpInfos : [b] (AOpInfo b -> SpecCalc.Env (AOpInfo b)) -> AOpMap b -> SpecCalc.Env (AOpMap b)
 def Env.mapOpInfos f ops =
   foldM
     (fn newMap -> fn id -> 
       let qualMap = STHMap.eval (ops,id) in
         foldM (fn newMap -> fn q ->
           let info = Map.eval (qualMap,q) in
             if primaryOpName? (q, id, info) then {
               %% When access is via a primary alias, update the info and
               %% record that (identical) new value for all the aliases.
               new_info <- f info; 
               return (foldl (fn (newMap, Qualified (q, id)) ->
                   insertAQualifierMap (newMap, q, id, new_info)) newMap info.names)
             }
             else
               %% For the non-primary aliases, do nothing,
               %% since they are handled derivatively above.
               return newMap) newMap (domainToList qualMap)) emptyMap (domainToList ops)

(*

       let info = STHMap.eval(ops,(id,w) in
       if primaryOpName? (q, id, info) then {
         %% When access is via a primary alias, update the info and
         %% record that (identical) new value for all the aliases.
         new_info <- f info; 
         return (List.foldl (fn (new_map, Qualified (q, id)) ->
             insertAQualifierMap (new_map, q, id, new_info)) new_map info.names)
       }
       else
         %% For the non-primary aliases, do nothing,
         %% since they are handled derivatively above.
         return new_map) emptyAOpMap (STHMap.domainToList ops)
*)
%}}}

%{{{  findOpInfo (non-monadic - unused)
(*
  % Given a qid for an op (presumably of function type), construct a term
  % referencing that op together with the type variables and source and
  % target types for the op.
  op findOpInfo(spc: Spec, qid: QualifiedId): Option(IsoInfo) =
    case findMatchingOps(spc,qid) of
      | [] \_rightarrow (warn("No op with name: " ^ printQualifiedId qid);
                         None)
      | [opinfo] \_rightarrow
        let (tvs, ty, tm) = unpackFirstTerm opinfo.dfn in
        let qid = primaryOpName opinfo in
        let qid_ref = mkInfixOp(qid, opinfo.fixity, ty) in
        (case arrowOpt(spc, ty) of
           | None -> (warn(printQualifiedId qid^" is not a function!");
                      None)
           | Some(src_ty, trg_ty) ->
             Some(qid_ref, tvs, src_ty, trg_ty))
      | _ -> (warn("Ambiguous op name: " ^ printQualifiedId qid);
              None)
*)
%}}}

  %{{{  dependsOnIsoInfo
  op dependsOnIsoInfo?(qid: QualifiedId, iso_info: IsoInfoList, spc: Spec, seen: List QualifiedId)
       : Boolean =
    let seen = Cons(qid, seen) in
    case findTheSort(spc, qid) of
      | None -> false
      | Some info ->
    let (_,def_ty) = unpackSort info.dfn in
    existsInType? (fn ty ->
                     case ty of
                       | Base(s_qid,_,_) ->
                         typeInIsoInfoList(s_qid, iso_info)
                           || (s_qid nin? seen
                                && dependsOnIsoInfo?(s_qid, iso_info, spc, seen))
                       | _ -> false)
       def_ty
  %}}}

  %{{{  identityFn
  op identityFn(ty: Sort): MS.Term = mkInfixOp(Qualified("Function","id"),Unspecified,mkArrow(ty,ty))
  op identityFn?(tm: MS.Term): Boolean =
    case tm of
      | Fun(Op(Qualified("Function","id"),_),_,_) -> true
      | _ -> false
  %}}}

  %{{{  mkCompose
  op mkCompose(f1: MS.Term, f2: MS.Term, spc: Spec): MS.Term =
    if identityFn? f1 then f2
      else if identityFn? f2 then f1
      else
        let f1_ty = inferType(spc,f1) in
        let f2_ty = inferType(spc,f2) in
        let Some (dom,_) = arrowOpt(spc,f2_ty) in
        let Some (_,ran) = arrowOpt(spc,f1_ty) in
        let compose_ty = mkArrow(mkProduct[f1_ty,f2_ty], mkArrow(dom, ran)) in
        let compose_fn = mkInfixOp(Qualified("Function","o"), Infix(Left,24), compose_ty) in
        mkAppl(compose_fn, [f1,f2])
  %}}}

  %{{{  createPrimeDef
  op createPrimeDef(spc: Spec, old_dfn: MS.Term, op_ty: Sort, src_ty: Sort, trg_ty: Sort,
                    iso_ref: MS.Term, osi_ref: MS.Term)
     : MS.Term =
    let
      def makePrimedPat (p: Pattern, sb: List(Var * MS.Term)): Pattern * List(Var * MS.Term) =
        case p of
          | VarPat(v as (vn,v_ty),a) ->
            if equalType?(v_ty,src_ty)
              then let v_pr = (vn^"'",trg_ty) in
                   (VarPat(v_pr,a),
                    Cons((v, mkApply(osi_ref,Var(v_pr,a))), sb))
              else
               (case v_ty of
                 | Base(Qualified("List","List"),[el_ty],a1) | equalType?(el_ty, src_ty) ->
                   let v_pr = (vn^"'",Base(Qualified("List","List"),[trg_ty],a1)) in
                   (VarPat(v_pr,a),
                    Cons((v, mkMapApply(osi_ref, Var(v_pr,a), trg_ty, src_ty, spc)), sb))
                 | _ -> (p, sb))
          | RecordPat(idprs,a) ->
            let (idprs_pr,sb) =
                foldr (fn ((id,p),(idprs_pr,sb)) ->
                         let (p_pr,sb) = makePrimedPat(p,sb) in
                         (Cons((id,p_pr), idprs_pr), sb))
                  ([],sb) idprs
            in
            (RecordPat(idprs_pr, a), sb)
          | RestrictedPat(p1,pred,a) ->
            let (p1_pr, sb) = makePrimedPat(p1, sb) in
            (RestrictedPat(p1_pr, substitute(pred,sb) ,a),
             sb)
          | _ -> (p, sb)
      def makePrimeBody (old_def_tm, sb, result_ty) =
        case old_def_tm of
          | Lambda(binds,a) ->
            let new_binds = map (fn (p, condn, body) ->
                                   let (p_pr, sb) = makePrimedPat(p, sb) in
                                   let body_ty = case arrowOpt(spc,result_ty) of
                                                   | Some(_,r) -> r
                                                   | None -> fail("Illegal type")
                                   in
                                     (p_pr, condn, makePrimeBody(body, sb, body_ty)))
                              binds
            in
              Lambda(new_binds,a)
           | _ ->
             let new_bod = substitute(old_def_tm, sb) in
             %% !! Generalize to handle tuple containing src_ty as a component
             if equivType? spc (result_ty, src_ty)
               then mkApply(iso_ref, new_bod)
             else
               case result_ty of
                 | Base(Qualified("List","List"),[el_ty],a) | equivType? spc (el_ty, src_ty) ->
                   %% map iso_ref new_bod
                   mkMapApply(iso_ref, new_bod, src_ty, trg_ty, spc)
                 | Base(Qualified("Option","Option"),[el_ty],a) | equivType? spc (el_ty, src_ty) ->
                   mkApply(mkApply(mkInfixOp
                                     (Qualified("Option","mapOption"),
                                      Unspecified,
                                      mkArrow(mkBase(Qualified("Function","Bijection"), [src_ty,trg_ty]),
                                              mkBase(Qualified("Function","Bijection"),
                                                     [mkBase(Qualified("Option","Option"), [src_ty]),
                                                      mkBase(Qualified("Option","Option"), [trg_ty])]))),
                                   iso_ref),
                           new_bod)
                 | _ -> new_bod
    in
    makePrimeBody(old_dfn, [], op_ty)    
  %}}}

  op typeQid(ty: Sort): QualifiedId =
    let Base(qid, _, _) = ty in
    qid

  op srcQId(((_,_,src_ty,_), _): IsoInfo * IsoInfo): QualifiedId = typeQid src_ty

  %{{{  checkTypeOpacity?
  (* The type checker annotates certain terms with a type. In particular
  a Fun term has a type associated with it. In the case of a Fun (Op
  (f, ...)) the type assigned is a (possibly polymorphic) instance of
  the declared type for f. In particular, if f is declared f : X ->
  Y where X is defined to be some type T, then the name X (rather than
  the unfolding to T) will be the type assigned in the Fun term.

  We are interested in the polymorphic case. Suppose we have types "Bit"
  and "BitList = List Bit" together with a function "length : [a] List a ->
  Nat". Also suppose we have a monomorphic reference to length of type
  "List Bit -> Nat". This is the "up type" - the type assigned from a
  bottom up traversal of the AST.  The "down type" is the type assigned
  to the reference to "length" from the context. For example in the term
  (length (x:BitList)), then down type for length is BitList -> Nat.

  type if the term does not look into the structure of the type *)

  op checkTypeOpacity?(tm: MS.Term, ty: Sort, base_src_QIds: List QualifiedId, src_QIds: List QualifiedId,
                       spc: Spec): Boolean =
    let def opacityPreserved?(d_ty, u_ty) =
          % let _ = writeLine("oP?: "^printSort d_ty^" =?= "^printSort u_ty) in
          equalType?(d_ty, u_ty)
            ||
          (let result =
             case (d_ty, u_ty) of
               | (Arrow(x1, y1,  _), Arrow(x2, y2,  _)) ->
                 opacityPreserved?(x1, x2) && opacityPreserved?(y1, y2)
               | (Product(xs1, _), Product(xs2, _)) ->
                 forall? (fn ((_, x1), (_, x2)) -> opacityPreserved?(x1, x2)) (zip(xs1, xs2))
               | (Subsort(x1, t1,  _), Subsort(x2, t2,  _)) ->
                 % equalTerm?(t1, t2) &&
                 opacityPreserved?(x1, x2)
               | (Base(q1, xs1, _), Base(q2, xs2, _)) | q1 = q2 ->
                 forall? (fn (x1, x2) -> opacityPreserved?(x1, x2)) (zip(xs1, xs2))
               | (Base(q1, xs1, _), Base(q2, xs2, _)) | q2 nin? base_src_QIds ->
                 (case tryUnfoldBase spc u_ty of
                  | Some u_ty1 -> opacityPreserved?(d_ty, u_ty1)
                  | None ->
                  if q1 in? base_src_QIds then false
                  else
                  case tryUnfoldBase spc d_ty of
                  | Some d_ty1 -> opacityPreserved?(d_ty1, u_ty)
                  | None -> false)
               | (Subsort(x1, _,  _), _) ->
                 opacityPreserved?(x1, u_ty)
               | (_, Subsort(x2, _,  _)) ->
                 opacityPreserved?(d_ty, x2)
               | (Base(q1, _, _), _) | q1 nin? base_src_QIds ->
                 (case tryUnfoldBase spc d_ty of
                  | Some d_ty1 -> opacityPreserved?(d_ty1, u_ty)
                  | None -> false)
               | (_, Base(q2, _, _)) | q2 nin? base_src_QIds ->
                 (case tryUnfoldBase spc u_ty of
                  | Some u_ty1 -> opacityPreserved?(d_ty, u_ty1)
                  | None -> false)
               | _ -> false
           in
             % let _ = writeLine(if result then "is opq" else "not opq") in
             result)
        def cto?(tm, d_ty) =
          % let _ = writeLine("cto?: "^printTerm tm) in
          let u_ty = inferType(spc, tm) in
          opacityPreserved?(d_ty, u_ty)
            &&
          (case tm of
           | Apply (t1, t2, _) ->
             let fn_ty = inferType(spc, t1) in
             (case arrowOpt(spc, fn_ty) of
              | None -> false
              | Some(dom, _) ->
                cto?(t1, mkArrow(dom, d_ty)) && cto?(t2, dom)
                  && (case t1 of
                      | Fun (RecordMerge, _, _) ->
                        recordTy? u_ty
                          && (case dom of
                              | Product([("1", ty1), ("2", ty2)], _) ->
                                recordTy? ty1 && recordTy? ty2
                              | _ -> false)
                      | Fun (Project _, _, _) ->
                        embed? Product (inferType(spc, t2))
                      | _ -> true))
           | Record (row, _) ->
             let srts = map (project 2) (product (spc, d_ty)) in
             forall? (fn (f_ty, (_, tmi)) -> cto?(tmi, f_ty))
               (zip(srts, row))
           | Bind (_, _, bod, _) -> cto?(bod, boolSort)
           | The  (var,  bod, _) -> cto?(bod, boolSort)
           | Let (decls, bdy, _) ->
             cto?(bdy, d_ty)
               && forall? (fn (pat, trm) -> cto?(trm, patternSort pat))
                    decls
           | LetRec (decls, bdy, _) ->
             cto?(bdy, d_ty)
               && forall? (fn ((_, lr_ty), trm) -> cto?(trm, lr_ty))
                    decls
           | Lambda (match, _) ->
             let ran = range(spc, d_ty) in
             forall? (fn (pat, condn, bod) ->
                    cto?(condn, boolSort) && cto?(bod, ran))
               match
           | IfThenElse (t1, t2, t3, _) ->
             cto?(t1, boolSort) && cto?(t2, d_ty) && cto?(t3, d_ty)
           | Seq (terms, _) ->
             let pre_trms = butLast terms in
             let lst_trm  =    last terms in
             cto?(lst_trm, d_ty)
               && forall? (fn trm -> cto?(trm, mkProduct [])) pre_trms
           | SortedTerm (trm, srt, _) -> cto?(trm, srt)
           | _ -> true)
      def recordTy? ty =
        case productOpt(spc, ty) of
          | None -> false
          | Some flds -> opacityPreserved?(ty, Product(flds, noPos))
    in
    cto?(tm, ty)
  %}}}

  %{{{  primeTermsTypes
  op primeTermsTypes(tm: MS.Term, qidPrMap: QualifiedIdMap, iso_info: IsoInfoList): MS.Term =
    mapTerm (fn t -> case t of
             | Fun(Op(qid as Qualified(q,idn), fx), ty, a) ->
               let nqid = case findAQualifierMap(qidPrMap, q, idn) of
                            | Some nqid -> nqid
                            | None      ->  qid
               in
               Fun(Op(nqid, fx), ty, a)
             | _ -> t,
             fn ty -> case ty of
             | Base(qid, params, a) ->
               (case lookupIsoInfo(qid, iso_info) of
                | Some((_,_,_,r_ty as Base(osi_qid,_,_)), _) ->
                  if params = [] then r_ty else Base(osi_qid, params, a)
                | _ -> ty)
             | _ -> ty,
             id)
      tm
  %}}}

  type QualifiedIdMap = AQualifierMap(QualifiedId)

  % Returns true if the predicate holds for some element of the qualified map
  op existsQMap : [a] (Qualifier * Id -> SpecCalc.Env Boolean) -> (AQualifierMap a) -> SpecCalc.Env Boolean

  def existsQMap pred qmap  =
    let 
      def f (qual,id,val,unit) =
        if unit then
          return unit
        else
          pred (qual,id)
    in
      foldOverQualifierMap f false qmap

  op invertQualifiedIdMap(qid_map: QualifiedIdMap): AQualifierMap Bool =
    foldriAQualifierMap (fn (q, id, Qualified(q', id'), result)  ->
                            insertAQualifierMap(result, q', id', true))
      emptyAQualifierMap qid_map

  op Env.findTheOp : Spec -> QualifiedId -> SpecCalc.Env OpInfo
  def Env.findTheOp spc qid =
    case findTheOp (spc, qid) of
      | None -> escape ("applyIso: " ^ show qid ^ " not found\n")
      | Some opInfo -> return opInfo

  % This should be moved to the specware monad.
  op escape : [a] String -> SpecCalc.Env a
  def escape str = {
    print str;
    raise Escape
  }
 
  %{{{  doList
  % Variation on foldM when the list is inside a product.
  % Metaslang doesn't support let-polymorphism so this must be at the outer scope
  op doList : [a,b,c] (a -> b -> SpecCalc.Env (a * c)) -> a -> List b -> SpecCalc.Env (a * List c)
  def doList f accum lst =
    case lst of
      | [] -> return (accum,[])
      | x::xs -> {
          (accum,y) <- f accum x;
          (accum,ys) <- doList f accum xs;
          return (accum,y::ys)
        }

  (* The above is meant to be equiv to something like what's below. Below
     used foldM (a monadic foldl) but the above avoids the append (++)
     to the end

  def doList f accum lst =
    let
      def f' (accum,lst) x = {
        (accum,x) <- f accum x
        return (accum, lst ++ [x])
      }
    in
      foldM f' (accum,[]) lst
   *)
  %}}}

  %{{{  findOpInfo
  op Env.findOpInfo (spc:Spec) (qid:QualifiedId) : SpecCalc.Env IsoInfo =
    case findMatchingOps (spc,qid) of
      | [] -> escape ("No op with name: " ^ show qid ^ "\n")
      | [opinfo] -> {
          (tvs, ty, tm) <- return (unpackFirstTerm opinfo.dfn); 
          qid <- return (primaryOpName opinfo); 
          qid_ref <- return (mkInfixOp(qid, opinfo.fixity, ty));
          case arrowOpt(spc, ty) of
            | None -> escape (show qid ^ " is not a function!\n")
            | Some (src_ty, trg_ty) -> return (qid_ref, tvs, src_ty, trg_ty)
         }
      | _ -> escape  ("Ambiguous op name: " ^ show qid ^ "\n")
  %}}}

  op traceIsomorphismGenerator?: Boolean = false
  op traceMono?: Bool = false
  op simplifyIsomorphism?: Boolean = true
  %% Temporary until we have slicing
  op simplifyUnPrimed?: Boolean = false
  op opaqueSimplifyScript: Script = Simplify[]

  def Isomorphism.makeIsoMorphism (spc: Spec, iso_qid_prs: List(QualifiedId * QualifiedId),
                                   newOptQual : Option String, extra_rules: List RuleSpec)
      : SpecCalc.Env Spec =
    let
      %{{{  newQId
      def makeDerivedQId (Qualified (qual,id)) =
        case newOptQual of
          | None -> Qualified (qual, id ^ "'")
          | Some newQual -> Qualified (newQual,id)

      def derivedQId? (Qualified (qual,id)) =
         case newOptQual of
          | None -> none?(findTheOp(spc, Qualified (qual, id ^ "'")))
          | Some newQual -> newQual = qual

      def makeFreshQId (spc:Spec) (qid:QualifiedId) : SpecCalc.Env QualifiedId =
        let newQId = makeDerivedQId qid in
        case findTheOp(spc, newQId) of
          | Some info -> {
              print ("Cannot make qualified id: " ^ (printQualifiedId newQId) ^ "\n"); 
              escape "An operator with that name already exists\n" 
            }
          | None ->
              (case findTheSort(spc, newQId) of
                | Some info -> {
                    print ("Cannot make qualified id: " ^ (printQualifiedId newQId) ^ "\n"); 
                    escape "A type with that name already exists\n" 
                  }
                | None -> return newQId)

      def makeFreshTypeQId (spc:Spec) (qid:QualifiedId) : SpecCalc.Env QualifiedId =
        makeFreshQId spc qid
      %}}}
      %{{{  isoTerm
      def isoTerm (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
                 (ty: Sort)
                 (tm: MS.Term): SpecCalc.Env MS.Term =
        let
          def makePrimedPat (p: Pattern, body: MS.Term, p_ty: Sort, sb: List(Var * MS.Term))
              : SpecCalc.Env (Pattern * MS.Term * List(Var * MS.Term)) =
            case p of
              | VarPat(v as (vn,v_ty),a) -> {
                  v_ty' <- isoType (spc, iso_info, iso_fn_info) false v_ty; 
                  if equalType?(v_ty,v_ty') then
                    return (p, body, sb)
                  else {
                    v' <- return (vn^"'",v_ty'); 
                    osi <- osiTerm (spc, iso_info, iso_fn_info) (v_ty') (Var(v',a));
                    return (VarPat(v',a), body, Cons((v, osi), sb))
                  }
                }
              | RestrictedPat(p1,pred,a) -> {
                  (p1_pr, body, sb) <- makePrimedPat(p1, body, p_ty, sb); 
                  return (RestrictedPat(p1_pr, substitute(pred,sb) ,a), body, sb)
                }
              | _ | embed? Base p_ty -> {
                  v <- return ("x",p_ty); 
                  makePrimedPat (mkVarPat v, mkSimpApply(mkLambda(p,body), mkVar v), p_ty, sb)
                }
              | RecordPat(idprs,a) ->
                (case productOpt(spc, p_ty) of
                   | None -> fail("Shouldn't happen!")
                   | Some fields -> {
                      (idprs_pr,body,sb) <-
                        foldrM (fn (idprs_pr,body,sb) -> fn (id,p) ->
                              case getTermField(fields, id) of
                                | None -> fail("Shouldn't happen!")
                                | Some f_ty -> {
                                    (p_pr, body, sb) <- makePrimedPat (p,body,f_ty,sb); 
                                    return (Cons((id,p_pr), idprs_pr), body, sb)
                                  }) ([],body,sb) idprs;
                       return (RecordPat(idprs_pr, a), body, sb)
                     })
              | _ -> return (p, body, sb)
          def makePrimeBody (old_def_tm, sb, result_ty) =
            case old_def_tm of
              | Lambda([(p, condn, body)],a) | ~(embed? Base result_ty)
                               % && (embed? Base (domain(spc, result_ty)) => embed? VarPat)
                                ->
                (case arrowOpt(spc,result_ty) of
                   | None -> fail("Illegal type")
                   | Some(d_ty,body_ty) -> {
                       (p_pr, body, sb) <- makePrimedPat(p, body, d_ty, sb);
                       new_body <- makePrimeBody(body, sb, body_ty); 
                       return (Lambda([(p_pr, condn, new_body)],a))
                     })
              | _ -> {
                  new_bod <- return (substitute(old_def_tm, sb)); 
                  result_ty' <- isoType (spc, iso_info, iso_fn_info) false result_ty; 
                  if equalType?(result_ty, result_ty') then
                    return new_bod
                  else {
                    iso_fn <- isoTypeFn (spc, iso_info, iso_fn_info) result_ty; 
                    % print ("itf: "^ printTermWithSorts iso_fn ^ ": _ -> "^printSort result_ty); 
                    return (simplifiedApply(iso_fn, new_bod, spc))
                  }
                }
        in
          makePrimeBody(tm, [], ty)    
      %}}}
      %{{{  isoType
      def isoType (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo) (recursive?: Boolean)
                    (ty: Sort): SpecCalc.Env Sort =
        let
          def isoType1 ty =
              case ty of
                %{{{  Base
                | Base(qid, params, a) -> {
                    iso_params <- mapM isoType1 params; 
                    case lookupIsoInfo(qid, iso_info) of
                      | Some((_,_,_,r_ty as Base(osi_qid,_,_)), _) ->
                          if params = [] then
                            return r_ty
                          else
                            return (Base(osi_qid,params,a))
                      | _ ->
                          if recursive? && dependsOnIsoInfo?(qid,iso_info,spc,[]) then {
                            newQId <- makeFreshQId spc qid;
                            return (Base(newQId, iso_params, a))
                          }
                          else
                            return (Base(qid, iso_params, a))
                  }
                %}}}
                %{{{  Arrow
                | Arrow (s1, s2, a) -> {
                    s1 <- isoType1 s1;
                    s2 <- isoType1 s2;
                    return (Arrow(s1, s2, a))
                  }
                %}}}
                %{{{  Product
                | Product (pairs,a) -> {
                    pairs <-
                      mapM (fn (id,typ) -> {
                        typ <- isoType1 typ;
                        return (id,typ)
                      }) pairs;
                    return (Product (pairs,a))
                  }
                %}}}
                %{{{  CoProduct
                | CoProduct(pairs,a) -> {
                    pairs <-
                      mapM (fn (id,optType) ->
                        case optType of
                          | None -> return (id,None)
                          | Some typ -> {
                              typ <- isoType1 typ;
                              return (id,Some typ)
                            }) pairs;
                    return (CoProduct (pairs,a))
                  }
                %}}}
                %{{{  Quotient
                | Quotient (s, tm, a) -> {
                    s' <- isoType1 s; 
                    if equalType? (s,s') then
                      return ty
                    else {
                      tm' <-
                        case tm of
                          | Fun(Op(qid,fx), tm_ty, b) | recursive? -> {
                              % Shouldn't happen otherwise
                              newQId <- makeFreshQId spc qid;
                              tm_ty' <- isoType1 tm_ty;
                              return (Fun(Op(newQId, fx),tm_ty',b))
                            }
                          | _ -> {
                              tm_ty <- return (inferType(spc,tm)); 
                              isoTerm (spc, iso_info, iso_fn_info) tm_ty tm
                            };
                      return (Quotient(s', tm', a))
                    }
                  }
                %}}}
                %{{{  Subsort
                | Subsort (s, tm, a) -> {
                    s1 <- isoType1 s; 
                    if equalType?(s,s1) then
                      return ty
                    else {
                      tm' <-
                        case tm of
                          | Fun(Op(qid,fx), tm_ty, b) | recursive? -> {
                              % Shouldn't happen otherwise
                              newQId <- makeFreshQId spc qid;
                              tm_ty' <- isoType1 tm_ty;
                              return (Fun(Op(newQId, fx),tm_ty',b))
                            }
                          | _ -> {
                              tm_ty <- return (inferType(spc,tm)); 
                              isoTerm (spc, iso_info, iso_fn_info) tm_ty tm
                            };
                      return (Subsort (s1, tm', a))
                    }
                  }
                %}}}
                %{{{  Pi
                | Pi (tvs, ty1, a) -> {
                    ty1' <- isoType1 ty1;
                    return (Pi (tvs, ty1', a))
                  }
                %}}}
                %{{{  And
                | And(tys, a) -> {
                    tys' <- mapM isoType1 tys;
                    return (And(tys', a))
                  }
                %}}}
                | _ -> return ty
        in
          isoType1 ty
      %}}}
      %{{{  newPrimedTypes
      def newPrimedTypes(init_spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
         : SpecCalc.Env (IsoInfoList * Spec) =
        foldOverQualifierMap 
          (fn (_,_,info,result as (new_iso_info, spc)) ->
             let qid = primarySortName info in
             let Qualified(q,id) = qid in
             if typeInIsoInfoList(qid, iso_info) then
               return result
             else
               let (tvs,ty) = unpackFirstSortDef info in {
                 %% Use init_spec because priming algorithm assumes primed types haven't been added yet
                 ty' <- isoType (init_spc, iso_info, iso_fn_info) true ty;
                 % print("type "^printQualifiedId qid^" = "^printSort ty^"\n--> "^printSort ty'^"\n");
                 if equalType? (ty,ty') then
                   return result
                 else {
                   qid' <- makeFreshTypeQId spc qid;
                   let spc  = addTypeDef(spc, qid', maybePiSort(tvs, ty')) in
                   let qid_ref  = mkBase(qid, map mkTyVar tvs) in
                   let qid'_ref = mkBase(qid',map mkTyVar tvs) in
          
                   let iso_qid = Qualified(q,"iso"^id) in
                   let iso_ty  = mkArrow(qid_ref, qid'_ref) in
                   let iso_fn  = mkInfixOp(iso_qid, Unspecified, iso_ty) in
                   let spc = addOpDef(spc, iso_qid, Unspecified, maybePiTerm(tvs, SortedTerm(Any noPos, iso_ty, noPos))) in
    
                   let osi_qid = Qualified(q,"osi"^id) in
                   let osi_ty  = mkArrow(qid'_ref, qid_ref) in
                   let osi_fn  = mkInfixOp(osi_qid, Unspecified, osi_ty) in
                   let spc = addOpDef(spc, osi_qid, Unspecified, maybePiTerm(tvs, SortedTerm(Any noPos, osi_ty, noPos))) in
                   return
                     (Cons(((iso_fn, tvs, qid_ref, qid'_ref), (osi_fn, tvs, qid'_ref, qid_ref)),
                         new_iso_info),
                      spc)
                 }}) ([], init_spc) init_spc.sorts
      %}}}
      %{{{  makeDerivedOps
      %% (search-forward-regexp specware-definition-regexp) (match-string 0) (match-string 2)
      % Construct a map from a qualified id to the primed qualified id for
      % a new primed op.
      % Make map identity for ops whose type doesn't change but uses type internally
      def makeDerivedOps(spc: Spec,
                         iso_info: IsoInfoList,
                         iso_fn_info: IsoFnInfo)
         : SpecCalc.Env QualifiedIdMap =
        % Ignore the ops in the the list of pairs of iso's?
        let ign_qids = foldl (fn (result, ((Fun(Op(iso_qid,_),_,_),_,_,_), (Fun(Op(osi_qid,_),_,_),_,_,_))) ->
                                [iso_qid, osi_qid] ++ result)
                         [] iso_info
        in
        foldOverQualifierMap
          (fn (q, nm, info, result) ->
           let qid = Qualified(q,nm) in
           let (tvs, op_ty, dfn) = unpackFirstTerm info.dfn in
           if anyTerm? dfn then
             return result
           else {
             op_ty_pr <- isoType (spc, iso_info, iso_fn_info) false op_ty; 
             % ### LE - we are folding over ops. Is the equivType? test where we
             % establish whether the op depends on a type subject to an isomorphism?
             % is there overlap with the ignore list? 
             if qid in? ign_qids || some?(findTheOp(spc, makeDerivedQId qid))
               then return result
             else if equivType? spc (op_ty_pr,op_ty)
               then if existsTypeInTerm? (fn Base(qid, _, _) -> some?(lookupIsoInfo(qid, iso_info))
                                                 | _ -> false)
                         dfn
                     then let _ = writeLine("refine "^show qid) in
                          return (insertAQualifierMap(result, q, nm, qid))
                     else return result
            else {
              qid_pr <- makeFreshQId spc qid;
              return (insertAQualifierMap(result, q, nm, qid_pr))
            }
          }) emptyAQualifierMap spc.ops
      %}}}
      %{{{  makeDerivedOpDefs
      (* We are given a map as produced above, For each pair (qid,qid') we
      retrieve opinfo for qid and construct a pair (opinfo_1,opinfo_2) where
      opinfo_1 is a reference to qid' (via the isomorphisms) and opinfo_2
      is opinfo in the new type.  ### LE not sure I understand opinfo_2? *)
      def makeDerivedOpDefs(spc:           Spec,
                            iso_info:      IsoInfoList,
                            iso_fn_info:   IsoFnInfo,
                            base_src_QIds: List QualifiedId,
                            src_QIds:      List QualifiedId,
                            qidPrMap:      QualifiedIdMap)
         : SpecCalc.Env (List (OpInfo * OpInfo) * QualifiedIds) =
        foldOverQualifierMap
          (fn (q, nm, qid_pr, (result, transformQIds)) ->
           let qid = Qualified(q,nm) in
           let Some info = findTheOp(spc, qid) in
           let (tvs, op_ty, dfn) = unpackFirstTerm info.dfn in {
             type_opaque_in_term? <- return(checkTypeOpacity?(dfn, op_ty, base_src_QIds, src_QIds, spc));
             op_ty_pr <- isoType (spc, iso_info, iso_fn_info) false op_ty; 
             % qid_pr <- makeFreshQId spc qid;
             (dfn_pr, transformQIds) <-
               if type_opaque_in_term? then
                 return ((primeTermsTypes(dfn, qidPrMap, iso_info), transformQIds))
               else
                 {dfn_pr <- isoTerm (spc, iso_info, iso_fn_info) op_ty dfn;
                  return(dfn_pr, qid_pr :: transformQIds)};
             if type_opaque_in_term? then {
               print ("mdod: " ^ printQualifiedId qid_pr ^ " opaque!\n");
               when (nm = "andd")
                 (let prim_dfn = primeTermsTypes(dfn, qidPrMap, iso_info) in
                  print (printTermWithSorts dfn ^ "\n"
                           ^ printTermWithSorts prim_dfn^"\n" ^ printTerm prim_dfn^"\n"))
             }
             else
               {print ("mdod: "^printQualifiedId qid_pr^" not opaque\n");
                when (nm = "andd") (print(printTermWithSorts dfn^"\n"))};
             if qid = qid_pr
               then    % refine def instead of generating new one
               return ((addRefinedDefToOpinfo(info, dfn_pr),
                        info)
                       :: result,
                       transformQIds)   
             else {
             qid_pr_ref <- return (mkInfixOp(qid_pr,info.fixity,op_ty_pr)); 
             id_def_pr <- return (makeTrivialDef(spc, dfn_pr, qid_pr_ref));
             new_dfn <- osiTerm (spc, iso_info, iso_fn_info) op_ty_pr id_def_pr; 
             % createPrimeDef(spc, id_def_pr, op_ty_pr, trg_ty, src_ty, osi_ref, iso_ref) in
             return ((info << {dfn = maybePiTerm(tvs, SortedTerm(new_dfn, op_ty, noPos))},
                      info << {names = [qid_pr],
                               dfn = maybePiTerm(tvs, SortedTerm(dfn_pr, op_ty_pr, noPos))})
                       ::result,
                     transformQIds)
          }}) ([], []) qidPrMap
      %}}}
      %{{{  isoTypeFn 
      def isoTypeFn (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
                   (ty: Sort): SpecCalc.Env MS.Term =
        case ty of
          %{{{  Base
          | Base(qid,params,a) ->
            (case lookupIsoFnInfo(qid,iso_fn_info) of  % find if qid is on the lhs of an iso pair
               | Some qid' ->
                 (case params of
                    | [p_ty] -> {
                        p_ty' <- isoType (spc, iso_info, iso_fn_info) false p_ty;
                        arg_iso_fn <- isoTypeFn (spc, iso_info, iso_fn_info) p_ty; 
                        return (mkHOIsoFn(qid, qid', arg_iso_fn, p_ty, p_ty', spc))
                      }
                    | _ -> fail("Multi-parameter types not yet handled: "^printQualifiedId qid))
               | None ->
                   (case lookupIsoInfo(qid, iso_info) of
                     | Some ((iso_fn,_,_,_),_) ->
                       (case typeMatch(domain(spc, inferType(spc, iso_fn)), ty, spc, false) of
                         | None -> return iso_fn         % Shouldn't happen
                         | Some subst -> return (instantiateTyVarsInTerm(iso_fn, subst)))
                     | None ->
                        let uf_ty = unfoldBaseOne(spc, ty) in
                        if ty = uf_ty then
                          return (identityFn ty)
                        else
                          isoTypeFn (spc, iso_info, iso_fn_info) uf_ty))
          %}}}
          %{{{  Arrow
          | Arrow(dom,ran,_) -> {
              fnarg <- return ("f",ty); 
              iso <- isoTypeFn (spc, iso_info, iso_fn_info) ran;
              osi <- osiTypeFn (spc, iso_info, iso_fn_info) dom;
              return (mkLambda(mkVarPat fnarg, mkCompose(iso, mkCompose(mkVar fnarg, osi, spc), spc)))
            }
          %}}}
          %{{{  Product
          | Product (row, a) -> {
              xv <- return ("x",ty); 
              pairs <-
                mapM (fn (id,i_ty) -> {
                  iso_proj <- isoTerm (spc, iso_info, iso_fn_info) i_ty (mkProjection(id,mkVar xv));
                  return (id, iso_proj)
                }) row;
              return (mkLambda(mkVarPat xv, mkRecord pairs))
            }
          %}}}
          %{{{  Coproduct
          | CoProduct (row, a) -> {
              xv <- return ("x",ty);
              matches <-
                mapM (fn (id,o_i_ty) ->
                      case o_i_ty of
                           | None -> return (mkEmbedPat(id,None,ty), trueTerm, mkEmbed0(id,ty))
                           | Some i_ty -> {
                               yv <- return ("y",i_ty); 
                               iso <- isoTerm (spc, iso_info, iso_fn_info) i_ty (mkVar yv);
                               return (mkEmbedPat(id,Some(mkVarPat yv),ty), trueTerm,
                                         mkApply(mkEmbed1(id,mkArrow(i_ty,ty)), iso))
                             }) row;
              return (mkLambda(mkVarPat xv, mkApply(Lambda (matches,noPos), mkVar xv)))
            }
          %}}}
          %{{{  Subsort
          | Subsort (sub_sort, trm, a) -> {
              xv <- return ("x",ty); 
              iso <- isoTerm (spc, iso_info, iso_fn_info) sub_sort (mkVar xv);
              return (mkLambda(mkVarPat xv, iso))
            }
          %}}}
      %     | Quotient (super_sort, trm, a) ->  %% Shouldn't happen as quotients should be at top level
          | _ -> return (identityFn ty)
      %}}}
      %{{{  osiTypeFn 
      def osiTypeFn (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
                   (ty: Sort): SpecCalc.Env MS.Term = {
          ty' <- isoType (spc, iso_info, iso_fn_info) false ty;
          isoTypeFn (spc, invertIsoInfo iso_info, iso_fn_info) ty'
        }
      %}}}
      %{{{  osiTerm 
      def osiTerm (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
                 (ty: Sort)
                 (tm: MS.Term): SpecCalc.Env MS.Term = {
          ty' <- isoType (spc, iso_info, iso_fn_info) false ty;
          isoTerm (spc, invertIsoInfo iso_info, iso_fn_info) ty' tm
        }
      %}}}
      %{{{  addIsoDefForIso   CHECK THIS
      def addIsoDefForIso (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo) (iso_ref: MS.Term): SpecCalc.Env Spec =
        case iso_ref of
          | Fun(Op(qid,fixity),ty,_) ->
            (case findTheOp(spc, qid) of
               | Some opinfo -> {
                   (tvs, srt as Arrow(dom,ran,_)) <-
                     case unpackFirstTerm opinfo.dfn of
                       | (tvs, srt as Arrow(dom,ran,_), _) -> return (tvs,srt)
                       | (_,srt,_) -> escape ("addIsoDefForIso: srt=" ^ anyToString srt ^ "\n");
                   uf_dom <- return (unfoldBaseOne(spc, dom));
                   newtm <-
                     case uf_dom of
                       | Quotient (super_sort, trm, a) -> {
                           xv <- return ("x",ty); 
                           yv <- return ("y",super_sort);
                           qid' <- 
                             case ran of
                               | Base(qid',_,_) -> return qid'
                               | _ -> escape ("addIsoDefForIso: ran=" ^ anyToString ran ^ "\n");
                           iso <- isoTerm (spc, iso_info, iso_fn_info) super_sort (mkVar yv);
                           return (mkLambda(mkVarPat xv,
                                  mkApply(mkChooseFun(dom, ty, ran,
                                                      mkLambda(mkVarPat yv,
                                                               mkQuotient(iso,qid',super_sort))),
                                          mkVar xv)))
                         }
                       | _ -> isoTypeFn (spc, iso_info, iso_fn_info) uf_dom;
                   newdfn <- return (maybePiTerm(tvs, SortedTerm (newtm, srt, termAnn opinfo.dfn)));
                   return (setOpInfo(spc,qid,opinfo << {dfn = newdfn}))
                 }
               | _ -> escape ("addIsoDefForIso: findTheOp failed qid=" ^ printQualifiedId qid ^ "\n"))
          | _ -> return spc
      %}}}
    in catch {
    %{{{  Extend the list
    % We are given a list of pairs of qids for ops purporting to be isomorphisms.
    % For each pair (qid1,qid2) we contruct a pair of 'infos' where an info
    % is a tuple consisting of (t,tvs,dom,cod) where
    %  t is a term referring to the op
    %  tvs are the type variables in the definition of of the op
    %  dom is the type for the domain of the op
    %  cod is the type for the codomain of the op
    base_iso_info <-
      mapM (fn (iso_qid, osi_qid) -> {
        iso_info <- findOpInfo spc iso_qid;
        osi_info <- findOpInfo spc osi_qid;
        return (iso_info,osi_info)
      }) iso_qid_prs;
    %}}}
    %{{{  Check compatibility of iso and osi
    mapM (fn ((iso,tvs,src_ty,trg_ty), (osi,inv_tvs,inv_src_ty,inv_trg_ty)) -> {
      when (~(length tvs = length inv_tvs
        && equivType? spc (src_ty,inv_trg_ty)
        && equivType? spc (trg_ty,inv_src_ty)))
          (escape (printTerm iso ^ " and " ^ printTerm osi ^ " types not inverses\n"));
      return ()
    }) base_iso_info;
    %}}}
    %{{{  get qid for src type for each iso (not osi) function
    base_src_QIds <- 
      mapM (fn ((_,_,src_ty,_),_) ->
        case src_ty of
          | Base(qid, _, _) -> return qid 
          | _ -> escape ("Domain of iso is not a named type\n")) base_iso_info;
    %}}}
    %{{{  find complex isos
    (* It may be that the spec provides ops that lift bijections to
    higher types.  For example, given isomorphic types A <-> B, then
    the map operator can lift the iso to an isomorphism to List A <->
    List B Later look to generate such liftings *)
    iso_fn_info <- return (findComplexIsoFns spc);
    %}}}

    (* For each type T in the spec that depends on one or more types,
    X_i, in the domain of an op in the iso pairs f_i:X_i <-> Y_i:g_i,
    extend the spec with new 'primed' type T' with each X_i replaced with
    Y_i. Also add placeholders for ops that witness the isomorphism T <->
    T'. Return the new spec plus an additional collection of iso_infos
    for the new types. No theorems for the iso's are added *)
    (prime_type_iso_info, spc) <- newPrimedTypes(spc, base_iso_info, iso_fn_info); 

    iso_info <- return (base_iso_info ++ prime_type_iso_info);

    src_QIds <- return (map srcQId iso_info);

    print (ppFormat (
      ppConcat [
        ppString "Domain QId's:",
        ppNewline,
        ppSep ppNewline (map (fn q -> ppString (printQualifiedId q)) src_QIds),
        ppNewline
      ]));

    %{{{  handle special case of monomorphic references to polymorphic functions 
    spc <-
      let
        %{{{  doPattern
        def doPattern accum pat =
          case pat of 
            %{{{  AliasPat
            | AliasPat (pat1,pat2,pos) -> {
                (accum,pat1) <- doPattern accum pat1;
                (accum,pat2) <- doPattern accum pat2;
                return (accum,AliasPat(pat1,pat2,pos))
              }
            %}}}
            %{{{  EmbedPat
            | EmbedPat (id,optPat,typ,pos) -> {
                (accum,optPat) <-
                  case optPat of
                    | None -> return (accum, None)
                    | Some pat -> {
                        (accum,pat) <- doPattern accum pat;
                        return (accum, Some pat)
                      };
                (accum,typ) <- doType accum typ;
                return (accum, EmbedPat (id,optPat,typ,pos))
              }
            %}}}
            %{{{  RecordPat
            | RecordPat (pairs,pos) -> {
                (accum,pairs) <-
                  doList (fn accum -> fn (id,pat) -> {
                    (accum,pat) <- doPattern accum pat;
                    return (accum,(id,pat))
                  }) accum pairs;
                return (accum, RecordPat (pairs,pos))
              }
            %}}}
            %{{{  WildPat
            | WildPat (typ,pos) -> {
                (accum,typ) <- doType accum typ;
                return (accum, WildPat (typ,pos))
              }
            %}}}
            %{{{  QuotientPat
            | QuotientPat (pat,typName,pos) -> {
                (accum,pat) <- doPattern accum pat;
                return (accum, QuotientPat (pat,typName,pos))
              }
            %}}}
            %{{{  RestrictedPat
            | RestrictedPat (pat,trm,pos) -> {
                (accum,pat) <- doPattern accum pat;
                (accum,trm) <- doTerm accum trm boolSort;  % ### LE Check!
                return (accum, RestrictedPat (pat,trm,pos))
              }
            %}}}
            %{{{  SortedPat
            | SortedPat (pat,typ,pos) -> {
                (accum,pat) <- doPattern accum pat;
                (accum,typ) <- doType accum typ;
                return (accum, SortedPat (pat,typ,pos))
              }
            %}}}
            | _ -> return (accum,pat)
        %}}}
        %{{{  doType
        def doType accum typ =
          case typ of
            %{{{  Arrow
            | Arrow (typ1,typ2,pos) -> {
                (accum, typ1) <- doType accum typ1;
                (accum, typ2) <- doType accum typ2;
                return (accum, Arrow (typ1,typ2,pos))
              }
            %}}}
            %{{{  Product
            | Product (pairs,pos) -> {
                (accum,pairs) <-
                  doList (fn accum -> fn (id,typ) -> {
                    (accum,typ) <- doType accum typ;
                    return (accum, (id,typ))
                  }) accum pairs;
                return (accum,Product(pairs,pos))
              }
            %}}}
            %{{{  CoProduct
            | CoProduct (pairs,pos) -> {
                (accum,pairs) <-
                  doList (fn accum -> fn (id,optTyp) ->
                    case optTyp of
                      | None -> return (accum, (id,optTyp))
                      | Some typ -> {
                          (accum,typ) <- doType accum typ;
                          return (accum,(id,Some typ))
                        }) accum pairs;
                return (accum,CoProduct (pairs,pos))
              }
            %}}}
            %{{{  Quotient
            | Quotient (typ,trm,pos) -> {
                (accum,typ) <- doType accum typ;
                (accum,trm) <- doTerm accum trm (mkArrow (mkProduct [typ,typ], boolSort));
                return (accum, Quotient (typ,trm,pos))
              }
            %}}}
            %{{{  Subsort
            | Subsort (typ,trm,pos) -> {
                (accum,typ) <- doType accum typ;
                (accum,trm) <- doTerm accum trm (mkArrow (typ,boolSort));
                return (accum, Subsort (typ,trm,pos))
              }
            %}}}
                %{{{  Pi
            | Pi (tyVars,typ,pos) -> {
                (accum,typ) <- doType accum typ;
                return (accum, Pi (tyVars,typ,pos))
              }
                %}}}
                %{{{  Base
            | Base (qid,typs,pos) -> {
                (accum,typs) <- doList doType accum typs;
                return (accum,Base (qid,typs,pos))
              }
                %}}}
            | _ -> return (accum,typ)
(*

            | Boolean b
            | TyVar TyVar * b
            | MetaTyVar    AMetaTyVar b * b  % Before elaborateSpec
            | And List (ASort b) * b  
            | Any b  % e.g. "sort S a b c "  has defn:  Pi ([a,b,c], Any p1, p2)
*)
        %}}}
        %{{{  doTerm
        def doTerm accum trm ctxtType = {
          when traceMono? (print ("doTerm:  " ^ printTerm trm ^ "\n"));
          when traceMono? (print ("  dnType=" ^ printSort ctxtType ^ "\n"));
          case trm of
            %{{{  Fun (Op (qid, fxty), ty, pos)
            | Fun (Op(qid, fxty), ty, pos) ->
                let
                  %{{{  monoInstance
                  def monoInstance dnType upType =
                   (if traceMono? then (writeLine ("mono dnType=" ^ printSort dnType);
                                        writeLine ("     upType=" ^ printSort upType))
                      else ();
                    case (dnType,upType) of
                      | (Base (dnQid,dnTypes,_), _) ->
                          if (dnQid in? src_QIds) && (dnTypes = []) then
                            case upType of
                              | Base (upQid,_::_,_) -> true
                              | _ -> false   % ### LE This is wrong what if it is eg (A -> Nat)
                          else
                            false   % ### LE or perhaps we need to unfold to the penultimate type (a Base)
                      | (Arrow (dnDom,dnCod,_), Arrow (upDom,upCod,_)) ->
                          % ### LE This test is not entirely correct. If we are
                          % comparing types (BitList -> X) with (List Bit -> Y) then
                          % the domain on the left is certainly a monomorphic instance
                          % of domain the right. But we only want the predicate to
                          % hold on the function space when X and Y are monomophic.
                          (monoInstance dnDom upDom) || (monoInstance dnCod upCod) 
                      | (Product (dnPairs,_), Product (upPairs,_)) ->
                          exists? (fn ((_,dnType),(_,upType)) -> monoInstance dnType upType) (zip (dnPairs,upPairs))
                      | (CoProduct (dnPairs,_), CoProduct (upPairs,_)) ->  % ### But we only find sums at the top level
                          exists? 
                          (fn | ((_,None),(_,None)) -> true
                              | ((_,Some dnType), (_,Some upType)) -> monoInstance dnType upType
                              | _ -> fail ("doTerm: monoInstance: coproduct\n")) (zip (dnPairs,upPairs))
                      | (Subsort (dnType,_,_),Subsort (upType,_,_)) -> monoInstance dnType upType
                      | (Subsort (dnType,_,_),                   _) -> monoInstance dnType upType
                      | (                   _,Subsort (upType,_,_)) -> monoInstance dnType upType
                      | (Quotient (dnType,_,_),Quotient (upType,_,_)) -> monoInstance dnType upType
                      | (TyVar _, _) -> false
                      | (_, TyVar _) -> false
                      | (MetaTyVar _, _) -> false
                      | (_, MetaTyVar _) -> false
                      | (Boolean _,_) -> false
                      | (_,Boolean _) -> false
                      | _ -> (%writeLine ("doTerm: monoInstance:\n  dnType=" ^ printSort dnType
                              %             ^ "\n  upType=" ^ printSort upType);
                              false))
                  %}}}
                in
                  if monoInstance ctxtType ty then {
                    print ("found monomorphic instance of " ^ printQualifiedId qid ^ "\n");
                    Qualified (qual,id) <- return qid;
                    (spc,opsDone) <- return accum;
                    %{{{  check if there has been an earlier occurrence of the name 
                    % In which case much of the work has already been done
                    found <- foldM (fn found -> fn (otherQual,otherId,otherTyp) ->
                        if found then
                          return found
                        else
                          if id = otherId then
                            if qual ~= otherQual then
                              if some? newOptQual
                                then escape ("applyIso: disparately qualified functions subject to iso transformation: "
                                               ^ qual ^ "." ^ id ^ " and " ^ otherQual ^ "." ^ id ^ "\n")
                                else return false
                            else
                              if ~(equivType? spc (maybePiSort(freeTyVars ty, ty),maybePiSort (freeTyVars otherTyp, otherTyp))) then {
                                print "makeIsomorphism: two functions with common qualified id by disparate types subject to iso transformation\n";
                                print ("funType: " ^ (printSort ty) ^ "\n");
                                print ("otherType: " ^ (printSort otherTyp) ^ "\n");
                                print "ignoring\n";
                                return true
                              }
                              else
                                return true  %  op with same qualifier, id and type already occurs
                          else
                            return false) false opsDone;
                    %}}}
                    % ### LE Need to think about how to names these - 
                    % The names generated here (copies of instantiated polymorphic
                    % functions) serve a different purpose from those generated
                    % as a result of applying the isomorphism transformation
                    newQId <- return (mkQualifiedId (qual ^ "*",id));
                    if ~found then {
                      %{{{  create a new op and replace this reference
                      % But first we must recursively transform the body of the new op
                      opsDone <- return (Cons ((qual,id,ty),opsDone));
                      info <- Env.findTheOp spc (mkQualifiedId (qual,id));
                      (defTypeVars,defnType,defnTerm) <- return (unpackFirstTerm info.dfn);
                      monoDefn <- case typeMatch(defnType, ty, spc, true) of
                         | None -> {
                             print ("defnType: " ^ printSort defnType ^ "\n");
                             print ("upType: " ^ printSort ty ^ "\n");
                             escape "makeIsoMorphism: typeMatch failed\n"
                           }
                         | Some subst -> return (instantiateTyVarsInTerm(defnTerm, subst));
                      ((spc,opsDone),defnTerm) <- doTerm (spc,opsDone) monoDefn ctxtType;
                      newDefnTerm <- return (SortedTerm (defnTerm, ctxtType,noPos));
                      spc <- return (addOpDef (spc, newQId, info.fixity, newDefnTerm));
                      print ("doTerm: adding defn " ^ printQualifiedId newQId ^ " : " ^ printTerm newDefnTerm ^ "\n");
                      return ((spc,opsDone), Fun (Op(newQId, fxty), ctxtType, pos))
                      %}}}
                    }
                    else {
                      print ("Already processed: " ^ printQualifiedId qid ^ "\n");
                      return (accum, Fun (Op(newQId, fxty), ctxtType, pos))
                    }
                  }
                  else
                    return (accum,trm)
            %}}}
            %{{{  Apply
            | Apply (M, N, pos) -> {
                (dom,cod) <- return (arrow(spc,inferType(spc, M)));
                when traceMono? {print ("doTerm: Apply: inferType M gives:\n");
                                 print ("  dom=" ^ printSort dom ^ "\n");
                                 print ("  cod=" ^ printSort cod ^ "\n");
                                 print ("doTerm: Apply: inferType N gives:\n")};
                dom <- return (inferType(spc, N));
                when traceMono? (print ("  dom=" ^ printSort dom ^ "\n"));
                (accum,M) <- doTerm accum M (mkArrow(dom,ctxtType));   % ### LE range ctxtType and cod should agree
                (accum,N) <- doTerm accum N dom;
                return (accum, Apply (M, N, pos))
              }
            %}}}
            %{{{  Record (pairs,pos)
            | Record (pairs, pos) -> {
                types <- return (recordTypes(spc,ctxtType));
                when (length types ~= length pairs)
                  (print("zip3err:\n"^printTerm trm^ " :\n"^ printSort ctxtType));
                triples <- 
                  let
                    def zip3 trms typs =
                      case (trms,typs) of
                        | ([],[]) -> []
                        | ((id,trm)::trms,typ::typs) -> (id,trm,typ) :: (zip3 trms typs)
                  in
                    return (zip3 pairs types);
                (accum,pairs) <-
                  doList (fn accum -> fn (id,trm,typ) -> {
                      (accum,trm) <- doTerm accum trm typ;
                      return (accum,(id,trm))   
                    }) accum triples;
                return (accum,Record (pairs,pos))
              }
            %}}}
            %{{{  Bind
            | Bind (binder,vars,trm,pos) -> {
                (accum,trm) <- doTerm accum trm boolSort;
                return (accum,Bind (binder,vars,trm,pos))       
              }
            %}}}
            %{{{  The
            | The (var,trm,pos) -> {
                (accum,trm) <- doTerm accum trm boolSort;
                return (accum,The (var,trm,pos))       
              }
            %}}}
            %{{{  Let
            | Let (decls,trm,pos) -> {
                (accum,decls) <-
                  doList (fn accum -> fn (pat,rhs) -> {
                      (accum,pat) <- doPattern accum pat;
                      (accum,rhs) <- doTerm accum rhs (patternSort pat);
                      return (accum,(pat,rhs))
                    }) accum decls;
                (accum,trm) <- doTerm accum trm ctxtType;
                return (accum,Let (decls,trm,pos))
              }
            %}}}
            %{{{  LetRec
            | LetRec (decls,trm,pos) -> {
                (accum,decls) <-
                  doList (fn accum -> fn (var as (id,typ),rhs) -> {
                      (accum,rhs) <- doTerm accum rhs typ;
                      return (accum,(var,rhs))
                    }) accum decls;
                (accum,trm) <- doTerm accum trm ctxtType;
                return (accum,LetRec (decls,trm,pos))
              }
            %}}}
            %{{{  Lambda
            | Lambda (matches,pos) -> {
                (accum,matches) <- 
                  doList (fn accum -> fn (pat,cond,trm) -> {
                      (accum,pat) <- doPattern accum pat;    % ### LE Should be (domain ctxtType)
                      (accum,cond) <- doTerm accum cond boolSort;
                      (accum,trm) <- doTerm accum trm (range (spc, ctxtType));
                      return (accum,(pat,cond,trm))
                    }) accum matches;
                return (accum,Lambda (matches,pos))
              }
            %}}}
            %{{{  IfThenElse
            | IfThenElse (pred,t1,t2,pos) -> {
                (accum,pred) <- doTerm accum pred boolSort;
                (accum,t1) <- doTerm accum t1 ctxtType;
                (accum,t2) <- doTerm accum t2 ctxtType;
                return (accum,IfThenElse (pred,t1,t2,pos))
              }
            %}}}
            %{{{  SortedTerm
            | SortedTerm (trm,typ,pos) -> {
                (accum,trm) <- doTerm accum trm typ;
                (accum,typ) <- doType accum typ;
                return (accum,SortedTerm (trm,typ,pos))
              }
            %}}}
            %{{{  Var
            | Var ((id,typ),pos) -> {
                when traceMono? (print ("doTerm: Var: id=" ^ id ^ "\n"));
                when traceMono? (print ("  typ=" ^ printSort typ ^ "\n"));
                return (accum,trm)
              }
            %}}}
            | _ -> return (accum,trm)
          }
        %}}}
        %{{{ doOp 
        def doOp (qual,id,opInfo,(spc,opsDone)) = {
            % ### LE what's the difference between unpackTerm and unpackFirstTerm?
            % ### LE we are folding over ops - but don't need to do the aliases.
            % ### LE Should we also 'doType typ' in the following.
            % ### LE This doesn't handle aliases properly
            % print ("doOp: " ^ qual ^ "." ^ id ^ ":" ^ printTerm opInfo.dfn ^ "\n");
            (typVars,typ,trm) <- return (unpackFirstTerm opInfo.dfn);  
            ((spc,opsDone),trm) <- doTerm (spc,opsDone) trm typ ;
            dfn <- return (maybePiTerm(typVars, SortedTerm (trm, typ, noPos))); 
            ops <- return (insertAQualifierMap (spc.ops,qual,id,opInfo << {dfn = dfn}));
            return (spc << {ops = ops},opsDone)
          }
        %}}}
        %{{{ doSort 
        def doSort (qual,id,sortInfo,(spc,opsDone)) = {
            ((spc,opsDone),dfn) <- doType (spc,opsDone) sortInfo.dfn;
            sorts <- return (insertAQualifierMap (spc.sorts,qual,id,sortInfo << {dfn = dfn}));
            return (spc << {sorts = sorts},opsDone)
          }
        %}}}
        def matchingQualifier (qual,_) = return (case newOptQual of
                                                   | Some newQual -> qual = newQual
                                                   | None -> false)
      in {
          %print ("applyIso: Qualifier=" ^ newQual ^"\n");
          %{{{  Fail if new qualifier conflicts with those in use
          % b1 <- existsQMap matchingQualifier spc.ops;
          % b2 <- existsQMap matchingQualifier spc.sorts;
          % when (b1 || b2) 
            % (escape ("Iso: new qualifier '" ^ newQual ^ "' conflicts with existing qualifiers\n"));
          %}}}
          % ### LE perhaps make "opsDone" a qualifier map rather than a list.
          (spc,opsDone) <- foldOverQualifierMap doOp (spc,[]) spc.ops;
          (spc,opsDone) <- foldOverQualifierMap doSort (spc,opsDone) spc.sorts;
          return spc 
      };
    %}}}

    print "adding definitions\n";
    %{{{  Add definitions for newly introduced iso fns - why is this separate?

    spc <-
      foldM (fn spc -> fn ((iso_ref,tvs,src_ty,trg_ty), (osi_ref,_,_,_)) -> {
        spc <- addIsoDefForIso(spc,iso_info,iso_fn_info) iso_ref;
        spc <- addIsoDefForIso(spc,invertIsoInfo iso_info,iso_fn_info) osi_ref;
        return spc
      }) spc prime_type_iso_info; 
    %}}}
    %{{{  Add the theorems that reflect that the isos are inverses 
    (spc, iso_thm_qids) <-
        return (foldl (fn ((spc, iso_thm_qids), ((iso_ref,tvs,src_ty,trg_ty), (osi_ref,_,_,_))) ->
                 makeIsoTheorems(spc, iso_ref, osi_ref, tvs, src_ty, trg_ty, iso_thm_qids))
          (spc, []) iso_info);
    %}}}
    print "make derived ops\n";
    %{{{  make derived ops
    (* For each operator "op f = t" whose type depends on one or more iso types
    X_i <-> Y_i, construct a new operator op f' = s' where 's' is expressed in terms
    of types Y_i. Also replace "t" with a term "t'" expressed in terms of "f'".The
    latter is needed as the new definition of "f" will be used to generate a rewrite
    rule enabling references to "f" to be replaced by references to "f'" *)
    % ### LE why is this two passes?
    qidPrMap <- makeDerivedOps(spc, iso_info, iso_fn_info); 
    %}}}
    qidPr_Set <- return(invertQualifiedIdMap qidPrMap);

    print "make derived op definitions\n";
    (new_defs, transformQIds) <- makeDerivedOpDefs(spc, iso_info, iso_fn_info, base_src_QIds, src_QIds, qidPrMap);
    print(show(length transformQIds)^" non opaque ops to transform.\n");
    let spc = foldl (fn (spc, (opinfo,opinfo_pr)) ->
                     let qid  = head opinfo.names in
                     let qid_pr = head opinfo_pr.names in
                     let spc = setOpInfo(spc,qid,opinfo) in
                     if qid = qid_pr
                       then   % Transformed
                       let spc = appendElement(spc, OpDef(qid, numTerms opinfo.dfn, noPos)) in
                       spc
                     else
                     let spc = appendElement(spc,Op(qid_pr,true,noPos)) in
                     let spc = setOpInfo(spc,qid_pr,opinfo_pr) in
                     spc)
                spc new_defs
    in
    % let _ = writeLine(printSpec spc) in
    %% Remove transformed defs
    let new_defs = filter (fn (opinfo,opinfo_pr) -> head opinfo.names ~= head opinfo_pr.names) new_defs in
    let recursive_ops = recursiveOps spc in
    (* Now construct a script to remove the ops defined in terms of
    the old types, create references to the new ops and simplify (eg
    replacing (osi (iso x)) with x). Note that we are not generating the
    rules here - rather a script of what rewrites and unfolds to apply *)
    let rewrite_old = map (fn (opinfo,_) -> Rewrite(head opinfo.names)) new_defs in
    let unfold_old  = map (fn (opinfo,_) -> Unfold (head opinfo.names)) new_defs in
    let iso_osi_rewrites = map (fn qid -> LeftToRight qid) iso_thm_qids in

    let osi_unfolds = mapPartial (fn (_,(Fun(Op(osi_qid,_),_,_),_,_,_)) ->
                                    if osi_qid in? recursive_ops
                                      || ~(definedOp?(spc, osi_qid))
                                      then None
                                      else Some(Unfold osi_qid))
                        iso_info
    in
    let iso_intro_unfolds = mapPartial (fn ((Fun(Op(iso_qid,_),_,_),_,_,_),_) ->
                                          if iso_qid in? recursive_ops then None
                                          else Some(Unfold iso_qid))
                              prime_type_iso_info
    in
    % let _ = writeLine("intro: "^anyToString iso_intro_unfolds) in
    let iso_unfolds = mapPartial (fn ((Fun(Op(iso_qid,_),_,_),_,_,_),_) ->
                                    if iso_qid in? recursive_ops then None
                                      else Some(Unfold iso_qid))
                        iso_info
    in
    % let _ = writeLine("iso: "^anyToString iso_unfolds) in
    let complex_iso_fn_unfolds = map (fn (_,qid) -> Rewrite qid) iso_fn_info in
    let gen_unfolds = [Unfold(mkQualifiedId("Function","o")),
                       Rewrite(mkQualifiedId("Function","id")),
                       Unfold(mkQualifiedId("Option","mapOption"))]
    in
    let main_script =
      Steps([% SimpStandard,
             Simplify (gen_unfolds
              % ++ iso_osi_rewrites
              % ++ osi_unfolds
              ++ complex_iso_fn_unfolds
              ++ rewrite_old
              ++ iso_osi_rewrites
              ++ extra_rules)
            ] ++
            [Simplify (gen_unfolds
              ++ complex_iso_fn_unfolds
              ++ iso_intro_unfolds
              ++ rewrite_old
              ++ iso_osi_rewrites
              ++ osi_unfolds
              ++ extra_rules)
               % AbstractCommonExpressions
             ] ++
             [Simplify (gen_unfolds
              ++ unfold_old
              ++ iso_osi_rewrites
              ++ osi_unfolds
              ++ iso_unfolds
              ++ extra_rules)
               % AbstractCommonExpressions
             ])
    in {

    (* Rewriting is performed on individual ops rather than on the entire spec. *)

    print "rewriting ... \n";
    print (scriptToString main_script^"\n"); 
    simp_ops
       <- Env.mapOpInfos
           (fn opinfo ->
              if exists? (fn (hidden_opinfo,_) -> opinfo = hidden_opinfo) new_defs then
                return opinfo
              else {
%                 when (existsSubTerm (fn t -> case t of
%                       | And(_::(_::_),_) -> true
%                       | _ -> false) opinfo.dfn) {
%                   print ("Multiple defs for " ^ printQualifiedId (head opinfo.names));
%                   escape (printTerm opinfo.dfn)
%                 };
                (tvs, ty, dfn) <- return (unpackFirstTerm opinfo.dfn);
                (qid as Qualified(q, id)) <- return (head opinfo.names);
                (simp_dfn,_) <-
                  if simplifyIsomorphism? then
                   { % print ("\nSimplify "^id^" ?\n"^printTerm dfn^"\n");
                    b <- existsSubTerm (fn t ->
                                          let ty = inferType(spc, t) in
                                          {isoTy <- isoType (spc, iso_info, iso_fn_info) false ty;
                                           return (equalType?(ty, isoTy))})
                           dfn;
                    if (simplifyUnPrimed? || (derivedQId? qid && some?(findAQualifierMap(qidPr_Set, q, id)))
                          || findAQualifierMap(qidPrMap, q, id) = Some(Qualified(q, id)))
                      then {
                      when traceIsomorphismGenerator? 
                        (print ("Simplify? " ^ printQualifiedId qid ^ "\n"));
                      interpretTerm(spc, if qid in? transformQIds
                                          then main_script
                                          else opaqueSimplifyScript,
                                    dfn, ty, qid, false)
                    }
                    else
                      return (dfn, false)
                  }
                  else
                    return (dfn, false);
                if equalTerm?(dfn, simp_dfn) then
                  return opinfo
                else {
                  when traceIsomorphismGenerator?
                    (printDef (spc, qid));
                  new_dfn <- return (maybePiTerm(tvs, SortedTerm (simp_dfn, ty, noPos))); 
                  when traceIsomorphismGenerator? {
                     print ("\n" ^ printQualifiedId qid ^ ":");
                     print (printTerm simp_dfn ^ "\n")
                  };
                  return (opinfo \_guillemotleft {dfn = new_dfn})
                }}) spc.ops;
    spc <- return (spc \_guillemotleft {ops = simp_ops});
    spc <- return
     (if orderElements? then
       adjustElementOrder spc
     else
       spc);
    return spc
  }
}
  (fn 
    | Escape -> return spc
    | except -> raise except)
endspec
