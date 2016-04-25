(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


% This spec formalizes the notion of a path to a subterm of a term.
% Each term construct has an ordered list of immediate subterms, and a
% path is then a sequence of Nats specifying which immediate subterm
% to choose at each term.
%
% README: paths are backwards, meaning that the first "step" in a path
% is actually the last subterm to be chosen in that path.
%
% README: files that seem to depend explicitly on how paths into terms
% are defined, i.e., the order of subterms in immediateSubterms
% (relative to /Languages/MetaSlang unless stated otherwise):
%
% Specs/Printer.sw  -- seems to be wrong and also not used (see TODOs)
% Transformations/MetaRules.sw  -- in pathToLastConjunct and structureCondEx
% Transformations/Rewriter.sw
% Transformations/Script.sw
% /Provers/ToIsabelle/IsaPrinter.sw

PathTerm qualifying
spec
import ../Specs/Utilities

type APathTerm a = ATerm a * Path

type PathTerm = APathTerm Position.Position

 op [a] topTerm(ptm: APathTerm a): ATerm a = ptm.1
 op [a] pathTermPath(ptm: APathTerm a): Path = ptm.2

 op [a] immediateSubTerms(term: ATerm a): List (ATerm a) =
    map (fn (_,subTerm) -> subTerm) (immediateSubTermsWithBindings term)

  % Return None if the path is in the term, otherwise return the
  % largest valid suffix of path, the subterm at that suffix of path,
  % and the first (from right to left, since paths are backwards)
  % invalid element of path
  op [a] validPathTermWithErr ((term, path): APathTerm a)
  : Option (Path * ATerm a * Nat) =
    let def helper p =
      case p of
        | [] -> (term, None)
        | i::p' ->
          case helper p' of
            | (ret_tm, None) ->
              if i < length (immediateSubTerms ret_tm) then
                ((immediateSubTerms ret_tm)@i, None)
              else
                (ret_tm, Some (p', i))
            | ret -> ret
    in
    case helper path of
      | (ret_tm, Some (valid_prefix, bad_step)) ->
        Some (valid_prefix, ret_tm, bad_step)
      | _ -> None

  % Return true iff the path is in the term
  op [a] validPathTerm ((term, path): APathTerm a) : Bool =
    validPathTermWithErr (term, path) = None

  % Return true iff the first argument is an extension of the second,
  % i.e., iff path_long always points to a subterm of path_short
  op pathExtends? (path_long: Path, path_short: Path) : Bool =
    if length path_long < length path_short then false else
      let path_long_suffix = suffix (path_long, length path_short) in
      path_long_suffix = path_short

  % Take the difference of one path minus another, that is, the path
  % that would have to be prepended to path_short to get path_long.
  % This is the same as splitting the left-hand path, path_long, into
  % a prefix and a suffix, where the latter equals the right-hand
  % path, path_short. Stated differently, if we took the subterm of
  % some term at path_short, and then took the subterm of the result
  % at the path given by pathDifference, we would get the subterm of
  % term at path_long. Return None if the paths diverge from each
  % other.
  op pathDifference (path_long: Path, path_short: Path) : Option Path =
    if pathExtends? (path_long, path_short) then
      Some (prefix (path_long, length path_long - length path_short))
    else None

  op printPath (path : Path) : String =
    "[" ^ flatten (intersperse "," (map show path)) ^ "]"

  type ABindingTerm a = List (AVar a) * ATerm a
  type BindingTerm = ABindingTerm Position
  type APathBindingTerm a = ABindingTerm a * Path
  type PathBindingTerm = APathBindingTerm Position

  % Get the immediate subterms of a Match
  op [a] matchImmediateSubTermsWithBindings (match: AMatch a) : List (ABindingTerm a) =
    flatten (map (fn (pat, _, t) ->
                    let patt_vars = removeDuplicateVars (patternVars pat) in
                    (map (fn gd -> (patt_vars, gd)) (getAllPatternGuards pat))
                    ++ [(patt_vars, t)])
               match)

  % Get the immediate subterms of a term, along with the new bound
  % variables for each of these subterms. This function is the sole
  % definition for mapping paths in terms to subterms
  op [a] immediateSubTermsWithBindings(term: ATerm a): List (ABindingTerm a) =
    case term of
      | Apply(x, y, _) -> [([], x), ([], y)]
      | Record(l, _) -> map (fn (_, t) -> ([], t)) l
      | Bind(_, vars, body, _) -> [(vars, body)]
      | The(x, body, _)  -> [([x], body)]
      | Let (l, b, _) ->
        let vars = flatten (map (fn (pat, _) ->
                                   removeDuplicateVars (patternVars pat)) l) in
        (map (fn (_, t) -> ([], t)) l) ++ [(vars, b)]
      | LetRec (l, b, _) ->
        let vars = map (fn (var, _) -> var) l in
        (map (fn (_, t) -> (vars, t)) l) ++ [(vars, b)]
      | Lambda (l, _) -> matchImmediateSubTermsWithBindings l
      | IfThenElse(x, y, z, _) -> [([], x), ([], y), ([], z)]
      | Seq(l, _) -> map (fn t -> ([], t)) l
      | TypedTerm(x, ty, _) ->
        (case postCondn? ty of
           | None -> [([], x)]
           | Some (post, bvs) -> [([], x), (parameterBindings x ++ bvs, post)])
      | And(l, _) -> map (fn t -> ([], t)) l
      | _ -> []

  % Cound the number of immediateSubTerms of an AMatch
  op [a] countMatchSubTerms (match: AMatch a) : Nat =
    length (matchImmediateSubTermsWithBindings match)

  % return the immediateSubTerm number for the body of the ith case,
  % which is the last immediateSubTerm of the last body
  op [a] ithLambdaBodyPos (match: AMatch a, i: Nat) : Nat =
    countMatchSubTerms (prefix (match, i+1)) - 1

  % return the immediateSubTerm number for the jth guard in the ith
  % pattern in a match
  op [a] lambdaGuardPos (match: AMatch a, i: Nat, j: Nat) : Nat =
    countMatchSubTerms (prefix (match, i)) + j

  % determine if an immediateSubTerm number points to the body of one of the
  % branches of a case expression (instead of a pattern guard), and, if so,
  % return which branch it is
  op [a] lambdaPosBranchNumber (match: AMatch a, pos: Nat) : Option Nat =
    let def aux (cases, i, cur_pos) =
      case cases of
        | [] -> fail ("lambdaPosBranchNumber: pos not valid for lambda")
        | (pat,_,_)::cases' ->
          let body_pos = cur_pos + length (getAllPatternGuards pat) in
          if pos = body_pos then Some i
          else if pos < body_pos then None else
            aux (cases', i+1, body_pos+1)
    in
    aux (match, 0, 0)

  op [a] ithSubTerm(term: ATerm a, i: Nat): ATerm a =
    let tms = immediateSubTerms term in
    if i < length tms
      then tms @ i
      else fail("Can't take subterm "^show i^" of term\n"^printTerm term)

  op ithSubTermWithBindings(term: MSTerm, i: Nat): BindingTerm =
    let tms_bindings = immediateSubTermsWithBindings term in
    if i < length tms_bindings
      then tms_bindings @ i
      else fail("Can't take subterm "^show i^" of term\n"^printTerm term)

  op ithSubTermWithBindings?(term: MSTerm, i: Nat): Option BindingTerm =
    let tms_bindings = immediateSubTermsWithBindings term in
    if i < length tms_bindings
      then Some(tms_bindings @ i)
      else None

  op [a] ithSubTerm?(term: ATerm a, i: Nat): Option(ATerm a) =
    let tms = immediateSubTerms term in
    if i < length tms then Some(tms @ i) else None

  op [a] toPathTerm(term: ATerm a): APathTerm a = (term, [])

  % tail-recursive version
  op [a] fromPathTerm((top_term, path): APathTerm a): ATerm a =
    foldl ithSubTerm top_term (reverse path)
  % op [a] fromPathTerm((top_term, path): APathTerm a): ATerm a =
  %   foldr (fn (i, tm) -> ithSubTerm(tm, i))
  %      top_term path

  op fromPathTermWithBindings((top_term, path): PathTerm): BindingTerm =
    foldl (fn ((vars, tm), i) ->
             let (new_vars, subterm) = ithSubTermWithBindings(tm, i) in
             (vars ++ new_vars, subterm))
       ([], top_term) (reverse path)
  % op fromPathTermWithBindings((top_term, path): PathTerm): BindingTerm =
  %   foldr (fn (i, (vars, tm)) ->
  %            let (new_vars, subterm) = ithSubTermWithBindings(tm, i) in
  %            (vars ++ new_vars, subterm))
  %      ([], top_term) path

  % A special version of the above for the Isabelle translator, which
  % removes the op ToIsa-Internal as well as an And constructors
  op fromPathTermWithBindingsAdjust((top_term, path): PathTerm): BindingTerm =
    let def aux(tm: MSTerm, path: Path, vars: MSVars): Option BindingTerm =
          % let _ = writeLine("aux: "^anyToString path^"\n"^printTerm tm) in
          let tm = case tm of
                     | Apply(Fun(Op(Qualified("ToIsa-Internal", _), _), _, _), t1, _) -> t1
                     | _ -> tm
          in
          case path of
            | [] -> Some(vars, tm)
            | i :: r_path -> 
          case ithSubTermWithBindings?(tm, i) of
            | Some(new_vars, subterm) ->
              (case aux(subterm, r_path, vars ++ new_vars) of
                | None -> 
                  (case tm of
                     | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) ->
                       let _ = writeLine "retry!" in
                       aux(q, path, vars)
                     | _ -> None)
                | rec_result -> rec_result) 
            | None -> None
    in
    case aux(top_term, reverse path, []) of
      | Some bterm -> bterm
      | None -> fail("Illegal path "^anyToString path^" for term "^printTerm top_term)
                 

  op fromPathBindingTerm((top_binding_term, path): PathBindingTerm): BindingTerm =
    foldl (fn ((vars, tm), i) ->
             let (new_vars, subterm) = ithSubTermWithBindings(tm, i) in
             (vars ++ new_vars, subterm))
       top_binding_term (reverse path)
  % op fromPathBindingTerm((top_binding_term, path): PathBindingTerm): BindingTerm =
  %   foldr (fn (i, (vars, tm)) ->
  %            let (new_vars, subterm) = ithSubTermWithBindings(tm, i) in
  %            (vars ++ new_vars, subterm))
  %      top_binding_term path

  % tail-recursive version of this function
  op [a] fromPathTerm?((top_term, path): APathTerm a): Option(ATerm a) =
    foldl (fn | (Some tm, i) -> ithSubTerm?(tm, i)
              | (None, i) -> None)
       (Some top_term) (reverse path)
  % op [a] fromPathTerm?((top_term, path): APathTerm a): Option(ATerm a) =
  %   foldr (fn (i, Some tm) -> ithSubTerm?(tm, i)
  %           | (i, None) -> None)
  %      (Some top_term) path

  op [a] nextToTopTerm((top_term, path): APathTerm a): ATerm a =
    if empty? path then top_term
      else ithSubTerm(top_term, last path)

  op [a] termFromTypedPathTerm(ptm: APathTerm a): ATerm a =
    case ptm.1 of
      | TypedTerm(tm, _, _) -> tm
      | tm -> tm

  op [a] parentTerm((top_term, path): APathTerm a): Option (APathTerm a) =
    case path of
      | _ :: par_path -> Some (top_term, par_path)
      | _ -> None

  op [a] grandParentTerm((top_term, path): APathTerm a): Option (APathTerm a) =
    case path of
      | _ :: _ :: gpar_path -> Some (top_term, gpar_path)
      | _ -> None

  op [a] moveToParent(ptm: APathTerm a): Option (APathTerm a) =
    case parentTerm ptm 
      | None -> None
      | Some par_ptm -> 
    case parentTerm par_ptm
      | None -> Some par_ptm
      | Some gpar_ptm -> 
    case fromPathTerm gpar_ptm
      | Apply(f, Record _, _) | infixFnTm? f -> % infix application
        Some gpar_ptm
      | _ -> Some par_ptm

  op [a] moveToFirst((top_term, path): APathTerm a): Option (APathTerm a) =
    if immediateSubTerms(fromPathTerm(top_term, path)) = [] then None
    else
      (case fromPathTerm(top_term, path) of
         | Apply(Lambda _, _, _) ->   % case expr
           Some(top_term, 1 :: path)
         | Apply(f, Record _, _) | infixFnTm? f -> % infix application
           Some(top_term, 0 :: 1 :: path)
         | _ -> Some(top_term, 0 :: path)) 

  op [a] moveToLast((top_term, path): APathTerm a): Option (APathTerm a) =
    let sub_tms = immediateSubTerms(fromPathTerm(top_term, path)) in
    if sub_tms = [] then None
    else
      (case fromPathTerm(top_term, path) of
         | Apply(Lambda _, _, _) ->   % case expr
           Some(top_term, 0 :: path)
         | Apply(f, Record _, _) | infixFnTm? f -> % infix application
           Some(top_term, 1 :: 1 :: path)
         | _ -> Some(top_term, (length sub_tms - 1) :: path)) 

  op [a] moveToNext((top_term, path): APathTerm a): Option (APathTerm a) =
    case path of
      | [] -> None
      | i :: r_path ->
    case fromPathTerm(top_term, r_path) of
      | Apply(Lambda _, _, _) ->   % parent is a case expr
        if i = 1 then Some(top_term, 0 :: r_path)
          else  % i = 0
            moveToNext(top_term, r_path) 
      | Apply(f, Record _, _) | infixFnTm? f ->
        if i = 0 then Some(top_term, 1 :: 1 :: r_path)
          else % i = 1
            moveToNext(top_term, r_path)
      | _ -> 
    case fromPathTerm?(top_term, i+1 :: r_path) of
      | Some _ -> Some(top_term, i+1 :: r_path)
      | None -> moveToNext(top_term, r_path)

  op [a] moveToPrev((top_term, path): APathTerm a):  Option(APathTerm a) =
    case path of
      | [] -> None
      | i :: r_path ->
    case fromPathTerm(top_term, r_path) of
      | Apply(Lambda _, _, _) ->   % parent is a case expr
        if i = 0 then Some(top_term, 1 :: r_path)
          else  % i = 0
            moveToPrev(top_term, r_path) 
      | _ -> 
    if i > 0 then Some(top_term, i-1 :: r_path)
      else moveToPrev(top_term, r_path)

  op [a] subTermIndicesSyntaxOrder(term: ATerm a): List Int =
    case term of
      | Apply(Lambda _, _, _) -> [1, 0]         % case expr
      | Apply(f, _, _) | infixFnTm? f -> [1]    % infix
      | tms -> tabulate(length(immediateSubTerms term), id)

  op [a] immediateSubTermsSyntaxOrder(term: ATerm a): List (ATerm a) =
    case immediateSubTerms term of
      | [f as Lambda _, x] -> [x, f]    % case
      | [f, x] | infixFnTm? f -> immediateSubTerms x    % infix
      | tms -> tms

  op [a] searchNextSt(path_term: APathTerm a, pred: ATerm a * APathTerm a -> Bool): Option(APathTerm a) =
    let def try_next(top_tm, path): Option(APathTerm a) =
          case path of
           | [] -> None
           | i :: r_path ->
         case subTermIndicesSyntaxOrder(fromPathTerm(top_tm, r_path)) of
           | [] -> None             % Shouldn't happen
           | inds -> 
             if i = last inds then try_next(top_tm, r_path)
               else let j = positionOf(inds, i) in
                    check_then_first(top_tm, (inds@(j+1)) :: r_path)
        def check_then_first(path_term: APathTerm a): Option(APathTerm a) =
          let term = fromPathTerm path_term in
          % let _ = writeLine("search: "^anyToString(reverse path_term.2)) in
          if pred (term, path_term)
            then Some path_term
          else try_first path_term
        def try_first (path_term as (top_term, path): APathTerm a): Option(APathTerm a) =
          let term = fromPathTerm path_term in
          case subTermIndicesSyntaxOrder term of
            | [] -> try_next path_term
            | i0 :: _ -> check_then_first(top_term, i0 :: path)
   in
   try_first path_term

 op [a] searchPrevSt(path_term: APathTerm a, pred: ATerm a * APathTerm a -> Bool):  Option(APathTerm a) =
   let def try_prev (top_tm, path) =
         case path of
           | [] -> None
           | i :: r_path ->
         case subTermIndicesSyntaxOrder(fromPathTerm(top_tm, r_path)) of
           | [] -> None             % Shouldn't happen
           | inds -> 
             if i = head inds then check_then_prev(top_tm, r_path)
               else let j = positionOf(inds, i) in
                    try_last(top_tm, (inds@(j-1)) :: r_path)
       def check_then_prev path_term =
         let term = fromPathTerm path_term in
         % let _ = writeLine("rsearch: "^anyToString(reverse path_term.2)) in
         if pred (term, path_term)
           then Some path_term
         else try_prev path_term
       def try_last (path_term as (top_term, path)) =
         let term = fromPathTerm path_term in
         case subTermIndicesSyntaxOrder term of
           | [] -> check_then_prev path_term
           | indices ->
             try_last(top_term, last indices :: path)
   in
   try_prev path_term

  op [a] replaceSubTerm(new_tm: ATerm a, (top_term, path): APathTerm a): APathTerm a =
    let def repl(tm, path) =
          % let _ = writeLine("rst: "^anyToString path^"\n"^printTerm tm) in
          case path of
            | [] -> new_tm
            | i :: r_path ->
          case tm of
            | Apply(x, y, a) ->
               if i = 0 
                 then Apply(repl(x, r_path), y, a)
                 else Apply(x, repl(y, r_path), a)
            | Record(l, a) ->
              Record(tabulate(length l, fn j -> let (id, t) = l@j in (id, if i = j then repl(t, r_path) else t)), a)
            | Bind(bdr, vs, x, a) -> Bind(bdr, vs, repl(x, r_path), a) 
            | The(vs, x, a)  -> The(vs, repl(x, r_path), a)
            | Let (l, b, a) ->
              let len = length l in
              Let (tabulate(len, fn j -> let (v, x) = l@j in (v, if i = j then repl(x, r_path) else x)),
                   if i = len then repl(b, r_path) else b, a)
            | LetRec (l, b, a) ->
              let len = length l in
              LetRec  (tabulate(len, fn j -> let (v, x) = l@j in (v, if i = j then repl(x, r_path) else x)),
                       if i = len then repl(b, r_path) else b, a)
            | Lambda (l, a) ->
              Lambda (replLambdaMatch(l, i, 0, r_path), a)
            | IfThenElse(x, y, z, a) ->
              (case i of
               | 0 -> IfThenElse(repl(x, r_path), y, z, a)
               | 1 -> IfThenElse(x, repl(y, r_path), z, a)
               | 2 -> IfThenElse(x, y, repl(z, r_path), a))
            | Seq(l, a) ->
              Seq(tabulate(length l, fn j -> if i = j then repl(l@j, r_path) else l@j), a)
            | TypedTerm(x, t, a) ->
              (case i of
                 | 0 -> TypedTerm(repl(x, r_path), t, a)
                 | 1 ->
               case postCondn? t of
                 | None -> tm           % shouldn't happen
                 | Some (post_condn, _) ->
                   let new_post_condn = repl(post_condn, r_path) in
                   TypedTerm(x, replacePostCondn(t, new_post_condn), a))
            | And(l, a) ->
              And(tabulate(length l, fn j -> if i = j then repl(l@j, r_path) else l@j), a)
            | _ -> tm
        def replLambdaMatch(match: AMatch a, i, j, r_path): AMatch a =
          case match of
            | [] -> []
            | (p, c, t) :: r_match ->
              let guard_tms = getAllPatternGuards p in
              let (guard_tm_subst, j) = foldl(fn ((sbst, j), gt) ->
                                                (if j = i then [(gt, repl(gt, r_path))]
                                                   else sbst,
                                                 j + 1))
                                          ([], j) guard_tms
              in
              let new_pat =
                  case guard_tm_subst of
                    | [] -> p
                    | [(old_tm, new_tm)] ->
                      mapPattern1 (fn pi -> case pi of
                                              | RestrictedPat(p, t, a) | t = old_tm ->
                                                RestrictedPat(p, new_tm, a)
                                              | _ -> pi)
                        p
              in
              (new_pat, c, if i = j then repl(t, r_path) else t)
                :: replLambdaMatch(r_match, i, j + 1, r_path)
    in
    (repl(top_term, reverse path), path)

  op [a] postCondn?(ty: AType a): Option (ATerm a * AVars a) =
    case ty of
      | Arrow(_, rng, _) -> postCondn? rng
      | Subtype(_, Lambda([(pat, _, pred)], _), _) -> Some(pred, patVars pat)
      | _ -> None

 op [a] replacePostCondn(ty: AType a, new_post_condn: ATerm a): AType a =
    case ty of
      | Arrow(dom, rng, a) -> Arrow(dom, replacePostCondn(rng, new_post_condn), a)
      | Subtype(st, Lambda([(p, c, pred)], a1), a3) ->
        Subtype(st, Lambda([(p, c, new_post_condn)], a1), a3) 
      | _ -> ty

op [a] getSisterConjuncts(path_term: APathTerm a): List(ATerm a) =
  case path_term of
     | (Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_), 0::r_path)
       -> getSisterConjuncts(p, r_path) ++ getConjuncts q
     | (Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_), 1::r_path)
       -> getConjuncts p ++ getSisterConjuncts(q, r_path)
     | _ -> []

 op [a] changedPathTerm(tm1: ATerm a, tm2: ATerm a): APathTerm a =
    let def choose2(po1, po2, path) =
          case (po1, po2) of
            | (None, None) -> None
            | (Some _, None) -> po1
            | (None, Some _) -> po2
            | _ -> Some path
        def chooseL(pos, path) =
          case filter some? pos of
            | [] -> None
            | [poi] -> poi
            | _ -> Some path
        def compare(stm1, stm2, path) =
          %% Returns path to first difference or else None if they are equal
          % let _ = writeLine("rst: "^anyToString path^"\n"^printTerm stm1^"\n"^printTerm stm2) in
          if equalTerm?(stm1, stm2) then None
          else
          case (stm1, stm2) of
            | (Apply(x1, y1, _), Apply(x2, y2, _)) ->
              choose2(compare(x1, x2, 0 :: path), compare(y1, y2, 1 :: path), path)
            | (Record(l1, _), Record(l2, _)) | sameFieldNames?(l1, l2) ->
              chooseL(tabulate(length l1,  fn i -> compare((l1@i).2, (l2@i).2, i :: path)), path)
            | (Bind(bdr1, vs1, x1, _), Bind(bdr2, vs2, x2, _)) | bdr1 = bdr2 && equalVars?(vs1, vs2) ->
              compare(x1, x2, 0 :: path)
            | (The(v1, x1, _), The(v2, x2, _)) | equalVar?(v1, v2) ->
              compare(x1, x2, 0 :: path)
            | (Let (l1, b1, _), Let (l2, b2, _)) | length l1 = length l2 ->
              let len = length l1 in
              chooseL(compare(b1, b2, len :: path)
                        :: tabulate(len, fn i -> let ((p1, e1), (p2, e2)) = (l1@i, l2@i) in
                                           if equalPattern?(p1, p2)
                                             then compare(e1, e2, i :: path)
                                             else Some path),
                      path)
            | (LetRec (l1, b1, _), LetRec (l2, b2, _)) | length l1 = length l2 ->
              let len = length l1 in
              chooseL(compare(b1, b2, len :: path)
                        :: tabulate(len, fn i -> let ((v1, e1), (v2, e2)) = (l1@i, l2@i) in
                                           if equalVar?(v1, v2)
                                             then compare(e1, e2, i :: path)
                                             else Some path),
                      path)
            | (Lambda (l1, _), Lambda (l2, _)) | length l1 = length l2  ->
              let stm1_subterms = immediateSubTerms stm1 in
              let stm2_subterms = immediateSubTerms stm2 in
              if length stm1_subterms ~= length stm2_subterms then Some path
                else chooseL(tabulate(length stm1_subterms,
                                      fn i -> let (e1, e2) = (stm1_subterms@i, stm2_subterms@i) in
                                              compare(e1, e2, i :: path)),
                             path)
            | (IfThenElse(x1, y1, z1, _), IfThenElse(x2, y2, z2, _)) ->
              chooseL([compare(x1, x2, 0 :: path), compare(y1, y2, 1 :: path), compare(z1, z2, 2 :: path)],
                      path)
            | (Seq(l1, _), Seq(l2, _)) | length l1 = length l2 ->
              chooseL(tabulate(length l1,  fn i -> compare(l1@i, l2@i, i :: path)), path)
            | (TypedTerm(x1, t1, _), TypedTerm(x2, t2, _)) ->
              (case (postCondn? t1, postCondn? t2) of
                 | (Some (pc1, _), Some (pc2, _)) ->
                   choose2(compare(x1, x2, 0 :: path), compare(pc1, pc2, 1 :: path), path)
                 | _ ->
                   if equalType?(t1, t2) then compare(x1, x2, 0 :: path)
                     else Some path)
            | (And(l1, _), And(l2, _)) | length l1 = length l2 ->    % Not sure if this is meaningful
              chooseL (tabulate(length l1, fn i -> compare(l1@i, l2@i, i :: path)), path)
            | _ -> Some path
    in
    case compare(tm1, tm2, []) of
      | None -> (tm1, [])
      | Some path -> (tm1, path)

op dummyPathTerm: PathTerm = toPathTerm dummyMSTerm

op pathToLambdaBody(tm: MSTerm): Path =
  case tm of
    | Lambda([_], _) ->
      let imm_sub_tms = immediateSubTerms tm in
      pathToLambdaBody(last imm_sub_tms) ++ [length imm_sub_tms - 1]
    | _ -> []

op [a] parameterBindings(tm: ATerm a): AVars a =
  case tm of
    | Lambda([(pat, _, bod)], _) ->
      patVars pat ++ parameterBindings bod
    | _ -> []

%% Used in transform-shell.lisp
op typedPathTerm(tm: MSTerm, ty: MSType) : PathTerm =
  (TypedTerm(tm, ty, termAnn tm),
  [if anyTerm? tm && some?(postCondn? ty)
    then 1 else 0])

end-spec
