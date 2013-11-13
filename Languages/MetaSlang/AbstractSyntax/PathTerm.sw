PathTerm qualifying
spec
import ../Specs/Utilities

type APathTerm a = ATerm a * Path

type PathTerm = APathTerm Position.Position

 op [a] topTerm(ptm: APathTerm a): ATerm a = ptm.1
 op [a] pathTermPath(ptm: APathTerm a): Path = ptm.2

 op [a] infixFn?(f: AFun a): Bool =
    case f of
      | Op(Qualified(_, s), Infix _) -> true
      | And -> true
      | Or -> true
      | Implies -> true
      | Iff -> true
      | Equals -> true
      | NotEquals -> true
      | _ -> false

  op [a] immediateSubTerms(term: ATerm a): List (ATerm a) =
    case term of
      | Apply(Fun(f, _, _), Record([("1", x), ("2", y)], _), _) | infixFn? f ->
        [x, y]
      | Apply(x, y, _) ->
        if embed? Lambda x then [y, x] else [x, y]
      | Record(l, _) -> map (fn (_, t) -> t) l
      | Bind(_, _, x, _) -> [x]
      | The(_, x, _)  -> [x]
      | Let (l, b, _) -> (map (fn (_, t) -> t) l) ++ [b]
      | LetRec (l, b, _) -> (map (fn (_, t) -> t) l) ++ [b]
      | Lambda (l, _) -> map (fn (_, _, t) -> t) l
      | IfThenElse(x, y, z, _) -> [x, y, z]
      | Seq(l, _) -> l
      | TypedTerm(x, ty, _) ->
        (case postCondn? ty of
           | None -> [x]
           | Some post -> [x,post])
      | And(l, _) -> l
      | _ -> []

  op [a] ithSubTerm(term: ATerm a, i: Nat): ATerm a =
    let tms = immediateSubTerms term in
    if i < length tms
      then tms @ i
      else fail("Can't take subterm "^show i^" of term\n"^printTerm term)

  op [a] ithSubTerm?(term: ATerm a, i: Nat): Option(ATerm a) =
    let tms = immediateSubTerms term in
    if i < length tms then Some(tms @ i) else None

  op [a] toPathTerm(term: ATerm a): APathTerm a = (term, [])
  op [a] fromPathTerm((top_term, path): APathTerm a): ATerm a =
    foldr (fn (i, tm) -> ithSubTerm(tm, i))
       top_term path

  op [a] fromPathTerm?((top_term, path): APathTerm a): Option(ATerm a) =
    foldr (fn (i, Some tm) -> ithSubTerm?(tm, i)
            | (i, None) -> None)
       (Some top_term) path

  op [a] typedPathTerm(term: ATerm a, ty: AType a): APathTerm a =
    (TypedTerm(term, ty, termAnn term),
     [if anyTerm? term && some?(postCondn? ty) then 1 else 0])

  op [a] termFromTypedPathTerm(ptm: APathTerm a): ATerm a =
    case ptm.1 of
      | TypedTerm(tm, _, _) -> tm
      | tm -> tm

  op [a] parentTerm((top_term, path): APathTerm a): Option (APathTerm a) =
    case path of
      | [] -> None
      | _::par_path -> Some (top_term, par_path)

  op [a] moveToNext((top_term, path): APathTerm a): Option (APathTerm a) =
    case path of
      | [] -> None
      | i :: r_path ->
    case fromPathTerm?(top_term, i+1 :: r_path) of
      | Some _ -> Some(top_term, i+1 :: r_path)
      | None -> moveToNext(top_term, r_path)

  op [a] moveToPrev((top_term, path): APathTerm a):  Option(APathTerm a) =
    case path of
      | [] -> None
      | i :: r_path ->
    if i > 0 then Some(top_term, i-1 :: r_path)
      else moveToPrev(top_term, r_path)

  op [a] searchNextSt(path_term: APathTerm a, pred: ATerm a -> Bool):  Option(APathTerm a) =
    let def try_next(path_term as (top_term, path)) =
          case path of
            | [] -> None
            | i :: r_path ->
          case fromPathTerm?(top_term, i+1 :: r_path) of
            | Some _ -> check_then_first(top_term, i+1 :: r_path)
            | None -> try_next(top_term, r_path)
        def check_then_first path_term =
          let term = fromPathTerm path_term in
          % let _ = writeLine("search: "^anyToString(reverse path_term.2)) in
          if pred term
            then Some path_term
          else try_first path_term
        def try_first (path_term as (top_term, path)) =
          let term = fromPathTerm path_term in
          case immediateSubTerms term of
            | [] -> try_next path_term
            | new_term :: _ -> check_then_first(top_term, 0 :: path)
   in
   try_first path_term

 op [a] searchPrevSt(path_term: APathTerm a, pred: ATerm a -> Bool):  Option(APathTerm a) =
   let def try_prev (top_term, path) =
         case path of
           | [] -> None
           | i :: r_path ->
             if i > 0 then
               let new_path_term = (top_term, i-1 :: r_path) in
               try_last new_path_term
             else check_then_prev(top_term, r_path)
       def check_then_prev path_term =
         let term = fromPathTerm path_term in
         % let _ = writeLine("rsearch: "^anyToString(reverse path_term.2)) in
         if pred term
           then Some path_term
         else try_prev path_term
       def try_last (path_term as (top_term, path)) =
         let term = fromPathTerm path_term in
         case immediateSubTerms term of
           | [] -> check_then_prev path_term
           | terms ->
             try_last(top_term,  (length terms - 1) :: path)
   in
   try_prev path_term

  op [a] replaceSubTerm(new_tm: ATerm a, (top_term, path): APathTerm a): APathTerm a =
    let def repl(tm, path) =
          % let _ = writeLine("rst: "^anyToString path^"\n"^printTerm tm) in
          case path of
            | [] -> new_tm
            | i :: r_path ->
          case tm of
            | Apply(infix_fn as Fun(f, _, _), Record([("1", x), ("2", y)], a1), a2) | infixFn? f ->
              (case i of
               | 0 -> Apply(infix_fn, Record([("1", repl(x, r_path)), ("2", y)], a1), a2)
               | 1 -> Apply(infix_fn, Record([("1", x), ("2", repl(y, r_path))], a1), a2))
            | Apply(x, y, a) ->
              (let case? = embed? Lambda x in
               if (case i of
                     | 0 -> ~case?
                     | 1 -> case?)
                 then Apply(repl(x, r_path), y, a)
                 else Apply(x, repl(y, r_path), a))
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
              Lambda (tabulate(length l, fn j -> let (v, c, x) = l@j in (v, c, if i = j then repl(x, r_path) else x)), a)
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
                 | Some post_condn ->
                   let new_post_condn = repl(post_condn, r_path) in
                   TypedTerm(x, replacePostCondn(t, new_post_condn), a))
            | And(l, a) ->
              And(tabulate(length l, fn j -> if i = j then repl(l@j, r_path) else l@j), a)
            | _ -> tm
    in
    (repl(top_term, reverse path), path)

  op [a] postCondn?(ty: AType a): Option (ATerm a) =
    case ty of
      | Arrow(_, rng, _) -> postCondn? rng
      | Subtype(_, Lambda([(_, _, pred)], _), _) -> Some pred 
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
            | (Apply(infix_fn1 as Fun(f, _, _), Record([("1", x1), ("2", y1)], _), _),
               Apply(infix_fn2, Record([("1", x2), ("2", y2)], _), _))
                | infixFn? f && equalTerm?(infix_fn1, infix_fn2) ->
              choose2(compare(x1, x2, 0 :: path), compare(y1, y2, 1 :: path), path)
            | (Apply(x1, y1, _), Apply(x2, y2, _)) | embed? Lambda x1 ->   % case expression
              choose2(compare(x1, x2, 1 :: path), compare(y1, y2, 0 :: path), path)
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
              chooseL (tabulate(length l1, fn i -> let ((p1, c1, e1), (p2, c2, e2)) = (l1@i, l2@i) in
                                                   if equalPattern?(p1, p2) && equalTerm?(c1, c2)
                                                     then compare(e1, e2, i :: path)
                                                     else Some path),
                       path)
            | (IfThenElse(x1, y1, z1, _), IfThenElse(x2, y2, z2, _)) ->
              chooseL([compare(x1, x2, 0 :: path), compare(y1, y2, 1 :: path), compare(z1, z2, 2 :: path)],
                      path)
            | (Seq(l1, _), Seq(l2, _)) | length l1 = length l2 ->
              chooseL(tabulate(length l1,  fn i -> compare(l1@i, l2@i, i :: path)), path)
            | (TypedTerm(x1, t1, _), TypedTerm(x2, t2, _)) ->
              (case (postCondn? t1, postCondn? t2) of
                 | (Some pc1, Some pc2) ->
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

end-spec
