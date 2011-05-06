PathTerm qualifying
spec
import ../Specs/Utilities

type Path = List Nat
type APathTerm a = ATerm a * Path

 op [a] infixFn?(f: AFun a): Boolean =
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
      | SortedTerm(x, ty, _) ->
        (case postCondn? ty of
           | None -> [x]
           | Some post -> [x,post])
      | And(l, _) -> l
      | _ -> []

  op [a] ithSubTerm(term: ATerm a, i: Nat): ATerm a =
    (immediateSubTerms term) @ i

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

  op [a] typedPathTerm(term: ATerm a, ty: ASort a): APathTerm a =
    (SortedTerm(term, ty, termAnn term),
     [if anyTerm? term then 1 else 0])

  op [a] termFromTypedPathTerm(ptm: APathTerm a): ATerm a =
    case ptm.1 of
      | SortedTerm(tm, _, _) -> tm
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

  op [a] searchNextSt(path_term: APathTerm a, pred: ATerm a -> Boolean):  Option(APathTerm a) =
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

 op [a] searchPrevSt(path_term: APathTerm a, pred: ATerm a -> Boolean):  Option(APathTerm a) =
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
            | SortedTerm(x, t, a) ->
              (case i of
                 | 0 -> SortedTerm(repl(x, r_path), t, a)
                 | 1 ->
               case postCondn? t of
                 | None -> tm           % shouldn't happen
                 | Some post_condn ->
                   let new_post_condn = repl(post_condn, r_path) in
                   SortedTerm(x, replacePostCondn(t, new_post_condn), a))
            | And(l, a) ->
              And(tabulate(length l, fn j -> if i = j then repl(l@j, r_path) else l@j), a)
            | _ -> tm
    in
    (repl(top_term, reverse path), path)

  op [a] postCondn?(ty: ASort a): Option (ATerm a) =
    case ty of
      | Arrow(_, rng, _) -> postCondn? rng
      | Subsort(_, Lambda([(_, _, pred)], _), _) -> Some pred 
      | _ -> None

 op [a] replacePostCondn(ty: ASort a, new_post_condn: ATerm a): ASort a =
    case ty of
      | Arrow(dom, rng, a) -> Arrow(dom, replacePostCondn(rng, new_post_condn), a)
      | Subsort(st, Lambda([(p, c, pred)], a1), a3) ->
        Subsort(st, Lambda([(p, c, new_post_condn)], a1), a3) 
      | _ -> ty

op [a] getSisterConjuncts(path_term: APathTerm a): List(ATerm a) =
  case path_term of
     | (Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_), 0::r_path)
       -> getSisterConjuncts(p, r_path) ++ getConjuncts q
     | (Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_), 1::r_path)
       -> getConjuncts p ++ getSisterConjuncts(q, r_path)
     | _ -> []

endspec
