(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* We refine the ops in spec ListExt to be executable. *)

spec

  import ListExt

  refine def [a] sorted? (ord: EndoRelation a) (l: List a) : Bool =
    let def loop (previous:a, l: List a) : Bool =
        case l of
        | []     -> true
        | hd::tl -> ord (previous,hd) && loop (hd, tl)
    in
    case l of
      | []     -> true
      | hd::tl -> loop (hd, tl)

  refine def [a] sortt (ord: LinearOrder a) : List a -> List a = fn
    % quick sort:
    | []     -> Nil
    | hd::tl -> let smaller    = filter (fn x -> ord(x,hd) && x ~= hd) tl in
                let largerOrEq = filter (fn x -> ord(hd,x))            tl in
                (sortt ord smaller) ++ [hd] ++ (sortt ord largerOrEq)


% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------


proof Isa sorted_p__1__obligation_refine_def
  sorry   
end-proof

proof Isa sortt__1__obligation_refine_def
  sorry   
end-proof

endspec
