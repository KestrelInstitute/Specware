(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Splay Tree}
Adapted from the SML/NJ distribution 

\begin{spec}
SplayTree qualifying spec {
  import /Library/Base

  type Splay a = | SplayNil
                 | SplayObj {
                              value : a,
                              right : Splay a,
                              left  : Splay a
                            }

  type ans_t(a) = | No | Eq a | Lt a | Gt a

  %% Exported:

  op splayEmpty     : fa(a) Splay(a)
  op splayNode      : fa(a) a * Splay(a) * Splay(a) -> Splay(a)
  op splaySingleton : fa(a) a -> Splay(a)
  op splayJoin      : fa(a) Splay(a) * Splay(a) -> Splay(a)

  %% Internal:

  op mkSplayNil : fa(a) Splay(a)
  op mkSplayObj : fa(a) {value : a, right : Splay(a), left : Splay(a)} -> Splay(a)

  op splay      : fa(a) (a -> Comparison) * Splay(a) -> Comparison * Splay(a)
  op lrotate    : fa(a) Splay(a) -> Splay(a)
  op join       : fa(a) Splay(a) * Splay(a) -> Splay(a)

  %% ========================================================================

  def mkSplayNil = SplayNil
  def mkSplayObj = SplayObj

  def splayEmpty = SplayNil

  def splayNode (a, l, r) =  SplayObj { value = a, left = l, right = r }

  def splayJoin = join

  def splaySingleton a = splayNode (a, splayEmpty, splayEmpty)

  op adj : fa(a) (a -> Comparison) -> Splay(a) -> ans_t(a) * Splay(a) * Splay(a)

  def adj compf sp = 
    case sp of
      | SplayNil -> (No, SplayNil, SplayNil)
      | SplayObj {value, left, right} ->
        (case compf value of
          | Equal -> (Eq value, left, right)
          | Greater ->
	    (case left of
               | SplayNil -> (Gt value, SplayNil, right)
               | SplayObj {value = left_V, left = left_L, right = left_R} ->
                 (case compf left_V of
		    | Equal -> (Eq left_V, left_L, SplayObj {value = value, left = left_R, right = right})
		    | Greater ->
		      (case left_L of
                         | SplayNil -> (Gt left_V, left_L, SplayObj {value = value, left = left_R, right = right})
			 | _ -> 
			   let (V, L, R) = adj compf left_L in
			   let rchild = mkSplayObj {value = value, left = left_R, right = right} in
			   (V, L, SplayObj {value = left_V, left = R, right = rchild}))
		    | _ ->
                      (case left_R of
                         | SplayNil -> (Lt left_V, left_L, SplayObj {value = value, left = left_R, right = right})
                         | _ ->
                           let (V, L, R) = adj compf left_R in
                           let rchild = mkSplayObj {value = value,  left = R,      right = right} in
                           let lchild = mkSplayObj {value = left_V, left = left_L, right = L} in
                           (V, lchild, rchild))))
          | _ (* Less *) -> 
            (case right of
              | SplayNil -> (Lt value, left, SplayNil)
              | SplayObj {value = right_V, left = right_L, right = right_R} ->
                (case compf right_V of
                  | Equal -> (Eq right_V, SplayObj {value = value, left = left, right = right_L}, right_R)
                  | Less ->
                   (case right_R of
                      | SplayNil -> (Lt right_V, SplayObj {value = value, left = left, right = right_L}, right_R)
                      | _ ->
                         let (V, L, R) = adj compf right_R in
                         let lchild = mkSplayObj {value = value, left = left, right = right_L} in
                         (V, SplayObj {value = right_V, left = lchild, right = L}, R))
                  | _ ->
                   (case right_L of
                      | SplayNil -> (Gt right_V, SplayObj {value = value, left = left, right = right_L}, right_R)
                      | _ ->
                        let (V, L, R) = adj compf right_L in
                        let rchild = mkSplayObj {value = right_V, left = R,    right = right_R} in
                        let lchild = mkSplayObj {value = value,   left = left, right = L} in
                        (V, lchild, rchild)))))

  def splay (compf, root) = 
    case adj compf root of
      | (No,_,_)   -> (Greater, SplayNil)
      | (Eq v,l,r) -> (Equal,   SplayObj{value = v,left = l,right = r})
      | (Lt v,l,r) -> (Less,    SplayObj{value = v,left = l,right = r})
      | (Gt v,l,r) -> (Greater, SplayObj{value = v,left = l,right = r})
      
  def lrotate sp = 
    case sp of
      | SplayNil -> SplayNil
      | SplayObj {value,left,right = SplayNil} -> sp
      | SplayObj {value,left,right = SplayObj {value = v,left = l,right = r}} ->
          lrotate (SplayObj {
                       value = v,
                       left = SplayObj {value = value,left = left,right = l},
                       right = r
                     })

  def join (sp1,sp2) = 
    case (sp1,sp2) of
      | (SplayNil,SplayNil) -> SplayNil
      | (SplayNil,t) -> t
      | (t,SplayNil) -> t
      | (l,r) ->
          (case lrotate l of
            | SplayNil -> r      (* impossible as l is not SplayNil *)
            | SplayObj {value,left,right} ->
                SplayObj {
                    value = value,
                    left = left,
                    right = r
                  })
}
\end{spec}
