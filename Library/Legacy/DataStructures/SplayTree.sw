\section{Splay Tree}
Adapted from the SML/NJ distribution 

\begin{spec}
SplayTree qualifying spec {
  import /Library/Base

  sort Splay a = | SplayNil
                 | SplayObj {
                              value : a,
                              right : Splay a,
                              left  : Splay a
                            }

  sort ans_t(a) = | No | Eq a | Lt a | Gt a

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
      | SplayNil -> (No,SplayNil,SplayNil)
      | SplayObj {value,left,right} ->
        (case compf value of
          | Equal -> (Eq value, left, right)
          | Greater ->
             (case left of
               | SplayNil -> (Gt value,SplayNil,right)
               | SplayObj {value = value_,left = left_,right = right_} ->
                (case compf value_ of
                   | Equal -> (Eq value_,left_,SplayObj{value = value,left = right_,right = right})
                   | Greater ->
                      (case left_ 
                         of SplayNil -> (Gt value_,left_,SplayObj{value = value,left = right_,right = right})
                          | _ -> 
                            let (V,L,R) = adj compf left_ in
                            let rchild = mkSplayObj{value = value,left = right_,right = right} in
                              (V,L,SplayObj{value = value_,left = R,right = rchild}))
                   | _ ->
                      (case right_ of
                         | SplayNil -> (Lt value_,left_,SplayObj{value = value,left = right_,right = right})
                         | _ ->
                           let (V,L,R) = adj compf right_ in
                           let rchild = mkSplayObj{value = value,left = R,right = right} in
                           let lchild = mkSplayObj{value = value_,left = left_,right = L} in
                           (V,lchild,rchild))))
          | _ (* Less *) -> 
            (case right of
              | SplayNil -> (Lt value,left,SplayNil)
              | SplayObj {value = value_,left = left_,right = right_} ->
                (case compf value_ of
                  | Equal -> (Eq value_,SplayObj{value = value,left = left,right = left_},right_)
                  | Less ->
                   (case right_ of
                      | SplayNil -> (Lt value_,SplayObj{value = value,left = left,right = left_},right_)
                      | _ ->
                         let (V,L,R) = adj compf right_ in
                         let lchild = mkSplayObj{value = value,left = left,right = left_} in
                         (V,SplayObj{value = value_,left = lchild,right = L},R))
                  | _ ->
                   (case left_ of
                      | SplayNil -> (Gt value_,SplayObj{value = value,left = left,right = left_},right_)
                      | _ ->
                        let (V,L,R) = adj compf left_ in
                        let rchild = mkSplayObj{value = value_,left = R,right = right_} in
                        let lchild = mkSplayObj{value = value,left = left,right = L} in
                        (V,lchild,rchild)))))

  def splay (compf, root) = 
    case adj compf root of
      | (No,_,_) -> (Greater,SplayNil)
      | (Eq v,l,r) -> (Equal,SplayObj{value = v,left = l,right = r})
      | (Lt v,l,r) -> (Less,SplayObj{value = v,left = l,right = r})
      | (Gt v,l,r) -> (Greater,SplayObj{value = v,left = l,right = r})
      
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
