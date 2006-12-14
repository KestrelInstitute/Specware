\section{Simple refinements of substutions as \Sort{OpInfo}}

The idea here is that we can apply a substitution to a spec by simply
adding the \Sort{OpInfo}s associated with the name to the spec. The
step of acually performing the reductions is done elsewhere.

So we can substitute only for ops and not variables using this scheme.
But the distinction between ops and variables is wrong in the first place.

\begin{spec}
Subst qualifying spec 
  import ../Subst
  import ../Op/Legacy
  import ../Spec/Legacy

  sort Subst.Binding = Op.OpInfo
  sort Subst.Subst = List Subst.Binding

  def Subst.filter = List.filter

  def Subst.pp subst =
    ppConcat [
        String.pp "[",
        ppSep (String.pp ",") (map ppShort subst),
        String.pp "]"
      ]
  def Subst.show subst = ppFormat (pp subst)

%%   op partition : Binding -> Subst -> Subst
%%   def partition a l =
%%     case l of
%%       | [] -> ([],[])
%%       | (x::l) = 
%%           let (l1,l2) = partition a l in
%%             if nameLT x a then
%%               (Cons (x,l1),l2)
%%             else
%%               (l1,Cons (x,l2))
%% 
%%   def Subst.order l of
%%     case l of
%%       | [] -> []
%%       | (x::l) ->
%%           let (l1,l2) = partition x l in
%%           let (s1,s2) = (order l1,order l2) in 
%%           s1 ++ (Cons (x,s2))

  op nameLT : Binding -> Binding -> Boolean
  def nameLT op1 op2 =
    case (Op.idOf op1, Op.idOf op2) of
      | (Qualified (q1,n1), Qualified (q2,n2)) -> String.lt (n1,n2)

  def Subst.order l =
    let
      def insert x l =
        case l of
          | [] -> [x]
          | (y::rest) ->
               if nameLT x y then
                 Cons (x,l)
               else
                 Cons (y, insert x rest)
    in
     case l of
       | [] -> []
       | (x::rest) -> insert x (Subst.order rest)

  def Subst.equalSubst? (s1,s2) = equalList? (s1,s2,equalStuff?)
  def Subst.eq? (s1,s2) = equalSubst? (s1,s2)

  op equalStuff? : Op.OpInfo * Op.OpInfo -> Boolean
  def equalStuff? (op1,op2) =
      ((idOf op1) = (idOf op2))
    & (case (term op1, term op2) of
        | (None,None) -> true
        | (Some trm1, Some trm2) -> myEqualTerm? (trm1,trm2)
        | _ -> false)

 (* Same as equalTerm? but ignores the sort information. The problem is that the
 two terms may have sorts that are the same in the context of a spec, but
 the spec is unavailable to us here to dereference against *)
 op myEqualTerm? : ATerm Position * ATerm Position   -> Boolean
 def myEqualTerm? (t1, t2) =
  case (t1, t2) of

     | (Apply      (x1, y1,      _), 
        Apply      (x2, y2,      _)) -> myEqualTerm? (x1, x2) & myEqualTerm? (y1, y2)

     | (ApplyN     (xs1,         _),   
        ApplyN     (xs2,         _)) -> equalList? (xs1, xs2, myEqualTerm?)

     | (Record     (xs1,         _), 
        Record     (xs2,         _)) -> equalList? (xs1, xs2, 
                                                    fn ((label1,x1),(label2,x2)) -> 
                                                       label1 = label2 & 
                                                       myEqualTerm? (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 & 
                                        %% Could check modulo alpha conversion...
                                        equalList? (vs1, vs2, equalVar?) &
                                        myEqualTerm? (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> myEqualTerm? (b1, b2) &
                                        equalList? (pts1, pts2,
                                                    fn ((p1,t1),(p2,t2)) -> 
                                                      equalPattern? (p1, p2) & 
                                                      myEqualTerm?    (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> myEqualTerm? (b1, b2) &
                                        equalList? (vts1, vts2,
                                                    fn ((v1,t1),(v2,t2)) -> 
                                                     equalVar?  (v1, v2) & 
                                                     myEqualTerm? (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equalVar?(v1,v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equalFun?(f1,f2) % & deprecated_equivType? spc (s1,s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((p1,c1,b1),(p2,c2,b2)) ->
                                                      equalPattern?  (p1, p2) & 
                                                      myEqualTerm?     (c1, c2) & 
                                                      myEqualTerm?     (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> myEqualTerm? (c1, c2) & 
                                        myEqualTerm? (x1, x2) & 
                                        myEqualTerm? (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equalList? (xs1, xs2, myEqualTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> myEqualTerm? (x1, x2) % & deprecated_equivType? spc (s1, s2)
     | _ -> false
endspec
\end{spec}
