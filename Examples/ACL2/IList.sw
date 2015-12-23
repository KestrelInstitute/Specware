(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

%% A spec for lists of integers.

%%%%%%%%%
% IList %
%%%%%%%%%

type IList =
  | INil
  | ICons Int * IList

%%%%%%%%%%%%%%%%%%%%%%%%%%
% IAppend, IRev, ILength %
%%%%%%%%%%%%%%%%%%%%%%%%%%

op IAppend (x:IList, y:IList) : IList = 
case x of
  | INil -> y
  | ICons (hd,tl) -> ICons (hd, (IAppend (tl,y)))

theorem IAppend_associative is
  fa (x:IList, y:IList, z:IList) (IAppend (IAppend (x,y), z) = IAppend (x, IAppend (y,z)))

theorem IAppend_of_INil_1 is
  fa (a:IList) IAppend(INil,a) = a

theorem IAppend_of_INil_2 is
  fa (a:IList) IAppend(a,INil) = a

op IRev (a:IList) : IList =
  case a of
  | INil -> a
  | ICons (x,xs) -> IAppend (IRev xs, ICons (x,INil))

theorem IRev_of_IAppend is
  fa (a:IList,b:IList) IRev (IAppend (a,b)) = IAppend (IRev b, IRev a)

theorem IRev_of_IRev is
  fa (a:IList) (IRev (IRev a)) = a

op ILength (a:IList) : Int =
  case a of
  | INil -> 0
  | ICons (_,xs) -> 1 + ILength(xs)

theorem ILength_of_IAppend is
  fa (a:IList,b:IList) ILength(IAppend(a,b)) = (ILength(a) + ILength(b))

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ISubBag, IPerm, IOrdered %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op IHowMany (x:Int, a:IList) : Nat = 
  case a of
  | INil -> 0
  | ICons (y,ys) | x = y -> 1 + IHowMany (x,ys)
  | ICons (_,ys)         -> IHowMany (x,ys)

theorem IHowMany_of_INil is
  fa(x:Int) IHowMany(x, INil) = 0

theorem IHowMany_of_ICons_diff is
  fa(x:Int,y:Int,a:IList) ~(x=y) => (IHowMany(x,ICons(y,a)) = IHowMany(x,a))

theorem IHowMany_of_ICons_same is
  fa(x:Int,y:Int,a:IList) IHowMany(x,ICons(x,a)) = 1 + IHowMany(x,a)

theorem IHowMany_of_ICons_both is
  fa(x:Int,y:Int,a:IList) IHowMany(x,ICons(y,a)) = (if x = y then (1 + IHowMany(x,a)) else IHowMany(x,a))

op ISubBag (a:IList, b:IList) : Bool =
  case a of
  | INil -> true
  | ICons (x,xs) -> IHowMany (x,a) <= IHowMany (x,b) && ISubBag (xs,b)

theorem ISubBag_of_ICons is
  fa(x:Int, a:IList, b:IList) ISubBag (a,b) => ISubBag (a, ICons(x,b))

theorem ISubBag_reflexive is
  fa (a:IList) ISubBag (a,a)

theorem ISubBag_transitive is
  fa (a:IList, b:IList, c:IList) ISubBag(a,b) && ISubBag(b,c) => ISubBag(a,c)

%rename?
theorem ISubBag_IHowManyLE is
  fa (x:Int, a:IList, b:IList) ISubBag(a,b) => IHowMany(x,a) <= IHowMany(x,b)

theorem ISubBag_of_INil_1 is
  fa (a:IList) ISubBag(INil,a) = true

theorem ISubBag_of_INil_2 is
  fa (a:IList) ISubBag(a,INil) = (a = INil)

op IPerm (a:IList, b:IList) : Bool =
  ISubBag (a,b) && ISubBag (b,a)

op IOrdered (a:IList) : Bool =
  case a of
  | INil -> true
  | ICons (_,INil) -> true
  | ICons (x,rst as ICons (y,_)) ->
    x <= y && IOrdered rst

%% uncomment this and see the crash: IOrdered(ICons(x,INil)) = true

theorem IOrdered_of_ICons_ICons is
  fa(x:Int, y:Int, z:IList) IOrdered(ICons(x,ICons(y,z))) = ((x <= y) && IOrdered(ICons(y,z)))

%% trying IOrdered_of_ICons_ICons (just above) instead.
%% %% FIXME This gives an error in ppterm:
%% %% It's odd not to have  "car" to state this:
%% theorem IOrdered_of_Icons is
%%   fa(x:Int, a:IList) IOrdered(ICons(x,a)) = (if (a = INil) then true else ((x < (let ICons(hd,tl) = a in hd)) && IOrdered a))

%% proof ACL2 -verbatim
%% (defthm IORDERED-of-ICONS
%%   (implies (and (int-p x)
%%                 (ilist-p a))
%%            (equal (IORDERED (ICONS x a))
%%                   (if (equal a (INil))
%%                       t
%%                     (and (<= x (ICONS-ARG1 A))
%%                          (IORDERED A)))))
%%   :hints (("Goal" :in-theory (enable IORDERED))))
%% end-proof

%% %% fixme unfortunate that I need this.  could defun-typed do this?  the elim rule almost gets us what we need, but we need a rule for iordered-listp of icons
%% proof ACL2 -verbatim
%% (defthm IORDERED-of-ICONS-ARG2
%%   (implies (and (IORDERED A)
%%                 (ICONS-P A))
%%            (IORDERED (ICONS-ARG2 A)))
%%   :hints (("Goal" :in-theory (enable IORDERED))))
%% end-proof

type IOrderedList = IList | IOrdered

%% fixme think about this.  can't easily state in Specware terms.
proof ACL2 -verbatim
(defthm IORDEREDLIST-P_of_ICONS-ARG-2
        (implies (and (IORDEREDLIST-P A)
                      (ICONS-P A))
                 (IORDEREDLIST-P (ICONS-ARG-2 A)))
         :hints (("Goal" :in-theory (enable IORDEREDLIST-P IORDERED))))
end-proof

%%%%%%%%%%%%%%%%%%
% IInsertionSort %
%%%%%%%%%%%%%%%%%%

op IInsert (x:Int, a:IOrderedList) : IOrderedList =
  case a of
  | INil -> ICons (x, INil)
  | ICons (y,ys) | x <= y -> ICons (x,a)
  | ICons (y,ys)          -> ICons (y, IInsert (x,ys))

%% FIXME: defun-typed could put things like this in automatically, whenever the return type of a function is a subtype. or put in a forward-chaining rule for the type of the function being defined.
proof ACL2 -verbatim
(defthm ilist-p_of_iinsert
  (implies (and (int-p x)
                (IOrderedList-P a))
           (ILIST-P (IINSERT X a)))
   :hints (("Goal" :in-theory (enable iinsert))))
end-proof

%% FIXME, or prove that howmany is insensitive to perm and then show that insert is a perm of cons...
theorem IHowMany_of_IInsert_diff is
  fa(x:Int,y:Int,a:IOrderedList) ~(x=y) => (IHowMany(x,IInsert(y,a)) = IHowMany(x,a))

theorem IHowMany_of_IInsert_same is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,IInsert(x,a)) = 1 + IHowMany(x,a)

theorem IHowMany_of_IInsert_both is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,IInsert(y,a)) = (if x = y then (1 + IHowMany(x,a)) else IHowMany(x,a))

%rename?
theorem IHowManyLE_Insert_3 is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,a) <= IHowMany(x,IInsert(y,a))

%rename
% strengthen to an equality?
theorem ISubBag_IInsert_1 is
  fa(x:Int,a:IOrderedList,b:IList) ISubBag(a,b) => ISubBag(IInsert(x,a), ICons(x,b))
  
theorem ISubBag_of_IInsert_1 is
  fa (a:IOrderedList, x:Int) ISubBag(a,IInsert(x,a)) = true

theorem ISubBag_of_IInsert_2 is
  fa(x:Int,a:IList,b:IOrderedList) ISubBag(a,b) => ISubBag(a,IInsert(x,b))

% could put the perm claim in the type too?
op IInsertionSort (a:IList) : IOrderedList =
  case a of
  | INil -> INil
  | ICons (x,xs) -> IInsert (x,IInsertionSort xs)

theorem IHowMany_of_IInsertionSort is
  fa (a:IList, val:Int) IHowMany(val, IInsertionSort a) = IHowMany(val, a)

%% Note that we've already proved that IInsertionSort returns an
%% ordered list (it's part of the type).
theorem Perm_of_IInsertionSort is
  fa (a:IList) IPerm(a, IInsertionSort a)

%%%%%%%%%%%%%%%%%%%% Proofs %%%%%%%%%%%%%%%%%%%%

%% FIXME allow just ':enable (IAppend)' as an abbreviation for the enable hint on "Goal"?

proof ACL2 IAppend_associative        :enable (IAppend) end-proof
proof ACL2 IAppend_of_INil_1          :enable (IAppend) end-proof
proof ACL2 IAppend_of_INil_2          :enable (IAppend) end-proof
proof ACL2 IRev_of_IAppend            :enable (IAppend IRev) end-proof
proof ACL2 IRev_of_IRev               :enable (IAppend IRev) end-proof
proof ACL2 ILength_of_IAppend         :enable (IAppend ILength) end-proof
proof ACL2 IHowMany_of_INil           :enable (IHowMany) end-proof
proof ACL2 ISubBag_of_ICons           :enable (ISubBag IHowMany) end-proof
proof ACL2 ISubBag_reflexive          :enable (ISubBag) end-proof
proof ACL2 ISubBag_transitive         :enable (ISubBag IHowMany) end-proof
proof ACL2 ISubBag_IHowManyLE         :enable (ISubBag IHowMany) end-proof
proof ACL2 ISubBag_of_INil_1          :enable (ISubBag ihowmany) end-proof
proof ACL2 ISubBag_of_INil_2          :enable (ISubBag ihowmany) end-proof
proof ACL2 IHowMany_of_IInsert_diff   :enable (IHowMany IInsert) end-proof
proof ACL2 IHowMany_of_IInsert_same   :enable (IHowMany IInsert) end-proof
proof ACL2 IHowMany_of_IInsert_both   :enable (IHowMany IInsert) end-proof
proof ACL2 IHowMany_of_ICons_same     :enable (IHowMany) end-proof
proof ACL2 IHowMany_of_ICons_diff     :enable (IHowMany) end-proof
proof ACL2 IHowMany_of_ICons_both     :enable (IHowMany) end-proof
proof ACL2 ISubBag_IInsert_1          :enable (IInsert ISubBag IHOWMANY) end-proof
proof ACL2 ISubBag_of_IInsert_1       :enable (ISubBag IInsert IHowMany) end-proof
proof ACL2 Perm_of_IInsertionSort     :enable (IInsertionSort IPerm ISubBag) end-proof
proof ACL2 IOrdered_of_ICons_ICons    :enable (IOrdered) end-proof
proof ACL2 IHowMany_of_IInsertionSort :enable (IHowMany IInsertionSort) end-proof

%%FIXME allow just :type-hints and :guard-hints (or even :guard-enable and :type-enable)?
proof ACL2 IInsert
  (declare (xargs :type-args
                  (:hints (("Goal" :in-theory 
                                   (enable IOrderedList-p
                                           IOrdered))))
                  :verify-guards-args
                  (:hints (("Goal" :in-theory
                                   (enable IOrderedList-p
                                           IOrdered))))))
end-proof

proof ACL2 IInsertionSort
  (declare (xargs :type-args
                  (:hints (("Goal" :in-theory 
                                   (enable IOrderedList-p
                                           IOrdered))))
                  :verify-guards-args
                  (:hints (("Goal" :in-theory
                                   (enable IOrderedList-p
                                           IOrdered))))))
end-proof

end-spec
