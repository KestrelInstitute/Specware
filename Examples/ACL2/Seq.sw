(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

type Seq a = 
  | SeqNil 
  | SeqCons a * (Seq a)

op [a] SeqAppend (x:Seq a, y:Seq a) : Seq a =
case x of
  | SeqNil -> y
  | SeqCons (hd,tl) -> SeqCons (hd, SeqAppend (tl, y)) 

theorem SeqAppend_Associative is [a]
  fa(x:Seq a,y:Seq a,z:Seq a) SeqAppend(SeqAppend(x,y),z) = SeqAppend(x,SeqAppend(y,z))

theorem SeqAppend_of_SeqNil_1 is [a]
  fa (x:Seq a) SeqAppend(SeqNil,x) = x

theorem SeqAppend_of_SeqNil_2 is [a]
  fa (x:Seq a) SeqAppend(x,SeqNil) = x

op [b] SeqRev (x:Seq b) : Seq b =
case x of
  | SeqNil -> SeqNil
  | SeqCons (hd,tl) -> SeqAppend (SeqRev tl, SeqCons (hd,SeqNil))

theorem SeqRev_of_SeqAppend is [a]
  fa (x:Seq a,y:Seq a) SeqRev (SeqAppend (x,y)) = SeqAppend (SeqRev y, SeqRev x)

theorem SeqRev_of_SeqRev is [a]
  fa (x:Seq a) (SeqRev (SeqRev x)) = x

op [a] SeqLength (x:Seq a) : Int =
  case x of
  | SeqNil -> 0
  | SeqCons (_,xs) -> 1 + SeqLength(xs)

theorem SeqLength_of_SeqAppend is [a]
  fa (x:Seq a, y:Seq a) SeqLength(SeqAppend(x,y)) = SeqLength(x) + SeqLength(y)

%op [a] SeqLength2 (x:Seq a) : Int = SeqLength x

% theorem SeqLength_of_SeqAppend is [a]
%   fa (x:Seq a,y:Seq a) SeqLength(SeqAppend(x,y)) = (SeqLength(x) + SeqLength(y))

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SeqSubBag, SeqPerm, SeqOrdered %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op [a] SeqHowMany (val:a, x:Seq a) : Nat = 
  case x of
  | SeqNil -> 0
  | SeqCons (y,ys) | val = y -> 1 + SeqHowMany (val,ys)
  | SeqCons (_,ys)         -> SeqHowMany (val,ys)

% theorem SeqHowMany_of_SeqNil is
%   fa(x:Int) SeqHowMany(x, SeqNil) = 0

% theorem SeqHowMany_of_SeqCons_diff is
%   fa(x:Int,y:Int,a:Seq a) ~(x=y) => (SeqHowMany(x,SeqCons(y,a)) = SeqHowMany(x,a))

% theorem SeqHowMany_of_SeqCons_same is
%   fa(x:Int,y:Int,a:Seq a) SeqHowMany(x,SeqCons(x,a)) = 1 + SeqHowMany(x,a)

% theorem SeqHowMany_of_SeqCons_both is
%   fa(x:Int,y:Int,a:Seq a) SeqHowMany(x,SeqCons(y,a)) = (if x = y then (1 + SeqHowMany(x,a)) else SeqHowMany(x,a))

% op SeqSubBag (a:Seq a, b:Seq a) : Bool =
%   case a of
%   | SeqNil -> true
%   | SeqCons (x,xs) -> SeqHowMany (x,a) <= SeqHowMany (x,b) && SeqSubBag (xs,b)

% theorem SeqSubBag_of_SeqCons is
%   fa(x:Int, a:Seq a, b:Seq a) SeqSubBag (a,b) => SeqSubBag (a, SeqCons(x,b))

% theorem SeqSubBag_reflexive is
%   fa (a:Seq a) SeqSubBag (a,a)

% theorem SeqSubBag_transitive is
%   fa (a:Seq a, b:Seq a, c:Seq a) SeqSubBag(a,b) && SeqSubBag(b,c) => SeqSubBag(a,c)

% %rename?
% theorem SeqSubBag_SeqHowManyLE is
%   fa (x:Int, a:Seq a, b:Seq a) SeqSubBag(a,b) => SeqHowMany(x,a) <= SeqHowMany(x,b)

% theorem SeqSubBag_of_SeqNil_1 is
%   fa (a:Seq a) SeqSubBag(SeqNil,a) = true

% theorem SeqSubBag_of_SeqNil_2 is
%   fa (a:Seq a) SeqSubBag(a,SeqNil) = (a = SeqNil)

% op SeqPerm (a:Seq a, b:Seq a) : Bool =
%   SeqSubBag (a,b) && SeqSubBag (b,a)

% op SeqOrdered (a:Seq a) : Bool =
%   case a of
%   | SeqNil -> true
%   | SeqCons (_,SeqNil) -> true
%   | SeqCons (x,rst as SeqCons (y,_)) ->
%     x <= y && SeqOrdered rst

% %% uncomment this and see the crash: SeqOrdered(SeqCons(x,SeqNil)) = true

% theorem SeqOrdered_of_SeqCons_SeqCons is
%   fa(x:Int, y:Int, z:Seq a) SeqOrdered(SeqCons(x,SeqCons(y,z))) = ((x <= y) && SeqOrdered(SeqCons(y,z)))

% %% trying SeqOrdered_of_SeqCons_SeqCons (just above) instead.
% %% %% FIXME This gives an error in ppterm:
% %% %% It's odd not to have  "car" to state this:
% %% theorem SeqOrdered_of_Icons is
% %%   fa(x:Int, a:Seq a) SeqOrdered(SeqCons(x,a)) = (if (a = SeqNil) then true else ((x < (let SeqCons(hd,tl) = a in hd)) && SeqOrdered a))

% %% proof ACL2 -verbatim
% %% (defthm IORDERED-of-ICONS
% %%   (implies (and (int-p x)
% %%                 (ilist-p a))
% %%            (equal (IORDERED (ICONS x a))
% %%                   (if (equal a (SeqNil))
% %%                       t
% %%                     (and (<= x (ICONS-ARG1 A))
% %%                          (IORDERED A)))))
% %%   :hints (("Goal" :in-theory (enable IORDERED))))
% %% end-proof

% %% %% fixme unfortunate that I need this.  could defun-typed do this?  the elim rule almost gets us what we need, but we need a rule for iordered-listp of icons
% %% proof ACL2 -verbatim
% %% (defthm IORDERED-of-ICONS-ARG2
% %%   (implies (and (IORDERED A)
% %%                 (ICONS-P A))
% %%            (IORDERED (ICONS-ARG2 A)))
% %%   :hints (("Goal" :in-theory (enable IORDERED))))
% %% end-proof

% type SeqOrderedList = Seq a | SeqOrdered

% %% fixme think about this.  can't easily state in Specware terms.
% proof ACL2 -verbatim
% (defthm IORDEREDLIST-P_of_ICONS-ARG-2
%         (implies (and (IORDEREDLIST-P A)
%                       (ICONS-P A))
%                  (IORDEREDLIST-P (ICONS-ARG-2 A)))
%                :hints (("Goal" :in-theory (enable IORDEREDLIST-P IORDERED))))
% end-proof

% %%%%%%%%%%%%%%%%%%
% % SeqInsertionSort %
% %%%%%%%%%%%%%%%%%%

% op SeqInsert (x:Int, a:SeqOrderedList) : SeqOrderedList =
%   case a of
%   | SeqNil -> SeqCons (x, SeqNil)
%   | SeqCons (y,ys) | x <= y -> SeqCons (x,a)
%   | SeqCons (y,ys)          -> SeqCons (y, SeqInsert (x,ys))

% %% FIXME: defun-typed could put things like this in automatically, whenever the return type of a function is a subtype. or put in a forward-chaining rule for the type of the function being defined.
% proof ACL2 -verbatim
% (defthm ilist-p_of_iinsert
%   (implies (and (int-p x)
%                 (SeqOrderedList-P a))
%            (ILIST-P (IINSERT X a)))
%   :hints (("Goal" :in-theory (enable iinsert))))
% end-proof

% %% FIXME, or prove that howmany is insensitive to perm and then show that insert is a perm of cons...
% theorem SeqHowMany_of_SeqInsert_diff is
%   fa(x:Int,y:Int,a:SeqOrderedList) ~(x=y) => (SeqHowMany(x,SeqInsert(y,a)) = SeqHowMany(x,a))

% theorem SeqHowMany_of_SeqInsert_same is
%   fa(x:Int,y:Int,a:SeqOrderedList) SeqHowMany(x,SeqInsert(x,a)) = 1 + SeqHowMany(x,a)

% theorem SeqHowMany_of_SeqInsert_both is
%   fa(x:Int,y:Int,a:SeqOrderedList) SeqHowMany(x,SeqInsert(y,a)) = (if x = y then (1 + SeqHowMany(x,a)) else SeqHowMany(x,a))

% %rename?
% theorem SeqHowManyLE_Insert_3 is
%   fa(x:Int,y:Int,a:SeqOrderedList) SeqHowMany(x,a) <= SeqHowMany(x,SeqInsert(y,a))

% %rename
% % strengthen to an equality?
% theorem SeqSubBag_SeqInsert_1 is
%   fa(x:Int,a:SeqOrderedList,b:Seq a) SeqSubBag(a,b) => SeqSubBag(SeqInsert(x,a), SeqCons(x,b))
  
% theorem SeqSubBag_of_SeqInsert_1 is
%   fa (a:SeqOrderedList, x:Int) SeqSubBag(a,SeqInsert(x,a)) = true

% theorem SeqSubBag_of_SeqInsert_2 is
%   fa(x:Int,a:Seq a,b:SeqOrderedList) SeqSubBag(a,b) => SeqSubBag(a,SeqInsert(x,b))

% % could put the perm claim in the type too?
% op SeqInsertionSort (a:Seq a) : SeqOrderedList =
%   case a of
%   | SeqNil -> SeqNil
%   | SeqCons (x,xs) -> SeqInsert (x,SeqInsertionSort xs)

% theorem SeqHowMany_of_SeqInsertionSort is
%   fa (a:Seq a, val:Int) SeqHowMany(val, SeqInsertionSort a) = SeqHowMany(val, a)

% %% Note that we've already proved that SeqInsertionSort returns an
% %% ordered list (it's part of the type).
% theorem Perm_of_SeqInsertionSort is
%   fa (a:Seq a) SeqPerm(a, SeqInsertionSort a)

%%%%%%%%%%%%%%%%%%%% Proofs %%%%%%%%%%%%%%%%%%%%

%% FIXME allow just ':enable (SeqAppend)' as an abbreviation for the enable hint on "Goal"?

proof ACL2 SeqAppend_associative        :hints (("Goal" :in-theory (enable SeqAppend))) end-proof
proof ACL2 SeqAppend_of_SeqNil_1-a          :hints (("Goal" :in-theory (enable SeqAppend-a))) end-proof
proof ACL2 SeqAppend_of_SeqNil_2-a          :hints (("Goal" :in-theory (enable SeqAppend-a-a))) end-proof
proof ACL2 SeqRev_of_SeqAppend-a            :hints (("Goal" :in-theory (enable SeqAppend-a SeqRev-a))) end-proof
proof ACL2 SeqRev_of_SeqRev               :hints (("Goal" :in-theory (enable SeqAppend-a SeqRev-a))) end-proof
proof ACL2 SeqLength_of_SeqAppend-a         :hints (("Goal" :in-theory (enable SeqAppend-a SeqLength-a))) end-proof
proof ACL2 SeqHowMany_of_SeqNil           :hints (("Goal" :in-theory (enable SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_of_SeqCons           :hints (("Goal" :in-theory (enable SeqSubBag-a SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_reflexive          :hints (("Goal" :in-theory (enable SeqSubBag-a))) end-proof
proof ACL2 SeqSubBag_transitive         :hints (("Goal" :in-theory (enable SeqSubBag-a SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_SeqHowManyLE         :hints (("Goal" :in-theory (enable SeqSubBag-a SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_of_SeqNil_1          :hints (("Goal" :in-theory (enable SeqSubBag-a SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_of_SeqNil_2          :hints (("Goal" :in-theory (enable SeqSubBag-a SeqHowMany-a))) end-proof
proof ACL2 SeqHowMany_of_SeqInsert_diff   :hints (("Goal" :in-theory (enable SeqHowMany-a SeqInsert))) end-proof
proof ACL2 SeqHowMany_of_SeqInsert_same   :hints (("Goal" :in-theory (enable SeqHowMany-a SeqInsert))) end-proof
proof ACL2 SeqHowMany_of_SeqInsert_both   :hints (("Goal" :in-theory (enable SeqHowMany-a SeqInsert))) end-proof
proof ACL2 SeqHowMany_of_SeqCons_same     :hints (("Goal" :in-theory (enable SeqHowMany-a))) end-proof
proof ACL2 SeqHowMany_of_SeqCons_diff     :hints (("Goal" :in-theory (enable SeqHowMany-a))) end-proof
proof ACL2 SeqHowMany_of_SeqCons_both     :hints (("Goal" :in-theory (enable SeqHowMany-a))) end-proof
proof ACL2 SeqSubBag_SeqInsert_1          :hints (("Goal" :in-theory (enable SeqInsert SeqSubBag-a IHOWMANY))) end-proof
proof ACL2 SeqSubBag_of_SeqInsert_1       :hints (("Goal" :in-theory (enable SeqSubBag-a SeqInsert SeqHowMany-a))) end-proof
proof ACL2 Perm_of_SeqInsertionSort     :hints (("Goal" :in-theory (enable SeqInsertionSort SeqPerm-a SeqSubBag-a))) end-proof
proof ACL2 SeqOrdered_of_SeqCons_SeqCons    :hints (("Goal" :in-theory (enable SeqOrdered)))end-proof
proof ACL2 SeqHowMany_of_SeqInsertionSort :hints (("Goal" :in-theory (enable SeqHowMany-a SeqInsertionSort))) end-proof

%%FIXME allow just :type-hints and :guard-hints (or even :guard-enable and :type-enable)?
proof ACL2 SeqInsert
  (declare (xargs :type-args
                  (:hints (("Goal" :in-theory 
                                   (enable SeqOrderedList-p
                                           SeqOrdered))))
                  :verify-guards-args
                  (:hints (("Goal" :in-theory
                                   (enable SeqOrderedList-p
                                           SeqOrdered))))))
end-proof

proof ACL2 SeqInsertionSort
  (declare (xargs :type-args
                  (:hints (("Goal" :in-theory 
                                   (enable SeqOrderedList-p
                                           SeqOrdered))))
                  :verify-guards-args
                  (:hints (("Goal" :in-theory
                                   (enable SeqOrderedList-p
                                           SeqOrdered))))))
end-proof

end-spec