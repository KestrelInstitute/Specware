(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


BankAccount = spec
  import /Library/DataStructures/Sets
  import /Library/DataStructures/StructuredTypes

  type Transaction = { Id : Nat, amount : Int }
  % op mk_trans (i:Nat) (amt:Int) : Transaction = { Id=i, amount=amt }
  op trans_max_id (ts : Set Transaction) : Nat =
    set_fold 0 (fn (x:Nat, xact) -> max (x, xact.Id)) ts
  proof Isa trans_max_id_Obligation_subtype
    apply (auto simp add: Set__foldable_p_def)
  end-proof

  op mk_new_trans (ts : Set Transaction) (amt : Int) : Transaction =
    { Id=trans_max_id ts + 1, amount=amt }
  proof Isa mk_new_trans_Obligation_subtype
    apply (auto simp add: trans_max_id_def)
    sorry
  end-proof

  op insert_new_trans (ts : Set Transaction) (amt : Int) : Set Transaction =
    set_insert (mk_new_trans ts amt, ts)

  theorem mk_new_trans_not_in is
    fa (ts, amt) ~((mk_new_trans ts amt) in? ts)
  proof Isa mk_new_trans_not_in
    sorry
  end-proof

  theorem insert_new_trans_max is
    fa (ts, amt) trans_max_id (insert_new_trans ts amt) = (trans_max_id ts) + 1
  proof Isa insert_new_trans_max
    sorry
  end-proof

  type Account

  op transactions : Account -> Set Transaction
  op max_id (a : Account) : Nat = trans_max_id (transactions a)

  op balance (a : Account) : Int =
    set_fold (0:Int) (fn (x:Int, xact : Transaction) -> x + xact.amount) (transactions a)
    % bag_sum (bag_map (fn t -> t.amount) (transactions a))
  proof Isa balance_Obligation_subtype
    by (auto simp add: Set__foldable_p_def)
  end-proof

  op deposit (amt : Nat) (a : Account)
  : {a' : Account | transactions a' = insert_new_trans (transactions a) amt }

  op withdraw (amt : Nat) (a : Account | balance a >= amt)
  : {a' : Account | transactions a' = insert_new_trans (transactions a) (-amt) }

  op try_withdraw (amt : Nat) (a : Account) : Account =
    if balance a >= amt then withdraw amt a else a

end-spec


BA1 = transform BankAccount by
{
  maintain (balance) [lr Bag.bag_fold2]
  % maintain (balance) [lr Bag.bag_sum_insert,
   %                    lr Bag.bag_map_insert]
}

BA2 = spec
  import BA1

  op transactions_list : Account -> List Transaction

  axiom transactions_def is
    fa (a : Account) transactions a = L2S (transactions_list a)

end-spec

BA3 = transform BA2 by {
                        implement (transactions, transactions_def) [ rl L2B_Cons ]
                        }

BA4 = transform BA3 by {
                        finalizeCoType(Account)
                        }
