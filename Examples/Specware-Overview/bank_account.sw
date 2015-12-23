(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


BankAccount = spec
  import /Library/DataStructures/Bags

  type Transaction = { time : Nat, amount : Int }
  type Account

  op transactions : Account -> Bag Transaction
  op balance (a : Account) : Int =
    % bag_fold (0:Int) (fn (x, xact : Transaction) -> x + xact.amount) (transactions a)
    bag_sum (bag_map (fn t -> t.amount) (transactions a))

  op deposit (now : Nat) (amt : Nat) (a : Account)
  : {a' : Account | transactions a' = bag_insert ({time=now, amount = (amt:Int)}, (transactions a)) }

  op withdraw (now : Nat) (amt : Nat) (a : Account | balance a >= amt)
  : {a' : Account | transactions a' = bag_insert ({time=now, amount = -amt}, (transactions a)) }

  op try_withdraw (now : Nat) (amt : Nat) (a : Account) : Account =
    if balance a >= amt then withdraw now amt a else a
end-spec


BA1 = transform BankAccount by
{
  % maintain (balance) [lr Bag.bag_fold2]
  maintain (balance) [lr Bag.bag_sum_insert,
                      lr Bag.bag_map_insert]
}

BA2 = spec
  import BA1
  import /Library/DataStructures/StructuredTypes

  op transactions_list : Account -> List Transaction

  axiom transactions_def is
    fa (a : Account) transactions a = L2B (transactions_list a)
end-spec

BA3 = transform BA2 by {
                        implement (transactions, transactions_def) [ rl L2B_Cons ]
                        }

BA4 = transform BA3 by {
                        finalizeCoType(Account)
                        }
