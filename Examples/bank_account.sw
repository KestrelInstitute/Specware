
BankAccount = spec
  import /Library/DataStructures/Bags

  type Transaction = { time : Nat, amount : Int }

  type Account
  op transactions : Account -> Bag Transaction
  %op last_transaction (a : Account) : Transaction = last (transactions a)
  op balance (a : Account) : Int =
    bag_fold (0:Int) (fn (x, xact : Transaction) -> x + xact.amount) (transactions a)

  op deposit (now : Nat) (amt : Nat) (a : Account)
  : {a' : Account | transactions a' = bag_insert ({time=now, amount = amt}, (transactions a)) }

  op withdraw (now : Nat) (amt : Nat) (a : Account | balance a >= amt)
  : {a' : Account | transactions a' = bag_insert ({time=now, amount = -amt}, (transactions a)) }

end-spec


BA1 = transform BankAccount by {
                                maintain (balance) [lr Bag.bag_fold2]
                                }

BA2 = spec
  import BA1
  import /Library/DataStructures/StructuredTypes

  op transations_list : Account -> List Transaction

  axiom transactions_def is
    fa (a : Account) transactions a = L2B (transations_list a)
end-spec

BA3 = transform BA2 by {
                        implement (transactions, transactions_def) [ rl L2B_Cons ]
                        }
