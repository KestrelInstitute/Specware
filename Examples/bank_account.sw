
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
