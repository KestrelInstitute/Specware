
BankAccount = spec

  type Transaction = { time : Nat, amount : Int }

  type Account
  op transactions : Account -> List Transaction
  op last_transaction (a : Account) : Transaction = last (transactions a)
  op balance (a : Account) : Int =
    foldr (fn (x, y) -> x+y) 0 (map (fn t -> t.amount) (transactions a))

  op deposit (now : Nat) (amt : Nat) (a : Account)
  : {a' : Account | transactions a' = transactions a ++ [{time=now, amount = amt}] }

  op withdraw (now : Nat) (amt : Nat) (a : Account)
  : {a' : Account | if balance a >= amt then
       transactions a' = transactions a ++ [{time=now, amount = -amt}]
     else transactions a' = transactions a}

end-spec
