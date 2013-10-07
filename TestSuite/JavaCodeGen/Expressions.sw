spec

  type Expr = | constant Int
              | plus  Expr * Expr
              | times Expr * Expr
              | power Expr * Expr

  op pow : {(x,y) : Int * Int | y >= 0} -> Int
  def pow(x,y) = if (y = 0) then 1
                 else x * pow(x,y-1)

  op depth : Expr -> Int
  def depth(e) = case e of
                    | constant i -> 0
                    | plus(e1,e2) -> 1 + maxdepth(e1,e2)
                    | times(e1,e2) -> 1 + maxdepth(e1,e2)
                    | power(e1,e2) -> 1 + maxdepth(e1,e2)

  op maxdepth : Expr * Expr -> Int
  def maxdepth(e1,e2) = let d1 = depth(e1) in
                        let d2 = depth(e2) in
                        if (d1 > d2) then d1 else d2

  op eval : Expr -> Int
  def eval(e) = case e of
                   | constant i -> i
                   | plus(e1,e2) -> eval(e1) + eval(e2)
                   | times(e1,e2) -> eval(e1) * eval(e2)
                   | power(e1,e2) -> pow(eval(e1),eval(e2))

endspec
