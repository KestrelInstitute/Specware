(*
2005:03:18
AC
Extension of the base spec Integer with exponentiation and ops for min/max of
sets as well as minimizers/maximizers of integer-valued functions.

ISSUE:
The notion of min/max(imizers) should be factored in a more general spec for
orders.
*)


Integer qualifying spec


  % exponentiation:
  op ** (base:Integer, exp:Nat) infixl 30 : Integer =
    if exp = 0 then 1 else base * (base ** (exp - 1))


  import /Library/General/Sets


  % integer is minimum in set:
  op isMinIn (i:Integer, s: Set Integer) infixl 20 : Boolean =
    i in? s && (fa(i1) i1 in? s => i <= i1)

  % set of integers has minimum:
  op hasMin? (s: Set Integer) : Boolean = (ex(i) i isMinIn s)

  % min integer in set:
  op minIn (s: Set Integer | hasMin? s) : Integer = the(i) i isMinIn s


  % integer is maximum in set:
  op isMaxIn (i:Integer, s: Set Integer) infixl 20 : Boolean =
    i in? s && (fa(i1) i1 in? s => i >= i1)

  % set of integers has maximum:
  op hasMax? (s: Set Integer) : Boolean = (ex(i) i isMaxIn s)

  % max integer in set:
  op maxIn (s: Set Integer | hasMax? s) : Integer = the(i) i isMaxIn s


  % value minimizes integer-valued function in set:
  op [a] minimizes? (x:a) (f: a -> Integer) (s: Set a) : Boolean =
    x in? s && (fa(x1) x1 in? s => f x <= f x1)

  % minimizers of function in set:
  op [a] minimizers (f: a -> Integer) (s: Set a) : Set a =
    fn x -> minimizes? x f s

  % value uniquely minimizes integer-valued function in set:
  op [a] uniquelyMinimizes? (x:a) (f: a -> Integer) (s: Set a) : Boolean =
    x onlyMemberOf (minimizers f s)

  % integer-valued function has unique minimizer in set:
  op [a] hasUniqueMinimizer? (f: a -> Integer) (s: Set a) : Boolean =
    single? (minimizers f s)

  % unique minimizer of integer-valued function in set:
  op [a] minimizer (f: a -> Integer, s: Set a | hasUniqueMinimizer? f s) : a =
    theMember (minimizers f s)


  % value maximizes integer-valued function in set:
  op [a] maximizes? (x:a) (f: a -> Integer) (s: Set a) : Boolean =
    x in? s && (fa(x1) x1 in? s => f x >= f x1)

  % maximizers of function in set:
  op [a] maximizers (f: a -> Integer) (s: Set a) : Set a =
    fn x -> maximizes? x f s

  % value uniquely maximizes integer-valued function in set:
  op [a] uniquelyMaximizes? (x:a) (f: a -> Integer) (s: Set a) : Boolean =
    x onlyMemberOf (maximizers f s)

  % integer-valued function has unique maximizer in set:
  op [a] hasUniqueMaximizer? (f: a -> Integer) (s: Set a) : Boolean =
    single? (maximizers f s)

  % unique maximizer of integer-valued function in set:
  op [a] maximizer (f: a -> Integer, s: Set a | hasUniqueMaximizer? f s) : a =
    theMember (maximizers f s)

endspec
