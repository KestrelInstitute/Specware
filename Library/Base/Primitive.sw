spec

  (*
  This is a special spec that introduces the primitive sorts and ops. These
  sorts and ops are primitive in the sense that their interpretation is fixed
  by definition in every model:
  - Boolean.Boolean denotes the set {T,F} of truth values;
  - Integer.Integer denotes the set of (all) integer numbers;
  - Integer.~ denotes unary minus on integers;
  - Integer.+ denotes addition on integers;
  - Integer.< denotes the less-than relation on integers;
  - Nat.Nat denotes the set of (all) natural numbers;
  - Char.Char denotes the set of 8-bit characters occupying decimal
    positions 0 to 255 in the ISO-8859-1 code table (the first 128
    characters of that code table are the ASCII characters);
  - Char.ord denotes the function that maps a character to its position
    in the code table;
  - List.List(a) denotes, for every set set A assigned to the sort variable
    a, the set of finite lists over A;
  - String.String the set of finite sequences of the characters denoted by
    Char.Char;
  - String.explode denotes the function that maps a string to the list of
    its component characters.

  The type checker has hardwired knowledge of the primitive sorts because
  it uses them to type certain constructs of the language, e.g. literals
  and axioms. Despite this hardwired knowledge in the type checker, the
  primitive sorts are not automatically available in specs, but they have
  to be explicitly introduced, together with the primitive ops, which is
  done in this spec.
  *)

  sort Boolean.Boolean

  sort Integer.Integer
  op Integer.~ : Integer.Integer -> Integer.Integer
  op Integer.+ infixl 25 : Integer.Integer * Integer.Integer -> Integer.Integer
  op Integer.< infixl 20 : Integer.Integer * Integer.Integer -> Boolean.Boolean

  sort Nat.Nat = {n : Integer.Integer | ~1 Integer.< n}
                                        % the reason for this rather involved
                                        % way to say that n is non-negative is
                                        % that the op >= is not available yet
                                        % (i.e. it is not primitive); it is
                                        % defined in spec Integer
                 % the definition of Nat.Nat as a subsort of Integer.Integer
                 % is needed because the type checker has no hardwired
                 % knowledge of this relationship between those two sorts

  sort Char.Char
  op Char.ord : Char.Char -> {n : Nat.Nat | n < 256}

  sort List.List a = | Nil | Cons a * List.List a
                     % the definition of List.List(a) as a coproduct is
                     % needed because the type checker has no hardwired
                     % knowledge of this property of List.List(a)

  sort String.String
  op String.explode : String.String -> List.List Char.Char

endspec
