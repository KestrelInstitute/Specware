(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


NonTerminal = CFG qualifying spec

type NonTerminal

op nonTerminal (s : String) : NonTerminal

end-spec



NonTerminalAsString = CFG qualifying spec

type NonTerminal = String

op nonTerminal (s : String) : NonTerminal = s

end-spec



NonTerminalAsStringM = morphism NonTerminal -> NonTerminalAsString {}
