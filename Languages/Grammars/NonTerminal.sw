
NonTerminal = CFG qualifying spec

type NonTerminal

op nonTerminal (s : String) : NonTerminal

end-spec



NonTerminalAsString = CFG qualifying spec

type NonTerminal = String

op nonTerminal (s : String) : NonTerminal = s

end-spec



NonTerminalAsStringM = morphism NonTerminal -> NonTerminalAsString {}
