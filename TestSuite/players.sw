players is spec 
   sort player
   op nextPlayer: player -> player
   op playerName: player -> String
   axiom namesDiffer is 
      fa(p1:player, p2:player, 
         s1:String, s2:String)
      (playerName p1) = s1 & (playerName p2) = s2 & ~(p1 = p2) 
          => ~(s1 = s2)
   end

twoPlayers is spec
   import players
   op me: player
   op you: player
   axiom nextChangesPlayer is 
      fa(p1,p2)
      nextPlayer p1 = p2 => ~(p1 = p2)
   axiom nextMeYou is
      nextPlayer me = you
   axiom nextYouMe is 
      nextPlayer you = me 
   axiom youNotMe is 
      ~(you = me)
   axiom meMe is 
      playerName me = "ME"
   axiom youYou is 
      playerName you = "YOU"
   end 

twoPlayersImpl is spec
   op playerName : Boolean -> String
   op nextPlayer : Boolean -> Boolean
   op me   : Boolean
   op you  : Boolean 
   def playerName(b) =
      if b then "ME" else "You"
   def nextPlayer(b) = ~b
   def me  = true
   def you = false
   end

twoPlayers = morphism 
    twoPlayers -> twoPlayersImpl {player +-> Boolean}

twoPlayersLisp = generate lisp twoPlayers