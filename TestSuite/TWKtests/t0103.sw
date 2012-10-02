player = spec
   op you:    Bool
   op me:     Bool
   op next:   Bool -> Bool
   op isMe?:  Bool -> Bool
   op isYou?: Bool -> Bool 

   axiom y is you = false
   axiom m is me  = true
   def next(b)    = ~b
   def isMe?(b)   = b
   def isYou?(b)  = ~b

   end

position = spec 
   import player

   type position = Nat * Nat * Nat * Nat * Bool

   op numPearls : position -> Nat
   def numPearls (b) = b.1 + b.2 + b.3 + b.4

   end

move = spec
    import position
    type row     = {n : Nat | n > 0 && n <= 4}
    type move    = position * row * Nat
    op legal?:   move -> Bool
    def legal?(m) = true
%   def legal?(mov) = 
%       let rw = mov.2 in 
%       let num = mov.3 in 
%       let pos = mov.1
%         in 
%           (project rw pos) >= num 
%            && num > 0 
%            && numPearls(pos) > n)
    type legalMove =  (move | legal?)
    end
