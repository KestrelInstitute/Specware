player = spec
   op you:    Boolean
   op me:     Boolean
   op next:   Boolean -> Boolean
   op isMe?:  Boolean -> Boolean
   op isYou?: Boolean -> Boolean 

   axiom y is you = false
   axiom m is me  = true
   def next(b)    = ~b
   def isMe?(b)   = b
   def isYou?(b)  = ~b

   end

position = spec 
   import player

   sort position = Nat * Nat * Nat * Nat * Boolean

   op numPearls : position -> Nat
   def numPearls (b) = b.1 + b.2 + b.3 + b.4

   end

move = spec
    import position
    sort row     = {n : Nat | n > 0 & n <= 4}
    sort move    = position * row * Nat
    op legal?:   move -> Boolean
    def legal?(m) = true
%   def legal?(mov) = 
%       let rw = mov.2 in 
%       let num = mov.3 in 
%       let pos = mov.1
%         in 
%           (project rw pos) >= num 
%            & num > 0 
%            & numPearls(pos) > n)
    sort legalMove =  {m: move | legal?}
    end
