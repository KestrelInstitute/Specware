obsolete -- booleans are now built-in

Boolean qualifying spec

  import Primitive

%%%  =====================================================================
%%%
%%%  Mon May 10 18:59:47 PDT 2004 
%%%
%%%  The parser now recognizes this names as a special sort:
%%%
%%%    "Boolean"  "Boolean.Boolean"    =>  Boolean   
%%%
%%%  The parser now recognizes these names as special Fun's :
%%%
%%%    "~"        "Boolean.~"          =>  Not       
%%%    "&"        "Boolean.&"          =>  And
%%%    "or"       "Boolean.or"         =>  Or
%%%    "=>"       "Boolean.=>"         =>  Implies
%%%    "<=>"      "Boolean.<=>"        =>  Iff
%%%    "="                             =>  Equals
%%%    "~="                            =>  NotEquals
%%%
%%%  Note that this means (for now) that "~" cannot be used as "Integer.~"
%%%
%%%  New names "&&"  "||"  will be forthcoming...
%%%
%%%  =====================================================================
%%% 
%%%   % sorts:
%%% 
%%%   % sort Boolean
%%% 
%%%   % ops whose Lisp code is hand-written:
%%% 
%%%   op ~             : Boolean -> Boolean
%%%   op &   infixr 15 : Boolean * Boolean -> Boolean 
%%%   op or  infixr 14 : Boolean * Boolean -> Boolean 
%%%   op =>  infixr 13 : Boolean * Boolean -> Boolean 
%%%   op <=> infixr 12 : Boolean * Boolean -> Boolean 
%%% 
%%%   axiom not_def is
%%%     fa (x : Boolean) ~x = (if x then false else true)
%%% 
%%%   axiom and_def is
%%%     fa (x,y : Boolean) (x & y)   = (if x then y    else false)
%%% 
%%%   axiom or_def is
%%%     fa (x,y : Boolean) (x or y)  = (if x then true else y)
%%% 
%%%   axiom implies_def is
%%%     fa (x,y : Boolean) (x => y)  = (if x then y    else true)
%%% 
%%%   axiom iff_def is
%%%     fa (x,y : Boolean) (x <=> y) = (if x then y    else ~y)
%%% 
%%%   % ops whose Lisp code is generated:
%%% 
%%%   op ~=  infixr 20 : fa(a) a * a -> Boolean
%%% 
%%%   def ~=  (x,y) = ~(x = y)
%%% 
%%%  =====================================================================

   % ops conceptually belonging to this spec but introduced elsewhere:
 
   % op compare  : Boolean * Boolean -> Comparison
   % op toString : Boolean -> String  % deprecated
   % op show     : Boolean -> String

endspec
