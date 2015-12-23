(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% ---------------------------------------------------------------------
% Link recursive functional programs to imperative programs with loops
% ---------------------------------------------------------------------

Imp = spec

import /Library/Structures/Data/Monad
% import /Library/Structures/Data/Monad/State

% ---------------------------------------------------------------------
% Control Structures
%  see also Specware/Library/Structures/Data/Monad/Control.sw
% ---------------------------------------------------------------------

% Importing the Monad specs enables us to use special syntax
% - Assignments         "x <- stmt"      are specified as monadBind
% - Compound statements "{stmt1; stmt2}" are specified as monadSeq 
% - Return statement    "return expr"    are specified
% 
% Note that these operations are not predefined
% We refine them to the extent that they operate on states and values
% but leave state ops unspecified
% ---------------------------------------------------------------------

type State 
type Result A = A
type Monad A  = State -> Result A * State 

op monadBind: [A,B] (Monad A) * (A -> Monad B) -> Monad B
def monadBind (stm, binder) =
    fn state -> (let (val, newState) = stm state
                 in 
                    binder val newState)
  
op monadSeq : [A,B] (Monad A) * (Monad B)      -> Monad B
def monadSeq (stm1, stm2) = monadBind(stm1, (fn _ -> stm2))

op return : [A]   A   -> Monad A 
def return val = fn state -> (val, state) 

% ---------------------------------------------------------------------
% Lift expressions into statements 
% ---------------------------------------------------------------------

%% TODO: backtick used to be named ` but that now seems to be an illegal name
op [A]   backtick (expr : A): Monad A   = return expr

op -                : Monad ()  = return ()

op [A]  '(stm : Monad A): A     = inverse return stm
   
% ---------------------------------------------------------------------
% Control Operations 
% ---------------------------------------------------------------------

% The following two are just needed for verification purposes 

op repeat (stm : Monad (), n : Nat): Monad () =
  if n = 0 then - else {stm; repeat (stm, n-1)}

op terminates?(goon?: Monad Bool, stm : Monad ()) : Bool =
   ex(n:Nat) {repeat(stm, n); goon?} = backtick false

% ---------------------------------------------------------------------

op [A] If (test?: Monad Bool, thencase: Monad A, elsecase: Monad A): Monad A
    = { b <- test?
      ; if b then thencase 
             else elsecase
      }

op while (goon?: Monad Bool) (body: Monad () | terminates? (goon?, body))
         : Monad ()
   = { b <- goon?
     ; if b then {body ; while goon? body}
            else return ()
     }


% ---------------------------------------------------------------------
% Generic functional and imperative program structures
% ---------------------------------------------------------------------

op [A,B] frec (init:A, base: B, expr: A * B -> B, decr: A->A, x:A) : B
  =  if x = init 
       then base  
       else expr (x, frec (init, base, expr, decr, decr x))

op [A,B] frec_aux (init:A, base: B, expr: A * B -> B, decr: A->A, limit:A) : B
  =  let def aux (x:A): B = if x = init 
                               then base   
                               else expr (x, aux (decr x))
     in aux limit 

op [A,B] floop (init:A, base: B, expr: A * B -> B, incr: A->A, limit:A) : 
                Monad B
  = {  x <- backtick init
    ;  r <- backtick base 
    ;  while ( backtick (x ~= limit) )
             { x <- backtick (incr x)
             ; r <- backtick (expr (x,r))
             ; -    % return ()
             }
    ;  return r
    } 

% ---------------------------------------------------------------------
% Linking functional and imperative program structures
% ---------------------------------------------------------------------


theorem rec_to_loop is [A,B]
   fa (init:A, base: B, expr: A * B -> B, decr: A->A, x:A)
           frec  (init, base, expr, decr, x)
       =  '(floop (init, base, expr, inverse decr, x) )
   
theorem rec_aux_to_loop is [A,B,C]
   fa (init:A, base: B, expr: A * B -> B, decr: A->A, limit:A)
          frec_aux  (init, base, expr, decr, limit)
       =  '(floop (init, base, expr, inverse decr, limit))

% ---------------------------------------------------------------------
% More direct versions that I can't use yet 
% Once the simplifier can handle let defs we could drop the
% definitions frec, frec_aux, and floop and the above two theorems
% and work directly on the function body
% ---------------------------------------------------------------------


theorem rec_to_loop1 is [A,B]
   fa (init:A, base: B, expr: A * B -> B, decr: A->A, z:A, f: A -> B)
      (fa (x:A) f x = (if x = init 
                         then base 
                         else expr (x, f (decr x))))
      =>
   f z        
   =  '{  x <- backtick init
       ;  r <- backtick base
       ;  while ( backtick (x ~= z) )
                { x <- backtick (inverse decr x); r <- backtick (expr (x,r)); - }
       ;  return r
       }    

theorem rec_aux_to_loop1 is [A,B]
   fa (init:A, base: B, expr: A * B -> B, decr: A->A, limit : A)
      (let def aux (x:A): B = if x = init 
                                 then base
                                 else expr (x, aux (decr x))
       in aux limit)       
   =  '{  x <- backtick init
       ;  r <- backtick base
       ;  while ( backtick (x ~= limit) )
                { x <- backtick (inverse decr x)
                ; r <- backtick (expr (x,r))
                ; -    % return ()
                }
       ;  return r
       } 

proof isa e_cqt_Obligation_subtype 
  sorry
end-proof


endspec
