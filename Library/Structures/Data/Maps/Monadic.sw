MonadicMap qualifying spec
  import /Library/Structures/Data/Monad
  import translate (Dom qualifying ../Elem) by {Dom.Elem +-> Dom.Dom}
  import translate (Cod qualifying ../Elem) by {Cod.Elem +-> Cod.Cod}

  sort MapRef

  op new : Monad MapRef
  op copy : MapRef -> Monad MapRef
  op eval : MapRef * Dom -> Monad Cod
  op update : MapRef * Dom * Cod -> Monad ()

  axiom update_idempotence is fa (m,x,y,z) {update (m,x,y);update(m,x,z)} = update (m,x,z)
  axiom update_1 is fa (m,x,y,z) {update (m,x,y);eval(m,x)} = return y
  axiom update_1 is fa (m,x,x',y) ~(x = x') => {update (m,x,y);eval(m,x')} = eval (m,x')
  axiom update_assoc is fa (m,x,y,x',y')
    ~(x = x') => {update (m,x,y, update (m,x',y')} = update (update m x' y') x y
  axiom update_idempotence is fa (m,x,y,y') 
    update (update m x y) x y' = update m x y'

endspec
