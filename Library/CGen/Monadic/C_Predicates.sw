(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Spec for writing and proving properties of computations in the C monad, using
% predicate monads

C_Predicates qualifying spec
  import C
  import /Library/Structures/Data/Monad/PredMonadState
  import /Library/Structures/Data/Monad/PredMonadReader
  import /Library/Structures/Data/Monad/PredMonadError
  % FIXME: add PredMonadNonTerm file, and import it here...

  (* The computation m is partially correct, in the sense of Hoare logic, with
     respect to pre- and post-conditions pre and post, respectively *)
  % FIXME: figure out how to prove m |= catchErrs (mtrue, fn _ -> mfalse) iff m
  % does not raise any errors
  op partially_correct (pre: R -> Storage -> Bool) (m : Monad ())
                       (post : R -> Storage -> Storage -> Bool) : Bool =
    m |= {r <- askR;
          st_pre <- getState;
          mimplies (liftProp (pre r st_pre),
                    {catchErrs (mtrue, fn _ -> mfalse);
                     st_post <- getState;
                     m_and (liftProp (post r st_pre st_post),
                            putState st_post)})}

  (* The computation m is totally correct, in the sense of Hoare logic, with
     respect to pre- and post-conditions pre and post, respectively. This is
     stated by saying that, for some function f, m is equivalent to a
     computation that modifies the current Storage to the first result of f and
     returns the second result of f, assuming the precondition is true, and that
     doing this always satisfies the post-condition. *)
  op [a] totally_correct (pre: R -> Storage -> Bool) (m : Monad a)
                         (post : R -> Storage -> Storage * a -> Bool) : Bool =
    m |= mexists (fn f ->
                    {r <- askR;
                     st_in <- getState;
                     mimplies (liftProp (pre r st_in),
                               m_and ({putState (f r st_in).1; return (f r st_in).2},
                                      liftProp (post r st_in (f r st_in))))})


  (* States that a computation depends only on the environment and the storage,
  that it does not change the storage, and that its result is res *)
  op [a] computation_has_value (r:R) (st:Storage) (m:Monad a) (res:a) : Bool =
    totally_correct
      (fn r_in -> fn st_in -> r_in = r && st_in = st)
      m
      (fn _ -> fn _ -> fn (st_out, res_out) -> st_out = st && res_out = res)

  (* Holds iff expression expr has value v in environment r and storage st *)
  op expression_has_value (r:R) (st:Storage) (expr:Expression) (v:Value) : Bool =
    computation_has_value r st (evaluate expr) v

  (* Holds iff lvalue lv has result res in environment r and storage st *)
  op lvalue_has_result (r:R) (st:Storage) (lv:LValue) (res:LValueResult) : Bool =
    computation_has_value r st (evaluateLValue lv) res

  (* Correctness predicate for XUMonad computations *)
  op [a] xu_computation_correct
    (pre: IncludeFileMap -> FunctionTable -> TranslationEnv -> Bool)
    (m: XUMonad a)
    (post: IncludeFileMap -> FunctionTable -> TranslationEnv ->
       TranslationEnv * (Option ObjectFile * a) -> Bool) : Bool =
    fa (incls,tab,xenv)
      pre incls tab xenv =>
      (case m incls tab xenv of
         | None -> false
         | Some res -> post incls tab xenv res)

  (* States that an XUMond computation has value res given certain inputs *)
  op [a] xu_computation_has_value
      (incls:IncludeFileMap, tab:FunctionTable,xenv_in:TranslationEnv)
      (m: XUMonad a) (res:a) : Bool =
    xu_computation_correct
      (fn incls' -> fn tab' -> fn xenv_in' ->
       incls = incls' && tab = tab' && xenv_in = xenv_in')
      m
      (fn _ -> fn _ -> fn _ ->
         fn (xenv_out,(opt_obj,a)) -> a = res)

end-spec
