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
     stated by saying that, for some f, m is equivalent to a computation that
     modifies the current Storage by applying f, assuming the precondition is
     true, and that doing this always satisfies the post-condition. *)
  op totally_correct (pre: R -> Storage -> Bool) (m : Monad ())
                     (post : R -> Storage -> Storage -> Bool) : Bool =
    m |= mexists (fn f ->
                    {r <- askR;
                     st_pre <- getState;
                     mimplies (liftProp (pre r st_pre),
                               m_and (putState (f r st_pre),
                                      liftProp (post r st_pre (f r st_pre))))})


end-spec
