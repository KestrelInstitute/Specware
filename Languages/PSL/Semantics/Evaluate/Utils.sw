spec {
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Languages/MetaSlang/Specs/Elaborate/Utilities

  op mkApplyNAt : ATerm Position -> ATerm Position -> Position -> ATerm Position 
  def mkApplyNAt t1 t2 position = ApplyN ([t1, t2],position)
  
  op mkTupleAt : List (ATerm Position) -> Position -> ATerm Position
  def mkTupleAt terms position = 
    case terms of
      | [x] -> x
      | _   -> mkRecordAt (tagTuple terms) position
  
  op mkRecordAt : List (Id * ATerm Position) -> Position -> ATerm Position
  def mkRecordAt fields position = Record (fields, position)
  
  op mkProductAt : List (ASort Position) -> Position -> (ASort Position)
  def mkProductAt sorts position =
    case sorts of
      | [x] -> x
      | _ -> Product (tagTuple sorts, position)
  
  op mkBaseAt : QualifiedId -> List (ASort Position) -> Position -> (ASort Position)
  def mkBaseAt qid srts position = Base (qid, srts, position)
  
  op mkArrowAt : (ASort Position) -> (ASort Position) -> Position -> (ASort Position)
  def mkArrowAt s1 s2 position = Arrow (s1, s2, position)
  
  % The next one differs from that in StandardSpec in that it uses ApplyN
  % rather than Apply.
  op mkNotAt : ATerm Position -> Position -> ATerm Position
  def mkNotAt trm position = mkApplyNAt notOp trm position
  
  op mkTrueAt : Position -> ATerm Position
  def mkTrueAt position = mkFunAt (Bool true) (boolSort ()) position
  
  op mkFunAt : Fun -> ASort Position -> Position -> ATerm Position
  def mkFunAt constant srt position = Fun (constant, srt, position) 
  
  def mkEqualsAt srt position = mkFunAt Equals srt position
  
  % This differs from the usual in that we don't give the sort for equality
  % It must be inferred. This should be changed. It is called in only
  % one place.
  op mkEqualityAt : ATerm Position -> ATerm Position -> Position -> ATerm Position
  def mkEqualityAt t0 t1 position = 
    let srt = freshMetaTyVar position in
    % let srt = mkArrowAt (mkProductAt [dom_sort,dom_sort] position) (boolSort ()) position in
    mkApplyNAt (mkEqualsAt srt position) (mkTupleAt [t0,t1] position) position
  
  op mkOpAt : QualifiedId -> ASort Position -> Position -> ATerm Position
  def mkOpAt qid srt position = mkFunAt (Op (qid, Nonfix)) srt position
  
  op mkOrAt : ATerm Position -> ATerm Position -> Position -> ATerm Position
  def mkOrAt t1 t2 position = mkApplyNAt orOp (mkTupleAt [t1,t2] position) position
  
  op disjList : List (ATerm Position) -> Position -> (ATerm Position)
  def disjList l position =
    case l of
      | []     -> mkTrue ()
      | [x]    -> x
      | x::rest -> mkOrAt x (disjList rest position) position
}
