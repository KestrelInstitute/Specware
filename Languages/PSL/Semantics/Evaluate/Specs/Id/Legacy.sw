Id qualifying spec
  import ../Id
  import ../Pretty/Legacy
  import /Languages/MetaSlang/AbstractSyntax/AnnTerm
  import translate (translate ../MonadicSets/AsLists by {Elem.Elem +-> Id.Id})
    by {Elem._ +-> Id._, MonadFold._ +-> IdSetEnv._, _ +-> IdSet._}

  sort Id.Id = QualifiedId

  % op makeId : String -> String -> Id
  def Id.makeId str1 str2 = mkQualifiedId (str1,str2)

  % op UnQualifiedId.makeId : String -> Id
  def UnQualifiedId.makeId str = mkUnQualifiedId str

  % op pp : Id -> Doc
  def Id.pp id = ppString (printQualifiedId id)

  % op show Id -> String
  def Id.show = printQualifiedId
endspec

