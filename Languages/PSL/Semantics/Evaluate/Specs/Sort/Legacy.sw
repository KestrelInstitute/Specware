\section{Refinement of spec defining MetaSlang types}

\begin{spec}
Type qualifying spec
  import ../Type
  import ../Id/Legacy
  import ../MetaSlang/Legacy
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter
  import ../Spec

  type Type.TypeInfo = AnnSpec.ATypeInfo Position

  % op Type.idOf : TypeInfo -> Id
  def Type.idOf info =
    case info.names of
      | [] -> fail "Type.idOf: type with empty list of ids"
      | [name] -> name
      | _::_ -> fail "Type.idOf: type with more than one id"

  % op ids : TypeInfo -> IdSet.Set

  % op Type.typeinfo_type : TypeInfo -> Type
  def Type.typeinfo_type info =
    case typeInfoDefs info of
      | [] -> fail "Type.typeinfo_type: type with empty list of type schemes"
      | [srt] -> unpackType srt
      | _::_ -> fail "Type.typeinfo_type: type with more than one type scheme"

  % op withId infixl 18 : TypeInfo * Id -> TypeInfo
  % op withIds infixl 18 : TypeInfo * IdSet.Set -> TypeInfo
  % op withType infixl 18 : TypeInfo * Type -> TypeInfo

  % op makeType : Id -> Type -> TypeInfo
  def Type.makeType id (tvs, typ) = 
    {names = [id],
     dfn   = maybePiType (tvs, typ)}

  def TypeNoType.makeType id = 
    {names = [id], 
     dfn   = Any noPos}

  % op join : TypeInfo -> TypeInfo -> Env TypeInfo

  % op pp : TypeInfo -> Doc
  def Type.pp = ppATypeInfo

  % op show : TypeInfo -> String
  def Type.show typeInfo = ppFormat (pp typeInfo)

  type Type.Ref = Id.Id

  % op TypeRef.pp : Type.Ref -> Doc
  def TypeRef.pp = Id.pp

  % op deref : Spec -> Ref -> Env TypeInfo
  def TypeEnv.deref spc ref = findTheType spc ref
    
  % op refOf : TypeInfo -> Ref
  def Type.refOf typeInfo = idOf typeInfo

  % op refOf : TypeInfo -> Env Ref
  def TypeEnv.refOf typeInfo = return (idOf typeInfo)
endspec
\end{spec}

Above we introduce \Type{Type} where there was \Type{TypeScheme}
before. The idea is that in the near term, we can refine \Type{Type}
in that way, and then later add polymorphism to the available types.

That being the case, we don't need an explicit set \verb{TypeVars}. 
as found in the current \verb{TypeInfo}.

There is an argument for restoring a list of type variables
and making them parameters to the type and obliging a user
to declare when a type is polymorphic.

So for example,
\begin{verbatim}
  type List Elem
\end{verbatim}
would not be valid unless \Type{Elem} had previously
been declared as a type. This might address something
that Alessandro had been requesting.

The \Op{with} operators are meant as a temporary measure until syntax
for updating formal products and maps is introduced. In the case of
records, such an update is straightforward. For abstract types it seems
trickier to me.
