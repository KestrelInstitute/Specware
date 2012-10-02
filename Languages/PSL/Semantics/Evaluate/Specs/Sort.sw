\section{Abstraction of MetaSlang Types}

Would prefer \Type{TypeInfo} to be called \Type{Type}.

We have included non-monadic and monadic versions of the make operators.
It is unlikely one will use both. The monadic version is there to
accommodate the case where each new operator is assigned an id. To do
so requires state.

It may be convenient to include monadic versions of some of the other operators.

\begin{spec}
Type qualifying spec
  import Id
  import Env
  import MetaSlang

  type TypeInfo

  op idOf : TypeInfo -> Id.Id
  op ids : TypeInfo -> IdSet.Set
  op typeinfo_type : TypeInfo -> Type

  op withId infixl 18 : TypeInfo * Id.Id -> TypeInfo
  op withIds infixl 18 : TypeInfo * IdSet.Set -> TypeInfo
  op withType infixl 18 : TypeInfo * Type -> TypeInfo

  op makeType : Id.Id -> Type -> TypeInfo
  
  op TypeEnv.makeType : Id.Id -> Type -> Env TypeInfo
  def TypeEnv.makeType id si_type = return (makeType id si_type)

  op TypeNoType.makeType : Id.Id -> TypeInfo

  op TypeNoTypeEnv.makeType : Id.Id -> Env TypeInfo
  def TypeNoTypeEnv.makeType id = return (makeType id)

  op join : TypeInfo -> TypeInfo -> Env TypeInfo

  op pp : TypeInfo -> Doc
  op show : TypeInfo -> String

  type Ref
  type Spec.Spec

  op TypeRef.pp : Ref -> Doc

  op deref : Spec.Spec -> Ref -> TypeInfo
  op refOf : TypeInfo -> Ref

  op TypeEnv.deref : Spec.Spec -> Ref -> Env TypeInfo
  op TypeEnv.refOf : TypeInfo -> Env Ref
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
