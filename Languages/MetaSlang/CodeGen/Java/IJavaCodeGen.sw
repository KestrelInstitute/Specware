(**
 * interface to MetaSlang Java code generation
 *)

JGen qualifying
spec

  %% IMPORTS

  import JGen qualifying /Languages/MetaSlang/Specs/Categories/Specs       % AnnSpec.Spec
  import Java qualifying /Languages/Java/Java
  import Monad

  %% TYPES

  type JSpec = Java.CompUnit
  type JavaSpec = JSpec
  type TCx = StringMap.Map JavaExpr


%  type JcgInfo = {
%		  clsDecls : List ClsDecl,
%		  collected : Collected
%		 }

%  type Collected = {
%		    arrowclasses : List Java.ClsDecl,
%		    productSorts : List Sort
%		   }

  %% OPERATIONS

  (**
   * performs the transformation as required by the Java code generation
   *)
  op transformSpecForJavaCodeGen: (* basespec: *) Spec -> (* spc: *) Spec -> Spec

  (**
   * takes a spec which is supposed to be the result of the above
   * transformSpecForJavaCodeGen operation and generates a Java spec
   * from it
   *)
  op generateJavaCodeFromTransformedSpec: Spec -> JSpec

  (**
   * same as above using the JGenEnv monad defined in Monad.sw
   *)
  op generateJavaCodeFromTransformedSpecM: Spec -> JGenEnv JSpec

  (**
   * returns the java type for the given MetaSlang type.
   * assumes that the sort and envspec in the monad are
   * already transformed using the above transform-op
   *)
  op metaSlangTypeToJavaType: Sort -> JGenEnv JavaType


  op metaSlangTermToJavaExpr: MS.Term -> JGenEnv (JavaBlock * JavaExpr)

  op metaSlangTermsToJavaExprs: (List MS.Term) -> JGenEnv (JavaBlock * List JavaExpr)

  (**
   * reads the optional option spec, which contains user-supplied
   * information concerning the target directory of the code generation,
   * package name, public methods, etc. (see README.JavaCodeGen for details)
   * and returns a list of Java Files, which are a partitioning of the
   * classes and interfaces of the input jspec. As a side-effect, it
   * also actually writes the corresponding java files.
   * (remark: the string argument is not used, should go away at some point)
   *)
  op processOptions : JSpec * Option Spec * String -> List JavaFile
  op printJavaFile : Java.JavaFile -> ()


  % utils for constructing Java elements ------------------------

  op mkBinExp       : Id       * List JavaExpr -> JavaExpr
  op mkMethInvName  : JavaName * List JavaExpr -> JavaExpr
  op mkVarJavaExpr  : Id                       -> JavaExpr
  op mkNewClasInst  : Id       * List JavaExpr -> JavaExpr

  op changeTimeVars : JavaBlockStmt            -> JavaBlockStmt


end-spec
