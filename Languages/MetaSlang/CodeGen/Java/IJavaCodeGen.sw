(**
 * interface to MetaSlang Java code generation
 *)

JGen qualifying
spec

  %% IMPORTS

  import /Languages/MetaSlang/Specs/Categories/Specs       % AnnSpec.Spec
  import Java qualifying /Languages/Java/Java

  %% TYPES

  type JSpec = Java.CompUnit
  type JavaSpec = JSpec

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


end-spec
