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

  %% OPERATIONS

  op processOptions : JSpec * Option Spec * String -> List JavaFile
  op printJavaFile : Java.JavaFile -> ()


end-spec
