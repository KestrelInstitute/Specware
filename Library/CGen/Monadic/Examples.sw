Examples_spec = spec
  import C_DSL

  (* Below is the semantic object for the following function:

     void copyByte (int src, int *dest) { *dest = src; }

   *)
  op copyByte : ExtDecl =
    FUNCTION (TN_void, "copyByte",
              [(TN_uint,"src"), (TN_pointer TN_uint, "dest")],
              ASSIGN (LSTAR (VAR "dest"), VAR "src"))

  (* This is the specification for the syntax, in the form of a top-level
  external declaration, whose semantics equals copyByte *)
  op copyByte_C : { d:ExternalDeclaration | compile1XU d = copyByte }

  (* This is the semantic object for the following function:

     void copyBytes (unsigned char *src, unsigned int src_len,
                     unsigned char *dest, unsigned int *dest_len) {
       unsigned int i;
       i = 0;
       while (i < src_len && i < *dest_len) {
         dest[i] = src[i];
         i = i + 1;
       }
       *dest_len = i;
     }
   *)
  op copyBytes : ExtDecl =
    FUNCTION (TN_void, "copyBytes",
              [(TN_pointer TN_uchar, "src"), (TN_uint, "src_len"),
               (TN_pointer TN_uchar, "dest"),
               (TN_pointer TN_uint, "dest_len")],
              BLOCK ([(TN_uint, "i")],
                     [ASSIGN (LVAR "i", ICONST "0"),
                      WHILE (LAND (LT (VAR "i", VAR "src_len"),
                                   LT (VAR "i", STAR (VAR "dest_len"))),
                             BLOCK
                               ([],
                                [ASSIGN (LSUBSCRIPT (VAR "dest", VAR "i"),
                                         SUBSCRIPT (VAR "src", VAR "i")),
                                 ASSIGN (LVAR "i", ADD (VAR "i", ICONST "1"))])),
                      ASSIGN (LSTAR (VAR "dest_len"), STAR (VAR "i"))]))

  (* This is the specification for the syntax, in the form of a top-level
  external declaration, whose semantics equals copyBytes *)
  op copyBytes_C : { d:ExternalDeclaration | compile1XU d = copyBytes }

end-spec

% README: need to load lisp for GenerateC.sw before running this!
Examples_impl =
transform Examples_spec by
{at copyByte_C { unfold copyByte; generateC}
   ;
 at copyBytes_C { unfold copyBytes; generateC}
   ;
 makeDefsFromPostConditions [copyByte_C, copyBytes_C]
 }

Examples_printed = spec
  import Examples_impl, CPrettyPrinter

  op copyByte_String : String = printTranslationUnitToString [copyByte_C]
end-spec
