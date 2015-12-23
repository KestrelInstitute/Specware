(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Examples_spec = spec
  import ../C_DSL

  (* Below is the semantic object for the following function:

     void copyByte (int src, int *dest) { *dest = src; }

   *)
  op copyByte : ExtDecl =
    FUNCTION_m (TN_void, "copyByte",
                [(TN_uint,"src"), (TN_pointer TN_uint, "dest")],
                ASSIGN_m (LSTAR_m (VAR_m "dest"), VAR_m "src"))

  (* This is the specification for the syntax, in the form of a top-level
  external declaration, whose semantics equals copyByte *)
  op copyByte_C : { d:TranslationUnitElem | evalTranslationUnitElem d = copyByte }

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
    FUNCTION_m (TN_void, "copyBytes",
                [(TN_pointer TN_uchar, "src"), (TN_uint, "src_len"),
                 (TN_pointer TN_uchar, "dest"),
                 (TN_pointer TN_uint, "dest_len")],
                BLOCK_m [VARDECL_m (TN_uint, "i"),
                         STMT_m (ASSIGN_m (LVAR_m "i", ICONST_m "0")),
                         STMT_m
                           (WHILE_m
                              (LAND_m (LT_m (VAR_m "i", VAR_m "src_len"),
                                       LT_m (VAR_m "i", STAR_m (VAR_m "dest_len"))),
                               BLOCK_m
                                 [STMT_m
                                    (ASSIGN_m (LSUBSCRIPT_m (VAR_m "dest", VAR_m "i"),
                                               SUBSCRIPT_m (VAR_m "src", VAR_m "i"))),
                                  STMT_m
                                    (ASSIGN_m (LVAR_m "i",
                                               ADD_m (VAR_m "i", ICONST_m "1")))])),
                         STMT_m
                           (ASSIGN_m (LSTAR_m (VAR_m "dest_len"), STAR_m (VAR_m "i")))])

  (* This is the specification for the syntax, in the form of a top-level
  external declaration, whose semantics equals copyBytes *)
  op copyBytes_C : { d:TranslationUnitElem | evalTranslationUnitElem d = copyBytes }

end-spec

Examples_impl =
transform Examples_spec by
{at copyByte_C  { unfold copyByte;  rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 at copyBytes_C { unfold copyBytes; rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [copyByte_C, copyBytes_C]
 }

Examples_string = spec
  import Examples_impl, ../CPrettyPrinter

  op copyByte_String : String = printTranslationUnitToString [copyByte_C]
  op copyBytes_String : String = printTranslationUnitToString [copyBytes_C]
end-spec

Examples_printed =
transform Examples_string by
{at copyByte_String {simplify};
 at copyBytes_String {simplify}}
