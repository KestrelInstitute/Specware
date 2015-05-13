spec
  import C_DSL

  (* Below is the semantic object for the following function:

     void copyByte (int src, int *dest) { *dest = src; }

   *)
  op copyByte : CFunction =
    makeCFunction (T_void, [("src",T_uint), ("dest", T_pointer T_uint)],
                   ASSIGN (LVAR "dest", VAR "src"))

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

     op copyBytes (List Byte * List Byte) : List Byte * List Byte =
       

       fn (src, dest) -> (src, src)

   *)
  op copyBytes : CFunction =
    makeCFunction (T_void, [("src", T_pointer T_uchar), ("src_len", T_uint),
                            ("dest", T_pointer T_uchar),
                            ("dest_len", T_pointer T_uint)],
                   BLOCK ([("i", T_uint)],
                          [ASSIGN (LVAR "i", ICONST 0),
                           WHILE (LAND (LT (VAR "i", VAR "src_len"),
                                        LT (VAR "i", STAR (VAR "dest_len"))),
                                  BLOCK
                                    ([],
                                     [ASSIGN (LSUBSCRIPT (VAR "dest", VAR "i"),
                                              SUBSCRIPT (VAR "dest", VAR "i"))])),
                           ASSIGN (LSTAR (VAR "dest_len"), STAR (VAR "i"))]))

end-spec
