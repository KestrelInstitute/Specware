spec
  import C#C1

  (* Below is the semantic object for the following function:

     void copyByte (int src, int *dest) { *dest = src; }

   *)
  op copyByte : CFunction =
    makeCFunction (T_void, [("src",T_uint), ("dest", T_pointer T_uint)],
                   {src_val <- lookupIdentifierValue "src";
                    dest_ptr <- lookupIdentifierAddr "dest";
                    writePtrValue (dest_ptr, src_val)})

  (* op copyByte_inC : {fd : FunctionDeclaration | ... eval fd = copyByte ... } *)


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
                   {addLocalBinding ("i", V_int (T_uint, 0));
                    mfix (fn recurse -> fn unit ->
                          {i <- lookupIdentifierInt "i";
                           src_len_int <- lookupIdentifierInt "src_len";
                           dest_len_val <- lookupIdentifierValue "dest_len";
                           dest_len_star <- readPtrValue dest_len_val;
                           dest_len_int <- intOfValue dest_len_star;
                           if i < src_len_int && i < dest_len_int then
                             {src_val <- lookupIdentifierValue "src";
                              src_i <- operator_ADD (src_val, V_int (T_uint, 1));
                              src_i_star <- readPtrValue src_i;
                              dest_val <- lookupIdentifierValue "dest";
                              dest_i <- operator_ADD (dest_val, V_int (T_uint, 1));
                              writePtrValue (dest_i, src_i_star);
                              i_ptr <- lookupIdentifierAddr "i";
                              writePtrValue (i_ptr, V_int (T_uint, i+1));
                              recurse ()}
                           else return ()}) ()})

end-spec
