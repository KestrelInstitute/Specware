PrintTypeAsC qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/Printer
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment

 op printTypeAsC (typ : MSType) : Pretty =
  case typ of

    | Base (Qualified (q, id), [], _) -> 
      string (if q = "C" then
                case id of
                  | "Uchar"  -> "unsigned char"
                  | "Schar"  -> "signed char"
                  | "Char"   -> "char"
                  | "Ushort" -> "unsigned short"
                  | "Uint"   -> "unsigned int"
                  | "Ulong"  -> "unsigned long"
                  | "Ullong" -> "unsigned long long"
                  | "Sshort" -> "short"
                  | "Sint"   -> "int"
                  | "Slong"  -> "long"
                  | "Sllong" -> "long long"
                  | _        -> "[unknown type: " ^ id ^ "]"
              else
                id)

    | Subtype (Base (Qualified ("C", "Array"), [element_type], _), 
               Apply (Fun (Op (Qualified ("C", "ofLength?"), _), _, _),
                      Fun (Nat n, _, _),
                      _),
               _)
      -> 
      %% TODO: if n = 0, signal error
      blockFill (0, 
                 [(0, printTypeAsC element_type),
                  (0, string "["), 
                  (0, string (show n)),
                  (0, string "]")])

    | Product ([], _) -> string "{}"

    | Product (row, _) -> 
      AnnTermPrinter.ppListPath []
                                (fn (path, (id, typ)) -> 
                                   blockFill (0, [(0, printTypeAsC typ),
                                                  (0, string " "),
                                                  (0, string id)]))
                                (string "{", string ", ", string "}")
                                row
            
    | _ -> string ("[unknown type: " ^ anyToString typ ^ "]")
      
endspec
