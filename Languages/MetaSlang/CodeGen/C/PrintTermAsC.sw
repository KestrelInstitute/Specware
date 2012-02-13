AnnSpecPrinter qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/AnnSpec
 % import /Library/IO/Primitive/IO                    % getEnv
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment
 % op SpecCalc.getBaseSpec : () -> Spec % defined in /Languages/SpecCalculus/Semantics/Environment
 op printPragmas?: Bool = true

 %% ========================================================================

 type CFunCall = {f : MSTerm, args : MSTerms}

 op uncurry (t1 : MSTerm, args : MSTerms) : CFunCall =
  case t1 of
    | Apply (t2, t3, _) -> uncurry (t2, [t3] ++ args)
    | _ -> {f = t1, args = args}

 op printTermAsC (trm : MSTerm) : Pretty = 
  case trm of
    | TypedTerm (tm, _,        _) -> printTermAsC tm
    | Lambda    ([(_, _, tm)], _) -> printTermAsC tm
    | Apply     (t1, t2,       _) -> 
      let {f, args} = uncurry (t1, [t2]) in
      let pretty_args = 
          AnnTermPrinter.ppListPath []
                                    (fn (_, arg) -> printTermAsC arg)
                                    (string "(", string ", ", string ")")
                                    args
      in
      blockFill (0, 
                 [(0, string (anyToString f)),
                  (0, pretty_args)])
    | _ -> string ("<term: " ^ anyToString trm ^ ">")

 %% ========================================================================


endspec
