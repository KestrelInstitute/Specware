%%  PSL Toplevel Specification

%% Moved body into AuxPSL.sw so other apps such as Accord could
%% access it without generating PSL.lisp 

let PSL =
  spec 
    import AuxPSL
    import /Languages/PSL/CodeGen/ToC
  endspec
in generate lisp PSL

