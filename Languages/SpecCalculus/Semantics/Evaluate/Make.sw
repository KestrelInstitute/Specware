(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Experimental file -- not accessed directly by SpecCalculus terms

Specware qualifying
spec

  import /Languages/MetaSlang/Specs/Elaborate/Utilities
  import ../../AbstractSyntax/Types
  import Spec
  import Java
  import Generate

  op Specware.run_cmd : String * List String -> () % defined in toplevel.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op makeLCJ (spec_info : ValueInfo)
             (spec_uid  : RelativeUID)
             (status    : PrismStatus)
   : Env () =
   %% make Lisp, C, and Java versions
   %% Lisp:  version/lisp/foo.lisp file
   %% C   :  version/C/foo.c, foo.h, foo.o, foo*, ...
   %% Java:  version/java/xyz.java, foo*
   {
    (target_path, name) <- case spec_uid of
                             | UnitId_Relative (uid as {path,hashSuffix}) -> 
                               { 
                                current_uid   <- getCurrentUID;
                                current_path  <- removeLast current_uid.path;
                                relative_path <- removeLast path;
                                name          <- last       path;
                                path          <- return (current_path ++ relative_path);
                                return (path, name)
                                }
                             | SpecPath_Relative uid -> 
                               {
                                path <- removeLast uid.path;
                                name <- last       uid.path;
                                return (path, name)
                                };
     print("\n-Lisp-\n");
     makeLisp name spec_info spec_uid target_path status;
     print("\n-C-\n");
     makeC    name spec_info spec_uid target_path status;
     print("\n-Java-\n");
    %makeJava name spec_info spec_uid target_path status;
     print("\n-----\n")
     }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op makeLisp (name        : String)
              (spec_info   : ValueInfo)
              (spec_uid    : RelativeUID)
              (target_path : List String)
              (status      : PrismStatus)
    : Env ValueInfo =
    let version = show status.version in
    {
     print ("\n;;; Generating Lisp " ^ version ^ "\n");
     %% Use a UnitId instead of just getting the path directly,
     %% so that uidToFullPath can look for device names, etc...
     uid <- return {path = target_path ++ ["Version_" ^ version, "lisp", name], hashSuffix = None};
     filename <- return ((uidToFullPath uid) ^ ".lisp");
     print ("\n;;; Filename = " ^ filename  ^ "\n");
     evaluateLispCompile (spec_info, (UnitId spec_uid, noPos), Some filename, false)
   }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op writeMakeFile?  : Bool = true  % make it easier to disable this
  op runMakeFile?    : Bool = true  % make it easier to disable this
  op writeReadyFile? : Bool = true  % make it easier to disable this

  op makeC (name        : String)
           (spec_info   : ValueInfo)
           (spec_uid    : RelativeUID)
           (target_path : List String)
           (status      : PrismStatus)
    : Env () =
    %% NOTE: This does not yet handle all the options in the lisp version to be found in toplevel.lisp
    let version = show status.version in
    {
     print ("\n;;; Generating C " ^ version ^ "\n");
     c_dir <- return (target_path ++ ["Version_" ^ version, "C"]);
     uid   <- return {path = c_dir ++ [name], hashSuffix = None};
     filename <- return (uidToFullPath uid);

     print ("\n;;; Filename = " ^ filename ^ ".c\n");
     return (ensureDirectoriesExist filename);

     evaluateCGen (spec_info, (UnitId spec_uid, noPos), Some filename);
     if writeMakeFile? then 
             {
              device <- return (Specware.currentDeviceAsString ());
              path   <- return ([device] ++ c_dir ++ ["swcmake.mk"]);
              makefile <- return (uidToFullPath (uid << {path = path}));
              print (";;; Local Makefile: " ^ makefile ^ "\n");
              sw_make_file <- return (case getEnv "SPECWARE4" of
                                        | Some s -> s ^ "/Library/Clib/Makerules"
                                        | _ -> "oops");
              print (";;; Specware Make file: " ^ sw_make_file ^ "\n");
              s <- return ("# ----------------------------------------------\n" ^
                             "# THIS MAKEFILE IS GENERATED, PLEASE DO NOT EDIT\n" ^
                             "# ----------------------------------------------\n" ^
                             "\n\n" ^
                             "# the toplevel target extracted from the :make command line:\n" ^
                             "all : " ^ name ^ "\n\n" ^
                             "# include the predefined make rules and variable:\n" ^
                             "include " ^ sw_make_file ^ "\n" ^
                             "# dependencies and rule for main target:\n" ^
                             name ^ ": " ^ name ^ ".o $(HWSRC) $(USERFILES) $(GCLIB)\n" ^
                             "	$(CC) -o " ^ name ^ " $(LDFLAGS) $(CPPFLAGS) $(CFLAGS) " ^ name ^ ".o $(HWSRC) $(USERFILES) $(LOADLIBES) $(LDLIBS)\n");
              return (writeStringToFile (s, makefile));
              if runMakeFile? then 
                {
                 dir       <- return (device ^ (uidToFullPath {path = c_dir, hashSuffix = None}));
                 make_fn   <- return ((case getEnv "SPECWARE4_MAKE" of
                                         | Some s -> s
                                         | _ -> "make"));
                 here <- return (pwdAsString());
                 print (";;; Connecting to ");
                 return (cd dir);
                 print ("\n;;; Running cmd to make C version: " ^ make_fn ^ "-f swcmake.mk\n");
                 return (run_cmd (make_fn, ["-f", "swcmake.mk"]));
                 print (";;; Connecting back to ");
                 return (cd here);
                 print ("\n")
                 }
              else   
                print ("\nNot running make file...\n")
                }
             else
               print ("\nNot creating make file...\n");
               
     if writeReadyFile? then
       let chars = explode filename in
       let c_dirname = case rightmostPositionSuchThat (chars, fn c -> c = #/) of
                         | Some n -> implode (prefix (chars, n + 1))
                         | _ -> ""
       in
       let ready_file = c_dirname ^ "Ready" in
       let line1 = "Wrote C code for " ^ name ^ ", version " ^ version in
       let line2 = "Using choices : " ^ anyToString status.choices         in
       let text  = line1 ^ "\n" ^ line2                                    in
       let _ = writeStringToFile (text, ready_file) in
       print ("\nWrote " ^ ready_file ^ "\n")
     else
       return ()
    }
    
  op Specware.cd          : String -> () % defined in Preface.lisp -- side effect: prints arg to screen
  op Specware.pwdAsString : () -> String % defined in Preface.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op makeJava (name                        : String)
              (spec_info as (Spec spc,_,_) : ValueInfo)
              (spec_uid                    : RelativeUID)
              (target_path                 : List String)
              (status                      : PrismStatus)
    : Env () =
    let version = "Version_" ^ show status.version in
    {

     (Spec option_spec, _, _) <- mkOptionsSpec (version ^ ".java");

     java_dir     <- return (target_path ++ [version, "java"]);
     uid          <- return {path = java_dir ++ [name], hashSuffix = None};
     javaFileName <- UIDtoJavaFile (uid, None);

     print (";;; Filename:  " ^ javaFileName ^ "\n");

     %% Generate Java files
     (optBaseUnitId,baseSpec) <- getBase;
     spc0 <- return (subtractSpec spc baseSpec);
     return (specToJava(baseSpec, spc0, Some option_spec, javaFileName));

     here <- return (pwdAsString());

     %% Compile java files to class files, 
     print (";;; Compiling java files: javac -sourcepath " ^ here ^ " " ^ version ^ "/java/Primitive.java");
     return (run_cmd ("javac", ["-sourcepath", here, version ^ "/java/Primitive.java"]));

     %% Create script to invoke java interpreter on given class files
     script      <- return ("#!/bin/sh\n\ncd `/usr/bin/dirname $0`\n\njava -cp ../.. " ^ version ^ "/java/Primitive $*");
     script_file <- return (version ^ "/java/" ^ (last uid.path));
     print (";;; Writing script to invoke java program: " ^ script_file ^ "\n");
     return (writeStringToFile (script, script_file));
     return (run_cmd ("chmod", ["a+x", script_file]))
    }

  op  mkOptionsSpec : String -> Env ValueInfo
  def mkOptionsSpec s =
    let mtv         : MSType = freshMetaTyVar ("gen", noPos)           in
    let list_type   : MSType = Base (mkQualifiedId ("List",    "List"),   [mtv], noPos) in
    let string_type : MSType = Base (mkQualifiedId ("String" , "String"), [],    noPos) in
    let public_element : SpecElemTerm = (Op ([mkUnQualifiedId "public"], 
                                             Unspecified,
                                             false,
                                             ApplyN ([Fun (Embed (Qualified("List", "Cons"), true),
                                                           Arrow (Product ([("1", mtv), 
                                                                            ("2", list_type)],
                                                                           noPos),
                                                                  list_type,
                                                                  noPos),
                                                           noPos),
                                                      Record ([("1", Fun (String "main",        string_type, noPos)),
                                                               ("2", Fun (Embed (Qualified("List", "Nil"), false), list_type,   noPos))],
                                                              noPos)],
                                                     noPos)),
                                         noPos)
    in
    let package_element : SpecElemTerm = (Op ([mkUnQualifiedId "package"], 
                                              Unspecified,
                                              false,
                                              Fun (String s, string_type, noPos)),
                                          noPos)
    in
    SpecCalc.evaluateSpec [public_element, package_element] UnQualified noPos 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
