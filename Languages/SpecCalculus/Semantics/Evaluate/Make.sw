%% Experimental file -- not accessed directly by SpecCalculus terms

Specware qualifying
spec

  import /Languages/MetaSlang/Specs/Elaborate/Utilities
  import ../../AbstractSyntax/Types
  import Spec
  import Java
  import Generate

  op Specware.run_cmd : String -> () % defined in toplevel.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  makeLCJ : ValueInfo -> RelativeUID -> String -> Env ()
  def makeLCJ spec_info rel_uid version =
    %% make Lisp, C, and Java versions
    %% Lisp:  version/lisp/foo.lisp file
    %% C   :  version/C/foo.c, foo.h, foo.o, foo*, ...
    %% Java:  version/java/xyz.java, foo*
    {
     makeLisp spec_info rel_uid version;
     makeC    spec_info rel_uid version;
     makeJava spec_info rel_uid version
     }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  makeLisp : ValueInfo -> RelativeUID -> String -> Env ValueInfo
  def makeLisp spec_info rel_uid version =
   {
    print ("\n;;; Generating Lisp " ^ version ^ "\n");
    %% Use a UnitId instead of just getting the path directly,
    %% so that uidToFullPath can look for device names, etc...
    uid <- case rel_uid of
	     | UnitId_Relative   (uid as {path,hashSuffix}) -> 
               { 
		current_uid <- getCurrentUID;
		prefix   <- removeLastElem current_uid.path;
		mainName <- lastElem       uid.path;
		path     <- return (prefix ++ [version, "lisp", mainName]);
		return (uid << {path = path})
	       }
	     | SpecPath_Relative uid -> 
	       return uid;
    filename <- return ((uidToFullPath uid) ^ ".lisp");
    evaluateLispCompile (spec_info, (UnitId rel_uid, noPos), Some filename)
   }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  makeC : ValueInfo -> RelativeUID -> String -> Env ()
  def makeC spec_info rel_uid version =
    %% NOTE: This does not yet handle all the options in the lisp version
    %%       to be found in toplevel.lisp
    {
     print ("\n;;; Generating C " ^ version ^ "\n");
     (prefix, cbase) <- case rel_uid of
			      | UnitId_Relative   (uid as {path,hashSuffix}) -> 
                                { 
				 current_uid <- getCurrentUID;
			         return (butLast current_uid.path,
					 last    uid.path)
				}
			      | SpecPath_Relative uid -> 
				return (butLast uid.path,
					last    uid.path);
     c_dir     <- return (prefix ++ [version, "C"]);
     full_path <- return (c_dir ++ [cbase]);
     uid       <- return ({path = full_path, hashSuffix = None});
     filename  <- return (uidToFullPath uid);
     print (";;; Filename: " ^ filename ^ "\n");
     return (ensureDirectoriesExist filename);

     junk <- evaluateCGen (spec_info, Some filename);
     makefile <- return (uidToFullPath (uid << {path = c_dir ++ ["swcmake.mk"]}));
     print (";;; Local Makefile: " ^ makefile ^ "\n");

     sw_make_file <- return (case getEnv "SPECWARE4" of
			       | Some s -> s ^ "/Languages/MetaSlang/CodeGen/C/Clib/Makerules"
			       | _ -> "oops");
     print (";;; Specware Make file: " ^ sw_make_file ^ "\n");
     s <- return ("# ----------------------------------------------\n" ^
		  "# THIS MAKEFILE IS GENERATED, PLEASE DO NOT EDIT\n" ^
		  "# ----------------------------------------------\n" ^
		  "\n\n" ^
		  "# the toplevel target extracted from the :make command line:\n" ^
		  "all : " ^ cbase ^ "\n\n" ^
		  "# include the predefined make rules and variable:\n" ^
 		  "include " ^ sw_make_file ^ "\n" ^
		  "# dependencies and rule for main target:\n" ^
		  cbase ^ ": " ^ cbase ^ ".o $(HWSRC) $(USERFILES) $(GCLIB)\n" ^
		  "	$(CC) -o " ^ cbase ^ " $(LDFLAGS) $(CPPFLAGS) $(CFLAGS) " ^ cbase ^ ".o $(HWSRC) $(USERFILES) $(LOADLIBES) $(LDLIBS)\n");
     return (writeStringToFile (s, makefile));
     cd_cmd        <- return ("cd " ^ (uidToFullPath {path = c_dir, hashSuffix = None}));
     make_cmd      <- return ((case getEnv "SPECWARE4_MAKE" of
				 | Some s -> s
				 | _ -> "make") ^ 
			      " -f swcmake.mk");
     full_make_cmd <- return (cd_cmd ^ " ; " ^ make_cmd);
     print (";;; Make command: " ^ full_make_cmd ^ "\n");
     return (run_cmd full_make_cmd)
     }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  makeJava : ValueInfo -> RelativeUID -> String -> Env ()
  def makeJava (spec_info as (Spec spc,_,_)) rel_uid version =
    {
     (Spec option_spec, _, _) <- mkOptionsSpec (version ^ ".java");
     uid <- case rel_uid of
	      | UnitId_Relative   (uid as {path,hashSuffix}) -> 
               { 
		 current_uid <- getCurrentUID;
		 prefix   <- removeLastElem current_uid.path;
		 mainName <- lastElem       uid.path;
		 path     <- return (prefix ++ [version, "java", mainName]);
		 return (uid << {path = path})
		}
	      | SpecPath_Relative uid -> 
		return uid;
     javaFileName <- UIDtoJavaFile (uid, None);
     (optBaseUnitId,baseSpec) <- getBase;
     spc0 <- return (subtractSpec spc baseSpec);

     %% Generate Java files
     return (specToJava(baseSpec, spc0, Some option_spec, javaFileName));

     %% Compile java files to class files, 
     compile_cmd  <- return ("javac -sourcepath `pwd` " ^ version ^ "/java/Primitive.java");
     print (";;; Compiling java files: " ^ compile_cmd ^ "\n");
     return (run_cmd compile_cmd);


     %% Create script to invoke java interpreter on given class files
     script      <- return ("#!/bin/sh\n\ncd `/usr/bin/dirname $0`\n\njava -cp ../.. " ^ version ^ "/java/Primitive $*");
     script_file <- return (version ^ "/java/" ^ (last uid.path));
     print (";;; Writing script to invoke java program: " ^ script_file ^ "\n");
     return (writeStringToFile (script, script_file));
     return (run_cmd ("chmod a+x " ^ script_file))
    }

  op  mkOptionsSpec : String -> Env ValueInfo
  def mkOptionsSpec s =
    let mtv         : Sort = freshMetaTyVar ("gen", noPos)           in
    let list_type   : Sort = Base (mkQualifiedId ("List",    "List"),   [mtv], noPos) in
    let string_type : Sort = Base (mkQualifiedId ("String" , "String"), [],    noPos) in
    let public_element : SpecElem Position = (Op ([mkUnQualifiedId "public"], 
						  Unspecified, 
						  ApplyN ([Fun (Embed ("Cons", true),
								Arrow (Product ([("1", mtv), 
										 ("2", list_type)],
										noPos),
								       list_type,
								       noPos),
								noPos),
							   Record ([("1", Fun (String "main",        string_type, noPos)),
								    ("2", Fun (Embed ("Nil", false), list_type,   noPos))],
								   noPos)],
							  noPos)),
					      noPos)
    in
    let package_element : SpecElem Position = (Op ([mkUnQualifiedId "package"], 
			      Unspecified, 
			      Fun (String s, string_type, noPos)),
					       noPos)
    in
      SpecCalc.evaluateSpec [public_element, package_element] noPos 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec