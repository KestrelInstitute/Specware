System qualifying spec 
  import String
  import List
  import Option

  op fail     : [a] String -> a

  %% The specwareDebug? flag is set using the lisp ":swdbg" top-level command.
  op debug    : [a] String -> a % calls lisp's break if the specwareDebug? flag is set.
  op proverUseBase?   : Boolean % Tests whether the proverUseBase? flag is set.
  op specwareDebug?   : Boolean % Tests whether the specwareDebug? flag is set.

  %% Renamed from toString to avoid ambiguity with monomorphic toStrings
  op anyToString : [a] a -> String
  op print    : [a] a -> a

  op warn     : [a] String -> a
  op time     : [a] a -> a

(*
  The following retrieves a UNIX / Windows environment variable. Other
  operators listed in this file have corresponding implementations in
  handwritten/system-base.lisp.  So such definitions have the effect of
  extending / overwriting the Lisp System package. To access the
  Lisp SYSTEM:getenv we need only extend this signature.
*)
  op getEnv : String -> Option String

  op msWindowsSystem?: Boolean

(*
 The following holds the name of the temporary directory on the current
 platform.  Under Unix, this is "/tmp". On Windows, there are a number
 of possibilities.  In handwritten/system-base.lisp, this is bound to 
 SYSTEM:*temporary-directory*. See the the Allegro documentation for
 further details.
*)
  op temporaryDirectory : String

(*
 The following chase symbolic links to get to the true name.
 The second arg to trueFilePath is true for relative paths,
 false for absolute paths.
*)

  op trueFilename : String -> String
  op trueFilePath : List String * Boolean -> List String

(* 
 The following allows you wrap the main body you wish to execute [arg 3]
 within a restart handler.

 If no error occurs, it is as if the third arg (a function of no arguments)
 is called directly.

 If an error occurs, the string argument will appear in the ensuing
 dialog as the description for some option numbered <n>.  

 Then if the user enters :CONT <n>, the second arg (a function of no
 arguments executed purely for side effects) will be evaluated and 
 then control will return to the beginning of this call.
*)
  op withRestartHandler : [a] String * (() -> ()) * (() -> a) -> a

  op garbageCollect : Boolean -> ()
  op hackMemory     : ()      -> ()
endspec
