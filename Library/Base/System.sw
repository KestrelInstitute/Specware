\section{System}
The following is a hack. The problem is that certain functions for
data structures use fail. Until they are fixed, we need the following.

\begin{spec}
System qualifying spec {
  import PrimitiveSorts
  import List
  import Option

  op fail     : fa(a) String -> a
  op toString : fa(a) a -> String
  op print    : fa(a) a -> a

  op warn     : fa(a) String -> a
  op time     : fa(a) a -> a

(*
  The following retrieves a UNIX / Windows environment variable. Other
  operators listed in this file have corresponding implementations in
  handwritten/system-base.lisp. However, MetaSlang outer specs / modules
  correspond to Lisp packages so such definitions have the effect of
  extending / overwriting the Lisp System package. This is a bit crufty,
  but on the other hand somewhat fortunate. It means that to access the
  Lisp SYSTEM:getenv we need only extend this signature.
*)
%  op getenv   : String -> String
  op getEnv : String -> Option String

(*
 The following holds the name of the temporary directory on the
 current platform.  Under Unix, this is "/tmp". On Windows, there a number
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
  op withRestartHandler : fa (a) String * (() -> ()) * (() -> a) -> a

  op garbageCollect : Boolean -> ()
  op hackMemory     : ()      -> ()
}
\end{spec}
