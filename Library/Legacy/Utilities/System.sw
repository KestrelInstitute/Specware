(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

System qualifying spec 

  op caseSensitiveSubstrate?: Bool

  op error    : [a] String -> a   % cl error
  op fail     : [a] String -> a   % cl break

  %% The specwareDebug? flag is set using the lisp ":swdbg" top-level command.
  op debug    : [a] String -> a % calls lisp's break if the specwareDebug? flag is set.
  op proverUseBase?   : Bool % Tests whether the proverUseBase? flag is set.
  op specwareDebug?   : Bool % Tests whether the specwareDebug? flag is set.

  %% Renamed from toString to avoid ambiguity with monomorphic toStrings
  op anyToString : [a] a -> String
  op anyToPrettyString : [a] a -> String
  op print    : [a] a -> ()
  op toScreen (s:String) : ()
  op writeLine (s:String) : ()


  op warn     : [a] String -> a
  op note     : [a] String -> a  %like warn but less severe
  op time     : [a] a -> a
  op internalRunTime () : Nat
  op random: Nat -> Nat

  op System.userName ()           : String % calls cl::user-name
  op System.currentTimeAndDate () : String % formats call to DECODE-UNIVERSAL-TIME of GET-UNIVERSAL-TIME

(*
  The following retrieves a UNIX / Windows environment variable. Other
  operators listed in this file have corresponding implementations in
  handwritten/system-base.lisp.  So such definitions have the effect of
  extending / overwriting the Lisp System package. To access the
  Lisp SYSTEM:getenv we need only extend this signature.
*)
  op getEnv : String -> Option String

  op msWindowsSystem?: Bool

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
  op trueFilePath : List String * Bool -> List String

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

  op garbageCollect : Bool -> ()
  op hackMemory     : ()      -> ()

  op [a] withoutInterrupts(body: a): a
  op [a] allowWithInterrupts(body: a): a

  op [a] List.app (f: a -> ()) (l: List a) : () =
    case l of
       | []     -> ()
       | hd::tl -> (f hd; app f tl)

#translate Haskell -morphism
System.error -> error
System.fail -> error
System.warn -> error
System.print -> error
System.toScreen -> error
System.writeLine -> error
System.anyToString -> error
#end

endspec
