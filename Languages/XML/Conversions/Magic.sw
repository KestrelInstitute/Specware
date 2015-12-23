(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Magic qualifying spec

  %% see /Languages/XML/Handwritten/Lisp/Magic.lisp for definitions of all of these

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% Product 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% MetaSlang => XML
  %% This creates a heterogenous list from the fields of a product
  %% Such a beast is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicElements      : [X,Y] Nat * X -> List Y           % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang 
  %% This creates a product from a heterogenous list.
  %% Such input is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicMakeProduct   : [X,Y] X -> Y                      % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% CoProduct 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% MetaSlang => XML
  %% This extracts the name of the constructor from the runtime datum
  %% The value (Y) is actually a reasonable metaslang construction,
  %% but we don't know it's type.

  op Magic.magicConstructorNameAndValue : [X,Y] X -> String * Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang 
  %% This creates a tagged coproduct from a constructor name (a string),
  %% and an arbitrary piece of data.
  %% The arguments and the result are all well formed in metaslang, 
  %% but the actual operation cannot be expressed in metaslang.

  op Magic.magicMakeConstructor : [X,Y] String * X -> Y           % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% Misc Casts
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% These are just identities that type cast their args, so that the result
  %% is pleasing to Specware for further processing.

  %% MetaSlang => XML
  op Magic.magicCastToBool     : [X]   X -> Bool       % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToInt      : [X]   X -> Int        % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToString   : [X]   X -> String     % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToChar     : [X]   X -> Char       % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToList     : [X,Y] X -> List   Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToOption   : [X,Y] X -> Option Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang
  op Magic.magicCastFromBool   : [X]   Bool     -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromInt    : [X]   Int      -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromString : [X]   String   -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromChar   : [X]   Char     -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromList   : [X,Y] List   Y -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromOption : [X,Y] Option Y -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

endspec
