
Magic qualifying spec

  %% see /Languages/XML/Handwritten/Lisp/Magic.lisp for definitions of all of these

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% Product 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% MetaSlang => XML
  %% This creates a heterogenous list from the fields of a product
  %% Such a beast is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicElements      : fa (X,Y) Nat * X -> List Y           % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang 
  %% This creates a product from a heterogenous list.
  %% Such input is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicMakeProduct   : fa (X,Y) X -> Y                      % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% CoProduct 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% MetaSlang => XML
  %% This extracts the name of the constructor from the runtime datum
  %% The value (Y) is actually a reasonable metaslang construction,
  %% but we don't know it's type.

  op Magic.magicConstructorNameAndValue : fa (X,Y) X -> String * Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang 
  %% This creates a tagged coproduct from a constructor name (a string),
  %% and an arbitrary piece of data.
  %% The arguments and the result are all well formed in metaslang, 
  %% but the actual operation cannot be expressed in metaslang.

  op Magic.magicMakeConstructor : fa (X,Y) String * X -> Y           % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% Misc Casts
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% These are just identities that type cast their args, so that the result
  %% is pleasing to Specware for further processing.

  %% MetaSlang => XML
  op Magic.magicCastToBoolean    : fa (X)   X -> Boolean    % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToInteger    : fa (X)   X -> Integer    % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToString     : fa (X)   X -> String     % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToChar       : fa (X)   X -> Char       % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToList       : fa (X,Y) X -> List   Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToOption     : fa (X,Y) X -> Option Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang
  op Magic.magicCastFromBoolean  : fa (X)   Boolean  -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromInteger  : fa (X)   Integer  -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromString   : fa (X)   String   -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromChar     : fa (X)   Char     -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromList     : fa (X,Y) List   Y -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromOption   : fa (X,Y) Option Y -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

endspec