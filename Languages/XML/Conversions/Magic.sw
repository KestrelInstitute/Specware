
Magic qualifying spec

  %% see /Languages/XML/Handwritten/Lisp/Magic.lisp for definitions of all of these

  %% MetaSlang => XML
  %% This creates a heterogenous list from the fields of a product
  %% Such a beast is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicElements      : fa (X,Y) X -> List Y                 % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang 
  %% This creates a product from a heterogenous list.
  %% Such input is not even well formed for metaslang, so it must
  %% be handled carefully!

  op Magic.magicMakeProduct   : fa (X,Y) X -> Y                      % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% ??
  %% This extracts the name of the constructor from the runtime datum
  %% The value (Y) is actually a reasonable metaslang construction,
  %% but we don't know it's type.

  op Magic.magicConstructorNameAndValue : fa (X,Y) X -> String * Y   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% These are just identities that type cast their args, so that the result
  %% is pleasing to Specware for further processing.

  %% MetaSlang => XML
  op Magic.magicCastToString     : fa (X)   X -> String     % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToInteger    : fa (X)   X -> Integer    % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToList       : fa (X,Y) X -> List Y     % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToChar       : fa (X)   X -> Char       % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastToBoolean    : fa (X)   X -> Boolean    % see /Languages/XML/Handwritten/Lisp/Magic.lisp

  %% XML => MetaSlang
  op Magic.magicCastFromString   : fa (X)   String   -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromInteger  : fa (X)   Integer  -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromList     : fa (X,Y) List Y   -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromChar     : fa (X)   Char     -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp
  op Magic.magicCastFromBoolean  : fa (X)   Boolean  -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp

endspec