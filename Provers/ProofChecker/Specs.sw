spec

  import Contexts

  % no top-level (type) variable declarations:
  op noVariables? : Context -> Boolean
  def noVariables? cx =
    ~(exists? (cx, embed? tVarDeclaration)) &&
    ~(exists? (cx, embed? varDeclaration))

  type Spec = (Context | noVariables?)

endspec
