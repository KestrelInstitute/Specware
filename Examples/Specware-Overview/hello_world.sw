(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


HelloWorld = spec
  import /Library/Legacy/Utilities/System

  op hello () : () =
    writeLine "Hello World!"
end-spec
