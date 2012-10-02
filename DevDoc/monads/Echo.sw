Echo qualifying spec
  import /Library/Structures/Data/Monad/IO
  import /Library/Structures/Data/Monad/Control
  import /Library/Structures/Data/Monad/State

  op echo : Monad ()
  def echo = {
    fileName <- readLine stdin;
    strm <- openFile fileName Read;
    v <- newVar 1;
    While (Not (atEOF? strm)) {
      line <- readString strm;
      n <- readVar v; 
      writeString stdout ((toString n) ++ " " ++ line);
      writeVar (v, n + 1)
    };
    closeFile strm
  }
endspec
