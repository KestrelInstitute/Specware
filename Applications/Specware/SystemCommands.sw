SpecwareShell qualifying spec

import CommandParser


op showCurrentDirectory (ctxt : CommandContext) 
 : Result CommandContext

op connectToDirectory (dir  : DirectoryName, 
                       ctxt : CommandContext)  
 : Result CommandContext

op listFilesInDirectory (dir        : DirectoryName, 
                         recursive? : Bool, 
                         ctxt       : CommandContext) 
 : Result CommandContext


end-spec
