JGen qualifying spec

import SpecCalc qualifying /Languages/MetaSlang/Specs/Position
import /Library/Legacy/Utilities/IO % for gotoFilePosition

sort Pos = Position.Position

sort JGenException = JGenError * Pos
sort JGenError =
       | NotSupported String
       | Fail String % generic error case
       | UnsupportedSubsortTerm String
       | UnsupportedQuotient String
       | UnsupportedSubsort String
       | UnsupportedPattern String
       | UnsupportTermInCase String
       | UnsupportedTermFormat String
       | UnsupportedSortInRestrict String
       | NoUserTypeInApplArgList String
       | UnsupportedLambdaTerm String

op errToString: JGenError -> String
def errToString err =
  case err of
    | UnsupportedLambdaTerm termstr -> "not yet supported: stand-alone lambda terms: '"^termstr^"'"
    | NoUserTypeInApplArgList termstr -> "no user type found in argument list of application "^termstr
    | UnsupportedSortInRestrict srtstr -> "unsupported sort in restrict term: "^srtstr
    | UnsupportTermInCase termstr -> "term format not supported for toplevel case term: '"^termstr^"'"
    | UnsupportedPattern patstr -> "pattern format not supported: '"^(patstr)^"'"
    | UnsupportedSubsort termstr -> "unsupported term for subsort: '"^termstr^"'; only operator names are supported."
    | UnsupportedQuotient termstr -> "unsupported term for quotient sort: '"^termstr^"'; only operator names are supported."
    | NotSupported s -> "Feature not supported: "^s
    | Fail msg -> msg
    | UnsupportedSubsortTerm srt -> "this format of subsorts/quotients is currently not supported: "^srt
    | UnsupportedTermFormat termstr -> "term format not supported: '"^termstr^"'"

% --------------------------------------------------------------------------------
% Error api
% --------------------------------------------------------------------------------

op JGenException.toString: JGenException -> String
def JGenException.toString(err,pos) =
  errorString(pos,errToString err)

op efail: fa(a) JGenException -> a
def efail(err,pos) =
  (gotoErrorLocation pos;
   fail(errorString(pos,"\n"^(errToString err))))

op gotoErrorLocation: Pos -> ()
def gotoErrorLocation pos =
  case pos of
     | File (file, (left_line, left_column, left_byte), right) ->   
       IO.gotoFilePosition (file, left_line, left_column)
     | _ -> ()

def errorString(pos,msg) =
  (msg^"\n found in "^(Position.print pos))

op issueError: Position * String -> ()
def issueError(pos,msg) =
  writeLine(errorString(pos,msg))

op warn: Position * String -> String
def warn(pos,msg) =
  "*** Warning: "^msg^" ["^(Position.print pos)^"]"

end-spec