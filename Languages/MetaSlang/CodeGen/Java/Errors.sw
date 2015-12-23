(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying spec

import /Languages/MetaSlang/Specs/Position
import /Library/Legacy/Utilities/IO % for gotoFilePosition
import /Library/Legacy/Utilities/System

type Pos = Position.Position

type JGenException = JGenError * Pos
type JGenError =
       | NoError % special constructor signaling no error, to avoid use of Option(JGenError)
                 % note: for now, this is used only by checkraise, and checkraise is never called
       | NotSupported              String
       | Fail                      String % generic error case
       | UnsupportedSubtypeTerm    String
       | UnsupportedQuotient       String
       | UnsupportedSubtype        String
       | UnsupportedPattern        String
       | UnsupportTermInCase       String
       | UnsupportedTermFormat     String
       | UnsupportedTypeInRestrict String
       | NoUserTypeInApplArgList   String
       | UnsupportedLambdaTerm     String

op  errToString: JGenError -> String
def errToString err =
  case err of
    | UnsupportedLambdaTerm     termstr -> "not yet supported: stand-alone lambda terms: \""^termstr^"\""
    | NoUserTypeInApplArgList   termstr -> "no user type found in argument list of application "^termstr
    | UnsupportedTypeInRestrict srtstr  -> "unsupported type in restrict term: "^srtstr
    | UnsupportTermInCase       termstr -> "term format not supported for toplevel case term: \""^termstr^"\""
    | UnsupportedPattern        patstr  -> "pattern format not supported: \""^patstr^"\""
    | UnsupportedSubtype        termstr -> "unsupported term for subtype: \""^termstr^"\"; only operator names are supported."
    | UnsupportedQuotient       termstr -> "unsupported term for quotient type: \""^termstr^"\"; only operator names are supported."
    | NotSupported              s       -> "Feature not supported: "^s
    | Fail                      msg     -> msg
    | UnsupportedSubtypeTerm    srt     -> "this format of subtypes/quotients is currently not supported: "^srt
    | UnsupportedTermFormat     termstr -> "term format not supported: \""^termstr^"\""

% --------------------------------------------------------------------------------
% Error api
% --------------------------------------------------------------------------------

op  JGenException.toString: JGenException -> String
def JGenException.toString(err,pos) =
  errorString(pos,errToString err)

op  efail: [a] JGenException -> a
def efail(err,pos) =
  (gotoErrorLocation pos;
   fail(errorString(pos,"\n"^(errToString err))))

op  gotoErrorLocation: Pos -> ()
def gotoErrorLocation pos =
  case pos of
     | File (file, (left_line, left_column, left_byte), right) ->   
       IO.gotoFilePosition (file, left_line, left_column)
     | _ -> ()

def errorString(pos,msg) =
  (msg^"\n found in "^(Position.print pos))

op  issueError: Position * String -> ()
def issueError(pos,msg) =
  writeLine(errorString(pos,msg))

op  warn: Position * String -> String
def warn(pos,msg) =
  "*** Warning: "^msg^" ["^(Position.print pos)^"]"

endspec
