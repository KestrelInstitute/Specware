(* $Id$ *)

(*
2007:07:05
AC
A spec of APDUs, a concept used in smart cards.

2007:08:08
AC
Added extended-length APDUs.

*)


APDU qualifying spec

  import BitSequences

  (* This spec formalizes command and response APDUs as specified in ISO
  7618-4. For now we do not cover notions such as the structure of the CLA byte,
  but we may add that in the future. *)

  (* Conceptually, a command APDU is defined by the four header bytes CLA, INS,
  P1, and P2 (upon which we do not impose any constraints for now), the command
  data (a sequence of bytes), the maximum length Le of the expected response
  data, and an indication of whether the command uses short or extended length
  fields. The length Lc of the command data is not included because it is
  redundant (it equals the length of the data); see representation into bytes
  below. If the command uses short length fields, the data cannot exceed 255
  bytes and Le cannot exceed 256; if the command uses extended length fields,
  the data cannot exceed 65535 bytes and Le cannot exceed 65536. *)

  type Command0 =
   {cla  : Byte,
    ins  : Byte,
    p1   : Byte,
    p2   : Byte,
    data : FSeq Byte,
    le   : Nat,
    ext  : Boolean}

  op extendedCommand? : Command0 -> Boolean = project ext
  op    shortCommand? : Command0 -> Boolean = ~~ extendedCommand?

  op shortLengthRestrictions? (cmd:Command0) : Boolean =
    shortCommand? cmd => length cmd.data <= 255 && cmd.le <= 256

  op extendedLengthRestrictions? (cmd:Command0) : Boolean =
    extendedCommand? cmd => length cmd.data <= 65535 && cmd.le <= 65536

  % if there are no length fields in the command, we consider it to be short
  % (this condition is actually necessary to define op unflattenCommand below):
  op shortIfNoLengthFields? (cmd:Command0) : Boolean =
    length cmd.data = 0 && cmd.le = 0 => shortCommand? cmd

  type Command = (Command0 | shortLengthRestrictions?
                          /\ extendedLengthRestrictions?
                          /\ shortIfNoLengthFields?)

  type    ShortCommand = (Command |    shortCommand?)
  type ExtendedCommand = (Command | extendedCommand?)

  % the four cases for commands (actually defined in ISO 7816-3):

  op case1? (cmd:Command) : Boolean = (length cmd.data  = 0 && cmd.le  = 0)

  op case2? (cmd:Command) : Boolean = (length cmd.data  = 0 && cmd.le ~= 0)

  op case3? (cmd:Command) : Boolean = (length cmd.data ~= 0 && cmd.le  = 0)

  op case4? (cmd:Command) : Boolean = (length cmd.data ~= 0 && cmd.le ~= 0)

  conjecture command_cases_are_exhaustive is
    fa(cmd:Command) case1? cmd || case2? cmd || case3? cmd || case4? cmd

  (* A command APDU as conceptually captured by type Command above is
  represented as a sequence of bytes. *)

  % representation of Lc field:
  op lcBytes (cmd: Command | (case3? \/ case4?) cmd) : FSeq Byte =
             % subtype restriction ensures length cmd.data ~= 0
    if shortCommand? cmd then
      % single byte containing length, 1 to 255:
      single (toByte (length cmd.data))
    else (* extendedCommand? cmd *)
      % 0 byte followed by two bytes containing length, 1 to 65535:
      (toByte 0) |> bitsToBytes (toWord16 (length cmd.data))

  % representation of Le field:
  op leBytes (cmd: Command | (case2? \/ case4?) cmd) : FSeq Byte =
             % subtype restriction ensures cmd.le ~= 0
    if shortCommand? cmd then
      % single byte containing 0 to represent 256, else unchanged:
      single (toByte (cmd.le rem 256))
    else (* extendedCommand? cmd *)
      % 0 byte if Lc absent, nothing if Lc present:
      (if case2? cmd then single (toByte 0) else empty)
      % followed by two bytes containing 0 to represent 65536, else unchanged:
      ++ bitsToBytes (toWord16 (cmd.le rem 65536))

  % flatten/encode/represent command into byte sequence:
  op flattenCommand (cmd:Command) : FSeq Byte =
    % header always consists of the four CLA, INS, P1, and P2 bytes:
    let header: (FSeq Byte | ofLength? 4) =
        single cmd.cla <| cmd.ins <| cmd.p1 <| cmd.p2 in
    % body depends on the case of the command:
    let body: FSeq Byte =
        if case1? cmd then
          empty
        else if case2? cmd then
          leBytes cmd
        else if case3? cmd then
          lcBytes cmd ++ cmd.data
        else (* case4? cmd *)
          lcBytes cmd ++ cmd.data ++ leBytes cmd in
    % header followed by body:
    header ++ body

  % command decoding:

  op flattenedCommand? (bytes: FSeq Byte) : Boolean =
    ex(cmd:Command) flattenCommand cmd = bytes

  op unflattenCommand (bytes: FSeq Byte | flattenedCommand? bytes) : Command =
    the(cmd) flattenCommand cmd = bytes

  (* Conceptually, a reponse APDU is defined by the response data (a sequence of
  bytes) and the 16-bit status word SW. A reponse to a short (length) command
  can contain at most 256 data bytes; a response to an extended (length) command
  can contain at most 65536 data bytes. Since the response itself contains no
  information about the command, we simply require the response data to not
  exceed 65535 bytes. *)

  type Response =
    {data : {x : FSeq Byte | length x <= 65536},
     sw   : Word16}

  (* We consider a response "short" if it contains no more than 256 data bytes,
  otherwise we consider it "extended". However, note that a short response (as
  defined below) may correspond to an extended length command (if the response
  data happens to not exceed 256 bytes). Again, the response itself contains no
  information about the command. *)

  op    shortResponse? (rsp:Response) : Boolean = (length rsp.data <= 256)
  op extendedResponse? :    Response -> Boolean = ~~ shortResponse?

  type    ShortResponse = (Response |    shortResponse?)
  type ExtendedResponse = (Response | extendedResponse?)

  (* A response APDU as conceptually captured by type Response above is
  represented as a sequence of bytes. *)

  % first byte of SW:
  op sw1 (rsp:Response) : Byte = (word16ToBytes rsp.sw).1

  % second byte of SW:
  op sw2 (rsp:Response) : Byte = (word16ToBytes rsp.sw).2

  % flatten/encode/represent response into byte sequence:
  op flattenResponse (rsp:Response) : FSeq Byte =
    rsp.data <| sw1 rsp <| sw2 rsp

  % response decoding:

  op flattenedResponse? (bytes: FSeq Byte) : Boolean =
    ex(rsp:Response) flattenResponse rsp = bytes

  op unflattenResponse
     (bytes: FSeq Byte | flattenedResponse? bytes) : Response =
    the(rsp) flattenResponse rsp = bytes

endspec
