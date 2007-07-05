(*
2007:07:05
AC
A spec of APDUs, a concept used in smart cards.

*)


APDU qualifying spec

  import BitSequences

  (* This spec provides a preliminary formalization of command and response
  APDUs as specified in ISO 7618-4. The formalization is preliminary because
  it does not cover extended-length APDUs and it does not cover notions such
  as the structure of the CLA byte. We will extend this formalization in the
  future, but for now it is sufficient. *)

  (* Conceptually, a command APDU is defined by the four header bytes CLA,
  INS, P1, and P2 (upon which we do not impose any constraints for now), the
  command data (a sequence of at most 255 bytes), and the length Le of the
  expected response data (at most 256). The Lc byte is not included because it
  is redundant (it equals the length of the data); see representation into
  bytes below. *)

  type Command =
   {cla  : Byte,
    ins  : Byte,
    p1   : Byte,
    p2   : Byte,
    data : {x : FSeq Byte | length x <= 255},
    le   : {x : Nat | x <= 256}}

  % the four cases for commands:

  op case1? (cmd:Command) : Boolean = (length cmd.data = 0 && cmd.le = 0)

  op case2? (cmd:Command) : Boolean = (length cmd.data = 0 && cmd.le ~= 0)

  op case3? (cmd:Command) : Boolean = (length cmd.data ~= 0 && cmd.le = 0)

  op case4? (cmd:Command) : Boolean = (length cmd.data ~= 0 && cmd.le ~= 0)

  conjecture command_cases_are_exhaustive is
    fa(cmd:Command) case1? cmd || case2? cmd || case3? cmd || case4? cmd

  (* A command APDU as conceptually captured by the record type above is
  represented as a sequence of at most 261 bytes (255 for data + 4 for header
  + 1 for Lc + 1 for Le). *)

  % byte representation of Lc:
  op lcByte (cmd: Command | (case3? \/ case4?) cmd) : Byte =
    % subtype restriction ensures length cmd.data ~= 0
    toByte (length cmd.data)

  % byte representation of Le:
  op leByte (cmd: Command | (case2? \/ case4?) cmd) : Byte =
    toByte (cmd.le rem 256)
    % i.e. 256 represented as 0, else unchanged;
    % subtype restriction ensures cmd.le ~= 0

  % flatten/encode/represent command into byte sequence:
  op flattenCommand (cmd:Command) : {x : FSeq Byte | length x <= 261} =
    % header always consists of the four CLA, INS, P1, and P2 bytes:
    let header : {x : FSeq Byte | length x = 4} =
        single cmd.cla <| cmd.ins <| cmd.p1 <| cmd.p2 in
    % body depends on the case of the command:
    let body : {x : FSeq Byte | length x <= 257} =
        if case1? cmd then
          empty
        else if case2? cmd then
          single (leByte cmd)
        else if case3? cmd then
          lcByte cmd |> cmd.data
        else (* case4? cmd *)
          lcByte cmd |> cmd.data <| leByte cmd in
    % header followed by body:
    header ++ body

  % command decoding:

  op flattenedCommand? (bytes: FSeq Byte) : Boolean =
    ex(cmd:Command) flattenCommand cmd = bytes

  op unflattenCommand (bytes: FSeq Byte | flattenedCommand? bytes) : Command =
    the(cmd) flattenCommand cmd = bytes

  (* Conceptually, a reponse APDU is defined by the response data (a sequence
  of at most 256 bytes) and the 16-bit status word SW. *)

  type Response =
    {data : {x : FSeq Byte | length x <= 256},
     sw   : Word16}

  (* A response APDU as conceptually captured by the record type above is
  represented as a sequence of at most 258 bytes (256 for data + 2 for SW). *)

  % first byte of SW:
  op sw1 (rsp:Response) : Byte = (word16ToBytes rsp.sw).1

  % second byte of SW:
  op sw2 (rsp:Response) : Byte = (word16ToBytes rsp.sw).2

  % flatten/encode/represent response into byte sequence:
  op flattenResponse (rsp:Response) : {x : FSeq Byte | length x <= 258} =
    rsp.data <| sw1 rsp <| sw2 rsp

  % response decoding:

  op flattenedResponse? (bytes: FSeq Byte) : Boolean =
    ex(rsp:Response) flattenResponse rsp = bytes

  op unflattenResponse (bytes : FSeq Byte | flattenedResponse? bytes) : Response =
    the(rsp) flattenResponse rsp = bytes

endspec
