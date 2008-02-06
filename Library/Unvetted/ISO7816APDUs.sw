(*
2007:07:05
AC
A spec of ISO7816 APDUs, a concept used in smart cards.

2007:08:08
AC
Added extended-length APDUs.

2007:09:21
AC
Renamed spec and qualifier with reference to the context (ISO7816, smart cards)
of APDUs.

2008:02:05
AC
Added constraints to CLA, INS, and SW. Added notions of interindustry,
proprietary, and reserved commands. Added notion of logical channels.

*)


ISO7816APDU qualifying spec

  import BitSequences

  (* This spec formalizes command and response APDUs as specified in ISO 7618
  Part 3 (3rd Edition) and ISO 7816 Part 4 (2nd Edition). In the comments in
  this spec, we refer to those standard as "[ISO3]" and [ISO4], possibly
  extended with references to (sub)sections (e.g. "[ISO4 5.1]"). *)

  % the CLA byte can have any value except 'FF' [ISO 5.1.1]:

  op claByte? (x:Byte) : Boolean =
    x ~= toByte 0xff

  type CLAByte = (Byte | claByte?)

  % the INS byte can have any value except '6X' and '9X' [ISO 5.1.2]:

  op insByte? (x:Byte) :Boolean =
    let (hi,lo) = byteToNibbles x in
    hi ~= toNibble 6 && hi ~= toNibble 9

  type INSByte = (Byte | insByte?)

  (* Conceptually, a command APDU [ISO4 5.1] is defined by the four header bytes
  CLA, INS, P1, and P2 (there are no constraints on P1 and P2), the command data
  (a sequence of bytes), the maximum length Le of the expected response data,
  and an indication of whether the command uses short or extended length
  fields. The length Lc of the command data is not included because it is
  redundant (it equals the length of the data); see representation into bytes
  below. If the command uses short length fields, the data cannot exceed 255
  bytes and Le cannot exceed 256; if the command uses extended length fields,
  the data cannot exceed 65535 bytes and Le cannot exceed 65536. *)

  type Command0 =
   {cla  : CLAByte,
    ins  : INSByte,
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

  % the four command cases [ISO3 12.1.2]:

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

  % the SW can only have a value of the form '6xxx' and '9xxx', except '60xx'
  % [ISO4 5.1.3]:

  op statusWord? (sw:Word16) : Boolean =
    let (hiByte, _) = word16ToBytes sw in
    let (hiNibble, _) = byteToNibbles hiByte in
    (hiNibble = toNibble 0x6 || hiNibble = toNibble 0x9) &&
    hiByte ~= toByte 0x60

  type StatusWord = (Word16 | statusWord?)

  (* Conceptually, a reponse APDU [ISO4 5.1] is defined by the response data (a
  sequence of bytes) and the 16-bit status word SW. A reponse to a short
  (length) command can contain at most 256 data bytes; a response to an extended
  (length) command can contain at most 65536 data bytes. Since the response
  itself contains no information about the command, we simply require the
  response data to not exceed 65535 bytes. *)

  type Response =
    {data : {x : FSeq Byte | length x <= 65536},
     sw   : StatusWord}

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

  % the first bit of the CLA byte distinguishes interindustry and proprietary
  % commands [ISO4 5.1.1]:

  op interindustry? (cmd:Command) : Boolean =
    first cmd.cla = 0

  op proprietary? (cmd:Command) : Boolean =
    first cmd.cla = 1

  % the interindustry CLA byte 001xxxxx is reserved for future use by ISO
  % [ISO 5.1.1]:

  op reserved? (cmd:Command) : Boolean =
    ex (xxxxx: (FSeq Bit | ofLength? 5)) cmd.cla = 0 |> 0 |> 1 |> xxxxx

  theorem reserved_is_interindustry is
    fa(cmd:Command) reserved? cmd => interindustry? cmd

  % the following are the non-reserved interindustry commands [ISO4 5.1.1],
  % which we simply call "ISO commands":

  type ISOCommand = (Command | interindustry? /\ ~~ reserved?)

  op firstInterindustry? (cmd:ISOCommand) : Boolean =
    ex (xxxxx: (FSeq Bit | ofLength? 5)) cmd.cla = 0 |> 0 |> 0 |> xxxxx

  op furtherInterindustry? (cmd:ISOCommand) : Boolean =
    ex (xxxxxx: (FSeq Bit | ofLength? 6)) cmd.cla = 0 |> 1 |> xxxxxx

  theorem first_and_further_interindustry_are_disjoint is
    fa(cmd:ISOCommand) ~ (firstInterindustry? cmd && furtherInterindustry? cmd)

  theorem first_and_further_interindustry_are_exhaustive is
    fa(cmd:ISOCommand) firstInterindustry? cmd || furtherInterindustry? cmd

  % ISO commands contain logical channel information [ISO4 5.1.1.2]:

  type LogicalChannel = {ch:Nat | ch <= 19}

  op logicalChannel (cmd:ISOCommand) : LogicalChannel =
    if firstInterindustry? cmd then
      let chBits: (FSeq Bit | ofLength? 2) = suffix (cmd.cla, 2) in
      toNat chBits  (* 0 thru 3 *)
    else (* furtherInterindustry? cmd *)
      let chBits: (FSeq Bit | ofLength? 4) = suffix (cmd.cla, 4) in
      4 + toNat chBits  (* 4 thru 19 *)

endspec
