(*
2007:07:05
AC
A spec for triple DES (basic computation; triple DES modes are specified
elsewhere).

*)


TDES qualifying spec

  (* This spec formally specifies the basics of triple DES (3DES), as
  described in NIST's FIPS PUB 46-3 as well as in a variety of textbooks and
  online resources. By "basics" we mean the encryption and decryption process
  for a single block. 3DES modes of operations like ECB and CBC are specified
  elsewhere. *)

  import DESCryptographyBasics

  (* A 3DES key consists of 3 (single) DES keys. We extend the parity check
  predicate from DES keys to 3DES keys. *)

  type Key = {key1 : DES.Key,
              key2 : DES.Key,
              key3 : DES.Key}

  op parityOK? (k:Key) : Boolean =
    parityOK? k.key1 && parityOK? k.key2 && parityOK? k.key3

  (* There are two commonly used 3DES variants: 3-key 3DES and 2-key 3DES. In
  the former, the 3 DES keys are independent from each other. In the latter,
  the first and the third key are equal, so that one is effectively using 2
  DES keys. We define a subtype for 2-key 3DES keys (while type Key above is
  for the general 3-key 3DES case). *)

  type Key2 = {k : Key | k.key1 = k.key1}

  (* If all 3 keys are equal, we are basically using a DES key. We define a
  subtype for 1-key 3DES. This kind of key supports backwards compatibility
  with single DES (see below). *)

  type Key1 = {k : Key | k.key1 = k.key2 && k.key2 = k.key3}

  (* 3DES encryption of a block consists of first encrypting the block using
  the first key, then decrypting the resulting block using the second key, and
  finally encrypting the resulting block using the third key. 3DES block
  decryption is the inverse: decrypt with the third key, encrypt with the
  second key, and decrypt with the first key. See Appendix 2 of FIPS PUB
  46-3. The DES qualifier is unnecessary (it can be inferred) but we use it
  for enhanced clarity. *)

  op encryptBlock (key:Key) : Block -> Block = (DES.encryptBlock key.key3)
                                             o (DES.decryptBlock key.key2)
                                             o (DES.encryptBlock key.key1)

  op decryptBlock (key:Key) : Block -> Block = (DES.decryptBlock key.key1)
                                             o (DES.encryptBlock key.key2)
                                             o (DES.decryptBlock key.key3)

  conjecture encrypt_and_decrypt_are_inverses is
    fa(key:Key) (decryptBlock key) o (encryptBlock key) = id
             && (encryptBlock key) o (decryptBlock key) = id

  (* The EDE/DED scheme (i.e. encrypt-decrypt-encrypt/decrypt-encrypt-decrypt)
  is the most commonly used in 3DES, and is in fact described in FIPS PUB
  46-3. Another possible scheme is EEE/DDD, but it is not used very much. *)

  (* As mentioned earlier, when the 3 DES keys are all equal, 3DES is
  equivalent to DES. This is true because of the EDE/DED scheme: in EDE, the
  first E is undone by the D, so the second E is like single DES encryption;
  the same is true for DED. This backward compatibility of 3DES with DES is
  stated as follows. *)

  conjecture triple_DES_is_backward_compatible_with_DES is
    fa(key:Key1) encryptBlock key = DES.encryptBlock key.key1
                                                      % .key2 same
                                                      % .key3 same
              && decryptBlock key = DES.decryptBlock key.key1
                                                      % .key2 same
                                                      % .key3 same

endspec
