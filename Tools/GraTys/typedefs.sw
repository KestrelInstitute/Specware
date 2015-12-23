(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  type Seq a = List a
  type ProperSeq a = {x : Seq a | length x > 0}
  type Identifier = | Identifier String

  type Type =
     | BooleanType
     | IntegerType IntegerType
     | ArrayType {tipo : Type, arrayBounds : ArrayBounds}
     | TypeName TypeName
     | KeyType KeyType

  type TypeDescriptor =
     | Type Type
     | RecordTypeDescriptor ProperSeq Component
     | EnumerationTypeDescriptor ProperSeq EnumerationOption

  type IntegerType =
     | Int {min : Expression, max : Expression}
     | Unsigned Expression
     | Signed Expression
     | Bit
     | Byte
     | Word

  type ArrayBounds = {min? : Option Expression, max : Expression}

  type TypeName = Identifier

  type KeyType =
     | AESKey Expression
     | DESKey Expression
     | RSAPublicKey Expression
     | RSAPrivateKey Expression
     | RSAPrivateCrtKey Expression
     | DSAPublicKey Expression
     | DSAPrivateKey Expression
     | ECFPPublicKey Expression
     | ECFPPrivateKey Expression

  type Component = {tipo : Type, componentName : ComponentName}

  type ComponentName = Identifier

  type EnumerationOption = {optionName : OptionName, types : Seq Type}

  type OptionName = Identifier

  type Expression =
     | ConstantName ConstantName
     | VariableName VariableName
     | ArgumentName ArgumentName
     | Literal Literal
     | BytesToWordConversion {hiByte : Expression, loByte : Expression}
     | ArrayConstruction ArrayConstruction
     | ArraySelection ArraySelection
     | BitToByteArrayConversion Expression
     | IntegerToArrayConversion
           {conversionIdentifier : ConversionIdentifier,
           width? : Option Expression, expression : Expression}
     | ArrayReversal Expression
     | RecordConstruction {tipo : Type,
           expressions : ProperSeq Expression}
     | RecordSelection {expression : Expression,
           componentName : ComponentName}
     | TaggedValueConstruction {optionName : OptionName,
           expressions : Seq Expression}
     | RandomExpression Type
     | CryptoExpression CryptoExpression
     | DigestExpression {digestMethod : DigestMethod,
           expression : Expression}
     | ChecksumExpression {checksumMethod : ChecksumMethod,
           expression : Expression,
           initializationVector : InitializationVector}
     | Formula Formula
     | ConditionalExpression {condition : Expression,
           ifTrue : Expression, ifFalse : Expression}

  type ConstantName = Identifier

  type VariableName = Identifier

  type ArgumentName = Identifier

  type Literal =
     | BooleanLiteral BooleanLiteral
     | IntegerLiteral Nat

  type BooleanLiteral =
     | True
     | False

  type ArrayConstruction =
     | Display Seq Expression
     | Repeat {expression : Expression, nTimes : Expression}

  type ArraySelection =
     | Element {expression : Expression, arraySelector : ArraySelector}
     | LengthOf Expression

  type ArraySelector =
     | Single Expression
     | SubFromTo {fromm : Expression, to : Expression}
     | SubFromLength {fromm : Expression, length : Expression}

  type ConversionIdentifier =
     | Ubits
     | Sbits
     | Ubytes
     | Sbytes

  type CryptoExpression =
     | EncryptDecryptExpression {encryptDecrypt : EncryptDecrypt,
           key : Key, message : Message,
           encryptDecryptParameters? : Option EncryptDecryptParameters}
     | SignExpression SignArguments
     | VerifyExpression {signature : Expression,
           signArguments : SignArguments}

  type EncryptDecrypt =
     | Encrypt
     | Decrypt

  type Key = Expression

  type Message = Expression

  type EncryptDecryptParameters =
     | SymmetricEncryptDecryptParameters {mode : Mode,
           symmetricPaddingMethod? : Option SymmetricPaddingMethod}
     | AsymmetricEncryptDecryptParameters AsymmetricPaddingMethod

  type Mode =
     | ECB
     | CBC Option InitializationVector

  type InitializationVector = Expression

  type SymmetricPaddingMethod =
     | ISO9797M1
     | ISO9797M2
     | PKCS5
     | ISO97971M2ALG3

  type AsymmetricPaddingMethod =
     | ISO14888
     | ISO9796
     | PKCS1
     | PKCS1OAEP
     | PKCS1PSS
     | RFC2409

  type SignArguments = {key : Key, message : Message,
           signParameters? : Option SignParameters}

  type SignParameters =
     | AESSignParameters InitializationVector
     | DESSignParameters {mac : Mac,
           initializationVector? : Option InitializationVector,
           symmetricPaddingMethod? : Option SymmetricPaddingMethod}
     | RSASignParameters {digestMethod : DigestMethod,
           asymmetricPaddingMethod : AsymmetricPaddingMethod}

  type Mac =
     | MAC4
     | MAC8

  type DigestMethod =
     | SHA
     | MD5
     | RIPEMD160

  type ChecksumMethod =
     | ISO3309CRC16
     | ISO3309CRC32

  type Formula =
     | PrefixFormula {prefixOp : PrefixOp, operand : Operand}
     | InfixFormula {operand1 : Operand, infixOp : InfixOp,
           operand2 : Operand}

  type Operator =
     | PrefixOp PrefixOp
     | InfixOp InfixOp

  type PrefixOp =
     | Minus
     | Not

  type InfixOp =
     | Plus
     | Minus
     | Times
     | DividedBy
     | Modulo
     | ToThepower
     | Equals
     | Unequal
     | LessThan
     | AtMost
     | GreaterThan
     | AtLeast
     | And
     | InclusiveOr
     | ExclusiveOr
     | Implies
     | Concatenate

  type Operand = Expression

  type Block = Seq Statement

  type Statement =
     | LocalVariableDeclaration {tipo : Type,
           variableName : VariableName,
           initializer? : Option Initializer}
     | Assignment {leftHandSide : LeftHandSide, expression : Expression}
     | ResponseStatement ResponseStatement
     | IfStatement IfStatement
     | SwitchStatement {expression : Expression,
           caseSequence : CaseSequence}
     | WhileStatement {expression : Expression, block : Block}
     | KeyGeneration {leftHandSide1 : LeftHandSide,
           leftHandSide2 : LeftHandSide, expressions : Seq Expression}

  type Initializer = Expression

  type LeftHandSide =
     | ConstantName ConstantName
     | VariableName VariableName
     | LHSArraySelection {leftHandSide : LeftHandSide,
           arraySelector : ArraySelector}
     | LHSRecordSelection {leftHandSide : LeftHandSide,
           componentName : ComponentName}

  type ResponseStatement =
     | Respond Response
     | Respondok Option Expression

  type Response =
     | OneExpr Expression
     | TwoExpr {expression1 : Expression, expression2 : Expression}
     | ThreeExpr {expression1 : Expression, expression2 : Expression,
           expression3 : Expression}

  type IfStatement = {expression : Expression, block : Block,
           elsePart? : Option ElsePart}

  type ElsePart =
     | Block Block
     | IfStatement IfStatement

  type CaseSequence = {cases : Seq Case, defaultCase? : Option Block}

  type Case = {pattern : Pattern, block : Block}

  type Pattern = {optionName : OptionName,
           argumentNames : Seq ArgumentName}

  type Specification = Seq Declaration

  type Declaration =
     | ConstantDeclaration ConstantDeclaration
     | TypeDeclaration {typeName : TypeName,
           typeDescriptor : TypeDescriptor}
     | StateSpaceDeclaration Seq StateVariableDeclaration
     | StateInvariantDeclaration Expression
     | InitDeclaration {formalArgumentList : FormalArgumentList,
           block : Block, byteRepresentation : Expression}
     | SelectDeclaration Block
     | DeselectDeclaration Block
     | CommandDeclaration {security? : Option Security,
           formalCommand : FormalCommand, block : Block,
           aPDURepresentation : ProperSeq Expression}

  type ConstantDeclaration =
     | Initialized {type? : Option Type, constantName : ConstantName,
           initializer : Initializer}
     | Uninitialized {tipo : Type, constantName : ConstantName}

  type StateVariableDeclaration = {tipo : Type,
           variableName : VariableName,
           initializer? : Option Initializer}

  type Security = Seq SecurityOption

  type SecurityOption =
     | Cmac
     | Rmac
     | Cdecrypt
     | Rencrypt
     | All

  type FormalCommand = {commandName : Identifier,
           formalArgumentList : FormalArgumentList}

  type FormalArgumentList = Seq {tipo : Type,
           argumentName : ArgumentName}

endspec
