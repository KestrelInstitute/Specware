/*
 * MetaSlangGrammar.g
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.4  2003/01/31 15:34:08  gilham
 * Defined nonWordSymbol[String expected] parser rule to handle ":", "=", "*", etc.
 * used in the language syntax.
 *
 * Revision 1.3  2003/01/31 00:47:15  gilham
 * Fixed a bug in the lexer rule for block comments.
 *
 * Revision 1.2  2003/01/30 22:02:38  gilham
 * Improved parse error messages for non-word symbols such as ":".
 *
 * Revision 1.1  2003/01/30 02:02:18  gilham
 * Initial version.
 *
 *
 */

header {
package edu.kestrel.netbeans.parser;
}

//---------------------------------------------------------------------------
//============================   MetaSlangParserFromAntlr   =============================
//---------------------------------------------------------------------------

{
import java.util.*;

import org.netbeans.modules.java.ErrConsumer;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.parser.ElementFactory;
import edu.kestrel.netbeans.parser.ParserUtil;
}

class MetaSlangParserFromAntlr extends Parser;
options {
    k=3;
    buildAST=false;
//    defaultErrorHandler=false;
}

//---------------------------------------------------------------------------
starts
{
    Token firstToken = LT(1);
}
    : (  scToplevelTerm
       | scToplevelDecls
      )                     {Token lastToken = LT(0);
                             if (lastToken != null && lastToken.getText() != null) {
                                 ParserUtil.setBodyBounds(builder, (ElementFactory.Item)builder, firstToken, lastToken);
                             }}
    ;

private scToplevelTerm 
{
    ElementFactory.Item ignore;
}
    : ignore=scTerm[null]
    ;

private scToplevelDecls
    : scDecl (scDecl)*
    ;

private scDecl
{
    String ignore;
    ElementFactory.Item ignore2;
    Token unitIdToken = null;
}
    : ignore=name           {unitIdToken = LT(0);}
      equals
      ignore2=scTerm[unitIdToken]
    ;

private scTerm[Token unitIdToken] returns[ElementFactory.Item item]
{
    Object[] objEnd = null;
    item = null;
    Object beginEnd = null;
}
    : (  item=specDefinition[unitIdToken]
//       | item=scQualify[unitIdToken]
//       | item=scURI
      )                     {if (item != null) builder.setParent(item, null);}
    ;

//---------------------------------------------------------------------------
private specDefinition[Token unitIdToken] returns[ElementFactory.Item spec]
{
    spec = null;
    ElementFactory.Item childItem = null;
    Token headerEnd = null;
    List children = new LinkedList();
    String name = (unitIdToken == null) ? "" : unitIdToken.getText();
}
    : begin:"spec"          {headerEnd = begin;}
      (childItem=declaration
                            {if (childItem != null) children.add(childItem);}
      )*
      end:"endspec"
                            {spec = builder.createSpec(name);
                             if (unitIdToken != null) {
                                 begin = unitIdToken;
                             }
                             builder.setParent(children, spec);
                             ParserUtil.setAllBounds(builder, spec, begin, headerEnd, end);
                             }
    ;

private qualifier returns[String qlf]
{
    qlf = null;
}
    : qlf=name
    ;

//!!! TO BE EXTENDED !!!
private name returns[String name]
{
    name = null;
}
    : name=idName
    ;

private declaration returns[ElementFactory.Item item]
{
    item = null;
}
    : importDeclaration
    | item=sortDeclaration
    | item=opDeclaration
//    | item=definition
    ;

//---------------------------------------------------------------------------
private importDeclaration
{
    ElementFactory.Item ignore;
}
    : "import" ignore=scTerm[null]
    ;

//---------------------------------------------------------------------------
private sortDeclaration returns[ElementFactory.Item sort]
{
    sort = null;
    String[] params = null;
    String name = null;
}
    : begin:"sort" 
      name=qualifiableNames
      (params=formalSortParameters
      )?
                            {sort = builder.createSort(name, params);
                             ParserUtil.setBounds(builder, sort, begin, LT(0));
                            }
    ;

private qualifiableNames returns[String name]
{
    name = null;
    String member = null;
    String qlf = null;
}
    : name=qualifiableName
    | LBRACE 
      member=qualifiableName
                            {name = "{" + member;}
      (COMMA member=qualifiableName
                            {name = name + ", " + member;}
      )*
      RBRACE                {name = name + "}";}
      
                            
    ;

private qualifiableName returns[String name]
{
    name = null;
    String qlf = null;
}
    : (qlf=qualifier DOT)?
      name=idName
                            {if (qlf != null) name = qlf + "." + name;}
    ;

private idName returns[String name]
{
    name = null;
}
    : id:IDENTIFIER         {name = id.getText();}
    ;

private formalSortParameters returns[String[] params]
{
    params = null;
    String param = null;
    List paramList = null;
}
    : param=idName
                            {params = new String[]{param};}
    | LPAREN                {paramList = new LinkedList();}
      param=idName
                            {paramList.add(param);}
      (COMMA 
       param=idName
                            {paramList.add(param);}
      )* 
      RPAREN                {params = (String[]) paramList.toArray(new String[]{});}
    ;

//---------------------------------------------------------------------------
//!!! TODO: fixity !!!
private opDeclaration returns[ElementFactory.Item op]
{
    op = null;
    String name = null;
    String sort = null;
}
    : begin:"op" 
      name=qualifiableNames
      nonWordSymbol[":"] 
      sort=sort
                            {op = builder.createOp(name, sort);
                             ParserUtil.setBounds(builder, op, begin, LT(0));
                            }
    ;

private sort returns[String sort]
{
    String text = null;
    sort = "";
}
    : (text=qualifiableRef
                            {sort = sort + text;}
       | text=literal
                            {sort = sort + text;}
       | text=specialSymbol
                            {sort = sort + text;}
       | text=expressionKeyword
                            {sort = sort + text;}
      )+
    ;

private specialSymbol returns[String text]
{
    text = null;
}
    : UBAR                  {text = "_";}
    | LPAREN                {text = "(";}
    | RPAREN                {text = "}";}
    | LBRACKET              {text = "[";}
    | RBRACKET              {text = "]";}
    | LBRACE                {text = "{";}
    | RBRACE                {text = "}";}
    | COMMA                 {text = ", ";}
//    | SEMICOLON             {text = ";";}
//    | DOT                   {text = ".";}
    ;

private literal returns[String text]
{
    text = null;
}
    : text=booleanLiteral
    | t1:NAT_LITERAL        {text = t1.getText();}
    | t2:CHAR_LITERAL       {text = t2.getText();}
    | t3:STRING_LITERAL     {text = t3.getText();}
    ;

private booleanLiteral returns[String text]
{
    text = null;
}
    : t1:"true"             {text = "true ";}
    | t2:"false"            {text = "false ";}
    ;

private expressionKeyword returns[String text]
{
    text = null;
}
    : "as"                  {text = "as ";}
    | "case"                {text = "case ";}
    | "choose"              {text = "choose ";}
    | "else"                {text = "else ";}
    | "embed"               {text = "embed ";}
    | "embed?"              {text = "embed? ";}
    | "ex"                  {text = "ex ";}
    | "fa"                  {text = "fa ";}
    | "fn"                  {text = "fn ";}
    | "if"                  {text = "if ";}
    | "in"                  {text = "in ";}
    | ("let"                {text = "let ";}
       ("def"               {text = "let def ";}
       )?)
    | "of"                  {text = "of ";}
    | "project"             {text = "project ";}
    | "quotient"            {text = "quotient ";}
    | "relax"               {text = "relax ";}
    | "restrict"            {text = "restrict ";}
    | "then"                {text = "then ";}
    | "where"               {text = "where ";}
    ; 

private qualifiableRef returns[String name]
{
    name = null;
}
    : name=qualifiableName
    ;

//---------------------------------------------------------------------------
private equals
    : nonWordSymbol["="]
    | "is"
    ;

//---------------------------------------------------------------------------
// Used to refer to any specific NON_WORD_SYMBOL in the Specware language syntax,
// e.g. ":", "=", "*", "/", "|", "->".  (If these are defined as tokens, the 
// lexer will be nonderterministic.)
private nonWordSymbol[String expected]
    : t:IDENTIFIER          {t.getText().equals(expected)}? 
    ;
    exception
    catch [RecognitionException ex] {
       int line = t.getLine();
       String msg = "expecting \"" + expected + "\", found \"" + t.getText() + "\"";
       throw new RecognitionException(msg, null, line);
    }

//---------------------------------------------------------------------------
//=============================   MetaSlangLexerFromAntlr   =============================
//---------------------------------------------------------------------------

class MetaSlangLexerFromAntlr extends Lexer;

options {
    k=4;
    testLiterals=false;
}

// a dummy rule to force vocabulary to be all characters (except special
// ones that ANTLR uses internally (0 to 2) 

protected
VOCAB
    : '\3'..'\377'
    ;

//-----------------------------
//====== WHITESPACE ===========
//-----------------------------

// Whitespace -- ignored
WHITESPACE
    : ( ' '
      | '\t'
      | '\f'
      // handle newlines
      | ( "\r\n"  // DOS
        | '\r'    // Macintosh
        | '\n'    // Unix
        )                   {newline();}
      )                     {_ttype = Token.SKIP;}
    ;


// Single-line comments -- ignored
LINE_COMMENT
    : '%'
      (~('\n'|'\r'))* ('\n'|'\r'('\n')?)
                            {newline();
			    _ttype = Token.SKIP;}
    ;


// multiple-line comments -- ignored
BLOCK_COMMENT
    : "(*"
      (// '\r' '\n' can be matched in one alternative or by matching
       // '\r' in one iteration and '\n' in another.  The language
       // that allows both "\r\n" and "\r" and "\n" to be valid
       // newlines is ambiguous.  Consequently, the resulting grammar
       // must be ambiguous.  This warning is shut off.
       options {generateAmbigWarnings=false;}
       : { LA(2)!=')' }? '*'
	 | '\r' '\n'		{newline();}
	 | '\r'			{newline();}
	 | '\n'			{newline();}
	 | ~('*'|'\n'|'\r')
      )*
      "*)"                  {_ttype = Token.SKIP;}
    ;

//-----------------------------
//==== SPECIFIC CHARACTERS  ===
//-----------------------------


UBAR
options {
  paraphrase = "'_'";
}
    :  "_"
    ;

LPAREN
options {
  paraphrase = "'('";
}
    : '('
    ;
RPAREN
options {
  paraphrase = "')'";
}
    : ')'
    ;
LBRACKET
options {
  paraphrase = "'['";
}
    : '['
    ;
RBRACKET
options {
  paraphrase = "']'";
}
    : ']'
    ;
LBRACE
options {
  paraphrase = "'{'";
}
    : '{'
    ;
RBRACE
options {
  paraphrase = "'}'";
}
    : '}'
    ;
COMMA
options {
  paraphrase = "','";
}
    : ','
    ;
SEMICOLON
options {
  paraphrase = "';'";
}
    : ';'
    ;
DOT
options {
  paraphrase = "'.'";
}
    : '.'
    ;
DOTDOT
options {
  paraphrase = "'..'";
}
    :  ".."
    ;

POUND
options {
  paraphrase = "'#'";
}
    :  "#"
    ;

//-----------------------------
//=== ALL LETTERS and DIGITS ==
//-----------------------------

protected
LETTER
    : ('A'..'Z')
    | ('a'..'z')
    ;

protected
DIGIT
    : ('0'..'9')
    ;

//-----------------------------
//=== Literals ================
//-----------------------------

NAT_LITERAL
options {
  paraphrase = "an integer";
}
    : '0'                   
    | ('1'..'9') ('0'..'9')*
    ;

// character literals
CHAR_LITERAL
options {
  paraphrase = "a character";
}
    : '#' ( ESC | ~'\'' ) 
    ;

// string literals
STRING_LITERAL
options {
  paraphrase = "a string";
}
    : '"' (ESC|~('"'|'\\'))* '"'
    ;

protected ESC
    : '\\'
      ( 'n'
      | 'r'
      | 't'
      | 'b'
      | 'f'
      | '"'
      | '\''
      | '\\'
      )
    ;

//-----------------------------
//====== IDENTIFIERS ==========
//-----------------------------

IDENTIFIER  options
{
    paraphrase = "an identifier";
    testLiterals = true;
}
    : WORD_SYMBOL | NON_WORD_SYMBOL 
    ;
    
//-----------------------------
//====== WORD SYMBOLS =========
//-----------------------------

protected WORD_SYMBOL
    : LETTER (LETTER | DIGIT | '_' | '?')*
    ;

//-----------------------------
//====== NON-WORD SYMBOLS =====
//-----------------------------

protected NON_WORD_SYMBOL
    : (NON_WORD_MARK)+
    ;

protected NON_WORD_MARK
    : '`' | '~' | '!' | '@' 
    | '$' | '^' | '&' | '-'
    | '+' | '<' | '>' | '?' 
    | '*' | '=' | ':' | '|' 
    | '\\' | '/' 
    ;


// java antlr.Tool MetaSlangGrammar.g > MetaSlangGrammar.log
