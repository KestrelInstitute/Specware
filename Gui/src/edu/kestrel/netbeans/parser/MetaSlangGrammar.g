/*
 * MetaSlangGrammar.g
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.25  2003/03/29 03:14:00  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.24  2003/03/23 02:55:35  weilyn
 * Reverted "sort" and "expression" rules because actual SpecCalculus grammar was too ambiguous and low performance (due to extensive need for syntactic predicates).  Kept pattern rules.  Eliminated most other syntactic predicates for performance.  TODO: resolve lexical nondetermisim warnings.
 *
 * Revision 1.23  2003/03/21 02:48:45  weilyn
 * Attempting to add entire SpecCalculus grammar.  Added patterns,
 * expressions, and sorts.  Updated existing rules to use new
 * SpecCalculus rules.  Still needs a lot of work...
 *
 * Revision 1.22  2003/03/19 21:33:13  gilham
 * Fixed LATEX_COMMENT to handle  comment blocks not ended with
 * "\begin{spec}".
 *
 * Revision 1.21  2003/03/19 19:25:43  weilyn
 * Added patterns.
 * Made "\end{spec}" a starting latex comment token in lexer.
 *
 * Revision 1.20  2003/03/19 18:36:46  gilham
 * Fixed a bug in the Lexer that caused the token for "\end{spec}" not being skipped.
 *
 * Revision 1.19  2003/03/14 04:15:31  weilyn
 * Added support for proof terms
 *
 * Revision 1.18  2003/03/13 01:23:55  gilham
 * Handle Latex comments.
 * Report Lexer errors.
 * Always display parser messages (not displayed before if the parsing succeeded
 * and the parser output window is not open).
 *
 * Revision 1.17  2003/03/12 03:01:56  weilyn
 * no message
 *
 * Revision 1.16  2003/03/07 23:44:24  weilyn
 * Added most top level terms
 *
 * Revision 1.15  2003/02/20 23:17:41  weilyn
 * Fixed parsing of assertions and options in prove term
 *
 * Revision 1.14  2003/02/18 18:10:14  weilyn
 * Added support for imports.
 *
 * Revision 1.13  2003/02/17 07:04:09  weilyn
 * Made scURI return an Item, and added more rules for scProve.
 *
 * Revision 1.12  2003/02/17 04:35:26  weilyn
 * Added support for expressions.
 *
 * Revision 1.11  2003/02/16 02:16:03  weilyn
 * Added support for defs.
 *
 * Revision 1.10  2003/02/14 17:00:38  weilyn
 * Added prove term to grammar.
 *
 * Revision 1.9  2003/02/13 19:44:09  weilyn
 * Added code to create claim objects.
 *
 * Revision 1.8  2003/02/10 15:38:36  gilham
 * Allow non-word symbols only as op names, not as sort names or unit ids.
 *
 * Revision 1.7  2003/02/08 01:26:59  weilyn
 * Added rules to recognize claims and sort definitions
 *
 * Revision 1.6  2003/02/07 20:06:19  gilham
 * Added opDefinition and scURI to MetaSlangGrammar.
 *
 * Revision 1.5  2003/01/31 17:38:33  gilham
 * Removed token recording code.
 *
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
    : (  scToplevelDecls
       | scToplevelTerm
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
    item = null;    
}
    : ( item=scBasicTerm[unitIdToken]
      | item=scSubstitute[unitIdToken]
      )                     {if (item != null) builder.setParent(item, null);}
    ;

// These are the non-left-recursive terms
private scBasicTerm[Token unitIdToken] returns[ElementFactory.Item item]
{
    item = null;
}
    : item=scPrint[unitIdToken]
    | item=scURI[unitIdToken]
    | item=specDefinition[unitIdToken]
    | item=scLet[unitIdToken]
    | item=scTranslate[unitIdToken]
    | item=scQualify[unitIdToken]
    | item=scDiagram[unitIdToken]
    | item=scColimit[unitIdToken]
    | item=scMorphism[unitIdToken]
    | item=scGenerate[unitIdToken]
    | item=scObligations[unitIdToken]
    | item=scProve[unitIdToken]
    ;

//---------------------------------------------------------------------------

private scPrint[Token unitIdToken] returns[ElementFactory.Item print]
{
    print = null;
    ElementFactory.Item ignore = null;
}
    : "print"
      ignore=scTerm[null]
    ;

// TODO: scURI should really be an object that has parameters (bool relOrAbs, string path, scTermItem optionalRef)
private scURI[Token unitIdToken] returns[ElementFactory.Item uri]
{
    uri = null;
    String strURI = null;
}
    : strURI=fullURIPath
    ;

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

private scLet[Token unitIdToken] returns[ElementFactory.Item let]
{
    let = null;
    ElementFactory.Item ignore = null;
}
    : "let"
      (scDecl
      )*
      "in"
      ignore=scTerm[unitIdToken]
    ;

private scTranslate[Token unitIdToken] returns[ElementFactory.Item translate]
{
    translate = null;
    ElementFactory.Item ignore = null;
}
    : "translate"
      ignore=scTerm[null]
      "by"
      nameMap
    ;

private scQualify[Token unitIdToken] returns[ElementFactory.Item qualify]
{
    qualify = null;
    String name = null;
    ElementFactory.Item childItem = null;
    Token headerEnd = null;
    List children = new LinkedList();
}
    : name=qualifier                    //{headerEnd = LT(0);}
      "qualifying"
      childItem=scTerm[null]            /*{if (childItem != null) children.add(childItem);}
                                        {qualify = builder.createQualification(name);
                                         if (unitIdToken != null) {
                                             begin = unitIdToken;
                                         }
                                         builder.setParent(children, qualify);
                                         ParserUtil.setAllBounds(builder, qualify, begin, headerEnd, end);
                                        }*/
    ;

private scDiagram[Token unitIdToken] returns[ElementFactory.Item diagram]
{
    diagram = null;
    ElementFactory.Item childItem = null;
    Token headerEnd = null;
    List children = new LinkedList();
    String name= (unitIdToken == null) ? "" : unitIdToken.getText();
}
    : begin:"diagram"                   {headerEnd = begin;}
      LBRACE
      (scDiagElem                        //TODO:{if (childItem != null) children.add(childItem);}
       (COMMA scDiagElem                 //TODO:{if (childItem != null) children.add(childItem);}
       )*
      )?
      end:RBRACE                  
                                        {diagram = builder.createDiagram(name);
                                         if (unitIdToken != null) {
                                             begin = unitIdToken;
                                         }
                                         builder.setParent(children, diagram);
                                         ParserUtil.setAllBounds(builder, diagram, begin, headerEnd, end);
                                        }
    ;

private scColimit[Token unitIdToken] returns[ElementFactory.Item colimit]
{
    colimit = null;
    ElementFactory.Item ignore = null;
    Token headerEnd = null;
    ElementFactory.Item childItem = null;
    List children = new LinkedList();
    String name = (unitIdToken == null) ? "" : unitIdToken.getText();
}
    : begin:"colimit"                   {headerEnd = begin;}
      childItem=scTerm[null]            {if (childItem != null) children.add(childItem);}

                                        {colimit = builder.createColimit(name);
                                         if (unitIdToken != null) {
                                            begin = unitIdToken;
                                         }
                                         builder.setParent(children, colimit);
                                         ParserUtil.setAllBounds(builder, colimit, begin, headerEnd, LT(0));
                                        }
    ;

private scSubstitute[Token unitIdToken] returns[ElementFactory.Item substitute]
{
    substitute = null;
    ElementFactory.Item ignore = null;
}
    : ignore=scBasicTerm[null]
      scSubstituteTermList
    ;

private scMorphism[Token unitIdToken] returns[ElementFactory.Item morphism]
{
    morphism = null;
    ElementFactory.Item src = null;
    ElementFactory.Item dest = null;
    ElementFactory.Item ignore = null;
    Token headerEnd = null;
    List children = new LinkedList();
    String name = (unitIdToken == null) ? "" : unitIdToken.getText();
}

    : begin:"morphism"            {headerEnd = begin;}
      src=scTerm[null]            {if (src != null) children.add(src);}
      ARROW
      dest=scTerm[null]           {if (dest != null) children.add(dest);}
      LBRACE
      nameMap                     //TODO:make this an Item object
      end:RBRACE

                                  {morphism = builder.createMorphism(name);
                                   if (unitIdToken != null) {
                                       begin = unitIdToken;
                                   }
                                   builder.setParent(children, morphism);
                                   ParserUtil.setAllBounds(builder, morphism, begin, headerEnd, end);
                                  }
    ;

private scGenerate[Token unitIdToken] returns[ElementFactory.Item generate]
{
    generate = null;
    String genName = null;
    String fileName = null;
    ElementFactory.Item ignore = null;
    Token headerEnd = null;
}
    : begin:"generate"        {headerEnd = begin;}
      genName=name
      ignore=scTerm[null]
      ("in" STRING_LITERAL
      )?
    ;

private scObligations[Token unitIdToken] returns[ElementFactory.Item obligations]
{
    obligations=null;
    ElementFactory.Item ignore=null;
    Token headerEnd = null;
}
    : begin:"obligations"     {headerEnd = begin;}
      ignore=scTerm[null]
    ;

private scProve[Token unitIdToken] returns[ElementFactory.Item proof]
{
    proof = null;
    ElementFactory.Item childItem = null;
    String ignore = null;
    Token headerEnd = null;
    List children = new LinkedList();
    String name = (unitIdToken == null) ? "" : unitIdToken.getText();
}
    : begin:"prove"                     {headerEnd = begin;}
      childItem=claimName               {if (childItem != null) children.add(childItem);}
      "in"
      childItem=scTerm[null]            {if (childItem != null) children.add(childItem);}
      (childItem=proverAssertions)?     {if (childItem != null) children.add(childItem);}
      (childItem=proverOptions)?        {if (childItem != null) children.add(childItem);}
                                        {proof = builder.createProof(name);
                                         if (unitIdToken != null) {
                                            begin = unitIdToken;
                                         }
                                         builder.setParent(new LinkedList()/*children*/, proof);
                                         ParserUtil.setAllBounds(builder, proof, begin, headerEnd, LT(0));
                                         }
    ;

//---------------------------------------------------------------------------

private fullURIPath returns[String path]
{
    path = "";
    String item = null;
}
    : ( slash:SLASH item=partialURIPath        {path = slash.getText() + item;}
        | item=partialURIPath                  {path = item;}
      )
      (ref:INNER_UNIT_REF                      {path += ref.getText();}
      )?
    ;

private partialURIPath returns[String path]
{
    path = "";
    String item = null;
}
    : ( id:IDENTIFIER                           {path = path + id.getText();} 
      | dotdot:DOTDOT                           {path = path + dotdot.getText();}
      )
      ( slash:SLASH item=partialURIPath         {path = path + slash.getText() + item;}
      |
      )
    ;

//------------------------------------------------------------------------------

private nameMap returns[String nameMap]
{
    nameMap = "";
    String text = null;
}   
    : (text=nameMapItem                 {nameMap = nameMap + text;}
       (comma:COMMA text=nameMapItem    {nameMap = nameMap + comma.getText() + text;}
       )*
      )?
    ;

private nameMapItem returns[String mapItem]
{
    mapItem = "";
}
    : mapItem=sortNameMapItem
    | mapItem=opNameMapItem
    ;

private sortNameMapItem returns[String mapItem]
{
    mapItem = "";
    String text = null;
}
    : ("sort"                           {mapItem = "sort ";}
      )?
      text=qualifiableSortNames         {mapItem = mapItem + text;}
      nonWordSymbol["+->"]              {mapItem = mapItem + " +-> ";}
      text=qualifiableSortNames         {mapItem = mapItem + text;}
    ;

private opNameMapItem returns[String mapItem]
{
    mapItem = "";
    String text = null;
}
    : ("op"                             {mapItem = "op ";}
      )?
      text=annotableQualifiableName     {mapItem = mapItem + text;}
      nonWordSymbol["+->"]              {mapItem = mapItem + " +-> ";}
      text=annotableQualifiableName     {mapItem = mapItem + text;}
    ;

private annotableQualifiableName returns[String name]
{
    name = "";
    String text = null;
}
    : text=qualifiableOpNames           {name = text;}
      (nonWordSymbol[":"]               {name = name + " : ";}
       text=sort                        {name = name + text;}
      )?
    ;

//------------------------------------------------------------------------------

private scDiagElem returns[ElementFactory.Item diagElem]
{
    diagElem = null;
}
    : diagElem=scDiagNode
    | diagElem=scDiagEdge
    ;

private scDiagNode returns[ElementFactory.Item diagNode]
{
    diagNode = null;
    String nodeName = null;
    ElementFactory.Item ignore = null;
}
    : nodeName=name
      nonWordSymbol["+->"]
      ignore=scTerm[null]
    ;

private scDiagEdge returns[ElementFactory.Item diagEdge]
{
    diagEdge = null;
    String name1 = null;
    String name2 = null;
    String name3 = null;
    ElementFactory.Item ignore = null;
}
    : name1=name
      COLON //nonWordSymbol[":"]
      name2=name
      ARROW //nonWordSymbol["->"]
      name3=name
      nonWordSymbol["+->"]
      ignore=scTerm[null]
    ;

//------------------------------------------------------------------------------

private scSubstituteTermList
{
    ElementFactory.Item ignore = null;
}
    : LBRACKET
      ignore=scTerm[null]
      RBRACKET
      (scSubstituteTermList
      )*
    ;

//------------------------------------------------------------------------------

private claimName returns[ElementFactory.Item claimName]
{
    claimName = null;
    String ignore = null;
}
    : ignore=name
    ;

private proverAssertions returns[ElementFactory.Item assertionsItem]
{
    assertionsItem = null;
    String anAssertion = null;
}
    : "using" 
      (anAssertion=name
       | COMMA anAssertion=name
      )+
    ;

private proverOptions returns[ElementFactory.Item optionsItem]
{
    optionsItem = null;
    String anOption = null;
}
    : "options"
      (anOption=literal
      )+
    ;

//------------------------------------------------------------------------------

private qualifier returns[String qlf]
{
    qlf = null;
}
    : qlf=name
    ;

private name returns[String name]
{
    name = null;
}
    : star:STAR                     {name=star.getText();}
    | sym:NON_WORD_SYMBOL           {name=sym.getText();}
    | name=idName
    | translate:"translate"         {name="translate";}
    | colimit:"colimit"             {name="colimit";}
    | diagram:"diagram"             {name="diagram";}
    | print:"print"                 {name="print";}
    | snark:"Snark"                 {name="Snark";}
    ;

private nonKeywordName returns[String name]
{
    name = null;
}
    : name=idName
    ;

//------------------------------------------------------------------------------

private declaration returns[ElementFactory.Item item]
{
    item = null;
}
    : item=importDeclaration
    | item=sortDeclarationOrDefinition
    | item=opDeclaration
    | item=definition
    ;

//---------------------------------------------------------------------------
private importDeclaration returns[ElementFactory.Item importItem]
{
    importItem = null;
    ElementFactory.Item term = null;
    String uri = null;
}
    : begin:"import"
      uri=fullURIPath       {importItem = builder.createImport(uri);
                             ParserUtil.setBounds(builder, importItem, begin, LT(0));
                            }
/*      term=scTerm[null]     {if (term != null) {
                                importItem = builder.createImport(term.getClass().getName());
                                ParserUtil.setBounds(builder, importItem, begin, LT(0));
                             }
                            }*/
    ;

//---------------------------------------------------------------------------
private sortDeclarationOrDefinition returns[ElementFactory.Item sort]
{
    sort = null;
    String[] params = null;
    String sortName = null;
    String sortDef = null;
}
    : begin:"sort" 
      sortName=qualifiableSortNames
      (params=formalSortParameters (equals sortDef=sort)?
       | (equals sortDef=sort)?
      )
                           {sort = builder.createSort(sortName, params);
                             ParserUtil.setBounds(builder, sort, begin, LT(0));
                           }
    ;

private qualifiableSortNames returns[String sortName]
{
    sortName = null;
    String member = null;
    String qlf = null;
}
    : sortName=qualifiableSortName
    | LBRACE 
      member=qualifiableSortName
                            {sortName = "{" + member;}
      (COMMA member=qualifiableSortName
                            {sortName = sortName + ", " + member;}
      )*
      RBRACE                {sortName = sortName + "}";}
      
                            
    ;

private qualifiableSortName returns[String sortName]
{
    sortName = null;
}   
    : sortName=unqualifiedSortName
    | sortName=qualifiedSortName
    ;

private unqualifiedSortName returns[String sortName]
{
    sortName = null;
}
    : sortName=nonKeywordName
    ;

private qualifiedSortName returns[String sortName]
{
    sortName = null;
    String text = null;
}
    : text=qualifier             {sortName = text;}
      dot:DOT                    {sortName = sortName + ".";}
      text=nonKeywordName        {sortName = sortName + text;}
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

private opDeclaration returns[ElementFactory.Item op]
{
    op = null;
    String name = null;
    String sort = null;
}
    : begin:"op" 
      name=qualifiableOpNames
      (fixity
      )?
      COLON
      sort=sortScheme
                            {op = builder.createOp(name, sort);
                             ParserUtil.setBounds(builder, op, begin, LT(0));
                            }
    ;

private qualifiableOpNames returns[String opName]
{
    opName = null;
    String member = null;
    String qlf = null;
}
    : opName=qualifiableOpName
    | LBRACE 
      member=qualifiableOpName
                            {opName = "{" + member;}
      (COMMA member=qualifiableOpName
                            {opName = opName + ", " + member;}
      )*
      RBRACE                {opName = opName + "}";}
    ;

private qualifiableOpName returns[String opName]
{
    opName = null;
    String qlf = null;
}
    : (qlf=qualifier DOT)?
      opName=opName
                            {if (qlf != null) opName = qlf + "." + opName;}
    ;

private opName returns[String opName]
{
    opName = null;
}
    : opName=name
    ;

private fixity
    : ("infixl"
       | "infixr"
      )
      NAT_LITERAL
    ;

private sortScheme returns[String sortScheme]
{
    sortScheme = "";
    String text = null;
}
    : (text=sortVariableBinder              {sortScheme = sortScheme + text;}
      )?
      text=sort                             {sortScheme = sortScheme + text;}
    ;

private sortVariableBinder returns[String binder]
{
    binder = "";
    String text = null;
}
    : "fa" text=localSortVariableList       {binder = "fa " + text;}
    ;

private localSortVariableList returns[String list]
{
    list = "";
    String text = null;
}
    : lparen:LPAREN                                {list = lparen.getText();}
      text=localSortVariable                       {list = list + text;}
      (comma:COMMA text=localSortVariable          {list = list + comma.getText() + text;}
      )*
      rparen:RPAREN                                {list = list + rparen.getText();}
    ;

private localSortVariable returns[String var]
{
    var = "";
}
    : var=nonKeywordName
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

//---------------------------------------------------------------------------
private definition returns[ElementFactory.Item item]
{
    item=null;
}
    : item=opDefinition
    | item=claimDefinition
    ;

private opDefinition returns[ElementFactory.Item def]
{
    def = null;
    String name = null;
    String[] params = null;
    String expr = null;
}
    : begin:"def"
      name=qualifiableOpNames
      (equals
       | params=formalOpParameters equals) 
      expr=expression            {def = builder.createDef(name, params, expr);
                                  ParserUtil.setBounds(builder, def, begin, LT(0));
                                 }
    ;

private claimDefinition returns[ElementFactory.Item claimDef]
{
    claimDef = null;
    String name = null;
    String kind = null;
    Token begin = null;
    String expr = null;
    String text = null;
    String sortQuant = null;
}
    : kind=claimKind                    {begin = LT(0);}
      name=idName
      equals
      (sortQuant=sortQuantification     {expr = sortQuant;}
      )?
      text=expression                   {expr = expr + " " + text;}
                                        {claimDef = builder.createClaim(name, kind, expr);
                                         ParserUtil.setBounds(builder, claimDef, begin, LT(0));
                                        }

    ;

private claimKind returns[String kind]
{
    kind = "";
}
    : "theorem"            {kind = "theorem";}
    | "axiom"              {kind = "axiom";}
    | "conjecture"         {kind = "conjecture";}
    ;

private sortQuantification returns[String sortQuant]
{
    sortQuant = "";
    String text = null;
}
    : "sort" "fa"                 {sortQuant = "sort fa ";}
      lparen:LPAREN               {sortQuant = sortQuant + lparen.getText();}
      text=name                   {sortQuant = sortQuant + text;}
      (comma:COMMA text=name      {sortQuant = sortQuant + comma.getText() + text;}
      )*
      rparen:RPAREN               {sortQuant = sortQuant + rparen.getText();}
    ;

private formalOpParameters returns[String[] params]
{
    params = null;
    List paramList = new LinkedList();
    String pattern = null;
}
    : (pattern=closedPattern      {paramList.add(pattern);}
      )*                          {params = (String[]) paramList.toArray(new String[]{});}
    ;

// patterns ---------------------------------------------------------------------------

private pattern returns[String pattern]
{
    pattern = "";
}
    : pattern=basicPattern
    | pattern=annotatedPattern
    ;

private annotatedPattern returns[String pattern]
{
    pattern = "";
    String sortStr = null;
}
    : pattern=basicPattern 
      colon:COLON                           {pattern = pattern + colon.getText();}
      sortStr=sort                          {pattern = pattern + sortStr;}
    ;

private basicPattern returns[String pattern]
{
    pattern = "";
}
    : pattern=tightPattern
    ;

private tightPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : pattern=aliasedPattern
    | pattern=quotientPattern
//the rule for relaxPattern wasn't in the official grammar...    | relaxPattern
    | (text=name                            {pattern = text;}
      )? 
      text=closedPattern                    {pattern = pattern + text;}
      (cc:COLONCOLON text=tightPattern      {pattern = pattern + cc.getText() + text;}
      )?
    ;

private aliasedPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : text=variablePattern               {pattern = text;}
      "as" text=tightPattern             {pattern = pattern + "as" + text;}
    ;

private embedPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : text=name                           {pattern = text;}
      text=closedPattern                  {pattern = pattern + text;}
    ;

private variablePattern returns[String pattern]
{
    pattern = "";
}
    : pattern=nonKeywordName
    ;

private closedPattern returns[String pattern]
{
    pattern = "";
}
    : pattern=parenthesizedPattern
    | pattern=variablePattern
    | pattern=literalPattern
    | pattern=listPattern
    | pattern=recordPattern
    | pattern=wildcardPattern
    ;

private wildcardPattern returns[String pattern]
{
    pattern = "";
}
    : ubar:UBAR                                {pattern = ubar.getText();}
    ;

private literalPattern returns[String pattern]
{
    pattern = "";
}
    : pattern=literal
    ;

private listPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : lbracket:LBRACKET                        {pattern = lbracket.getText();}
      (text=pattern                            {pattern = pattern + text;}
       (comma:COMMA text=pattern               {pattern = pattern + comma.getText() + text;}
       )*
      )?
      rbracket:RBRACKET                        {pattern = pattern + rbracket.getText();}
    ;

private parenthesizedPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : lparen:LPAREN                            {pattern = lparen.getText();}
      (text=pattern                            {pattern = pattern + text;}
       (comma:COMMA text=pattern               {pattern = pattern + comma.getText() + text;}
       )*
      )?
      rparen:RPAREN                            {pattern = pattern + rparen.getText();}
    ;

private recordPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : lbrace:LBRACE                            {pattern = lbrace.getText();}
      text=fieldPattern                        {pattern = pattern + text;}
      (comma:COMMA text=fieldPattern           {pattern = pattern + comma.getText() + text;}
      )*
      rbrace:RBRACE                            {pattern = pattern + rbrace.getText();}
    ;

private fieldPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : text=name                                {pattern = text;}
      (equals                                  {pattern = pattern + "=";}
       text=pattern                            {pattern = pattern + text;}
      )?
    ;

private quotientPattern returns[String pattern]
{
    pattern = "";
    String text = null;
}
    : "quotient" text=expression               {pattern = "quotient " + text;}
      text=tightPattern                        {pattern = pattern + " " + text;}
    ;

// expressions ---------------------------------------------------------------------------
private expression returns[String expr]
{
    expr = "";
    String item = null;
}
    : (    item=qualifiableRef    {expr = expr + item + " ";}
         | item=literal           {expr = expr + item + " ";}
         | item=specialSymbol     {expr = expr + item + " ";}
         | item=expressionKeyword {expr = expr + item + " ";}
      )+
    ;

//---------------------------------------------------------------------------
private specialSymbol returns[String text]
{
    text = null;
}
    : UBAR                  {text = "_";}
    | LPAREN                {text = "(";}
    | RPAREN                {text = ")";}
    | LBRACKET              {text = "[";}
    | RBRACKET              {text = "]";}
    | LBRACE                {text = "{";}
    | RBRACE                {text = "}";}
    | COMMA                 {text = ", ";}

    | STAR                  {text = "*";}
    | ARROW                 {text = "->";}
    | COLON                 {text = ":";}
    | VERTICALBAR           {text = "|";}
    | COLONCOLON            {text = "::";}
    | SEMICOLON             {text = ";";}
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
    | (  ("let" "def") => "let" "def"               
                            {text = "let def";}
       | "let"              {text = "let";}
      )
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
    : name=qualifiableOpName
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
    : t:NON_WORD_SYMBOL     {t.getText().equals(expected)}? 
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
      "*)"                      {_ttype = Token.SKIP;}
    ;

// Latex comments -- ignored
LATEX_COMMENT
    : ( "\\end{spec}"
      | "\\section{"
      | "\\subsection{"
      | "\\document{"
      )
      (// '\r' '\n' can be matched in one alternative or by matching
       // '\r' in one iteration and '\n' in another.  The language
       // that allows both "\r\n" and "\r" and "\n" to be valid
       // newlines is ambiguous.  Consequently, the resulting grammar
       // must be ambiguous.  This warning is shut off.
       options {generateAmbigWarnings=false;}
       : { LA(2)!='b' || LA(3)!='e' || LA(4) !='g' || LA(5) !='i' || LA(6) !='n' || LA(7) != '{' || LA(8) != 's' || LA(9) != 'p' || LA(10) != 'e' || LA(11) != 'c' || LA(12) != '}'}? '\\'
	 | '\r' '\n'		{newline();}
	 | '\r'			{newline();}
	 | '\n'			{newline();}
	 | ~('\\'|'\n'|'\r')    
         )*
       (("\\begin{spec}") => "\\begin{spec}"
       |)                       {_ttype = Token.SKIP;}
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
COLON
options {
  paraphrase = "':'";
}
    :  ":"
    ;
COLONCOLON
options {
  paraphrase = "'::'";
}
    :  "::"
    ;
VERTICALBAR
options {
  paraphrase = "'|'";
}
    :  "|"
    ;
STAR
options {
  paraphrase = "'*'";
}
    :  "*"
    ;
ARROW
options {
  paraphrase = "'->'";
}
    :  "->"
    ;
BACKWARDSARROW
options {
  paraphrase = "'<-'";
}
    :  "<-"
    ;
SLASH
options {
  paraphrase = "'/'";
}
    :  "/"
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
//=== INNER_UNIT_REF ================
//-----------------------------

INNER_UNIT_REF
options {
  paraphrase = "an inner-unit reference";
}
    : '#' WORD_START_MARK (WORD_CONTINUE_MARK)+
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
    : '#' CHAR_GLYPH
    ;

protected CHAR_GLYPH
    : LETTER
    | DIGIT
    | OTHER_CHAR_GLYPH
    ;

protected OTHER_CHAR_GLYPH
    : '!' | ':' | '@' | '#' | '$' | '%' | '^' | '&' | '*' | '(' | ')' | '_' | '-' | '+' | '='
    | '|' | '~' | '`' | '.' | ',' | '<' | '>' | '?' | '/' | ';' | '\'' | '[' | ']' | '{' | '}'
    | ESC
    | '\\' 'x' HEXADECIMAL_DIGIT HEXADECIMAL_DIGIT
    ;

protected ESC
    : '\\'
      ( 'a'
      | 'b'
      | 't'
      | 'n'
      | 'v'
      | 'f'
      | 'r'
      | 's'
      | '"'
      | '\\'
      )
    ;

protected HEXADECIMAL_DIGIT
    : DIGIT
    | ('a'..'f')
    | ('A'..'F')
    ;

// string literals
STRING_LITERAL
options {
  paraphrase = "a string";
}
    : '"' (STRING_LITERAL_GLYPH)* '"'
    ;

protected STRING_LITERAL_GLYPH
    : LETTER
    | DIGIT
    | OTHER_CHAR_GLYPH
    | ' '
    ;



//-----------------------------
//====== IDENTIFIERS ==========
//-----------------------------

IDENTIFIER  options
{
    paraphrase = "an identifier";
    testLiterals = true;
}
    : WORD_START_MARK (WORD_CONTINUE_MARK)*
    ;

protected WORD_START_MARK
    : LETTER
    ;

protected WORD_CONTINUE_MARK
    : LETTER | DIGIT | '_' | '?'
    ;

//-----------------------------
//====== NON-WORD SYMBOLS =====
//-----------------------------

NON_WORD_SYMBOL
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
