// $ANTLR 2.7.1: "MetaSlangGrammar.g" -> "MetaSlangParserFromAntlr.java"$

package edu.kestrel.netbeans.parser;

import antlr.TokenBuffer;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.ANTLRException;
import antlr.LLkParser;
import antlr.Token;
import antlr.TokenStream;
import antlr.RecognitionException;
import antlr.NoViableAltException;
import antlr.MismatchedTokenException;
import antlr.SemanticException;
import antlr.ParserSharedInputState;
import antlr.collections.impl.BitSet;
import antlr.collections.AST;
import antlr.ASTPair;
import antlr.collections.impl.ASTArray;

import java.util.*;

import org.netbeans.modules.java.ErrConsumer;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.parser.ElementFactory;
import edu.kestrel.netbeans.parser.ParserUtil;

public class MetaSlangParserFromAntlr extends antlr.LLkParser
       implements MetaSlangParserFromAntlrTokenTypes
 {

    ParseObjectRequest request;
    ElementFactory builder;
    Token firstToken;
    Token lastToken;
    Set processedUnitNames = new HashSet();

    public void reportError(RecognitionException ex) {
        request.setSyntaxErrors(request.getSyntaxErrors() + 1);
        ErrConsumer errConsumer = request.getErrConsumer();
        if (errConsumer != null) {
            errConsumer.pushError(null, ex.getLine(), ex.getColumn(), ex.getMessage(), "");
        }
    }

    public MetaSlangParserFromAntlr(TokenStream lexer, ParseObjectRequest request) {
        this(lexer);
        this.request = request;
        this.builder = request.getFactory();
    }

protected MetaSlangParserFromAntlr(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public MetaSlangParserFromAntlr(TokenBuffer tokenBuf) {
  this(tokenBuf,3);
}

protected MetaSlangParserFromAntlr(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public MetaSlangParserFromAntlr(TokenStream lexer) {
  this(lexer,3);
}

public MetaSlangParserFromAntlr(ParserSharedInputState state) {
  super(state,3);
  tokenNames = _tokenNames;
}

	public final void starts() throws RecognitionException, TokenStreamException {
		
		
		firstToken = null;
		lastToken = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_spec:
			{
				scToplevelTerm();
				break;
			}
			case IDENTIFIER:
			{
				scToplevelDecls();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if (firstToken != null && lastToken != null) {
			ParserUtil.setBodyBounds(builder, (ElementFactory.Item)builder, firstToken, lastToken);}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void scToplevelTerm() throws RecognitionException, TokenStreamException {
		
		
		ElementFactory.Item ignore;
		
		
		try {      // for error handling
			ignore=scTerm(null, true);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void scToplevelDecls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			scDecl(true);
			{
			_loop6:
			do {
				if ((LA(1)==IDENTIFIER)) {
					scDecl(false);
				}
				else {
					break _loop6;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final ElementFactory.Item  scTerm(
		Token unitIdToken, boolean recordFirstToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		Object[] objEnd = null;
		item = null;
		Object beginEnd = null;
		
		
		try {      // for error handling
			{
			item=specDefinition(unitIdToken, recordFirstToken);
			}
			if (item != null) builder.setParent(item, null);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_1);
		}
		return item;
	}
	
	private final void scDecl(
		boolean first
	) throws RecognitionException, TokenStreamException {
		
		
		String ignore;
		ElementFactory.Item ignore2;
		Token unitIdToken = null;
		
		
		try {      // for error handling
			ignore=name(true);
			unitIdToken = lastToken;
			if (first) firstToken = unitIdToken;
			equals();
			ignore2=scTerm(unitIdToken, false);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_2);
		}
	}
	
	private final String  name(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=idName(recordToken);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_3);
		}
		return name;
	}
	
	private final void equals() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				eq();
				break;
			}
			case LITERAL_is:
			{
				match(LITERAL_is);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_4);
		}
	}
	
	private final ElementFactory.Item  specDefinition(
		Token unitIdToken, boolean recordFirstToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item spec;
		
		Token  begin = null;
		Token  end = null;
		
		spec = null;
		ElementFactory.Item childItem = null;
		Token headerEnd = null;
		List children = new LinkedList();
		String name = (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_spec);
			headerEnd = begin;
			if (recordFirstToken) firstToken = begin;
			{
			_loop12:
			do {
				if ((LA(1)==LITERAL_import||LA(1)==LITERAL_sort||LA(1)==LITERAL_op)) {
					childItem=declaration();
					if (childItem != null) children.add(childItem);
				}
				else {
					break _loop12;
				}
				
			} while (true);
			}
			end = LT(1);
			match(LITERAL_endspec);
			spec = builder.createSpec(name);
			if (unitIdToken != null) {
			begin = unitIdToken;
			}
			builder.setParent(children, spec);
			lastToken = end;
			ParserUtil.setAllBounds(builder, spec, begin, headerEnd, end);
			
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_1);
		}
		return spec;
	}
	
	private final ElementFactory.Item  declaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_import:
			{
				importDeclaration();
				break;
			}
			case LITERAL_sort:
			{
				item=sortDeclaration();
				break;
			}
			case LITERAL_op:
			{
				item=opDeclaration();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return item;
	}
	
	private final String  qualifier(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String qlf;
		
		
		qlf = null;
		
		
		try {      // for error handling
			qlf=name(recordToken);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_6);
		}
		return qlf;
	}
	
	private final String  idName(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String name;
		
		Token  id = null;
		
		name = null;
		
		
		try {      // for error handling
			id = LT(1);
			match(IDENTIFIER);
			name = id.getText();
			if (recordToken) lastToken = id;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_7);
		}
		return name;
	}
	
	private final void importDeclaration() throws RecognitionException, TokenStreamException {
		
		
		ElementFactory.Item ignore;
		
		
		try {      // for error handling
			match(LITERAL_import);
			ignore=scTerm(null, false);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
	}
	
	private final ElementFactory.Item  sortDeclaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item sort;
		
		Token  begin = null;
		
		sort = null;
		String[] params = null;
		String name = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_sort);
			name=qualifiableNames(true);
			{
			switch ( LA(1)) {
			case IDENTIFIER:
			case LPAREN:
			{
				params=formalSortParameters(true);
				break;
			}
			case LITERAL_endspec:
			case LITERAL_import:
			case LITERAL_sort:
			case LITERAL_op:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			sort = builder.createSort(name, params);
			ParserUtil.setBounds(builder, sort, begin, lastToken);
			
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return sort;
	}
	
	private final ElementFactory.Item  opDeclaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item op;
		
		Token  begin = null;
		
		op = null;
		String name = null;
		String sort = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_op);
			name=qualifiableNames(false);
			colon();
			sort=sort(true);
			op = builder.createOp(name, sort);
			ParserUtil.setBounds(builder, op, begin, lastToken);
			
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return op;
	}
	
	private final String  qualifiableNames(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String name;
		
		Token  end = null;
		
		name = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				name=qualifiableName(recordToken);
				break;
			}
			case LBRACE:
			{
				{
				match(LBRACE);
				member=qualifiableName(false);
				name = "{" + member;
				{
				_loop22:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableName(false);
						name = name + ", " + member;
					}
					else {
						break _loop22;
					}
					
				} while (true);
				}
				end = LT(1);
				match(RBRACE);
				name = name + "}";
				if (recordToken) lastToken = end;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_8);
		}
		return name;
	}
	
	private final String[]  formalSortParameters(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String[] params;
		
		Token  end = null;
		
		params = null;
		String param = null;
		List paramList = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				param=idName(recordToken);
				params = new String[]{param};
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				paramList = new LinkedList();
				param=idName(false);
				paramList.add(param);
				{
				_loop28:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param=idName(false);
						paramList.add(param);
					}
					else {
						break _loop28;
					}
					
				} while (true);
				}
				end = LT(1);
				match(RPAREN);
				params = (String[]) paramList.toArray(new String[]{});
				if (recordToken) lastToken = end;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return params;
	}
	
	private final String  qualifiableName(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		String qlf = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==IDENTIFIER) && (LA(2)==DOT)) {
				qlf=qualifier(false);
				match(DOT);
			}
			else if ((LA(1)==IDENTIFIER) && (_tokenSet_9.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			name=idName(recordToken);
			if (qlf != null) name = qlf + "." + name;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return name;
	}
	
	private final void colon() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals(":")))
			  throw new SemanticException("LT(1).getText().equals(\":\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_10);
		}
	}
	
	private final String  sort(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String sort;
		
		
		String text = null;
		sort = "";
		
		
		try {      // for error handling
			{
			int _cnt32=0;
			_loop32:
			do {
				switch ( LA(1)) {
				case IDENTIFIER:
				{
					text=qualifiableRef(recordToken);
					sort = sort + text;
					break;
				}
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				{
					text=literal(recordToken);
					sort = sort + text;
					break;
				}
				case LBRACE:
				case COMMA:
				case RBRACE:
				case LPAREN:
				case RPAREN:
				case UBAR:
				case LBRACKET:
				case RBRACKET:
				{
					text=specialSymbol(recordToken);
					sort = sort + text;
					break;
				}
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 29:
				case LITERAL_ex:
				case LITERAL_fa:
				case LITERAL_fn:
				case LITERAL_if:
				case LITERAL_in:
				case LITERAL_let:
				case LITERAL_of:
				case LITERAL_project:
				case LITERAL_quotient:
				case LITERAL_relax:
				case LITERAL_restrict:
				case LITERAL_then:
				case LITERAL_where:
				{
					text=expressionKeyword(recordToken);
					sort = sort + text;
					break;
				}
				default:
				{
					if ( _cnt32>=1 ) { break _loop32; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt32++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return sort;
	}
	
	private final String  qualifiableRef(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=qualifiableName(recordToken);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return name;
	}
	
	private final String  literal(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String text;
		
		Token  t1 = null;
		Token  t2 = null;
		Token  t3 = null;
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_true:
			case LITERAL_false:
			{
				text=booleanLiteral(recordToken);
				break;
			}
			case NAT_LITERAL:
			{
				t1 = LT(1);
				match(NAT_LITERAL);
				text = t1.getText();
				if (recordToken) lastToken = t1;
				break;
			}
			case CHAR_LITERAL:
			{
				t2 = LT(1);
				match(CHAR_LITERAL);
				text = t2.getText();
				if (recordToken) lastToken = t2;
				break;
			}
			case STRING_LITERAL:
			{
				t3 = LT(1);
				match(STRING_LITERAL);
				text = t3.getText();
				if (recordToken) lastToken = t3;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return text;
	}
	
	private final String  specialSymbol(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String text;
		
		Token  t1 = null;
		Token  t2 = null;
		Token  t3 = null;
		Token  t4 = null;
		Token  t5 = null;
		Token  t6 = null;
		Token  t7 = null;
		Token  t8 = null;
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case UBAR:
			{
				t1 = LT(1);
				match(UBAR);
				text = "_";
				if (recordToken) lastToken = t1;
				break;
			}
			case LPAREN:
			{
				t2 = LT(1);
				match(LPAREN);
				text = "(";
				if (recordToken) lastToken = t2;
				break;
			}
			case RPAREN:
			{
				t3 = LT(1);
				match(RPAREN);
				text = "}";
				if (recordToken) lastToken = t3;
				break;
			}
			case LBRACKET:
			{
				t4 = LT(1);
				match(LBRACKET);
				text = "[";
				if (recordToken) lastToken = t4;
				break;
			}
			case RBRACKET:
			{
				t5 = LT(1);
				match(RBRACKET);
				text = "]";
				if (recordToken) lastToken = t5;
				break;
			}
			case LBRACE:
			{
				t6 = LT(1);
				match(LBRACE);
				text = "{";
				if (recordToken) lastToken = t6;
				break;
			}
			case RBRACE:
			{
				t7 = LT(1);
				match(RBRACE);
				text = "}";
				if (recordToken) lastToken = t7;
				break;
			}
			case COMMA:
			{
				t8 = LT(1);
				match(COMMA);
				text = ", ";
				if (recordToken) lastToken = t8;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return text;
	}
	
	private final String  expressionKeyword(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String text;
		
		Token  t1 = null;
		Token  t2 = null;
		Token  t3 = null;
		Token  t4 = null;
		Token  t5 = null;
		Token  t6 = null;
		Token  t7 = null;
		Token  t8 = null;
		Token  t9 = null;
		Token  t10 = null;
		Token  t11 = null;
		Token  t12 = null;
		Token  t13 = null;
		Token  t14 = null;
		Token  t15 = null;
		Token  t16 = null;
		Token  t17 = null;
		Token  t18 = null;
		Token  t19 = null;
		Token  t20 = null;
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_as:
			{
				t1 = LT(1);
				match(LITERAL_as);
				text = "as ";
				if (recordToken) lastToken = t1;
				break;
			}
			case LITERAL_case:
			{
				t2 = LT(1);
				match(LITERAL_case);
				text = "case ";
				if (recordToken) lastToken = t2;
				break;
			}
			case LITERAL_choose:
			{
				t3 = LT(1);
				match(LITERAL_choose);
				text = "choose ";
				if (recordToken) lastToken = t3;
				break;
			}
			case LITERAL_else:
			{
				t4 = LT(1);
				match(LITERAL_else);
				text = "else ";
				if (recordToken) lastToken = t4;
				break;
			}
			case LITERAL_embed:
			{
				t5 = LT(1);
				match(LITERAL_embed);
				text = "embed ";
				if (recordToken) lastToken = t5;
				break;
			}
			case 29:
			{
				t6 = LT(1);
				match(29);
				text = "embed? ";
				if (recordToken) lastToken = t6;
				break;
			}
			case LITERAL_ex:
			{
				t7 = LT(1);
				match(LITERAL_ex);
				text = "ex ";
				if (recordToken) lastToken = t7;
				break;
			}
			case LITERAL_fa:
			{
				t8 = LT(1);
				match(LITERAL_fa);
				text = "fa ";
				if (recordToken) lastToken = t8;
				break;
			}
			case LITERAL_fn:
			{
				t9 = LT(1);
				match(LITERAL_fn);
				text = "fn ";
				if (recordToken) lastToken = t9;
				break;
			}
			case LITERAL_if:
			{
				t10 = LT(1);
				match(LITERAL_if);
				text = "if ";
				if (recordToken) lastToken = t10;
				break;
			}
			case LITERAL_in:
			{
				t11 = LT(1);
				match(LITERAL_in);
				text = "in ";
				if (recordToken) lastToken = t11;
				break;
			}
			case LITERAL_let:
			{
				{
				t12 = LT(1);
				match(LITERAL_let);
				text = "let ";
				if (recordToken) lastToken = t12;
				{
				switch ( LA(1)) {
				case LITERAL_def:
				{
					t13 = LT(1);
					match(LITERAL_def);
					text = "let def ";
					if (recordToken) lastToken = t13;
					break;
				}
				case LITERAL_endspec:
				case LITERAL_import:
				case LITERAL_sort:
				case LBRACE:
				case COMMA:
				case RBRACE:
				case IDENTIFIER:
				case LPAREN:
				case RPAREN:
				case LITERAL_op:
				case UBAR:
				case LBRACKET:
				case RBRACKET:
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 29:
				case LITERAL_ex:
				case LITERAL_fa:
				case LITERAL_fn:
				case LITERAL_if:
				case LITERAL_in:
				case LITERAL_let:
				case LITERAL_of:
				case LITERAL_project:
				case LITERAL_quotient:
				case LITERAL_relax:
				case LITERAL_restrict:
				case LITERAL_then:
				case LITERAL_where:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				}
				break;
			}
			case LITERAL_of:
			{
				t14 = LT(1);
				match(LITERAL_of);
				text = "of ";
				if (recordToken) lastToken = t14;
				break;
			}
			case LITERAL_project:
			{
				t15 = LT(1);
				match(LITERAL_project);
				text = "project ";
				if (recordToken) lastToken = t15;
				break;
			}
			case LITERAL_quotient:
			{
				t16 = LT(1);
				match(LITERAL_quotient);
				text = "quotient ";
				if (recordToken) lastToken = t16;
				break;
			}
			case LITERAL_relax:
			{
				t17 = LT(1);
				match(LITERAL_relax);
				text = "relax ";
				if (recordToken) lastToken = t17;
				break;
			}
			case LITERAL_restrict:
			{
				t18 = LT(1);
				match(LITERAL_restrict);
				text = "restrict ";
				if (recordToken) lastToken = t18;
				break;
			}
			case LITERAL_then:
			{
				t19 = LT(1);
				match(LITERAL_then);
				text = "then ";
				if (recordToken) lastToken = t19;
				break;
			}
			case LITERAL_where:
			{
				t20 = LT(1);
				match(LITERAL_where);
				text = "where ";
				if (recordToken) lastToken = t20;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return text;
	}
	
	private final String  booleanLiteral(
		boolean recordToken
	) throws RecognitionException, TokenStreamException {
		String text;
		
		Token  t1 = null;
		Token  t2 = null;
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_true:
			{
				t1 = LT(1);
				match(LITERAL_true);
				text = "true ";
				if (recordToken) lastToken = t1;
				break;
			}
			case LITERAL_false:
			{
				t2 = LT(1);
				match(LITERAL_false);
				text = "false ";
				if (recordToken) lastToken = t2;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return text;
	}
	
	private final void eq() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals("=")))
			  throw new SemanticException("LT(1).getText().equals(\"=\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_4);
		}
	}
	
	private final void rarrow() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals("->")))
			  throw new SemanticException("LT(1).getText().equals(\"->\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void star() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals("*")))
			  throw new SemanticException("LT(1).getText().equals(\"*\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void vbar() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals("|")))
			  throw new SemanticException("LT(1).getText().equals(\"|\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void slash() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if (!(LT(1).getText().equals("/")))
			  throw new SemanticException("LT(1).getText().equals(\"/\")");
			match(IDENTIFIER);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"spec\"",
		"\"endspec\"",
		"\"import\"",
		"\"sort\"",
		"'{'",
		"','",
		"'}'",
		"'.'",
		"an identifier",
		"'('",
		"')'",
		"\"op\"",
		"'_'",
		"'['",
		"']'",
		"an integer",
		"a character",
		"a string",
		"\"true\"",
		"\"false\"",
		"\"as\"",
		"\"case\"",
		"\"choose\"",
		"\"else\"",
		"\"embed\"",
		"\"embed?\"",
		"\"ex\"",
		"\"fa\"",
		"\"fn\"",
		"\"if\"",
		"\"in\"",
		"\"let\"",
		"\"def\"",
		"\"of\"",
		"\"project\"",
		"\"quotient\"",
		"\"relax\"",
		"\"restrict\"",
		"\"then\"",
		"\"where\"",
		"\"is\"",
		"VOCAB",
		"WHITESPACE",
		"LINE_COMMENT",
		"BLOCK_COMMENT",
		"';'",
		"'..'",
		"'#'",
		"LETTER",
		"DIGIT",
		"ESC",
		"WORD_SYMBOL",
		"NON_WORD_SYMBOL",
		"NON_WORD_MARK"
	};
	
	private static final long _tokenSet_0_data_[] = { 2L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 37090L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { 4098L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 17592186050560L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { 16L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { 32992L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { 2048L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 35115652612064L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { 45280L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	private static final long _tokenSet_9_data_[] = { 17523466565600L, 0L };
	public static final BitSet _tokenSet_9 = new BitSet(_tokenSet_9_data_);
	private static final long _tokenSet_10_data_[] = { 17523466532608L, 0L };
	public static final BitSet _tokenSet_10 = new BitSet(_tokenSet_10_data_);
	
	}
