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
		
		
		Token firstToken = LT(1);
		
		
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
			Token lastToken = LT(0);
			if (lastToken != null && lastToken.getText() != null) {
			ParserUtil.setBodyBounds(builder, (ElementFactory.Item)builder, firstToken, lastToken);
			}
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
			ignore=scTerm(null);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_0);
		}
	}
	
	private final void scToplevelDecls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			scDecl();
			{
			_loop6:
			do {
				if ((LA(1)==IDENTIFIER)) {
					scDecl();
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
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		Object[] objEnd = null;
		item = null;
		Object beginEnd = null;
		
		
		try {      // for error handling
			{
			item=specDefinition(unitIdToken);
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
	
	private final void scDecl() throws RecognitionException, TokenStreamException {
		
		
		String ignore;
		ElementFactory.Item ignore2;
		Token unitIdToken = null;
		
		
		try {      // for error handling
			ignore=name();
			unitIdToken = LT(0);
			equals();
			ignore2=scTerm(unitIdToken);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_2);
		}
	}
	
	private final String  name() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=idName();
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
				nonWordSymbol("=");
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
		Token unitIdToken
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
	
	private final String  qualifier() throws RecognitionException, TokenStreamException {
		String qlf;
		
		
		qlf = null;
		
		
		try {      // for error handling
			qlf=name();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_6);
		}
		return qlf;
	}
	
	private final String  idName() throws RecognitionException, TokenStreamException {
		String name;
		
		Token  id = null;
		
		name = null;
		
		
		try {      // for error handling
			id = LT(1);
			match(IDENTIFIER);
			name = id.getText();
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
			ignore=scTerm(null);
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
			name=qualifiableNames();
			{
			switch ( LA(1)) {
			case IDENTIFIER:
			case LPAREN:
			{
				params=formalSortParameters();
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
			ParserUtil.setBounds(builder, sort, begin, LT(0));
			
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
			name=qualifiableNames();
			nonWordSymbol(":");
			sort=sort();
			op = builder.createOp(name, sort);
			ParserUtil.setBounds(builder, op, begin, LT(0));
			
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_5);
		}
		return op;
	}
	
	private final String  qualifiableNames() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				name=qualifiableName();
				break;
			}
			case LBRACE:
			{
				match(LBRACE);
				member=qualifiableName();
				name = "{" + member;
				{
				_loop21:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableName();
						name = name + ", " + member;
					}
					else {
						break _loop21;
					}
					
				} while (true);
				}
				match(RBRACE);
				name = name + "}";
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
	
	private final String[]  formalSortParameters() throws RecognitionException, TokenStreamException {
		String[] params;
		
		
		params = null;
		String param = null;
		List paramList = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				param=idName();
				params = new String[]{param};
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				paramList = new LinkedList();
				param=idName();
				paramList.add(param);
				{
				_loop27:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param=idName();
						paramList.add(param);
					}
					else {
						break _loop27;
					}
					
				} while (true);
				}
				match(RPAREN);
				params = (String[]) paramList.toArray(new String[]{});
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
	
	private final String  qualifiableName() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		String qlf = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==IDENTIFIER) && (LA(2)==DOT)) {
				qlf=qualifier();
				match(DOT);
			}
			else if ((LA(1)==IDENTIFIER) && (_tokenSet_9.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			name=idName();
			if (qlf != null) name = qlf + "." + name;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return name;
	}
	
	private final void nonWordSymbol(
		String expected
	) throws RecognitionException, TokenStreamException {
		
		Token  t = null;
		
		try {      // for error handling
			t = LT(1);
			match(IDENTIFIER);
			if (!(t.getText().equals(expected)))
			  throw new SemanticException("t.getText().equals(expected)");
		}
		catch (RecognitionException ex) {
			
			int line = t.getLine();
			String msg = "expecting \"" + expected + "\", found \"" + t.getText() + "\"";
			throw new RecognitionException(msg, null, line);
			
		}
	}
	
	private final String  sort() throws RecognitionException, TokenStreamException {
		String sort;
		
		
		String text = null;
		sort = "";
		
		
		try {      // for error handling
			{
			int _cnt31=0;
			_loop31:
			do {
				switch ( LA(1)) {
				case IDENTIFIER:
				{
					text=qualifiableRef();
					sort = sort + text;
					break;
				}
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				{
					text=literal();
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
					text=specialSymbol();
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
					text=expressionKeyword();
					sort = sort + text;
					break;
				}
				default:
				{
					if ( _cnt31>=1 ) { break _loop31; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt31++;
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
	
	private final String  qualifiableRef() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=qualifiableName();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_9);
		}
		return name;
	}
	
	private final String  literal() throws RecognitionException, TokenStreamException {
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
				text=booleanLiteral();
				break;
			}
			case NAT_LITERAL:
			{
				t1 = LT(1);
				match(NAT_LITERAL);
				text = t1.getText();
				break;
			}
			case CHAR_LITERAL:
			{
				t2 = LT(1);
				match(CHAR_LITERAL);
				text = t2.getText();
				break;
			}
			case STRING_LITERAL:
			{
				t3 = LT(1);
				match(STRING_LITERAL);
				text = t3.getText();
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
	
	private final String  specialSymbol() throws RecognitionException, TokenStreamException {
		String text;
		
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case UBAR:
			{
				match(UBAR);
				text = "_";
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				text = "(";
				break;
			}
			case RPAREN:
			{
				match(RPAREN);
				text = "}";
				break;
			}
			case LBRACKET:
			{
				match(LBRACKET);
				text = "[";
				break;
			}
			case RBRACKET:
			{
				match(RBRACKET);
				text = "]";
				break;
			}
			case LBRACE:
			{
				match(LBRACE);
				text = "{";
				break;
			}
			case RBRACE:
			{
				match(RBRACE);
				text = "}";
				break;
			}
			case COMMA:
			{
				match(COMMA);
				text = ", ";
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
	
	private final String  expressionKeyword() throws RecognitionException, TokenStreamException {
		String text;
		
		
		text = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_as:
			{
				match(LITERAL_as);
				text = "as ";
				break;
			}
			case LITERAL_case:
			{
				match(LITERAL_case);
				text = "case ";
				break;
			}
			case LITERAL_choose:
			{
				match(LITERAL_choose);
				text = "choose ";
				break;
			}
			case LITERAL_else:
			{
				match(LITERAL_else);
				text = "else ";
				break;
			}
			case LITERAL_embed:
			{
				match(LITERAL_embed);
				text = "embed ";
				break;
			}
			case 29:
			{
				match(29);
				text = "embed? ";
				break;
			}
			case LITERAL_ex:
			{
				match(LITERAL_ex);
				text = "ex ";
				break;
			}
			case LITERAL_fa:
			{
				match(LITERAL_fa);
				text = "fa ";
				break;
			}
			case LITERAL_fn:
			{
				match(LITERAL_fn);
				text = "fn ";
				break;
			}
			case LITERAL_if:
			{
				match(LITERAL_if);
				text = "if ";
				break;
			}
			case LITERAL_in:
			{
				match(LITERAL_in);
				text = "in ";
				break;
			}
			case LITERAL_let:
			{
				{
				match(LITERAL_let);
				text = "let ";
				{
				switch ( LA(1)) {
				case LITERAL_def:
				{
					match(LITERAL_def);
					text = "let def ";
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
				match(LITERAL_of);
				text = "of ";
				break;
			}
			case LITERAL_project:
			{
				match(LITERAL_project);
				text = "project ";
				break;
			}
			case LITERAL_quotient:
			{
				match(LITERAL_quotient);
				text = "quotient ";
				break;
			}
			case LITERAL_relax:
			{
				match(LITERAL_relax);
				text = "relax ";
				break;
			}
			case LITERAL_restrict:
			{
				match(LITERAL_restrict);
				text = "restrict ";
				break;
			}
			case LITERAL_then:
			{
				match(LITERAL_then);
				text = "then ";
				break;
			}
			case LITERAL_where:
			{
				match(LITERAL_where);
				text = "where ";
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
	
	private final String  booleanLiteral() throws RecognitionException, TokenStreamException {
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
				break;
			}
			case LITERAL_false:
			{
				t2 = LT(1);
				match(LITERAL_false);
				text = "false ";
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
	
	}
