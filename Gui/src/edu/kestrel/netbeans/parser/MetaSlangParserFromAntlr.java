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
			case IDENTIFIER:
			{
				scToplevelDecls();
				break;
			}
			case LITERAL_spec:
			case LITERAL_prove:
			{
				scToplevelTerm();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				Token lastToken = LT(0);
				if (lastToken != null && lastToken.getText() != null) {
				ParserUtil.setBodyBounds(builder, (ElementFactory.Item)builder, firstToken, lastToken);
				}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void scDecl() throws RecognitionException, TokenStreamException {
		
		
		String ignore;
		ElementFactory.Item ignore2;
		Token unitIdToken = null;
		
		
		try {      // for error handling
			ignore=name();
			if ( inputState.guessing==0 ) {
				unitIdToken = LT(0);
			}
			equals();
			ignore2=scTerm(unitIdToken);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void scToplevelDecls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			scDecl();
			{
			_loop8:
			do {
				if ((LA(1)==IDENTIFIER)) {
					scDecl();
				}
				else {
					break _loop8;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void scToplevelTerm() throws RecognitionException, TokenStreamException {
		
		
		ElementFactory.Item ignore;
		
		
		try {      // for error handling
			ignore=scTerm(null);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	private final ElementFactory.Item  scTerm(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_spec:
			{
				item=specDefinition(unitIdToken);
				break;
			}
			case LITERAL_prove:
			{
				item=scProve(unitIdToken);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				if (item != null) builder.setParent(item, null);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		return item;
	}
	
	private final String  name() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=idName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	private final void equals() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case NON_WORD_SYMBOL:
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_3);
			} else {
			  throw ex;
			}
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
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			{
			_loop23:
			do {
				if ((_tokenSet_4.member(LA(1)))) {
					childItem=declaration();
					if ( inputState.guessing==0 ) {
						if (childItem != null) children.add(childItem);
					}
				}
				else {
					break _loop23;
				}
				
			} while (true);
			}
			end = LT(1);
			match(LITERAL_endspec);
			if ( inputState.guessing==0 ) {
				spec = builder.createSpec(name);
				if (unitIdToken != null) {
				begin = unitIdToken;
				}
				builder.setParent(children, spec);
				ParserUtil.setAllBounds(builder, spec, begin, headerEnd, end);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		return spec;
	}
	
	private final ElementFactory.Item  scProve(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item proveItem;
		
		Token  begin = null;
		
		proveItem = null;
		ElementFactory.Item childItem = null;
		Token headerEnd = null;
		List children = new LinkedList();
		String name = (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_prove);
			{
			_loop26:
			do {
				if ((LA(1)==IDENTIFIER) && (LA(2)==EOF||LA(2)==IDENTIFIER) && (_tokenSet_5.member(LA(3)))) {
					name();
				}
				else {
					break _loop26;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		return proveItem;
	}
	
	private final void scURI() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case NON_WORD_SYMBOL:
			{
				nonWordSymbol("/");
				scURIPath();
				break;
			}
			case IDENTIFIER:
			{
				scURIPath();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case INNER_UNIT_REF:
			{
				match(INNER_UNIT_REF);
				break;
			}
			case LITERAL_endspec:
			case LITERAL_import:
			case LITERAL_sort:
			case LITERAL_op:
			case LITERAL_def:
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void nonWordSymbol(
		String expected
	) throws RecognitionException, TokenStreamException {
		
		Token  t = null;
		
		try {      // for error handling
			t = LT(1);
			match(NON_WORD_SYMBOL);
			if (!(t.getText().equals(expected)))
			  throw new SemanticException("t.getText().equals(expected)");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				
				int line = t.getLine();
				String msg = "expecting \"" + expected + "\", found \"" + t.getText() + "\"";
				throw new RecognitionException(msg, null, line);
				
			} else {
				throw ex;
			}
		}
	}
	
	private final void scURIPath() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(IDENTIFIER);
			{
			switch ( LA(1)) {
			case NON_WORD_SYMBOL:
			{
				nonWordSymbol("/");
				scURIPath();
				break;
			}
			case INNER_UNIT_REF:
			case LITERAL_endspec:
			case LITERAL_import:
			case LITERAL_sort:
			case LITERAL_op:
			case LITERAL_def:
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_7);
			} else {
			  throw ex;
			}
		}
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
				item=sortDeclarationOrDefinition();
				break;
			}
			case LITERAL_op:
			{
				item=opDeclaration();
				break;
			}
			case LITERAL_def:
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
			{
				item=definition();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_8);
			} else {
			  throw ex;
			}
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
			if ( inputState.guessing==0 ) {
				name = id.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_9);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	private final void importDeclaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LITERAL_import);
			scURI();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	private final ElementFactory.Item  sortDeclarationOrDefinition() throws RecognitionException, TokenStreamException {
		ElementFactory.Item sort;
		
		Token  begin = null;
		
		sort = null;
		String[] params = null;
		String sortName = null;
		String sortDef = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_sort);
			sortName=qualifiableSortNames();
			{
			switch ( LA(1)) {
			case IDENTIFIER:
			case LPAREN:
			{
				{
				params=formalSortParameters();
				}
				{
				switch ( LA(1)) {
				case NON_WORD_SYMBOL:
				case LITERAL_is:
				{
					equals();
					sortDef=sort();
					break;
				}
				case LITERAL_endspec:
				case LITERAL_import:
				case LITERAL_sort:
				case LITERAL_op:
				case LITERAL_def:
				case LITERAL_theorem:
				case LITERAL_axiom:
				case LITERAL_conjecture:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case LITERAL_endspec:
			case LITERAL_import:
			case LITERAL_sort:
			case LITERAL_op:
			case NON_WORD_SYMBOL:
			case LITERAL_def:
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
			case LITERAL_is:
			{
				{
				switch ( LA(1)) {
				case NON_WORD_SYMBOL:
				case LITERAL_is:
				{
					equals();
					sortDef=sort();
					break;
				}
				case LITERAL_endspec:
				case LITERAL_import:
				case LITERAL_sort:
				case LITERAL_op:
				case LITERAL_def:
				case LITERAL_theorem:
				case LITERAL_axiom:
				case LITERAL_conjecture:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				sort = builder.createSort(sortName, params);
				ParserUtil.setBounds(builder, sort, begin, LT(0));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
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
			name=qualifiableOpNames();
			nonWordSymbol(":");
			sort=sort();
			if ( inputState.guessing==0 ) {
				op = builder.createOp(name, sort);
				ParserUtil.setBounds(builder, op, begin, LT(0));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return op;
	}
	
	private final ElementFactory.Item  definition() throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item=null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_def:
			{
				opDefinition();
				break;
			}
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
			{
				item=claimDefinition();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return item;
	}
	
	private final String  qualifiableSortNames() throws RecognitionException, TokenStreamException {
		String sortName;
		
		
		sortName = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				sortName=qualifiableSortName();
				break;
			}
			case LBRACE:
			{
				match(LBRACE);
				member=qualifiableSortName();
				if ( inputState.guessing==0 ) {
					sortName = "{" + member;
				}
				{
				_loop40:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableSortName();
						if ( inputState.guessing==0 ) {
							sortName = sortName + ", " + member;
						}
					}
					else {
						break _loop40;
					}
					
				} while (true);
				}
				match(RBRACE);
				if ( inputState.guessing==0 ) {
					sortName = sortName + "}";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_10);
			} else {
			  throw ex;
			}
		}
		return sortName;
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
				if ( inputState.guessing==0 ) {
					params = new String[]{param};
				}
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				if ( inputState.guessing==0 ) {
					paramList = new LinkedList();
				}
				param=idName();
				if ( inputState.guessing==0 ) {
					paramList.add(param);
				}
				{
				_loop46:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param=idName();
						if ( inputState.guessing==0 ) {
							paramList.add(param);
						}
					}
					else {
						break _loop46;
					}
					
				} while (true);
				}
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					params = (String[]) paramList.toArray(new String[]{});
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return params;
	}
	
	private final String  sort() throws RecognitionException, TokenStreamException {
		String sort;
		
		
		String text = null;
		sort = "";
		
		
		try {      // for error handling
			{
			int _cnt56=0;
			_loop56:
			do {
				switch ( LA(1)) {
				case IDENTIFIER:
				case NON_WORD_SYMBOL:
				{
					text=qualifiableRef();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
					break;
				}
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				{
					text=literal();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
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
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
					break;
				}
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 36:
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
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
					break;
				}
				default:
				{
					if ( _cnt56>=1 ) { break _loop56; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt56++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return sort;
	}
	
	private final String  qualifiableSortName() throws RecognitionException, TokenStreamException {
		String sortName;
		
		
		sortName = null;
		String qlf = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==IDENTIFIER) && (LA(2)==DOT)) {
				qlf=qualifier();
				match(DOT);
			}
			else if ((LA(1)==IDENTIFIER) && (_tokenSet_12.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			sortName=idName();
			if ( inputState.guessing==0 ) {
				if (qlf != null) sortName = qlf + "." + sortName;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_12);
			} else {
			  throw ex;
			}
		}
		return sortName;
	}
	
	private final String  qualifiableOpNames() throws RecognitionException, TokenStreamException {
		String opName;
		
		
		opName = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			case NON_WORD_SYMBOL:
			{
				opName=qualifiableOpName();
				break;
			}
			case LBRACE:
			{
				match(LBRACE);
				member=qualifiableOpName();
				if ( inputState.guessing==0 ) {
					opName = "{" + member;
				}
				{
				_loop50:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableOpName();
						if ( inputState.guessing==0 ) {
							opName = opName + ", " + member;
						}
					}
					else {
						break _loop50;
					}
					
				} while (true);
				}
				match(RBRACE);
				if ( inputState.guessing==0 ) {
					opName = opName + "}";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  qualifiableOpName() throws RecognitionException, TokenStreamException {
		String opName;
		
		
		opName = null;
		String qlf = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==IDENTIFIER) && (LA(2)==DOT)) {
				qlf=qualifier();
				match(DOT);
			}
			else if ((LA(1)==IDENTIFIER||LA(1)==NON_WORD_SYMBOL) && (_tokenSet_14.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			opName=opName();
			if ( inputState.guessing==0 ) {
				if (qlf != null) opName = qlf + "." + opName;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_14);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  opName() throws RecognitionException, TokenStreamException {
		String opName;
		
		Token  id = null;
		Token  sym = null;
		
		opName = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				id = LT(1);
				match(IDENTIFIER);
				if ( inputState.guessing==0 ) {
					opName = id.getText();
				}
				break;
			}
			case NON_WORD_SYMBOL:
			{
				sym = LT(1);
				match(NON_WORD_SYMBOL);
				if ( inputState.guessing==0 ) {
					opName = sym.getText();
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_14);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  qualifiableRef() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=qualifiableOpName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_15);
			} else {
			  throw ex;
			}
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
				if ( inputState.guessing==0 ) {
					text = t1.getText();
				}
				break;
			}
			case CHAR_LITERAL:
			{
				t2 = LT(1);
				match(CHAR_LITERAL);
				if ( inputState.guessing==0 ) {
					text = t2.getText();
				}
				break;
			}
			case STRING_LITERAL:
			{
				t3 = LT(1);
				match(STRING_LITERAL);
				if ( inputState.guessing==0 ) {
					text = t3.getText();
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_15);
			} else {
			  throw ex;
			}
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
				if ( inputState.guessing==0 ) {
					text = "_";
				}
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				if ( inputState.guessing==0 ) {
					text = "(";
				}
				break;
			}
			case RPAREN:
			{
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					text = "}";
				}
				break;
			}
			case LBRACKET:
			{
				match(LBRACKET);
				if ( inputState.guessing==0 ) {
					text = "[";
				}
				break;
			}
			case RBRACKET:
			{
				match(RBRACKET);
				if ( inputState.guessing==0 ) {
					text = "]";
				}
				break;
			}
			case LBRACE:
			{
				match(LBRACE);
				if ( inputState.guessing==0 ) {
					text = "{";
				}
				break;
			}
			case RBRACE:
			{
				match(RBRACE);
				if ( inputState.guessing==0 ) {
					text = "}";
				}
				break;
			}
			case COMMA:
			{
				match(COMMA);
				if ( inputState.guessing==0 ) {
					text = ", ";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_15);
			} else {
			  throw ex;
			}
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
				if ( inputState.guessing==0 ) {
					text = "as ";
				}
				break;
			}
			case LITERAL_case:
			{
				match(LITERAL_case);
				if ( inputState.guessing==0 ) {
					text = "case ";
				}
				break;
			}
			case LITERAL_choose:
			{
				match(LITERAL_choose);
				if ( inputState.guessing==0 ) {
					text = "choose ";
				}
				break;
			}
			case LITERAL_else:
			{
				match(LITERAL_else);
				if ( inputState.guessing==0 ) {
					text = "else ";
				}
				break;
			}
			case LITERAL_embed:
			{
				match(LITERAL_embed);
				if ( inputState.guessing==0 ) {
					text = "embed ";
				}
				break;
			}
			case 36:
			{
				match(36);
				if ( inputState.guessing==0 ) {
					text = "embed? ";
				}
				break;
			}
			case LITERAL_ex:
			{
				match(LITERAL_ex);
				if ( inputState.guessing==0 ) {
					text = "ex ";
				}
				break;
			}
			case LITERAL_fa:
			{
				match(LITERAL_fa);
				if ( inputState.guessing==0 ) {
					text = "fa ";
				}
				break;
			}
			case LITERAL_fn:
			{
				match(LITERAL_fn);
				if ( inputState.guessing==0 ) {
					text = "fn ";
				}
				break;
			}
			case LITERAL_if:
			{
				match(LITERAL_if);
				if ( inputState.guessing==0 ) {
					text = "if ";
				}
				break;
			}
			case LITERAL_in:
			{
				match(LITERAL_in);
				if ( inputState.guessing==0 ) {
					text = "in ";
				}
				break;
			}
			case LITERAL_let:
			{
				{
				boolean synPredMatched77 = false;
				if (((LA(1)==LITERAL_let) && (LA(2)==LITERAL_def) && (_tokenSet_15.member(LA(3))))) {
					int _m77 = mark();
					synPredMatched77 = true;
					inputState.guessing++;
					try {
						{
						match(LITERAL_let);
						match(LITERAL_def);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched77 = false;
					}
					rewind(_m77);
					inputState.guessing--;
				}
				if ( synPredMatched77 ) {
					match(LITERAL_let);
					match(LITERAL_def);
					if ( inputState.guessing==0 ) {
						text = "let def";
					}
				}
				else if ((LA(1)==LITERAL_let) && (_tokenSet_15.member(LA(2))) && (_tokenSet_16.member(LA(3)))) {
					match(LITERAL_let);
					if ( inputState.guessing==0 ) {
						text = "let";
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				break;
			}
			case LITERAL_of:
			{
				match(LITERAL_of);
				if ( inputState.guessing==0 ) {
					text = "of ";
				}
				break;
			}
			case LITERAL_project:
			{
				match(LITERAL_project);
				if ( inputState.guessing==0 ) {
					text = "project ";
				}
				break;
			}
			case LITERAL_quotient:
			{
				match(LITERAL_quotient);
				if ( inputState.guessing==0 ) {
					text = "quotient ";
				}
				break;
			}
			case LITERAL_relax:
			{
				match(LITERAL_relax);
				if ( inputState.guessing==0 ) {
					text = "relax ";
				}
				break;
			}
			case LITERAL_restrict:
			{
				match(LITERAL_restrict);
				if ( inputState.guessing==0 ) {
					text = "restrict ";
				}
				break;
			}
			case LITERAL_then:
			{
				match(LITERAL_then);
				if ( inputState.guessing==0 ) {
					text = "then ";
				}
				break;
			}
			case LITERAL_where:
			{
				match(LITERAL_where);
				if ( inputState.guessing==0 ) {
					text = "where ";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_15);
			} else {
			  throw ex;
			}
		}
		return text;
	}
	
	private final void opDefinition() throws RecognitionException, TokenStreamException {
		
		
		String name = null;
		String[] params = null;
		
		
		try {      // for error handling
			match(LITERAL_def);
			name=qualifiableOpNames();
			{
			switch ( LA(1)) {
			case IDENTIFIER:
			case LPAREN:
			{
				params=formalOpParameters();
				equals();
				break;
			}
			case NON_WORD_SYMBOL:
			case LITERAL_is:
			{
				equals();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			expression();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	private final ElementFactory.Item  claimDefinition() throws RecognitionException, TokenStreamException {
		ElementFactory.Item claim;
		
		
		claim = null;
		String name = null;
		String kind = null;
		Token begin = null;
		
		
		try {      // for error handling
			kind=claimKind();
			if ( inputState.guessing==0 ) {
				begin = LT(0);
			}
			name=idName();
			equals();
			expression();
			if ( inputState.guessing==0 ) {
				claim = builder.createClaim(name, kind);
				ParserUtil.setBounds(builder, claim, begin, LT(0));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return claim;
	}
	
	private final String[]  formalOpParameters() throws RecognitionException, TokenStreamException {
		String[] params;
		
		
		params = null;
		String param = null;
		List paramList = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				param=idName();
				if ( inputState.guessing==0 ) {
					params = new String[]{param};
				}
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				if ( inputState.guessing==0 ) {
					paramList = new LinkedList();
				}
				{
				switch ( LA(1)) {
				case IDENTIFIER:
				{
					param=idName();
					if ( inputState.guessing==0 ) {
						paramList.add(param);
					}
					{
					_loop70:
					do {
						if ((LA(1)==COMMA)) {
							match(COMMA);
							param=idName();
							if ( inputState.guessing==0 ) {
								paramList.add(param);
							}
						}
						else {
							break _loop70;
						}
						
					} while (true);
					}
					break;
				}
				case RPAREN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					params = (String[]) paramList.toArray(new String[]{});
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_17);
			} else {
			  throw ex;
			}
		}
		return params;
	}
	
	private final void expression() throws RecognitionException, TokenStreamException {
		
		
		String ignore = null;
		
		
		try {      // for error handling
			{
			int _cnt66=0;
			_loop66:
			do {
				switch ( LA(1)) {
				case IDENTIFIER:
				case NON_WORD_SYMBOL:
				{
					ignore=qualifiableRef();
					break;
				}
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				{
					ignore=literal();
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
					ignore=specialSymbol();
					break;
				}
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 36:
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
					ignore=expressionKeyword();
					break;
				}
				default:
				{
					if ( _cnt66>=1 ) { break _loop66; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt66++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	private final String  claimKind() throws RecognitionException, TokenStreamException {
		String kind;
		
		
		kind = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_theorem:
			{
				match(LITERAL_theorem);
				if ( inputState.guessing==0 ) {
					kind = "theorem";
				}
				break;
			}
			case LITERAL_axiom:
			{
				match(LITERAL_axiom);
				if ( inputState.guessing==0 ) {
					kind = "axiom";
				}
				break;
			}
			case LITERAL_conjecture:
			{
				match(LITERAL_conjecture);
				if ( inputState.guessing==0 ) {
					kind = "conjecture";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_18);
			} else {
			  throw ex;
			}
		}
		return kind;
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
				if ( inputState.guessing==0 ) {
					text = "true ";
				}
				break;
			}
			case LITERAL_false:
			{
				t2 = LT(1);
				match(LITERAL_false);
				if ( inputState.guessing==0 ) {
					text = "false ";
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
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_15);
			} else {
			  throw ex;
			}
		}
		return text;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"an inner-unit reference",
		"an identifier",
		"\"spec\"",
		"\"endspec\"",
		"\"prove\"",
		"\"import\"",
		"\"sort\"",
		"'{'",
		"','",
		"'}'",
		"'.'",
		"'('",
		"')'",
		"\"op\"",
		"NON_WORD_SYMBOL",
		"\"def\"",
		"\"theorem\"",
		"\"axiom\"",
		"\"conjecture\"",
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
		"LETTER",
		"DIGIT",
		"CHAR_GLYPH",
		"OTHER_CHAR_GLYPH",
		"ESC",
		"HEXADECIMAL_DIGIT",
		"STRING_LITERAL_GLYPH",
		"WORD_START_MARK",
		"WORD_CONTINUE_MARK",
		"NON_WORD_MARK"
	};
	
	private static final long _tokenSet_0_data_[] = { 2L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 34L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { 1125899907121186L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 1125899898829152L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { 7996928L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { 1125899907104802L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { 7997056L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 7997072L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { 16384L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	private static final long _tokenSet_9_data_[] = { 1125899915228834L, 0L };
	public static final BitSet _tokenSet_9 = new BitSet(_tokenSet_9_data_);
	private static final long _tokenSet_10_data_[] = { 1125899915134624L, 0L };
	public static final BitSet _tokenSet_10 = new BitSet(_tokenSet_10_data_);
	private static final long _tokenSet_11_data_[] = { 1125899915101824L, 0L };
	public static final BitSet _tokenSet_11 = new BitSet(_tokenSet_11_data_);
	private static final long _tokenSet_12_data_[] = { 1125899915146912L, 0L };
	public static final BitSet _tokenSet_12 = new BitSet(_tokenSet_12_data_);
	private static final long _tokenSet_13_data_[] = { 1125899907137568L, 0L };
	public static final BitSet _tokenSet_13 = new BitSet(_tokenSet_13_data_);
	private static final long _tokenSet_14_data_[] = { 2251799813668512L, 0L };
	public static final BitSet _tokenSet_14 = new BitSet(_tokenSet_14_data_);
	private static final long _tokenSet_15_data_[] = { 1125899906825888L, 0L };
	public static final BitSet _tokenSet_15 = new BitSet(_tokenSet_15_data_);
	private static final long _tokenSet_16_data_[] = { 1125899906842274L, 0L };
	public static final BitSet _tokenSet_16 = new BitSet(_tokenSet_16_data_);
	private static final long _tokenSet_17_data_[] = { 1125899907104768L, 0L };
	public static final BitSet _tokenSet_17 = new BitSet(_tokenSet_17_data_);
	private static final long _tokenSet_18_data_[] = { 32L, 0L };
	public static final BitSet _tokenSet_18 = new BitSet(_tokenSet_18_data_);
	
	}
