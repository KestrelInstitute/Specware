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
        request.pushError(ex.getLine(), ex.getColumn(), ex.getMessage());
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
			boolean synPredMatched4 = false;
			if (((LA(1)==IDENTIFIER) && (LA(2)==NON_WORD_SYMBOL||LA(2)==LITERAL_is) && (_tokenSet_0.member(LA(3))))) {
				int _m4 = mark();
				synPredMatched4 = true;
				inputState.guessing++;
				try {
					{
					scDecl();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched4 = false;
				}
				rewind(_m4);
				inputState.guessing--;
			}
			if ( synPredMatched4 ) {
				scToplevelDecls();
			}
			else if ((_tokenSet_0.member(LA(1))) && (_tokenSet_1.member(LA(2))) && (_tokenSet_2.member(LA(3)))) {
				scToplevelTerm();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
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
				consumeUntil(_tokenSet_3);
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
				consumeUntil(_tokenSet_4);
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
				consumeUntil(_tokenSet_3);
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
				consumeUntil(_tokenSet_3);
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
			boolean synPredMatched13 = false;
			if (((_tokenSet_0.member(LA(1))) && (_tokenSet_5.member(LA(2))) && (_tokenSet_6.member(LA(3))))) {
				int _m13 = mark();
				synPredMatched13 = true;
				inputState.guessing++;
				try {
					{
					scSubstitute(unitIdToken);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched13 = false;
				}
				rewind(_m13);
				inputState.guessing--;
			}
			if ( synPredMatched13 ) {
				item=scSubstitute(unitIdToken);
			}
			else if ((_tokenSet_0.member(LA(1))) && (_tokenSet_7.member(LA(2))) && (_tokenSet_8.member(LA(3)))) {
				item=scBasicTerm(unitIdToken);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
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
				consumeUntil(_tokenSet_9);
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
				consumeUntil(_tokenSet_10);
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
	}
	
	private final ElementFactory.Item  scSubstitute(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item substitute;
		
		
		substitute = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			ignore=scBasicTerm(null);
			scSubstituteTermList();
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
		return substitute;
	}
	
	private final ElementFactory.Item  scBasicTerm(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_print:
			{
				item=scPrint(unitIdToken);
				break;
			}
			case LITERAL_spec:
			{
				item=specDefinition(unitIdToken);
				break;
			}
			case LITERAL_let:
			{
				item=scLet(unitIdToken);
				break;
			}
			case LITERAL_translate:
			{
				item=scTranslate(unitIdToken);
				break;
			}
			case LITERAL_diagram:
			{
				item=scDiag(unitIdToken);
				break;
			}
			case LITERAL_colimit:
			{
				item=scColimit(unitIdToken);
				break;
			}
			case LITERAL_morphism:
			{
				item=scSpecMorph(unitIdToken);
				break;
			}
			case LITERAL_generate:
			{
				item=scGenerate(unitIdToken);
				break;
			}
			case LITERAL_obligations:
			{
				item=scObligations(unitIdToken);
				break;
			}
			case LITERAL_prove:
			{
				item=scProve(unitIdToken);
				break;
			}
			default:
				if ((LA(1)==IDENTIFIER||LA(1)==NON_WORD_SYMBOL) && (_tokenSet_12.member(LA(2)))) {
					item=scURI(unitIdToken);
				}
				else if ((LA(1)==IDENTIFIER) && (LA(2)==LITERAL_qualifying)) {
					item=scQualify(unitIdToken);
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
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
		return item;
	}
	
	private final ElementFactory.Item  scPrint(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item print;
		
		
		print = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_print);
			ignore=scTerm(null);
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
		return print;
	}
	
	private final ElementFactory.Item  scURI(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item uri;
		
		
		uri = null;
		String strURI = null;
		
		
		try {      // for error handling
			strURI=fullURIPath();
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
		return uri;
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
			_loop19:
			do {
				if ((_tokenSet_13.member(LA(1)))) {
					childItem=declaration();
					if ( inputState.guessing==0 ) {
						if (childItem != null) children.add(childItem);
					}
				}
				else {
					break _loop19;
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
				consumeUntil(_tokenSet_9);
			} else {
			  throw ex;
			}
		}
		return spec;
	}
	
	private final ElementFactory.Item  scLet(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item let;
		
		
		let = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_let);
			{
			_loop22:
			do {
				if ((LA(1)==IDENTIFIER)) {
					scDecl();
				}
				else {
					break _loop22;
				}
				
			} while (true);
			}
			match(LITERAL_in);
			ignore=scTerm(unitIdToken);
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
		return let;
	}
	
	private final ElementFactory.Item  scTranslate(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item translate;
		
		
		translate = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_translate);
			ignore=scTerm(null);
			match(LITERAL_by);
			nameMap();
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
		return translate;
	}
	
	private final ElementFactory.Item  scQualify(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item qualify;
		
		
		qualify = null;
		String strIgnore = null;
		ElementFactory.Item itemIgnore = null;
		
		
		try {      // for error handling
			strIgnore=qualifier();
			match(LITERAL_qualifying);
			itemIgnore=scTerm(null);
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
		return qualify;
	}
	
	private final ElementFactory.Item  scDiag(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item diag;
		
		
		diag = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_diagram);
			match(LBRACE);
			scDiagElem();
			{
			_loop27:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					scDiagElem();
				}
				else {
					break _loop27;
				}
				
			} while (true);
			}
			match(RBRACE);
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
		return diag;
	}
	
	private final ElementFactory.Item  scColimit(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item colimit;
		
		
		colimit = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_colimit);
			ignore=scTerm(null);
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
		return colimit;
	}
	
	private final ElementFactory.Item  scSpecMorph(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item morph;
		
		Token  begin = null;
		
		morph = null;
		ElementFactory.Item childItem = null;
		ElementFactory.Item ignore = null;
		Token headerEnd = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_morphism);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			ignore=scTerm(null);
			nonWordSymbol("->");
			ignore=scTerm(null);
			nameMap();
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
		return morph;
	}
	
	private final ElementFactory.Item  scGenerate(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item generate;
		
		Token  begin = null;
		
		generate = null;
		String genName = null;
		String fileName = null;
		ElementFactory.Item ignore = null;
		Token headerEnd = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_generate);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			genName=name();
			ignore=scTerm(null);
			{
			if ((LA(1)==LITERAL_in) && (LA(2)==IDENTIFIER) && (_tokenSet_9.member(LA(3)))) {
				match(LITERAL_in);
				fileName=name();
			}
			else if ((_tokenSet_9.member(LA(1))) && (_tokenSet_14.member(LA(2))) && (_tokenSet_15.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
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
		return generate;
	}
	
	private final ElementFactory.Item  scObligations(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item obligations;
		
		Token  begin = null;
		
		obligations=null;
		ElementFactory.Item ignore=null;
		Token headerEnd = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_obligations);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			ignore=scTerm(null);
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
		return obligations;
	}
	
	private final ElementFactory.Item  scProve(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item proof;
		
		Token  begin = null;
		
		proof = null;
		ElementFactory.Item childItem = null;
		String ignore = null;
		Token headerEnd = null;
		List children = new LinkedList();
		String name = (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_prove);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			childItem=claimName();
			if ( inputState.guessing==0 ) {
				if (childItem != null) children.add(childItem);
			}
			match(LITERAL_in);
			childItem=scTerm(null);
			if ( inputState.guessing==0 ) {
				if (childItem != null) children.add(childItem);
			}
			{
			if ((LA(1)==LITERAL_using) && (LA(2)==COMMA||LA(2)==IDENTIFIER) && (_tokenSet_9.member(LA(3)))) {
				childItem=proverAssertions();
			}
			else if ((_tokenSet_9.member(LA(1))) && (_tokenSet_14.member(LA(2))) && (_tokenSet_15.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			if ( inputState.guessing==0 ) {
				if (childItem != null) children.add(childItem);
			}
			{
			if ((LA(1)==LITERAL_options) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
				childItem=proverOptions();
			}
			else if ((_tokenSet_9.member(LA(1))) && (_tokenSet_14.member(LA(2))) && (_tokenSet_15.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			if ( inputState.guessing==0 ) {
				if (childItem != null) children.add(childItem);
			}
			if ( inputState.guessing==0 ) {
				proof = builder.createProof(name);
				if (unitIdToken != null) {
				begin = unitIdToken;
				}
				builder.setParent(new LinkedList()/*children*/, proof);
				ParserUtil.setAllBounds(builder, proof, begin, headerEnd, LT(0));
				
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
		return proof;
	}
	
	private final String  fullURIPath() throws RecognitionException, TokenStreamException {
		String path;
		
		Token  ref = null;
		
		path = null;
		String item = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case NON_WORD_SYMBOL:
			{
				nonWordSymbol("/");
				item=partialURIPath();
				if ( inputState.guessing==0 ) {
					path = "/" + item;
				}
				break;
			}
			case IDENTIFIER:
			{
				item=partialURIPath();
				if ( inputState.guessing==0 ) {
					path = item;
				}
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
				ref = LT(1);
				match(INNER_UNIT_REF);
				if ( inputState.guessing==0 ) {
					path += ref.getText();
				}
				break;
			}
			case EOF:
			case LITERAL_endspec:
			case LITERAL_in:
			case LITERAL_by:
			case LBRACE:
			case COMMA:
			case RBRACE:
			case IDENTIFIER:
			case LITERAL_sort:
			case LITERAL_op:
			case LBRACKET:
			case RBRACKET:
			case LITERAL_using:
			case LITERAL_options:
			case LITERAL_import:
			case NON_WORD_SYMBOL:
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
				consumeUntil(_tokenSet_9);
			} else {
			  throw ex;
			}
		}
		return path;
	}
	
	private final ElementFactory.Item  declaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_import:
			{
				item=importDeclaration();
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
				consumeUntil(_tokenSet_18);
			} else {
			  throw ex;
			}
		}
		return item;
	}
	
	private final void nameMap() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LBRACE);
			{
			switch ( LA(1)) {
			case LBRACE:
			case IDENTIFIER:
			case LITERAL_sort:
			case LITERAL_op:
			case NON_WORD_SYMBOL:
			{
				nameMapItem();
				{
				_loop49:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						nameMapItem();
					}
					else {
						break _loop49;
					}
					
				} while (true);
				}
				break;
			}
			case RBRACE:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RBRACE);
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
				consumeUntil(_tokenSet_19);
			} else {
			  throw ex;
			}
		}
		return qlf;
	}
	
	private final void scDiagElem() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if ((LA(1)==IDENTIFIER) && (LA(2)==NON_WORD_SYMBOL) && (_tokenSet_0.member(LA(3)))) {
				scDiagNode();
			}
			else if ((LA(1)==IDENTIFIER) && (LA(2)==NON_WORD_SYMBOL) && (LA(3)==IDENTIFIER)) {
				scDiagEdge();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void scSubstituteTermList() throws RecognitionException, TokenStreamException {
		
		
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			match(LBRACKET);
			ignore=scTerm(null);
			match(RBRACKET);
			{
			_loop62:
			do {
				if ((LA(1)==LBRACKET) && (_tokenSet_0.member(LA(2))) && (_tokenSet_21.member(LA(3)))) {
					scSubstituteTermList();
				}
				else {
					break _loop62;
				}
				
			} while (true);
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
	
	private final ElementFactory.Item  claimName() throws RecognitionException, TokenStreamException {
		ElementFactory.Item claimName;
		
		
		claimName = null;
		String ignore = null;
		
		
		try {      // for error handling
			ignore=name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_22);
			} else {
			  throw ex;
			}
		}
		return claimName;
	}
	
	private final ElementFactory.Item  proverAssertions() throws RecognitionException, TokenStreamException {
		ElementFactory.Item assertionsItem;
		
		
		assertionsItem = null;
		String anAssertion = null;
		
		
		try {      // for error handling
			match(LITERAL_using);
			{
			int _cnt66=0;
			_loop66:
			do {
				if ((LA(1)==IDENTIFIER) && (_tokenSet_9.member(LA(2))) && (_tokenSet_14.member(LA(3)))) {
					anAssertion=name();
				}
				else if ((LA(1)==COMMA) && (LA(2)==IDENTIFIER) && (_tokenSet_9.member(LA(3)))) {
					match(COMMA);
					anAssertion=name();
				}
				else {
					if ( _cnt66>=1 ) { break _loop66; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt66++;
			} while (true);
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
		return assertionsItem;
	}
	
	private final ElementFactory.Item  proverOptions() throws RecognitionException, TokenStreamException {
		ElementFactory.Item optionsItem;
		
		
		optionsItem = null;
		String anOption = null;
		
		
		try {      // for error handling
			match(LITERAL_options);
			{
			int _cnt69=0;
			_loop69:
			do {
				if ((_tokenSet_16.member(LA(1)))) {
					anOption=literal();
				}
				else {
					if ( _cnt69>=1 ) { break _loop69; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt69++;
			} while (true);
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
		return optionsItem;
	}
	
	private final String  partialURIPath() throws RecognitionException, TokenStreamException {
		String path;
		
		Token  id = null;
		
		path = "";
		String item = null;
		
		
		try {      // for error handling
			id = LT(1);
			match(IDENTIFIER);
			if ( inputState.guessing==0 ) {
				path = path + id.getText();
			}
			{
			boolean synPredMatched45 = false;
			if (((LA(1)==NON_WORD_SYMBOL) && (LA(2)==IDENTIFIER) && (_tokenSet_12.member(LA(3))))) {
				int _m45 = mark();
				synPredMatched45 = true;
				inputState.guessing++;
				try {
					{
					nonWordSymbol("/");
					}
				}
				catch (RecognitionException pe) {
					synPredMatched45 = false;
				}
				rewind(_m45);
				inputState.guessing--;
			}
			if ( synPredMatched45 ) {
				nonWordSymbol("/");
				item=partialURIPath();
				if ( inputState.guessing==0 ) {
					path = path + "/" + item;
				}
			}
			else if ((_tokenSet_12.member(LA(1))) && (_tokenSet_14.member(LA(2))) && (_tokenSet_15.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
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
		return path;
	}
	
	private final void nameMapItem() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if ((LA(1)==LBRACE||LA(1)==IDENTIFIER||LA(1)==LITERAL_sort) && (_tokenSet_23.member(LA(2))) && (_tokenSet_24.member(LA(3)))) {
				sortNameMapItem();
			}
			else if ((_tokenSet_25.member(LA(1))) && (_tokenSet_23.member(LA(2))) && (_tokenSet_26.member(LA(3)))) {
				opNameMapItem();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void sortNameMapItem() throws RecognitionException, TokenStreamException {
		
		
		String ignore = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_sort:
			{
				match(LITERAL_sort);
				break;
			}
			case LBRACE:
			case IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			ignore=qualifiableSortNames();
			nonWordSymbol("+->");
			ignore=qualifiableSortNames();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void opNameMapItem() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_op:
			{
				match(LITERAL_op);
				break;
			}
			case LBRACE:
			case IDENTIFIER:
			case NON_WORD_SYMBOL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			annotableQualifiableName();
			nonWordSymbol("+->");
			annotableQualifiableName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
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
				_loop83:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableSortName();
						if ( inputState.guessing==0 ) {
							sortName = sortName + ", " + member;
						}
					}
					else {
						break _loop83;
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
				consumeUntil(_tokenSet_27);
			} else {
			  throw ex;
			}
		}
		return sortName;
	}
	
	private final void annotableQualifiableName() throws RecognitionException, TokenStreamException {
		
		
		String ignore = null;
		
		
		try {      // for error handling
			ignore=qualifiableOpNames();
			{
			if ((LA(1)==NON_WORD_SYMBOL) && (_tokenSet_28.member(LA(2))) && (_tokenSet_29.member(LA(3)))) {
				nonWordSymbol(":");
				ignore=sort();
			}
			else if ((LA(1)==COMMA||LA(1)==RBRACE||LA(1)==NON_WORD_SYMBOL) && (_tokenSet_9.member(LA(2))) && (_tokenSet_30.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_31);
			} else {
			  throw ex;
			}
		}
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
				_loop94:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableOpName();
						if ( inputState.guessing==0 ) {
							opName = opName + ", " + member;
						}
					}
					else {
						break _loop94;
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
				consumeUntil(_tokenSet_32);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  sort() throws RecognitionException, TokenStreamException {
		String sort;
		
		
		String text = null;
		sort = "";
		
		
		try {      // for error handling
			{
			int _cnt102=0;
			_loop102:
			do {
				switch ( LA(1)) {
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
				case LITERAL_let:
				case LITERAL_in:
				case LITERAL_fa:
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 52:
				case LITERAL_ex:
				case LITERAL_fn:
				case LITERAL_if:
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
					if ((LA(1)==IDENTIFIER||LA(1)==NON_WORD_SYMBOL) && (_tokenSet_33.member(LA(2))) && (_tokenSet_34.member(LA(3)))) {
						text=qualifiableRef();
						if ( inputState.guessing==0 ) {
							sort = sort + text;
						}
					}
					else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_36.member(LA(2))) && (_tokenSet_34.member(LA(3)))) {
						text=specialSymbol();
						if ( inputState.guessing==0 ) {
							sort = sort + text;
						}
					}
				else {
					if ( _cnt102>=1 ) { break _loop102; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt102++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_37);
			} else {
			  throw ex;
			}
		}
		return sort;
	}
	
	private final void scDiagNode() throws RecognitionException, TokenStreamException {
		
		
		String nodeName = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			nodeName=name();
			nonWordSymbol("+->");
			ignore=scTerm(null);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	private final void scDiagEdge() throws RecognitionException, TokenStreamException {
		
		
		String name1 = null;
		String name2 = null;
		String name3 = null;
		ElementFactory.Item ignore = null;
		
		
		try {      // for error handling
			name1=name();
			nonWordSymbol(":");
			name2=name();
			nonWordSymbol("->");
			name3=name();
			nonWordSymbol("+->");
			ignore=scTerm(null);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_20);
			} else {
			  throw ex;
			}
		}
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
				consumeUntil(_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		return text;
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
				consumeUntil(_tokenSet_39);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	private final ElementFactory.Item  importDeclaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item importItem;
		
		Token  begin = null;
		
		importItem = null;
		ElementFactory.Item term = null;
		//String strURI = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_import);
			term=scTerm(null);
			if ( inputState.guessing==0 ) {
				if (term != null) {
				importItem = builder.createImport(term.getClass().getName());
				ParserUtil.setBounds(builder, importItem, begin, LT(0));
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
		return importItem;
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
				case LITERAL_sort:
				case LITERAL_op:
				case LITERAL_import:
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
			case LITERAL_sort:
			case LITERAL_op:
			case LITERAL_import:
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
				case LITERAL_sort:
				case LITERAL_op:
				case LITERAL_import:
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
				consumeUntil(_tokenSet_18);
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
			{
			switch ( LA(1)) {
			case LITERAL_infixl:
			case LITERAL_infixr:
			{
				fixity();
				break;
			}
			case NON_WORD_SYMBOL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
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
				consumeUntil(_tokenSet_18);
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
				item=opDefinition();
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
				consumeUntil(_tokenSet_18);
			} else {
			  throw ex;
			}
		}
		return item;
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
				_loop89:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param=idName();
						if ( inputState.guessing==0 ) {
							paramList.add(param);
						}
					}
					else {
						break _loop89;
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
				consumeUntil(_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		return params;
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
			else if ((LA(1)==IDENTIFIER) && (_tokenSet_27.member(LA(2)))) {
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
				consumeUntil(_tokenSet_27);
			} else {
			  throw ex;
			}
		}
		return sortName;
	}
	
	private final void fixity() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_infixl:
			{
				match(LITERAL_infixl);
				break;
			}
			case LITERAL_infixr:
			{
				match(LITERAL_infixr);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(NAT_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_41);
			} else {
			  throw ex;
			}
		}
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
			else if ((LA(1)==IDENTIFIER||LA(1)==NON_WORD_SYMBOL) && (_tokenSet_42.member(LA(2)))) {
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
				consumeUntil(_tokenSet_42);
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
				consumeUntil(_tokenSet_42);
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
				consumeUntil(_tokenSet_36);
			} else {
			  throw ex;
			}
		}
		return name;
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
					text = ")";
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
				consumeUntil(_tokenSet_36);
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
			case 52:
			{
				match(52);
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
				boolean synPredMatched127 = false;
				if (((LA(1)==LITERAL_let) && (LA(2)==LITERAL_def) && (_tokenSet_36.member(LA(3))))) {
					int _m127 = mark();
					synPredMatched127 = true;
					inputState.guessing++;
					try {
						{
						match(LITERAL_let);
						match(LITERAL_def);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched127 = false;
					}
					rewind(_m127);
					inputState.guessing--;
				}
				if ( synPredMatched127 ) {
					match(LITERAL_let);
					match(LITERAL_def);
					if ( inputState.guessing==0 ) {
						text = "let def";
					}
				}
				else if ((LA(1)==LITERAL_let) && (_tokenSet_36.member(LA(2))) && (_tokenSet_34.member(LA(3)))) {
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
				consumeUntil(_tokenSet_36);
			} else {
			  throw ex;
			}
		}
		return text;
	}
	
	private final ElementFactory.Item  opDefinition() throws RecognitionException, TokenStreamException {
		ElementFactory.Item def;
		
		Token  begin = null;
		
		def = null;
		String name = null;
		String[] params = null;
		String expr = null;
		
		
		try {      // for error handling
			begin = LT(1);
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
			expr=expression();
			if ( inputState.guessing==0 ) {
				def = builder.createDef(name, params, expr);
				ParserUtil.setBounds(builder, def, begin, LT(0));
				
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
		return def;
	}
	
	private final ElementFactory.Item  claimDefinition() throws RecognitionException, TokenStreamException {
		ElementFactory.Item claimDef;
		
		
		claimDef = null;
		String name = null;
		String kind = null;
		Token begin = null;
		String expr = null;
		
		
		try {      // for error handling
			kind=claimKind();
			if ( inputState.guessing==0 ) {
				begin = LT(0);
			}
			name=idName();
			equals();
			{
			switch ( LA(1)) {
			case LITERAL_sort:
			{
				sortQuantification();
				break;
			}
			case LITERAL_let:
			case LITERAL_in:
			case LBRACE:
			case COMMA:
			case RBRACE:
			case IDENTIFIER:
			case LBRACKET:
			case RBRACKET:
			case LPAREN:
			case RPAREN:
			case NON_WORD_SYMBOL:
			case NAT_LITERAL:
			case LITERAL_fa:
			case UBAR:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_as:
			case LITERAL_case:
			case LITERAL_choose:
			case LITERAL_else:
			case LITERAL_embed:
			case 52:
			case LITERAL_ex:
			case LITERAL_fn:
			case LITERAL_if:
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
			expr=expression();
			if ( inputState.guessing==0 ) {
				claimDef = builder.createClaim(name, kind, expr);
				ParserUtil.setBounds(builder, claimDef, begin, LT(0));
				
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
		return claimDef;
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
					_loop120:
					do {
						if ((LA(1)==COMMA)) {
							match(COMMA);
							param=idName();
							if ( inputState.guessing==0 ) {
								paramList.add(param);
							}
						}
						else {
							break _loop120;
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
				consumeUntil(_tokenSet_43);
			} else {
			  throw ex;
			}
		}
		return params;
	}
	
	private final String  expression() throws RecognitionException, TokenStreamException {
		String expr;
		
		
		expr = "";
		String item = null;
		
		
		try {      // for error handling
			{
			int _cnt116=0;
			_loop116:
			do {
				switch ( LA(1)) {
				case IDENTIFIER:
				case NON_WORD_SYMBOL:
				{
					item=qualifiableRef();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
					break;
				}
				case NAT_LITERAL:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case LITERAL_true:
				case LITERAL_false:
				{
					item=literal();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
					break;
				}
				case LBRACE:
				case COMMA:
				case RBRACE:
				case LBRACKET:
				case RBRACKET:
				case LPAREN:
				case RPAREN:
				case UBAR:
				{
					item=specialSymbol();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
					break;
				}
				case LITERAL_let:
				case LITERAL_in:
				case LITERAL_fa:
				case LITERAL_as:
				case LITERAL_case:
				case LITERAL_choose:
				case LITERAL_else:
				case LITERAL_embed:
				case 52:
				case LITERAL_ex:
				case LITERAL_fn:
				case LITERAL_if:
				case LITERAL_of:
				case LITERAL_project:
				case LITERAL_quotient:
				case LITERAL_relax:
				case LITERAL_restrict:
				case LITERAL_then:
				case LITERAL_where:
				{
					item=expressionKeyword();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
					break;
				}
				default:
				{
					if ( _cnt116>=1 ) { break _loop116; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt116++;
			} while (true);
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
		return expr;
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
				consumeUntil(_tokenSet_44);
			} else {
			  throw ex;
			}
		}
		return kind;
	}
	
	private final void sortQuantification() throws RecognitionException, TokenStreamException {
		
		
		String ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_sort);
			match(LITERAL_fa);
			match(LPAREN);
			ignore=name();
			{
			_loop113:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					ignore=name();
				}
				else {
					break _loop113;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_28);
			} else {
			  throw ex;
			}
		}
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
				consumeUntil(_tokenSet_38);
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
		"\"print\"",
		"\"spec\"",
		"\"endspec\"",
		"\"let\"",
		"\"in\"",
		"\"translate\"",
		"\"by\"",
		"\"qualifying\"",
		"\"diagram\"",
		"'{'",
		"','",
		"'}'",
		"\"colimit\"",
		"\"morphism\"",
		"\"generate\"",
		"\"obligations\"",
		"\"prove\"",
		"an inner-unit reference",
		"an identifier",
		"\"sort\"",
		"\"op\"",
		"'['",
		"']'",
		"\"using\"",
		"\"options\"",
		"\"import\"",
		"'.'",
		"'('",
		"')'",
		"NON_WORD_SYMBOL",
		"\"infixl\"",
		"\"infixr\"",
		"an integer",
		"\"def\"",
		"\"theorem\"",
		"\"axiom\"",
		"\"conjecture\"",
		"\"fa\"",
		"'_'",
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
		"\"fn\"",
		"\"if\"",
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
		"LATEX_COMMENT",
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
	
	private static final long _tokenSet_0_data_[] = { 8596165296L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 2070778166258L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { -9223369966076608526L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 2L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { 4194562L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { 2070778166256L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { -9223369966076608528L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 2071247978482L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { -9223237955491987470L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	private static final long _tokenSet_9_data_[] = { 2071243842882L, 0L };
	public static final BitSet _tokenSet_9 = new BitSet(_tokenSet_9_data_);
	private static final long _tokenSet_10_data_[] = { -9223369960240185358L, 0L };
	public static final BitSet _tokenSet_10 = new BitSet(_tokenSet_10_data_);
	private static final long _tokenSet_11_data_[] = { 9223369921698722736L, 0L };
	public static final BitSet _tokenSet_11 = new BitSet(_tokenSet_11_data_);
	private static final long _tokenSet_12_data_[] = { 2071245940034L, 0L };
	public static final BitSet _tokenSet_12 = new BitSet(_tokenSet_12_data_);
	private static final long _tokenSet_13_data_[] = { 2062146338816L, 0L };
	public static final BitSet _tokenSet_13 = new BitSet(_tokenSet_13_data_);
	private static final long _tokenSet_14_data_[] = { -9223237955494086670L, 0L };
	public static final BitSet _tokenSet_14 = new BitSet(_tokenSet_14_data_);
	private static final long _tokenSet_15_data_[] = { -9223237900731154446L, 0L };
	public static final BitSet _tokenSet_15 = new BitSet(_tokenSet_15_data_);
	private static final long _tokenSet_16_data_[] = { 132010114809856L, 0L };
	public static final BitSet _tokenSet_16 = new BitSet(_tokenSet_16_data_);
	private static final long _tokenSet_17_data_[] = { 134081358652738L, 0L };
	public static final BitSet _tokenSet_17 = new BitSet(_tokenSet_17_data_);
	private static final long _tokenSet_18_data_[] = { 2062146338880L, 0L };
	public static final BitSet _tokenSet_18 = new BitSet(_tokenSet_18_data_);
	private static final long _tokenSet_19_data_[] = { 1073743872L, 0L };
	public static final BitSet _tokenSet_19 = new BitSet(_tokenSet_19_data_);
	private static final long _tokenSet_20_data_[] = { 49152L, 0L };
	public static final BitSet _tokenSet_20 = new BitSet(_tokenSet_20_data_);
	private static final long _tokenSet_21_data_[] = { 2070845275120L, 0L };
	public static final BitSet _tokenSet_21 = new BitSet(_tokenSet_21_data_);
	private static final long _tokenSet_22_data_[] = { 256L, 0L };
	public static final BitSet _tokenSet_22 = new BitSet(_tokenSet_22_data_);
	private static final long _tokenSet_23_data_[] = { 9667878912L, 0L };
	public static final BitSet _tokenSet_23 = new BitSet(_tokenSet_23_data_);
	private static final long _tokenSet_24_data_[] = { 9667928064L, 0L };
	public static final BitSet _tokenSet_24 = new BitSet(_tokenSet_24_data_);
	private static final long _tokenSet_25_data_[] = { 8610914304L, 0L };
	public static final BitSet _tokenSet_25 = new BitSet(_tokenSet_25_data_);
	private static final long _tokenSet_26_data_[] = { 9223369922762039680L, 0L };
	public static final BitSet _tokenSet_26 = new BitSet(_tokenSet_26_data_);
	private static final long _tokenSet_27_data_[] = { -9223369963966775232L, 0L };
	public static final BitSet _tokenSet_27 = new BitSet(_tokenSet_27_data_);
	private static final long _tokenSet_28_data_[] = { 9223369921688297856L, 0L };
	public static final BitSet _tokenSet_28 = new BitSet(_tokenSet_28_data_);
	private static final long _tokenSet_29_data_[] = { 9223370060200993152L, 0L };
	public static final BitSet _tokenSet_29 = new BitSet(_tokenSet_29_data_);
	private static final long _tokenSet_30_data_[] = { -9223237954420344846L, 0L };
	public static final BitSet _tokenSet_30 = new BitSet(_tokenSet_30_data_);
	private static final long _tokenSet_31_data_[] = { 8589983744L, 0L };
	public static final BitSet _tokenSet_31 = new BitSet(_tokenSet_31_data_);
	private static final long _tokenSet_32_data_[] = { -9223371974573506560L, 0L };
	public static final BitSet _tokenSet_32 = new BitSet(_tokenSet_32_data_);
	private static final long _tokenSet_33_data_[] = { 9223371984908378560L, 0L };
	public static final BitSet _tokenSet_33 = new BitSet(_tokenSet_33_data_);
	private static final long _tokenSet_34_data_[] = { 9223371985313069042L, 0L };
	public static final BitSet _tokenSet_34 = new BitSet(_tokenSet_34_data_);
	private static final long _tokenSet_35_data_[] = { 4404589682688L, 0L };
	public static final BitSet _tokenSet_35 = new BitSet(_tokenSet_35_data_);
	private static final long _tokenSet_36_data_[] = { 9223371983834636736L, 0L };
	public static final BitSet _tokenSet_36 = new BitSet(_tokenSet_36_data_);
	private static final long _tokenSet_37_data_[] = { 2070736322624L, 0L };
	public static final BitSet _tokenSet_37 = new BitSet(_tokenSet_37_data_);
	private static final long _tokenSet_38_data_[] = { 9223371984237290946L, 0L };
	public static final BitSet _tokenSet_38 = new BitSet(_tokenSet_38_data_);
	private static final long _tokenSet_39_data_[] = { -9223369958092701710L, 0L };
	public static final BitSet _tokenSet_39 = new BitSet(_tokenSet_39_data_);
	private static final long _tokenSet_40_data_[] = { -9223369966118502336L, 0L };
	public static final BitSet _tokenSet_40 = new BitSet(_tokenSet_40_data_);
	private static final long _tokenSet_41_data_[] = { 8589934592L, 0L };
	public static final BitSet _tokenSet_41 = new BitSet(_tokenSet_41_data_);
	private static final long _tokenSet_42_data_[] = { -1480531520L, 0L };
	public static final BitSet _tokenSet_42 = new BitSet(_tokenSet_42_data_);
	private static final long _tokenSet_43_data_[] = { -9223372028264841216L, 0L };
	public static final BitSet _tokenSet_43 = new BitSet(_tokenSet_43_data_);
	private static final long _tokenSet_44_data_[] = { 4194304L, 0L };
	public static final BitSet _tokenSet_44 = new BitSet(_tokenSet_44_data_);
	
	}
