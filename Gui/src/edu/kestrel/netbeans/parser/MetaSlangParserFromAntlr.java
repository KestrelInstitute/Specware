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
			if ((_tokenSet_0.member(LA(1))) && (LA(2)==EQUALS||LA(2)==LITERAL_is) && (_tokenSet_1.member(LA(3)))) {
				scToplevelDecls();
			}
			else if ((_tokenSet_1.member(LA(1))) && (_tokenSet_2.member(LA(2))) && (_tokenSet_3.member(LA(3)))) {
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
			_loop6:
			do {
				if ((_tokenSet_0.member(LA(1)))) {
					scDecl();
				}
				else {
					break _loop6;
				}
				
			} while (true);
			}
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
	
	private final void scToplevelTerm() throws RecognitionException, TokenStreamException {
		
		
		Object ignore;
		
		
		try {      // for error handling
			ignore=scTerm(true, null);
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
	
	private final Object  scTerm(
		boolean isTopLevel, Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		Object term;
		
		
		term = null;
		ElementFactory.Item item = null;
		String unitID = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==SLASH||LA(1)==IDENTIFIER||LA(1)==DOTDOT) && (_tokenSet_5.member(LA(2))) && (_tokenSet_6.member(LA(3)))) {
				unitID=scUnitID(unitIdToken);
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2))) && (_tokenSet_9.member(LA(3)))) {
				item=scBasicTerm(unitIdToken);
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2))) && (_tokenSet_10.member(LA(3)))) {
				item=scSubstitute(unitIdToken);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			if ( inputState.guessing==0 ) {
				if (unitID != null) {
				term = unitID;
				} else if (item != null && isTopLevel) {
				term = item;
				builder.setParent(item, null);
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
		return term;
	}
	
	private final void scDecl() throws RecognitionException, TokenStreamException {
		
		
		String ignore;
		Object ignore2;
		Token unitIdToken = null;
		
		
		try {      // for error handling
			ignore=name();
			if ( inputState.guessing==0 ) {
				unitIdToken = LT(0);
			}
			equals();
			ignore2=scTerm(true, unitIdToken);
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
	}
	
	private final String  name() throws RecognitionException, TokenStreamException {
		String name;
		
		Token  star = null;
		Token  colon = null;
		Token  equals = null;
		Token  sym = null;
		Token  translate = null;
		Token  colimit = null;
		Token  diagram = null;
		Token  print = null;
		Token  snark = null;
		
		name = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case STAR:
			{
				star = LT(1);
				match(STAR);
				if ( inputState.guessing==0 ) {
					name=star.getText();
				}
				break;
			}
			case COLON:
			{
				colon = LT(1);
				match(COLON);
				if ( inputState.guessing==0 ) {
					name=colon.getText();
				}
				break;
			}
			case EQUALS:
			{
				equals = LT(1);
				match(EQUALS);
				if ( inputState.guessing==0 ) {
					name=equals.getText();
				}
				break;
			}
			case NON_WORD_SYMBOL:
			{
				sym = LT(1);
				match(NON_WORD_SYMBOL);
				if ( inputState.guessing==0 ) {
					name=sym.getText();
				}
				break;
			}
			case IDENTIFIER:
			{
				name=idName();
				break;
			}
			case LITERAL_translate:
			{
				translate = LT(1);
				match(LITERAL_translate);
				if ( inputState.guessing==0 ) {
					name="translate";
				}
				break;
			}
			case LITERAL_colimit:
			{
				colimit = LT(1);
				match(LITERAL_colimit);
				if ( inputState.guessing==0 ) {
					name="colimit";
				}
				break;
			}
			case LITERAL_diagram:
			{
				diagram = LT(1);
				match(LITERAL_diagram);
				if ( inputState.guessing==0 ) {
					name="diagram";
				}
				break;
			}
			case LITERAL_print:
			{
				print = LT(1);
				match(LITERAL_print);
				if ( inputState.guessing==0 ) {
					name="print";
				}
				break;
			}
			case LITERAL_Snark:
			{
				snark = LT(1);
				match(LITERAL_Snark);
				if ( inputState.guessing==0 ) {
					name="Snark";
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
		return name;
	}
	
	private final void equals() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case EQUALS:
			{
				match(EQUALS);
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
				consumeUntil(_tokenSet_14);
			} else {
			  throw ex;
			}
		}
	}
	
	private final String  scUnitID(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		String unitID;
		
		
		unitID = null;
		String partialPath = "";
		
		
		try {      // for error handling
			unitID=fullURIPath();
			if ( inputState.guessing==0 ) {
				UnitID.addInstance(unitID);
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
		return unitID;
	}
	
	private final ElementFactory.Item  scBasicTerm(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item item;
		
		
		item = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
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
			case LITERAL_morphism:
			{
				item=scMorphism(unitIdToken);
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
				if ((LA(1)==LITERAL_print) && (_tokenSet_1.member(LA(2)))) {
					item=scPrint(unitIdToken);
				}
				else if ((LA(1)==LITERAL_translate) && (_tokenSet_1.member(LA(2)))) {
					item=scTranslate(unitIdToken);
				}
				else if ((_tokenSet_0.member(LA(1))) && (LA(2)==LITERAL_qualifying)) {
					item=scQualify(unitIdToken);
				}
				else if ((LA(1)==LITERAL_diagram) && (LA(2)==LBRACE)) {
					item=scDiagram(unitIdToken);
				}
				else if ((LA(1)==LITERAL_colimit) && (_tokenSet_1.member(LA(2)))) {
					item=scColimit(unitIdToken);
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return item;
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return substitute;
	}
	
	private final ElementFactory.Item  scPrint(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item print;
		
		
		print = null;
		Object ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_print);
			ignore=scTerm(false, null);
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
		return print;
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
			_loop16:
			do {
				if ((_tokenSet_15.member(LA(1)))) {
					childItem=declaration();
					if ( inputState.guessing==0 ) {
						if (childItem != null) children.add(childItem);
					}
				}
				else {
					break _loop16;
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
				consumeUntil(_tokenSet_11);
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
		Object ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_let);
			{
			_loop19:
			do {
				if ((_tokenSet_0.member(LA(1)))) {
					scDecl();
				}
				else {
					break _loop19;
				}
				
			} while (true);
			}
			match(LITERAL_in);
			ignore=scTerm(false, unitIdToken);
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
		return let;
	}
	
	private final ElementFactory.Item  scTranslate(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item translate;
		
		
		translate = null;
		Object ignore = null;
		
		
		try {      // for error handling
			match(LITERAL_translate);
			ignore=scTerm(false, null);
			match(LITERAL_by);
			nameMap();
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
		return translate;
	}
	
	private final ElementFactory.Item  scQualify(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item qualify;
		
		
		qualify = null;
		String name = null;
		Object item = null;
		ElementFactory.Item childItem = null;
		Token headerEnd = null;
		List children = new LinkedList();
		
		
		try {      // for error handling
			name=qualifier();
			match(LITERAL_qualifying);
			item=scTerm(false, null);
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
		return qualify;
	}
	
	private final ElementFactory.Item  scDiagram(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item diagram;
		
		Token  begin = null;
		Token  end = null;
		
		diagram = null;
		ElementFactory.Item childItem = null;
		Token headerEnd = null;
		List children = new LinkedList();
		String name= (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_diagram);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			match(LBRACE);
			{
			switch ( LA(1)) {
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			{
				childItem=scDiagElem();
				if ( inputState.guessing==0 ) {
					if (childItem != null) children.add(childItem);
				}
				{
				_loop25:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						childItem=scDiagElem();
						if ( inputState.guessing==0 ) {
							if (childItem != null) children.add(childItem);
						}
					}
					else {
						break _loop25;
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
			end = LT(1);
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				diagram = builder.createDiagram(name);
				if (unitIdToken != null) {
				begin = unitIdToken;
				}
				builder.setParent(children, diagram);
				ParserUtil.setAllBounds(builder, diagram, begin, headerEnd, end);
				
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
		return diagram;
	}
	
	private final ElementFactory.Item  scColimit(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item colimit;
		
		Token  begin = null;
		
		colimit = null;
		ElementFactory.Item ignore = null;
		Token headerEnd = null;
		Object childItem = null;
		List children = new LinkedList();
		String name = (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_colimit);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			childItem=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (childItem instanceof ElementFactory.Item)
				children.add((ElementFactory.Item)childItem);
			}
			if ( inputState.guessing==0 ) {
				colimit = builder.createColimit(name);
				if (unitIdToken != null) {
				begin = unitIdToken;
				}
				builder.setParent(children, colimit);
				ParserUtil.setAllBounds(builder, colimit, begin, headerEnd, LT(0));
				
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
		return colimit;
	}
	
	private final ElementFactory.Item  scMorphism(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item morphism;
		
		Token  begin = null;
		Token  end = null;
		
		morphism = null;
		Object item = null;
		String src = null;
		String dest = null;
		ElementFactory.Item ignore = null;
		Token headerEnd = null;
		List children = new LinkedList();
		String name = (unitIdToken == null) ? "" : unitIdToken.getText();
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_morphism);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			item=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (item instanceof String) src = (String)item;
			}
			match(ARROW);
			item=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (item instanceof String) dest = (String)item;
			}
			match(LBRACE);
			nameMap();
			end = LT(1);
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				if (src != null && dest != null) {
				morphism = builder.createMorphism(name, src, dest);
				if (unitIdToken != null) {
				begin = unitIdToken;
				}
				//builder.setParent(children, morphism);
				ParserUtil.setAllBounds(builder, morphism, begin, headerEnd, end);
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
		return morphism;
	}
	
	private final ElementFactory.Item  scGenerate(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item generate;
		
		Token  begin = null;
		
		generate = null;
		String genName = null;
		String fileName = null;
		Object ignore = null;
		Token headerEnd = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_generate);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			genName=name();
			ignore=scTerm(false, null);
			{
			if ((LA(1)==LITERAL_in) && (LA(2)==STRING_LITERAL) && (_tokenSet_11.member(LA(3)))) {
				match(LITERAL_in);
				match(STRING_LITERAL);
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
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
				consumeUntil(_tokenSet_11);
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
		Object ignore=null;
		Token headerEnd = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_obligations);
			if ( inputState.guessing==0 ) {
				headerEnd = begin;
			}
			ignore=scTerm(false, null);
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
		return obligations;
	}
	
	private final ElementFactory.Item  scProve(
		Token unitIdToken
	) throws RecognitionException, TokenStreamException {
		ElementFactory.Item proof;
		
		Token  begin = null;
		
		proof = null;
		Object item = null;
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
			match(LITERAL_in);
			item=scTerm(false, null);
			{
			if ((LA(1)==LITERAL_using) && (_tokenSet_18.member(LA(2))) && (_tokenSet_11.member(LA(3)))) {
				childItem=proverAssertions();
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			if ((LA(1)==LITERAL_options) && (_tokenSet_19.member(LA(2))) && (_tokenSet_20.member(LA(3)))) {
				childItem=proverOptions();
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return proof;
	}
	
	private final String  fullURIPath() throws RecognitionException, TokenStreamException {
		String path;
		
		Token  slash = null;
		Token  ref = null;
		
		path = "";
		String item = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case SLASH:
			{
				slash = LT(1);
				match(SLASH);
				item=partialURIPath();
				if ( inputState.guessing==0 ) {
					path = slash.getText() + item;
				}
				break;
			}
			case IDENTIFIER:
			case DOTDOT:
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
			case LITERAL_print:
			case LITERAL_endspec:
			case LITERAL_in:
			case LITERAL_translate:
			case LITERAL_by:
			case LITERAL_diagram:
			case LBRACE:
			case COMMA:
			case RBRACE:
			case LITERAL_colimit:
			case ARROW:
			case IDENTIFIER:
			case LITERAL_sort:
			case LITERAL_op:
			case COLON:
			case LBRACKET:
			case RBRACKET:
			case LITERAL_using:
			case LITERAL_options:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
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
		return path;
	}
	
	private final void scSubstituteTermList() throws RecognitionException, TokenStreamException {
		
		
		Object ignore = null;
		
		
		try {      // for error handling
			match(LBRACKET);
			ignore=scTerm(false, null);
			match(RBRACKET);
			{
			_loop56:
			do {
				if ((LA(1)==LBRACKET) && (_tokenSet_1.member(LA(2))) && (_tokenSet_21.member(LA(3)))) {
					scSubstituteTermList();
				}
				else {
					break _loop56;
				}
				
			} while (true);
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
				consumeUntil(_tokenSet_22);
			} else {
			  throw ex;
			}
		}
		return item;
	}
	
	private final String  nameMap() throws RecognitionException, TokenStreamException {
		String nameMap;
		
		Token  comma = null;
		
		nameMap = null;
		String text = null;
		
		
		try {      // for error handling
			{
			if ((_tokenSet_23.member(LA(1))) && (_tokenSet_24.member(LA(2))) && (_tokenSet_25.member(LA(3)))) {
				text=nameMapItem();
				if ( inputState.guessing==0 ) {
					nameMap = nameMap + text;
				}
				{
				_loop43:
				do {
					if ((LA(1)==COMMA) && (_tokenSet_23.member(LA(2))) && (_tokenSet_24.member(LA(3)))) {
						comma = LT(1);
						match(COMMA);
						text=nameMapItem();
						if ( inputState.guessing==0 ) {
							nameMap = nameMap + comma.getText() + text;
						}
					}
					else {
						break _loop43;
					}
					
				} while (true);
				}
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return nameMap;
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
				consumeUntil(_tokenSet_26);
			} else {
			  throw ex;
			}
		}
		return qlf;
	}
	
	private final ElementFactory.Item  scDiagElem() throws RecognitionException, TokenStreamException {
		ElementFactory.Item diagElem;
		
		
		diagElem = null;
		
		
		try {      // for error handling
			if ((_tokenSet_0.member(LA(1))) && (LA(2)==NON_WORD_SYMBOL)) {
				diagElem=scDiagNode();
			}
			else if ((_tokenSet_0.member(LA(1))) && (LA(2)==COLON)) {
				diagElem=scDiagEdge();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
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
		return diagElem;
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
				consumeUntil(_tokenSet_28);
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
			int _cnt60=0;
			_loop60:
			do {
				if ((_tokenSet_0.member(LA(1))) && (_tokenSet_11.member(LA(2))) && (_tokenSet_16.member(LA(3)))) {
					anAssertion=name();
				}
				else if ((LA(1)==COMMA) && (_tokenSet_0.member(LA(2))) && (_tokenSet_11.member(LA(3)))) {
					match(COMMA);
					anAssertion=name();
				}
				else {
					if ( _cnt60>=1 ) { break _loop60; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt60++;
			} while (true);
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
		return assertionsItem;
	}
	
	private final ElementFactory.Item  proverOptions() throws RecognitionException, TokenStreamException {
		ElementFactory.Item optionsItem;
		
		
		optionsItem = null;
		String anOption = null;
		
		
		try {      // for error handling
			match(LITERAL_options);
			{
			int _cnt63=0;
			_loop63:
			do {
				if ((_tokenSet_19.member(LA(1)))) {
					anOption=literal();
				}
				else {
					if ( _cnt63>=1 ) { break _loop63; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt63++;
			} while (true);
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
		return optionsItem;
	}
	
	private final String  partialURIPath() throws RecognitionException, TokenStreamException {
		String path;
		
		Token  id = null;
		Token  dotdot = null;
		Token  slash = null;
		
		path = "";
		String item = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case IDENTIFIER:
			{
				id = LT(1);
				match(IDENTIFIER);
				if ( inputState.guessing==0 ) {
					path = path + id.getText();
				}
				break;
			}
			case DOTDOT:
			{
				dotdot = LT(1);
				match(DOTDOT);
				if ( inputState.guessing==0 ) {
					path = path + dotdot.getText();
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
			case SLASH:
			{
				slash = LT(1);
				match(SLASH);
				item=partialURIPath();
				if ( inputState.guessing==0 ) {
					path = path + slash.getText() + item;
				}
				break;
			}
			case EOF:
			case LITERAL_print:
			case LITERAL_endspec:
			case LITERAL_in:
			case LITERAL_translate:
			case LITERAL_by:
			case LITERAL_diagram:
			case LBRACE:
			case COMMA:
			case RBRACE:
			case LITERAL_colimit:
			case ARROW:
			case INNER_UNIT_REF:
			case IDENTIFIER:
			case LITERAL_sort:
			case LITERAL_op:
			case COLON:
			case LBRACKET:
			case RBRACKET:
			case LITERAL_using:
			case LITERAL_options:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_29);
			} else {
			  throw ex;
			}
		}
		return path;
	}
	
	private final String  nameMapItem() throws RecognitionException, TokenStreamException {
		String mapItem;
		
		
		mapItem = "";
		
		
		try {      // for error handling
			if ((_tokenSet_30.member(LA(1))) && (_tokenSet_24.member(LA(2))) && (_tokenSet_31.member(LA(3)))) {
				mapItem=sortNameMapItem();
			}
			else if ((_tokenSet_32.member(LA(1))) && (_tokenSet_24.member(LA(2))) && (_tokenSet_25.member(LA(3)))) {
				mapItem=opNameMapItem();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
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
		return mapItem;
	}
	
	private final String  sortNameMapItem() throws RecognitionException, TokenStreamException {
		String mapItem;
		
		
		mapItem = "";
		String text = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_sort:
			{
				match(LITERAL_sort);
				if ( inputState.guessing==0 ) {
					mapItem = "sort ";
				}
				break;
			}
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			text=qualifiableSortNames();
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + text;
			}
			nonWordSymbol("+->");
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + " +-> ";
			}
			text=qualifiableSortNames();
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + text;
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
		return mapItem;
	}
	
	private final String  opNameMapItem() throws RecognitionException, TokenStreamException {
		String mapItem;
		
		
		mapItem = "";
		String text = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_op:
			{
				match(LITERAL_op);
				if ( inputState.guessing==0 ) {
					mapItem = "op ";
				}
				break;
			}
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			text=annotableQualifiableName();
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + text;
			}
			nonWordSymbol("+->");
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + " +-> ";
			}
			text=annotableQualifiableName();
			if ( inputState.guessing==0 ) {
				mapItem = mapItem + text;
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
		return mapItem;
	}
	
	private final String  qualifiableSortNames() throws RecognitionException, TokenStreamException {
		String sortName;
		
		
		sortName = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
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
				_loop75:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableSortName();
						if ( inputState.guessing==0 ) {
							sortName = sortName + ", " + member;
						}
					}
					else {
						break _loop75;
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
				consumeUntil(_tokenSet_33);
			} else {
			  throw ex;
			}
		}
		return sortName;
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
	
	private final String  annotableQualifiableName() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = "";
		String text = null;
		
		
		try {      // for error handling
			text=qualifiableOpNames();
			if ( inputState.guessing==0 ) {
				name = text;
			}
			{
			if ((LA(1)==NON_WORD_SYMBOL) && (_tokenSet_34.member(LA(2))) && (_tokenSet_35.member(LA(3)))) {
				nonWordSymbol(":");
				if ( inputState.guessing==0 ) {
					name = name + " : ";
				}
				text=sort();
				if ( inputState.guessing==0 ) {
					name = name + text;
				}
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_16.member(LA(2))) && (_tokenSet_17.member(LA(3)))) {
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
				consumeUntil(_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	private final String  qualifiableOpNames() throws RecognitionException, TokenStreamException {
		String opName;
		
		
		opName = null;
		String member = null;
		String qlf = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
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
				_loop87:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						member=qualifiableOpName();
						if ( inputState.guessing==0 ) {
							opName = opName + ", " + member;
						}
					}
					else {
						break _loop87;
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
				consumeUntil(_tokenSet_36);
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
				if ((_tokenSet_0.member(LA(1))) && (_tokenSet_37.member(LA(2))) && (_tokenSet_38.member(LA(3)))) {
					text=qualifiableRef();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
				}
				else if ((_tokenSet_19.member(LA(1))) && (_tokenSet_39.member(LA(2))) && (_tokenSet_38.member(LA(3)))) {
					text=literal();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
				}
				else if ((_tokenSet_40.member(LA(1))) && (_tokenSet_39.member(LA(2))) && (_tokenSet_38.member(LA(3)))) {
					text=specialSymbol();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
				}
				else if ((_tokenSet_41.member(LA(1))) && (_tokenSet_39.member(LA(2))) && (_tokenSet_38.member(LA(3)))) {
					text=expressionKeyword();
					if ( inputState.guessing==0 ) {
						sort = sort + text;
					}
				}
				else {
					if ( _cnt102>=1 ) { break _loop102; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt102++;
			} while (true);
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
		return sort;
	}
	
	private final ElementFactory.Item  scDiagNode() throws RecognitionException, TokenStreamException {
		ElementFactory.Item diagNode;
		
		
		diagNode = null;
		String nodeName = "";
		String partialName = null;
		Object item = null;
		ElementFactory.Item term = null;
		Token headerEnd = null;
		Token begin = null;
		
		
		try {      // for error handling
			partialName=name();
			if ( inputState.guessing==0 ) {
				headerEnd = begin = LT(0);
				nodeName = partialName;
			}
			nonWordSymbol("+->");
			if ( inputState.guessing==0 ) {
				nodeName = nodeName + " +-> ";
			}
			item=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (item instanceof ElementFactory.Item)
				nodeName = nodeName + ((ElementFactory.Item)item).toString();
				else if (item instanceof String)
				nodeName = nodeName + (String)item;
			}
			if ( inputState.guessing==0 ) {
				diagNode = builder.createDiagElem(nodeName);
				ParserUtil.setAllBounds(builder, diagNode, begin, headerEnd, LT(0));
				
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
		return diagNode;
	}
	
	private final ElementFactory.Item  scDiagEdge() throws RecognitionException, TokenStreamException {
		ElementFactory.Item diagEdge;
		
		Token  colon = null;
		Token  arrow = null;
		
		diagEdge = null;
		String edgeName = "";
		String partialName = null;
		Object item = null;
		ElementFactory.Item term = null;
		Token headerEnd = null;
		Token begin = null;
		
		
		try {      // for error handling
			partialName=name();
			if ( inputState.guessing==0 ) {
				headerEnd = begin = LT(0);
				edgeName = partialName;
			}
			colon = LT(1);
			match(COLON);
			if ( inputState.guessing==0 ) {
				edgeName = edgeName + " " + colon.getText() + " ";
			}
			partialName=name();
			if ( inputState.guessing==0 ) {
				edgeName = edgeName + partialName;
			}
			arrow = LT(1);
			match(ARROW);
			if ( inputState.guessing==0 ) {
				edgeName = edgeName + " " + arrow.getText() + " ";
			}
			partialName=name();
			if ( inputState.guessing==0 ) {
				edgeName = edgeName + partialName;
			}
			nonWordSymbol("+->");
			if ( inputState.guessing==0 ) {
				edgeName = edgeName + " +-> ";
			}
			item=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (item instanceof ElementFactory.Item) 
				edgeName = edgeName + ((ElementFactory.Item)item).toString();
				else if (item instanceof String)
				edgeName = edgeName + (String)item;
			}
			if ( inputState.guessing==0 ) {
				diagEdge = builder.createDiagElem(edgeName);
				ParserUtil.setAllBounds(builder, diagEdge, begin, headerEnd, LT(0));
				
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
		return diagEdge;
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
				consumeUntil(_tokenSet_39);
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
				consumeUntil(_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	private final String  nonKeywordName() throws RecognitionException, TokenStreamException {
		String name;
		
		
		name = null;
		
		
		try {      // for error handling
			name=idName();
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
		return name;
	}
	
	private final ElementFactory.Item  importDeclaration() throws RecognitionException, TokenStreamException {
		ElementFactory.Item importItem;
		
		Token  begin = null;
		
		importItem = null;
		Object item = null;
		ElementFactory.Item term = null;
		String uri = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_import);
			item=scTerm(false, null);
			if ( inputState.guessing==0 ) {
				if (item instanceof ElementFactory.Item) {
				importItem = builder.createImport(((ElementFactory.Item)item).toString(), 
				(ElementFactory.Item)item);
				} else if (item instanceof String) {
				importItem = builder.createImport((String)item, null);
				}
				if (importItem != null) {
				ParserUtil.setBounds(builder, importItem, begin, LT(0));
				}
				
			}
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
				params=formalSortParameters();
				{
				switch ( LA(1)) {
				case EQUALS:
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
			case EQUALS:
			case LITERAL_import:
			case LITERAL_def:
			case LITERAL_theorem:
			case LITERAL_axiom:
			case LITERAL_conjecture:
			case LITERAL_is:
			{
				{
				switch ( LA(1)) {
				case EQUALS:
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
				consumeUntil(_tokenSet_22);
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
			case COLON:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(COLON);
			sort=sortScheme();
			if ( inputState.guessing==0 ) {
				op = builder.createOp(name, sort);
				ParserUtil.setBounds(builder, op, begin, LT(0));
				
			}
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
				consumeUntil(_tokenSet_22);
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
				_loop82:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param=idName();
						if ( inputState.guessing==0 ) {
							paramList.add(param);
						}
					}
					else {
						break _loop82;
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
				consumeUntil(_tokenSet_44);
			} else {
			  throw ex;
			}
		}
		return params;
	}
	
	private final String  qualifiableSortName() throws RecognitionException, TokenStreamException {
		String sortName;
		
		
		sortName = null;
		
		
		try {      // for error handling
			if ((LA(1)==IDENTIFIER) && (_tokenSet_33.member(LA(2)))) {
				sortName=unqualifiedSortName();
			}
			else if ((_tokenSet_0.member(LA(1))) && (LA(2)==DOT)) {
				sortName=qualifiedSortName();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_33);
			} else {
			  throw ex;
			}
		}
		return sortName;
	}
	
	private final String  unqualifiedSortName() throws RecognitionException, TokenStreamException {
		String sortName;
		
		
		sortName = null;
		
		
		try {      // for error handling
			sortName=nonKeywordName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_33);
			} else {
			  throw ex;
			}
		}
		return sortName;
	}
	
	private final String  qualifiedSortName() throws RecognitionException, TokenStreamException {
		String sortName;
		
		Token  dot = null;
		
		sortName = null;
		String text = null;
		
		
		try {      // for error handling
			text=qualifier();
			if ( inputState.guessing==0 ) {
				sortName = text;
			}
			dot = LT(1);
			match(DOT);
			if ( inputState.guessing==0 ) {
				sortName = sortName + ".";
			}
			text=nonKeywordName();
			if ( inputState.guessing==0 ) {
				sortName = sortName + text;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_33);
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
				consumeUntil(_tokenSet_45);
			} else {
			  throw ex;
			}
		}
	}
	
	private final String  sortScheme() throws RecognitionException, TokenStreamException {
		String sortScheme;
		
		
		sortScheme = "";
		String text = null;
		
		
		try {      // for error handling
			{
			if ((LA(1)==LITERAL_fa) && (LA(2)==LPAREN) && (LA(3)==IDENTIFIER)) {
				text=sortVariableBinder();
				if ( inputState.guessing==0 ) {
					sortScheme = sortScheme + text;
				}
			}
			else if ((_tokenSet_34.member(LA(1))) && (_tokenSet_46.member(LA(2))) && (_tokenSet_47.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			text=sort();
			if ( inputState.guessing==0 ) {
				sortScheme = sortScheme + text;
			}
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
		return sortScheme;
	}
	
	private final String  qualifiableOpName() throws RecognitionException, TokenStreamException {
		String opName;
		
		
		opName = null;
		String qlf = null;
		
		
		try {      // for error handling
			{
			if ((_tokenSet_0.member(LA(1))) && (LA(2)==DOT)) {
				qlf=qualifier();
				match(DOT);
			}
			else if ((_tokenSet_0.member(LA(1))) && (_tokenSet_48.member(LA(2)))) {
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
				consumeUntil(_tokenSet_48);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  opName() throws RecognitionException, TokenStreamException {
		String opName;
		
		
		opName = null;
		
		
		try {      // for error handling
			opName=name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_48);
			} else {
			  throw ex;
			}
		}
		return opName;
	}
	
	private final String  sortVariableBinder() throws RecognitionException, TokenStreamException {
		String binder;
		
		
		binder = "";
		String text = null;
		
		
		try {      // for error handling
			match(LITERAL_fa);
			text=localSortVariableList();
			if ( inputState.guessing==0 ) {
				binder = "fa " + text;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_34);
			} else {
			  throw ex;
			}
		}
		return binder;
	}
	
	private final String  localSortVariableList() throws RecognitionException, TokenStreamException {
		String list;
		
		Token  lparen = null;
		Token  comma = null;
		Token  rparen = null;
		
		list = "";
		String text = null;
		
		
		try {      // for error handling
			lparen = LT(1);
			match(LPAREN);
			if ( inputState.guessing==0 ) {
				list = lparen.getText();
			}
			text=localSortVariable();
			if ( inputState.guessing==0 ) {
				list = list + text;
			}
			{
			_loop98:
			do {
				if ((LA(1)==COMMA)) {
					comma = LT(1);
					match(COMMA);
					text=localSortVariable();
					if ( inputState.guessing==0 ) {
						list = list + comma.getText() + text;
					}
				}
				else {
					break _loop98;
				}
				
			} while (true);
			}
			rparen = LT(1);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				list = list + rparen.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_34);
			} else {
			  throw ex;
			}
		}
		return list;
	}
	
	private final String  localSortVariable() throws RecognitionException, TokenStreamException {
		String var;
		
		
		var = "";
		
		
		try {      // for error handling
			var=nonKeywordName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_49);
			} else {
			  throw ex;
			}
		}
		return var;
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
				consumeUntil(_tokenSet_39);
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
			case STAR:
			{
				match(STAR);
				if ( inputState.guessing==0 ) {
					text = "*";
				}
				break;
			}
			case ARROW:
			{
				match(ARROW);
				if ( inputState.guessing==0 ) {
					text = "->";
				}
				break;
			}
			case COLON:
			{
				match(COLON);
				if ( inputState.guessing==0 ) {
					text = ":";
				}
				break;
			}
			case VERTICALBAR:
			{
				match(VERTICALBAR);
				if ( inputState.guessing==0 ) {
					text = "|";
				}
				break;
			}
			case COLONCOLON:
			{
				match(COLONCOLON);
				if ( inputState.guessing==0 ) {
					text = "::";
				}
				break;
			}
			case SEMICOLON:
			{
				match(SEMICOLON);
				if ( inputState.guessing==0 ) {
					text = ";";
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
				consumeUntil(_tokenSet_39);
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
			case 63:
			{
				match(63);
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
				boolean synPredMatched152 = false;
				if (((LA(1)==LITERAL_let) && (LA(2)==LITERAL_def) && (_tokenSet_39.member(LA(3))))) {
					int _m152 = mark();
					synPredMatched152 = true;
					inputState.guessing++;
					try {
						{
						match(LITERAL_let);
						match(LITERAL_def);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched152 = false;
					}
					rewind(_m152);
					inputState.guessing--;
				}
				if ( synPredMatched152 ) {
					match(LITERAL_let);
					match(LITERAL_def);
					if ( inputState.guessing==0 ) {
						text = "let def";
					}
				}
				else if ((LA(1)==LITERAL_let) && (_tokenSet_39.member(LA(2))) && (_tokenSet_38.member(LA(3)))) {
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
				consumeUntil(_tokenSet_39);
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
		String ignore = null;
		
		
		try {      // for error handling
			begin = LT(1);
			match(LITERAL_def);
			{
			switch ( LA(1)) {
			case LITERAL_fa:
			{
				ignore=sortVariableBinder();
				break;
			}
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case LITERAL_colimit:
			case IDENTIFIER:
			case COLON:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			name=qualifiableOpNames();
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				sort();
				break;
			}
			case LBRACE:
			case STRING_LITERAL:
			case IDENTIFIER:
			case LBRACKET:
			case EQUALS:
			case LPAREN:
			case NAT_LITERAL:
			case UBAR:
			case CHAR_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_is:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			if ((LA(1)==EQUALS||LA(1)==LITERAL_is) && (_tokenSet_34.member(LA(2))) && (_tokenSet_46.member(LA(3)))) {
				equals();
			}
			else if ((_tokenSet_50.member(LA(1))) && (_tokenSet_51.member(LA(2))) && (_tokenSet_52.member(LA(3)))) {
				params=formalOpParameters();
				equals();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
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
				consumeUntil(_tokenSet_22);
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
		String text = null;
		String sortQuant = null;
		
		
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
				sortQuant=sortQuantification();
				if ( inputState.guessing==0 ) {
					expr = sortQuant;
				}
				break;
			}
			case LITERAL_print:
			case LITERAL_let:
			case LITERAL_in:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case COMMA:
			case RBRACE:
			case LITERAL_colimit:
			case ARROW:
			case STRING_LITERAL:
			case IDENTIFIER:
			case COLON:
			case LBRACKET:
			case RBRACKET:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			case LPAREN:
			case RPAREN:
			case NAT_LITERAL:
			case LITERAL_fa:
			case COLONCOLON:
			case LITERAL_as:
			case UBAR:
			case LITERAL_quotient:
			case VERTICALBAR:
			case SEMICOLON:
			case CHAR_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_case:
			case LITERAL_choose:
			case LITERAL_else:
			case LITERAL_embed:
			case 63:
			case LITERAL_ex:
			case LITERAL_fn:
			case LITERAL_if:
			case LITERAL_of:
			case LITERAL_project:
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
			text=expression();
			if ( inputState.guessing==0 ) {
				expr = expr + " " + text;
			}
			if ( inputState.guessing==0 ) {
				claimDef = builder.createClaim(name, kind, expr);
				ParserUtil.setBounds(builder, claimDef, begin, LT(0));
				
			}
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
		return claimDef;
	}
	
	private final String[]  formalOpParameters() throws RecognitionException, TokenStreamException {
		String[] params;
		
		
		params = null;
		List paramList = new LinkedList();
		String pattern = null;
		
		
		try {      // for error handling
			{
			_loop116:
			do {
				if ((_tokenSet_53.member(LA(1)))) {
					pattern=closedPattern();
					if ( inputState.guessing==0 ) {
						paramList.add(pattern);
					}
				}
				else {
					break _loop116;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				params = (String[]) paramList.toArray(new String[]{});
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_54);
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
			int _cnt145=0;
			_loop145:
			do {
				if ((_tokenSet_0.member(LA(1))) && (_tokenSet_46.member(LA(2))) && (_tokenSet_47.member(LA(3)))) {
					item=qualifiableRef();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
				}
				else if ((_tokenSet_19.member(LA(1))) && (_tokenSet_55.member(LA(2))) && (_tokenSet_47.member(LA(3)))) {
					item=literal();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
				}
				else if ((_tokenSet_40.member(LA(1))) && (_tokenSet_55.member(LA(2))) && (_tokenSet_47.member(LA(3)))) {
					item=specialSymbol();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
				}
				else if ((_tokenSet_41.member(LA(1))) && (_tokenSet_55.member(LA(2))) && (_tokenSet_47.member(LA(3)))) {
					item=expressionKeyword();
					if ( inputState.guessing==0 ) {
						expr = expr + item + " ";
					}
				}
				else {
					if ( _cnt145>=1 ) { break _loop145; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt145++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_56);
			} else {
			  throw ex;
			}
		}
		return expr;
	}
	
	private final String  claimKind() throws RecognitionException, TokenStreamException {
		String kind;
		
		
		kind = "";
		
		
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
				consumeUntil(_tokenSet_57);
			} else {
			  throw ex;
			}
		}
		return kind;
	}
	
	private final String  sortQuantification() throws RecognitionException, TokenStreamException {
		String sortQuant;
		
		Token  lparen = null;
		Token  comma = null;
		Token  rparen = null;
		
		sortQuant = "";
		String text = null;
		
		
		try {      // for error handling
			match(LITERAL_sort);
			match(LITERAL_fa);
			if ( inputState.guessing==0 ) {
				sortQuant = "sort fa ";
			}
			lparen = LT(1);
			match(LPAREN);
			if ( inputState.guessing==0 ) {
				sortQuant = sortQuant + lparen.getText();
			}
			text=name();
			if ( inputState.guessing==0 ) {
				sortQuant = sortQuant + text;
			}
			{
			_loop113:
			do {
				if ((LA(1)==COMMA)) {
					comma = LT(1);
					match(COMMA);
					text=name();
					if ( inputState.guessing==0 ) {
						sortQuant = sortQuant + comma.getText() + text;
					}
				}
				else {
					break _loop113;
				}
				
			} while (true);
			}
			rparen = LT(1);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				sortQuant = sortQuant + rparen.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_34);
			} else {
			  throw ex;
			}
		}
		return sortQuant;
	}
	
	private final String  closedPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			{
				pattern=parenthesizedPattern();
				break;
			}
			case IDENTIFIER:
			{
				pattern=variablePattern();
				break;
			}
			case STRING_LITERAL:
			case NAT_LITERAL:
			case CHAR_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			{
				pattern=literalPattern();
				break;
			}
			case LBRACKET:
			{
				pattern=listPattern();
				break;
			}
			case LBRACE:
			{
				pattern=recordPattern();
				break;
			}
			case UBAR:
			{
				pattern=wildcardPattern();
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
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  pattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			if ((_tokenSet_59.member(LA(1))) && (_tokenSet_34.member(LA(2))) && (_tokenSet_60.member(LA(3)))) {
				pattern=basicPattern();
			}
			else if ((_tokenSet_59.member(LA(1))) && (_tokenSet_34.member(LA(2))) && (_tokenSet_61.member(LA(3)))) {
				pattern=annotatedPattern();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_62);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  basicPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		
		
		try {      // for error handling
			pattern=tightPattern();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_63);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  annotatedPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  colon = null;
		
		pattern = "";
		String sortStr = null;
		
		
		try {      // for error handling
			pattern=basicPattern();
			colon = LT(1);
			match(COLON);
			if ( inputState.guessing==0 ) {
				pattern = pattern + colon.getText();
			}
			sortStr=sort();
			if ( inputState.guessing==0 ) {
				pattern = pattern + sortStr;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_62);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  tightPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  cc = null;
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			if ((LA(1)==IDENTIFIER) && (LA(2)==LITERAL_as)) {
				pattern=aliasedPattern();
			}
			else if ((LA(1)==LITERAL_quotient)) {
				pattern=quotientPattern();
			}
			else if ((_tokenSet_64.member(LA(1))) && (_tokenSet_65.member(LA(2)))) {
				{
				if ((_tokenSet_0.member(LA(1))) && (_tokenSet_53.member(LA(2))) && (_tokenSet_65.member(LA(3)))) {
					text=name();
					if ( inputState.guessing==0 ) {
						pattern = text;
					}
				}
				else if ((_tokenSet_53.member(LA(1))) && (_tokenSet_65.member(LA(2))) && (_tokenSet_66.member(LA(3)))) {
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				text=closedPattern();
				if ( inputState.guessing==0 ) {
					pattern = pattern + text;
				}
				{
				switch ( LA(1)) {
				case COLONCOLON:
				{
					cc = LT(1);
					match(COLONCOLON);
					text=tightPattern();
					if ( inputState.guessing==0 ) {
						pattern = pattern + cc.getText() + text;
					}
					break;
				}
				case COMMA:
				case RBRACE:
				case COLON:
				case RBRACKET:
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
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_63);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  aliasedPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			text=variablePattern();
			if ( inputState.guessing==0 ) {
				pattern = text;
			}
			match(LITERAL_as);
			text=tightPattern();
			if ( inputState.guessing==0 ) {
				pattern = pattern + "as" + text;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_63);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  quotientPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			match(LITERAL_quotient);
			text=expression();
			if ( inputState.guessing==0 ) {
				pattern = "quotient " + text;
			}
			text=tightPattern();
			if ( inputState.guessing==0 ) {
				pattern = pattern + " " + text;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_63);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  variablePattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		
		
		try {      // for error handling
			pattern=nonKeywordName();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_67);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  embedPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			text=name();
			if ( inputState.guessing==0 ) {
				pattern = text;
			}
			text=closedPattern();
			if ( inputState.guessing==0 ) {
				pattern = pattern + text;
			}
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
		return pattern;
	}
	
	private final String  parenthesizedPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  lparen = null;
		Token  comma = null;
		Token  rparen = null;
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			lparen = LT(1);
			match(LPAREN);
			if ( inputState.guessing==0 ) {
				pattern = lparen.getText();
			}
			{
			switch ( LA(1)) {
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case LITERAL_colimit:
			case STRING_LITERAL:
			case IDENTIFIER:
			case COLON:
			case LBRACKET:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			case LPAREN:
			case NAT_LITERAL:
			case UBAR:
			case LITERAL_quotient:
			case CHAR_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			{
				text=pattern();
				if ( inputState.guessing==0 ) {
					pattern = pattern + text;
				}
				{
				_loop136:
				do {
					if ((LA(1)==COMMA)) {
						comma = LT(1);
						match(COMMA);
						text=pattern();
						if ( inputState.guessing==0 ) {
							pattern = pattern + comma.getText() + text;
						}
					}
					else {
						break _loop136;
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
			rparen = LT(1);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				pattern = pattern + rparen.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  literalPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		
		
		try {      // for error handling
			pattern=literal();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  listPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  lbracket = null;
		Token  comma = null;
		Token  rbracket = null;
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			lbracket = LT(1);
			match(LBRACKET);
			if ( inputState.guessing==0 ) {
				pattern = lbracket.getText();
			}
			{
			switch ( LA(1)) {
			case LITERAL_print:
			case LITERAL_translate:
			case LITERAL_diagram:
			case LBRACE:
			case LITERAL_colimit:
			case STRING_LITERAL:
			case IDENTIFIER:
			case COLON:
			case LBRACKET:
			case STAR:
			case EQUALS:
			case NON_WORD_SYMBOL:
			case LITERAL_Snark:
			case LPAREN:
			case NAT_LITERAL:
			case UBAR:
			case LITERAL_quotient:
			case CHAR_LITERAL:
			case LITERAL_true:
			case LITERAL_false:
			{
				text=pattern();
				if ( inputState.guessing==0 ) {
					pattern = pattern + text;
				}
				{
				_loop132:
				do {
					if ((LA(1)==COMMA)) {
						comma = LT(1);
						match(COMMA);
						text=pattern();
						if ( inputState.guessing==0 ) {
							pattern = pattern + comma.getText() + text;
						}
					}
					else {
						break _loop132;
					}
					
				} while (true);
				}
				break;
			}
			case RBRACKET:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			rbracket = LT(1);
			match(RBRACKET);
			if ( inputState.guessing==0 ) {
				pattern = pattern + rbracket.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  recordPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  lbrace = null;
		Token  comma = null;
		Token  rbrace = null;
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			lbrace = LT(1);
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				pattern = lbrace.getText();
			}
			text=fieldPattern();
			if ( inputState.guessing==0 ) {
				pattern = pattern + text;
			}
			{
			_loop139:
			do {
				if ((LA(1)==COMMA)) {
					comma = LT(1);
					match(COMMA);
					text=fieldPattern();
					if ( inputState.guessing==0 ) {
						pattern = pattern + comma.getText() + text;
					}
				}
				else {
					break _loop139;
				}
				
			} while (true);
			}
			rbrace = LT(1);
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				pattern = pattern + rbrace.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  wildcardPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		Token  ubar = null;
		
		pattern = "";
		
		
		try {      // for error handling
			ubar = LT(1);
			match(UBAR);
			if ( inputState.guessing==0 ) {
				pattern = ubar.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				consume();
				consumeUntil(_tokenSet_58);
			} else {
			  throw ex;
			}
		}
		return pattern;
	}
	
	private final String  fieldPattern() throws RecognitionException, TokenStreamException {
		String pattern;
		
		
		pattern = "";
		String text = null;
		
		
		try {      // for error handling
			text=name();
			if ( inputState.guessing==0 ) {
				pattern = text;
			}
			{
			switch ( LA(1)) {
			case EQUALS:
			case LITERAL_is:
			{
				equals();
				if ( inputState.guessing==0 ) {
					pattern = pattern + "=";
				}
				text=pattern();
				if ( inputState.guessing==0 ) {
					pattern = pattern + text;
				}
				break;
			}
			case COMMA:
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
		return pattern;
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
				consumeUntil(_tokenSet_39);
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
		"'->'",
		"\"generate\"",
		"a string",
		"\"obligations\"",
		"\"prove\"",
		"'/'",
		"an inner-unit reference",
		"an identifier",
		"'..'",
		"\"sort\"",
		"\"op\"",
		"':'",
		"'['",
		"']'",
		"\"using\"",
		"\"options\"",
		"'*'",
		"'='",
		"NON_WORD_SYMBOL",
		"\"Snark\"",
		"\"import\"",
		"'.'",
		"'('",
		"')'",
		"\"infixl\"",
		"\"infixr\"",
		"an integer",
		"\"fa\"",
		"\"def\"",
		"\"theorem\"",
		"\"axiom\"",
		"\"conjecture\"",
		"'::'",
		"\"as\"",
		"'_'",
		"\"quotient\"",
		"'|'",
		"';'",
		"a character",
		"\"true\"",
		"\"false\"",
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
		"'<-'",
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
	
	private static final long _tokenSet_0_data_[] = { 258268533264L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 258350977712L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { 1056064810990578L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 1091250257117170L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { 2L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { 1056080910481234L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { 505512015742105586L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 258275480240L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { 1056064794213360L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	private static final long _tokenSet_9_data_[] = { 1091265289519090L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_9 = new BitSet(_tokenSet_9_data_);
	private static final long _tokenSet_10_data_[] = { 1091250257117168L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_10 = new BitSet(_tokenSet_10_data_);
	private static final long _tokenSet_11_data_[] = { 1056080818206546L, 0L };
	public static final BitSet _tokenSet_11 = new BitSet(_tokenSet_11_data_);
	private static final long _tokenSet_12_data_[] = { 258268533522L, 0L };
	public static final BitSet _tokenSet_12 = new BitSet(_tokenSet_12_data_);
	private static final long _tokenSet_13_data_[] = { -16777230L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_13 = new BitSet(_tokenSet_13_data_);
	private static final long _tokenSet_14_data_[] = { -1069563106036816L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_14 = new BitSet(_tokenSet_14_data_);
	private static final long _tokenSet_15_data_[] = { 1055806443225088L, 0L };
	public static final BitSet _tokenSet_15 = new BitSet(_tokenSet_15_data_);
	private static final long _tokenSet_16_data_[] = { 505512015725328370L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_16 = new BitSet(_tokenSet_16_data_);
	private static final long _tokenSet_17_data_[] = { 510030458776453106L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_17 = new BitSet(_tokenSet_17_data_);
	private static final long _tokenSet_18_data_[] = { 258268549648L, 0L };
	public static final BitSet _tokenSet_18 = new BitSet(_tokenSet_18_data_);
	private static final long _tokenSet_19_data_[] = { 504420750452588544L, 0L };
	public static final BitSet _tokenSet_19 = new BitSet(_tokenSet_19_data_);
	private static final long _tokenSet_20_data_[] = { 505476831270795090L, 0L };
	public static final BitSet _tokenSet_20 = new BitSet(_tokenSet_20_data_);
	private static final long _tokenSet_21_data_[] = { 1056066958474224L, 0L };
	public static final BitSet _tokenSet_21 = new BitSet(_tokenSet_21_data_);
	private static final long _tokenSet_22_data_[] = { 1055806443225152L, 0L };
	public static final BitSet _tokenSet_22 = new BitSet(_tokenSet_22_data_);
	private static final long _tokenSet_23_data_[] = { 258671194640L, 0L };
	public static final BitSet _tokenSet_23 = new BitSet(_tokenSet_23_data_);
	private static final long _tokenSet_24_data_[] = { 808024355344L, 0L };
	public static final BitSet _tokenSet_24 = new BitSet(_tokenSet_24_data_);
	private static final long _tokenSet_25_data_[] = { -1069013566884976L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_25 = new BitSet(_tokenSet_25_data_);
	private static final long _tokenSet_26_data_[] = { 549755815936L, 0L };
	public static final BitSet _tokenSet_26 = new BitSet(_tokenSet_26_data_);
	private static final long _tokenSet_27_data_[] = { 49152L, 0L };
	public static final BitSet _tokenSet_27 = new BitSet(_tokenSet_27_data_);
	private static final long _tokenSet_28_data_[] = { 256L, 0L };
	public static final BitSet _tokenSet_28 = new BitSet(_tokenSet_28_data_);
	private static final long _tokenSet_29_data_[] = { 1056080834983762L, 0L };
	public static final BitSet _tokenSet_29 = new BitSet(_tokenSet_29_data_);
	private static final long _tokenSet_30_data_[] = { 258402759184L, 0L };
	public static final BitSet _tokenSet_30 = new BitSet(_tokenSet_30_data_);
	private static final long _tokenSet_31_data_[] = { 808024404496L, 0L };
	public static final BitSet _tokenSet_31 = new BitSet(_tokenSet_31_data_);
	private static final long _tokenSet_32_data_[] = { 258536976912L, 0L };
	public static final BitSet _tokenSet_32 = new BitSet(_tokenSet_32_data_);
	private static final long _tokenSet_33_data_[] = { 1057180329834322L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_33 = new BitSet(_tokenSet_33_data_);
	private static final long _tokenSet_34_data_[] = { -1069563322698864L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_34 = new BitSet(_tokenSet_34_data_);
	private static final long _tokenSet_35_data_[] = { -13194238756910L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_35 = new BitSet(_tokenSet_35_data_);
	private static final long _tokenSet_36_data_[] = { 509994724549326674L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_36 = new BitSet(_tokenSet_36_data_);
	private static final long _tokenSet_37_data_[] = { -13194238756910L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_37 = new BitSet(_tokenSet_37_data_);
	private static final long _tokenSet_38_data_[] = { -13194156312590L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_38 = new BitSet(_tokenSet_38_data_);
	private static final long _tokenSet_39_data_[] = { -13743994570798L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_39 = new BitSet(_tokenSet_39_data_);
	private static final long _tokenSet_40_data_[] = { 59676014535827456L, 0L };
	public static final BitSet _tokenSet_40 = new BitSet(_tokenSet_40_data_);
	private static final long _tokenSet_41_data_[] = { -565166568862908032L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_41 = new BitSet(_tokenSet_41_data_);
	private static final long _tokenSet_42_data_[] = { 509983729433048914L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_42 = new BitSet(_tokenSet_42_data_);
	private static final long _tokenSet_43_data_[] = { 513361429153576786L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_43 = new BitSet(_tokenSet_43_data_);
	private static final long _tokenSet_44_data_[] = { 1055840802963520L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_44 = new BitSet(_tokenSet_44_data_);
	private static final long _tokenSet_45_data_[] = { 536870912L, 0L };
	public static final BitSet _tokenSet_45 = new BitSet(_tokenSet_45_data_);
	private static final long _tokenSet_46_data_[] = { -13207123659824L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_46 = new BitSet(_tokenSet_46_data_);
	private static final long _tokenSet_47_data_[] = { -13194156312590L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_47 = new BitSet(_tokenSet_47_data_);
	private static final long _tokenSet_48_data_[] = { -549855037486L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_48 = new BitSet(_tokenSet_48_data_);
	private static final long _tokenSet_49_data_[] = { 2199023271936L, 0L };
	public static final BitSet _tokenSet_49 = new BitSet(_tokenSet_49_data_);
	private static final long _tokenSet_50_data_[] = { 508925485058629632L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_50 = new BitSet(_tokenSet_50_data_);
	private static final long _tokenSet_51_data_[] = { -1069563322698864L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_51 = new BitSet(_tokenSet_51_data_);
	private static final long _tokenSet_52_data_[] = { -13207123659824L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_52 = new BitSet(_tokenSet_52_data_);
	private static final long _tokenSet_53_data_[] = { 508925450698891264L, 0L };
	public static final BitSet _tokenSet_53 = new BitSet(_tokenSet_53_data_);
	private static final long _tokenSet_54_data_[] = { 34359738368L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_54 = new BitSet(_tokenSet_54_data_);
	private static final long _tokenSet_55_data_[] = { -13756879473712L, 511L, 0L, 0L };
	public static final BitSet _tokenSet_55 = new BitSet(_tokenSet_55_data_);
	private static final long _tokenSet_56_data_[] = { 518988714631836240L, 0L };
	public static final BitSet _tokenSet_56 = new BitSet(_tokenSet_56_data_);
	private static final long _tokenSet_57_data_[] = { 33554432L, 0L };
	public static final BitSet _tokenSet_57 = new BitSet(_tokenSet_57_data_);
	private static final long _tokenSet_58_data_[] = { 510053586673131522L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_58 = new BitSet(_tokenSet_58_data_);
	private static final long _tokenSet_59_data_[] = { 517932908188611088L, 0L };
	public static final BitSet _tokenSet_59 = new BitSet(_tokenSet_59_data_);
	private static final long _tokenSet_60_data_[] = { -998644822707310L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_60 = new BitSet(_tokenSet_60_data_);
	private static final long _tokenSet_61_data_[] = { -998644822707312L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_61 = new BitSet(_tokenSet_61_data_);
	private static final long _tokenSet_62_data_[] = { 2201170788352L, 0L };
	public static final BitSet _tokenSet_62 = new BitSet(_tokenSet_62_data_);
	private static final long _tokenSet_63_data_[] = { 2201707659264L, 0L };
	public static final BitSet _tokenSet_63 = new BitSet(_tokenSet_63_data_);
	private static final long _tokenSet_64_data_[] = { 508925708933870096L, 0L };
	public static final BitSet _tokenSet_64 = new BitSet(_tokenSet_64_data_);
	private static final long _tokenSet_65_data_[] = { 519061009266242064L, 0L };
	public static final BitSet _tokenSet_65 = new BitSet(_tokenSet_65_data_);
	private static final long _tokenSet_66_data_[] = { -1069563322698862L, 1023L, 0L, 0L };
	public static final BitSet _tokenSet_66 = new BitSet(_tokenSet_66_data_);
	private static final long _tokenSet_67_data_[] = { 512305386486816770L, 512L, 0L, 0L };
	public static final BitSet _tokenSet_67 = new BitSet(_tokenSet_67_data_);
	
	}
