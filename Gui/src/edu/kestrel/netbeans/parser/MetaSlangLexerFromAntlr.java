// $ANTLR 2.7.1: "MetaSlangGrammar.g" -> "MetaSlangLexerFromAntlr.java"$

package edu.kestrel.netbeans.parser;

import java.io.InputStream;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.TokenStreamRecognitionException;
import antlr.CharStreamException;
import antlr.CharStreamIOException;
import antlr.ANTLRException;
import java.io.Reader;
import java.util.Hashtable;
import antlr.CharScanner;
import antlr.InputBuffer;
import antlr.ByteBuffer;
import antlr.CharBuffer;
import antlr.Token;
import antlr.CommonToken;
import antlr.RecognitionException;
import antlr.NoViableAltForCharException;
import antlr.MismatchedCharException;
import antlr.TokenStream;
import antlr.ANTLRHashString;
import antlr.LexerSharedInputState;
import antlr.collections.impl.BitSet;
import antlr.SemanticException;

public class MetaSlangLexerFromAntlr extends antlr.CharScanner implements MetaSlangParserFromAntlrTokenTypes, TokenStream
 {

    ParseObjectRequest request;
    public void reportError(RecognitionException ex) {
        request.pushError(ex.getLine(), ex.getColumn(), ex.getMessage());
    }

    public MetaSlangLexerFromAntlr(Reader in, ParseObjectRequest request) {
        this(in);
        this.request = request;
    }
public MetaSlangLexerFromAntlr(InputStream in) {
	this(new ByteBuffer(in));
}
public MetaSlangLexerFromAntlr(Reader in) {
	this(new CharBuffer(in));
}
public MetaSlangLexerFromAntlr(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public MetaSlangLexerFromAntlr(LexerSharedInputState state) {
	super(state);
	literals = new Hashtable();
	literals.put(new ANTLRHashString("case", this), new Integer(61));
	literals.put(new ANTLRHashString("op", this), new Integer(31));
	literals.put(new ANTLRHashString("ex", this), new Integer(66));
	literals.put(new ANTLRHashString("embed", this), new Integer(64));
	literals.put(new ANTLRHashString("spec", this), new Integer(5));
	literals.put(new ANTLRHashString("quotient", this), new Integer(54));
	literals.put(new ANTLRHashString("false", this), new Integer(60));
	literals.put(new ANTLRHashString("restrict", this), new Integer(72));
	literals.put(new ANTLRHashString("print", this), new Integer(4));
	literals.put(new ANTLRHashString("true", this), new Integer(59));
	literals.put(new ANTLRHashString("let", this), new Integer(7));
	literals.put(new ANTLRHashString("obligations", this), new Integer(21));
	literals.put(new ANTLRHashString("qualifying", this), new Integer(13));
	literals.put(new ANTLRHashString("choose", this), new Integer(62));
	literals.put(new ANTLRHashString("def", this), new Integer(47));
	literals.put(new ANTLRHashString("generate", this), new Integer(19));
	literals.put(new ANTLRHashString("infixl", this), new Integer(43));
	literals.put(new ANTLRHashString("theorem", this), new Integer(48));
	literals.put(new ANTLRHashString("import", this), new Integer(41));
	literals.put(new ANTLRHashString("infixr", this), new Integer(44));
	literals.put(new ANTLRHashString("where", this), new Integer(74));
	literals.put(new ANTLRHashString("conjecture", this), new Integer(50));
	literals.put(new ANTLRHashString("embed?", this), new Integer(65));
	literals.put(new ANTLRHashString("Snark", this), new Integer(40));
	literals.put(new ANTLRHashString("prove", this), new Integer(22));
	literals.put(new ANTLRHashString("in", this), new Integer(8));
	literals.put(new ANTLRHashString("diagram", this), new Integer(14));
	literals.put(new ANTLRHashString("options", this), new Integer(36));
	literals.put(new ANTLRHashString("fn", this), new Integer(67));
	literals.put(new ANTLRHashString("of", this), new Integer(69));
	literals.put(new ANTLRHashString("morphism", this), new Integer(17));
	literals.put(new ANTLRHashString("is", this), new Integer(75));
	literals.put(new ANTLRHashString("fa", this), new Integer(46));
	literals.put(new ANTLRHashString("project", this), new Integer(70));
	literals.put(new ANTLRHashString("translate", this), new Integer(9));
	literals.put(new ANTLRHashString("relax", this), new Integer(71));
	literals.put(new ANTLRHashString("axiom", this), new Integer(49));
	literals.put(new ANTLRHashString("endspec", this), new Integer(6));
	literals.put(new ANTLRHashString("if", this), new Integer(68));
	literals.put(new ANTLRHashString("colimit", this), new Integer(16));
	literals.put(new ANTLRHashString("using", this), new Integer(35));
	literals.put(new ANTLRHashString("else", this), new Integer(63));
	literals.put(new ANTLRHashString("sort", this), new Integer(29));
	literals.put(new ANTLRHashString("by", this), new Integer(10));
	literals.put(new ANTLRHashString("then", this), new Integer(73));
	literals.put(new ANTLRHashString("as", this), new Integer(52));
caseSensitiveLiterals = true;
setCaseSensitive(true);
}

public Token nextToken() throws TokenStreamException {
	Token theRetToken=null;
tryAgain:
	for (;;) {
		Token _token = null;
		int _ttype = Token.INVALID_TYPE;
		resetText();
		try {   // for char stream error handling
			try {   // for lexical error handling
				switch ( LA(1)) {
				case '\t':  case '\n':  case '\u000c':  case '\r':
				case ' ':
				{
					mWHITESPACE(true);
					theRetToken=_returnToken;
					break;
				}
				case '%':
				{
					mLINE_COMMENT(true);
					theRetToken=_returnToken;
					break;
				}
				case '_':
				{
					mUBAR(true);
					theRetToken=_returnToken;
					break;
				}
				case ')':
				{
					mRPAREN(true);
					theRetToken=_returnToken;
					break;
				}
				case '[':
				{
					mLBRACKET(true);
					theRetToken=_returnToken;
					break;
				}
				case ']':
				{
					mRBRACKET(true);
					theRetToken=_returnToken;
					break;
				}
				case '{':
				{
					mLBRACE(true);
					theRetToken=_returnToken;
					break;
				}
				case '}':
				{
					mRBRACE(true);
					theRetToken=_returnToken;
					break;
				}
				case ',':
				{
					mCOMMA(true);
					theRetToken=_returnToken;
					break;
				}
				case ';':
				{
					mSEMICOLON(true);
					theRetToken=_returnToken;
					break;
				}
				case '0':  case '1':  case '2':  case '3':
				case '4':  case '5':  case '6':  case '7':
				case '8':  case '9':
				{
					mNAT_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case '"':
				{
					mSTRING_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case 'A':  case 'B':  case 'C':  case 'D':
				case 'E':  case 'F':  case 'G':  case 'H':
				case 'I':  case 'J':  case 'K':  case 'L':
				case 'M':  case 'N':  case 'O':  case 'P':
				case 'Q':  case 'R':  case 'S':  case 'T':
				case 'U':  case 'V':  case 'W':  case 'X':
				case 'Y':  case 'Z':  case 'a':  case 'b':
				case 'c':  case 'd':  case 'e':  case 'f':
				case 'g':  case 'h':  case 'i':  case 'j':
				case 'k':  case 'l':  case 'm':  case 'n':
				case 'o':  case 'p':  case 'q':  case 'r':
				case 's':  case 't':  case 'u':  case 'v':
				case 'w':  case 'x':  case 'y':  case 'z':
				{
					mIDENTIFIER(true);
					theRetToken=_returnToken;
					break;
				}
				default:
					if ((LA(1)=='+') && (LA(2)=='-') && (LA(3)=='>') && (true)) {
						mMAPS_TO(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='#') && (_tokenSet_0.member(LA(2))) && (_tokenSet_1.member(LA(3))) && (true)) {
						mINNER_UNIT_REF(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='(') && (LA(2)=='*')) {
						mBLOCK_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='\\') && (LA(2)=='d'||LA(2)=='e'||LA(2)=='s')) {
						mLATEX_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='.') && (LA(2)=='.')) {
						mDOTDOT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)==':') && (LA(2)==':') && (true) && (true)) {
						mCOLONCOLON(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (LA(2)=='>') && (true) && (true)) {
						mARROW(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='<') && (LA(2)=='-') && (true) && (true)) {
						mBACKWARDSARROW(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='#') && (_tokenSet_2.member(LA(2))) && (true) && (true)) {
						mCHAR_LITERAL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='(') && (true)) {
						mLPAREN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='.') && (true)) {
						mDOT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)==':') && (true) && (true) && (true)) {
						mCOLON(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (true) && (true) && (true)) {
						mVERTICALBAR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='*') && (true) && (true) && (true)) {
						mSTAR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (true) && (true) && (true)) {
						mSLASH(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='=') && (true) && (true) && (true)) {
						mEQUALS(true);
						theRetToken=_returnToken;
					}
					else if ((_tokenSet_3.member(LA(1))) && (true) && (true) && (true)) {
						mNON_WORD_SYMBOL(true);
						theRetToken=_returnToken;
					}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
				}
				}
				if ( _returnToken==null ) continue tryAgain; // found SKIP token
				_ttype = _returnToken.getType();
				_returnToken.setType(_ttype);
				return _returnToken;
			}
			catch (RecognitionException e) {
				throw new TokenStreamRecognitionException(e);
			}
		}
		catch (CharStreamException cse) {
			if ( cse instanceof CharStreamIOException ) {
				throw new TokenStreamIOException(((CharStreamIOException)cse).io);
			}
			else {
				throw new TokenStreamException(cse.getMessage());
			}
		}
	}
}

	protected final void mVOCAB(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = VOCAB;
		int _saveIndex;
		
		matchRange('\3','\377');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mWHITESPACE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = WHITESPACE;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case ' ':
		{
			match(' ');
			break;
		}
		case '\t':
		{
			match('\t');
			break;
		}
		case '\u000c':
		{
			match('\f');
			break;
		}
		case '\n':  case '\r':
		{
			{
			if ((LA(1)=='\r') && (LA(2)=='\n')) {
				match("\r\n");
			}
			else if ((LA(1)=='\r') && (true)) {
				match('\r');
			}
			else if ((LA(1)=='\n')) {
				match('\n');
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
			}
			
			}
			if ( inputState.guessing==0 ) {
				newline();
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLINE_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LINE_COMMENT;
		int _saveIndex;
		
		match('%');
		{
		_loop171:
		do {
			if ((_tokenSet_4.member(LA(1)))) {
				{
				match(_tokenSet_4);
				}
			}
			else {
				break _loop171;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case '\n':
		{
			match('\n');
			break;
		}
		case '\r':
		{
			match('\r');
			{
			if ((LA(1)=='\n')) {
				match('\n');
			}
			else {
			}
			
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			newline();
						    _ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBLOCK_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BLOCK_COMMENT;
		int _saveIndex;
		
		match("(*");
		{
		_loop177:
		do {
			if ((LA(1)=='\r') && (LA(2)=='\n') && ((LA(3) >= '\u0003' && LA(3) <= '\u00ff')) && ((LA(4) >= '\u0003' && LA(4) <= '\u00ff'))) {
				match('\r');
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if (((LA(1)=='*') && ((LA(2) >= '\u0003' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0003' && LA(3) <= '\u00ff')))&&( LA(2)!=')' )) {
				match('*');
			}
			else if ((LA(1)=='\r') && ((LA(2) >= '\u0003' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0003' && LA(3) <= '\u00ff')) && (true)) {
				match('\r');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if ((LA(1)=='\n')) {
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if ((_tokenSet_5.member(LA(1)))) {
				{
				match(_tokenSet_5);
				}
			}
			else {
				break _loop177;
			}
			
		} while (true);
		}
		match("*)");
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLATEX_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LATEX_COMMENT;
		int _saveIndex;
		
		{
		if ((LA(1)=='\\') && (LA(2)=='s') && (LA(3)=='e')) {
			match("\\section{");
		}
		else if ((LA(1)=='\\') && (LA(2)=='s') && (LA(3)=='u')) {
			match("\\subsection{");
		}
		else if ((LA(1)=='\\') && (LA(2)=='e')) {
			match("\\end{spec}");
		}
		else if ((LA(1)=='\\') && (LA(2)=='d')) {
			match("\\document{");
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		{
		_loop182:
		do {
			if ((LA(1)=='\r') && (LA(2)=='\n') && (true) && (true)) {
				match('\r');
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if (((LA(1)=='\\') && (true) && (true) && (true))&&( LA(2)!='b' || LA(3)!='e' || LA(4) !='g' || LA(5) !='i' || LA(6) !='n' || LA(7) != '{' || LA(8) != 's' || LA(9) != 'p' || LA(10) != 'e' || LA(11) != 'c' || LA(12) != '}')) {
				match('\\');
			}
			else if ((LA(1)=='\r') && (true) && (true) && (true)) {
				match('\r');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if ((LA(1)=='\n')) {
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if ((_tokenSet_6.member(LA(1)))) {
				{
				match(_tokenSet_6);
				}
			}
			else {
				break _loop182;
			}
			
		} while (true);
		}
		{
		boolean synPredMatched185 = false;
		if (((LA(1)=='\\'))) {
			int _m185 = mark();
			synPredMatched185 = true;
			inputState.guessing++;
			try {
				{
				match("\\begin{spec}");
				}
			}
			catch (RecognitionException pe) {
				synPredMatched185 = false;
			}
			rewind(_m185);
			inputState.guessing--;
		}
		if ( synPredMatched185 ) {
			match("\\begin{spec}");
		}
		else {
		}
		
		}
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mUBAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = UBAR;
		int _saveIndex;
		
		match("_");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LPAREN;
		int _saveIndex;
		
		match('(');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RPAREN;
		int _saveIndex;
		
		match(')');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLBRACKET(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LBRACKET;
		int _saveIndex;
		
		match('[');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRBRACKET(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RBRACKET;
		int _saveIndex;
		
		match(']');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLBRACE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LBRACE;
		int _saveIndex;
		
		match('{');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRBRACE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RBRACE;
		int _saveIndex;
		
		match('}');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOMMA(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COMMA;
		int _saveIndex;
		
		match(',');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSEMICOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SEMICOLON;
		int _saveIndex;
		
		match(';');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOT;
		int _saveIndex;
		
		match('.');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOTDOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOTDOT;
		int _saveIndex;
		
		match("..");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COLON;
		int _saveIndex;
		
		match(":");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOLONCOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COLONCOLON;
		int _saveIndex;
		
		match("::");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mVERTICALBAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = VERTICALBAR;
		int _saveIndex;
		
		match("|");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STAR;
		int _saveIndex;
		
		match("*");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mARROW(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ARROW;
		int _saveIndex;
		
		match("->");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBACKWARDSARROW(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BACKWARDSARROW;
		int _saveIndex;
		
		match("<-");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mMAPS_TO(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MAPS_TO;
		int _saveIndex;
		
		match("+->");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSLASH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SLASH;
		int _saveIndex;
		
		match("/");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEQUALS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EQUALS;
		int _saveIndex;
		
		match("=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mLETTER(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LETTER;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':
		{
			{
			matchRange('A','Z');
			}
			break;
		}
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':  case 'g':  case 'h':
		case 'i':  case 'j':  case 'k':  case 'l':
		case 'm':  case 'n':  case 'o':  case 'p':
		case 'q':  case 'r':  case 's':  case 't':
		case 'u':  case 'v':  case 'w':  case 'x':
		case 'y':  case 'z':
		{
			{
			matchRange('a','z');
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mDIGIT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DIGIT;
		int _saveIndex;
		
		{
		matchRange('0','9');
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mINNER_UNIT_REF(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = INNER_UNIT_REF;
		int _saveIndex;
		
		match('#');
		mWORD_START_MARK(false);
		{
		int _cnt213=0;
		_loop213:
		do {
			if ((_tokenSet_1.member(LA(1)))) {
				mWORD_CONTINUE_MARK(false);
			}
			else {
				if ( _cnt213>=1 ) { break _loop213; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
			}
			
			_cnt213++;
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mWORD_START_MARK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = WORD_START_MARK;
		int _saveIndex;
		
		mLETTER(false);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mWORD_CONTINUE_MARK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = WORD_CONTINUE_MARK;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':  case 'a':  case 'b':
		case 'c':  case 'd':  case 'e':  case 'f':
		case 'g':  case 'h':  case 'i':  case 'j':
		case 'k':  case 'l':  case 'm':  case 'n':
		case 'o':  case 'p':  case 'q':  case 'r':
		case 's':  case 't':  case 'u':  case 'v':
		case 'w':  case 'x':  case 'y':  case 'z':
		{
			mLETTER(false);
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			mDIGIT(false);
			break;
		}
		case '_':
		{
			match('_');
			break;
		}
		case '?':
		{
			match('?');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNAT_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NAT_LITERAL;
		int _saveIndex;
		
		switch ( LA(1)) {
		case '0':
		{
			match('0');
			break;
		}
		case '1':  case '2':  case '3':  case '4':
		case '5':  case '6':  case '7':  case '8':
		case '9':
		{
			{
			matchRange('1','9');
			}
			{
			_loop217:
			do {
				if (((LA(1) >= '0' && LA(1) <= '9'))) {
					matchRange('0','9');
				}
				else {
					break _loop217;
				}
				
			} while (true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCHAR_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = CHAR_LITERAL;
		int _saveIndex;
		
		match('#');
		mCHAR_GLYPH(false);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mCHAR_GLYPH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = CHAR_GLYPH;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':  case 'a':  case 'b':
		case 'c':  case 'd':  case 'e':  case 'f':
		case 'g':  case 'h':  case 'i':  case 'j':
		case 'k':  case 'l':  case 'm':  case 'n':
		case 'o':  case 'p':  case 'q':  case 'r':
		case 's':  case 't':  case 'u':  case 'v':
		case 'w':  case 'x':  case 'y':  case 'z':
		{
			mLETTER(false);
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			mDIGIT(false);
			break;
		}
		case '!':  case '#':  case '$':  case '%':
		case '&':  case '\'':  case '(':  case ')':
		case '*':  case '+':  case ',':  case '-':
		case '.':  case '/':  case ':':  case ';':
		case '<':  case '=':  case '>':  case '?':
		case '@':  case '[':  case '\\':  case ']':
		case '^':  case '_':  case '`':  case '{':
		case '|':  case '}':  case '~':
		{
			mOTHER_CHAR_GLYPH(false);
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mOTHER_CHAR_GLYPH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = OTHER_CHAR_GLYPH;
		int _saveIndex;
		
		switch ( LA(1)) {
		case '!':
		{
			match('!');
			break;
		}
		case ':':
		{
			match(':');
			break;
		}
		case '@':
		{
			match('@');
			break;
		}
		case '#':
		{
			match('#');
			break;
		}
		case '$':
		{
			match('$');
			break;
		}
		case '%':
		{
			match('%');
			break;
		}
		case '^':
		{
			match('^');
			break;
		}
		case '&':
		{
			match('&');
			break;
		}
		case '*':
		{
			match('*');
			break;
		}
		case '(':
		{
			match('(');
			break;
		}
		case ')':
		{
			match(')');
			break;
		}
		case '_':
		{
			match('_');
			break;
		}
		case '-':
		{
			match('-');
			break;
		}
		case '+':
		{
			match('+');
			break;
		}
		case '=':
		{
			match('=');
			break;
		}
		case '|':
		{
			match('|');
			break;
		}
		case '~':
		{
			match('~');
			break;
		}
		case '`':
		{
			match('`');
			break;
		}
		case '.':
		{
			match('.');
			break;
		}
		case ',':
		{
			match(',');
			break;
		}
		case '<':
		{
			match('<');
			break;
		}
		case '>':
		{
			match('>');
			break;
		}
		case '?':
		{
			match('?');
			break;
		}
		case '/':
		{
			match('/');
			break;
		}
		case ';':
		{
			match(';');
			break;
		}
		case '\'':
		{
			match('\'');
			break;
		}
		case '[':
		{
			match('[');
			break;
		}
		case ']':
		{
			match(']');
			break;
		}
		case '{':
		{
			match('{');
			break;
		}
		case '}':
		{
			match('}');
			break;
		}
		default:
			if ((LA(1)=='\\') && (_tokenSet_7.member(LA(2)))) {
				mESC(false);
			}
			else if ((LA(1)=='\\') && (LA(2)=='x')) {
				match('\\');
				match('x');
				mHEXADECIMAL_DIGIT(false);
				mHEXADECIMAL_DIGIT(false);
			}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mESC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ESC;
		int _saveIndex;
		
		match('\\');
		{
		switch ( LA(1)) {
		case 'a':
		{
			match('a');
			break;
		}
		case 'b':
		{
			match('b');
			break;
		}
		case 't':
		{
			match('t');
			break;
		}
		case 'n':
		{
			match('n');
			break;
		}
		case 'v':
		{
			match('v');
			break;
		}
		case 'f':
		{
			match('f');
			break;
		}
		case 'r':
		{
			match('r');
			break;
		}
		case 's':
		{
			match('s');
			break;
		}
		case '"':
		{
			match('"');
			break;
		}
		case '\\':
		{
			match('\\');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mHEXADECIMAL_DIGIT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = HEXADECIMAL_DIGIT;
		int _saveIndex;
		
		switch ( LA(1)) {
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			mDIGIT(false);
			break;
		}
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':
		{
			{
			matchRange('a','f');
			}
			break;
		}
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':
		{
			{
			matchRange('A','F');
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTRING_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STRING_LITERAL;
		int _saveIndex;
		
		match('"');
		{
		_loop228:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				mSTRING_LITERAL_GLYPH(false);
			}
			else {
				break _loop228;
			}
			
		} while (true);
		}
		match('"');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mSTRING_LITERAL_GLYPH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STRING_LITERAL_GLYPH;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':  case 'a':  case 'b':
		case 'c':  case 'd':  case 'e':  case 'f':
		case 'g':  case 'h':  case 'i':  case 'j':
		case 'k':  case 'l':  case 'm':  case 'n':
		case 'o':  case 'p':  case 'q':  case 'r':
		case 's':  case 't':  case 'u':  case 'v':
		case 'w':  case 'x':  case 'y':  case 'z':
		{
			mLETTER(false);
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			mDIGIT(false);
			break;
		}
		case '!':  case '#':  case '$':  case '%':
		case '&':  case '\'':  case '(':  case ')':
		case '*':  case '+':  case ',':  case '-':
		case '.':  case '/':  case ':':  case ';':
		case '<':  case '=':  case '>':  case '?':
		case '@':  case '[':  case '\\':  case ']':
		case '^':  case '_':  case '`':  case '{':
		case '|':  case '}':  case '~':
		{
			mOTHER_CHAR_GLYPH(false);
			break;
		}
		case ' ':
		{
			match(' ');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mIDENTIFIER(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IDENTIFIER;
		int _saveIndex;
		
		mWORD_START_MARK(false);
		{
		_loop232:
		do {
			if ((_tokenSet_1.member(LA(1)))) {
				mWORD_CONTINUE_MARK(false);
			}
			else {
				break _loop232;
			}
			
		} while (true);
		}
		_ttype = testLiteralsTable(_ttype);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNON_WORD_SYMBOL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NON_WORD_SYMBOL;
		int _saveIndex;
		
		{
		int _cnt237=0;
		_loop237:
		do {
			if ((_tokenSet_3.member(LA(1)))) {
				mNON_WORD_MARK(false);
			}
			else {
				if ( _cnt237>=1 ) { break _loop237; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
			}
			
			_cnt237++;
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNON_WORD_MARK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NON_WORD_MARK;
		int _saveIndex;
		
		switch ( LA(1)) {
		case '`':
		{
			match('`');
			break;
		}
		case '~':
		{
			match('~');
			break;
		}
		case '!':
		{
			match('!');
			break;
		}
		case '@':
		{
			match('@');
			break;
		}
		case '$':
		{
			match('$');
			break;
		}
		case '^':
		{
			match('^');
			break;
		}
		case '&':
		{
			match('&');
			break;
		}
		case '-':
		{
			match('-');
			break;
		}
		case '+':
		{
			match('+');
			break;
		}
		case '<':
		{
			match('<');
			break;
		}
		case '>':
		{
			match('>');
			break;
		}
		case '?':
		{
			match('?');
			break;
		}
		case '*':
		{
			match('*');
			break;
		}
		case '=':
		{
			match('=');
			break;
		}
		case ':':
		{
			match(':');
			break;
		}
		case '|':
		{
			match('|');
			break;
		}
		case '\\':
		{
			match('\\');
			break;
		}
		case '/':
		{
			match('/');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	
	private static final long _tokenSet_0_data_[] = { 0L, 576460743847706622L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { -8935423135679774720L, 576460745995190270L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { -25769803776L, 9223372036854775807L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { -864501660267839488L, 5764607528671379457L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { -9224L, -1L, -1L, -1L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { -4398046520328L, -1L, -1L, -1L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { -9224L, -268435457L, -1L, -1L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 17179869184L, 25966367517704192L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { -21474836480L, 9223372036854775807L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	
	}
