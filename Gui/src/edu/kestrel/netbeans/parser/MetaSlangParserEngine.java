/*
 * MetaSlangParserEngine.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/03/13 01:23:57  gilham
 * Handle Latex comments.
 * Report Lexer errors.
 * Always display parser messages (not displayed before if the parsing succeeded
 * and the parser output window is not open).
 *
 * Revision 1.1  2003/01/30 02:02:20  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.io.IOException;
import java.io.Reader;

import org.openide.filesystems.FileObject;

import antlr.RecognitionException;
import antlr.SemanticException;
import antlr.TokenStreamException;
import antlr.TokenStreamException;
import antlr.TokenStreamRecognitionException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.ParserEngine;
import edu.kestrel.netbeans.parser.ParseObjectRequest;

/** Simple interface to a parser engine
 *  The engine should process passed source file(s) and give out enough information
 *  to produce MetaSlang Hierarchy classes for the source. The engine should not only
 *  parse, but resolve identifiers as well; doing that, it is free to open other
 *  source files.
 */
public class MetaSlangParserEngine implements ParserEngine{

    private boolean DEBUG = false;

    /** Registers a new request with the parser engine.
        When a request is registered, it can be processed at any time. The engine
        can carry this task during processing of other requests.
     * @param r Request to be registered
     * @param fo FileObject that the request should be bound to. The request will
     * be processed if the parser/compiler touches `fo' during other processing.
     */
    public void register(ParseObjectRequest r, FileObject fo) {
    }

    /**
     * Unregisters a request filed for the given FileObject. 
     */
    public void unregister(FileObject fo) {
    }

    /** Determines if a parse request is already registered with the engine.
    */
    public boolean isRegistered(ParseObjectRequest r) {
	return false;
    }

    /** Clears all requests in the parser engine.
    */
    public void unregisterAll() {
    }

    /** Process the request immediately. The method returns after the request is
        completed (either successfully or with some errors).
        If request was already completed, it is processed again yielding fresh
        results.
    */
    public void process(ParseObjectRequest r) throws IOException {
	if (DEBUG) edu.kestrel.netbeans.Util.trace("*** MetaSlangParserEngine.process()");
	// Create a scanner that reads from the input stream
	Reader reader = r.getSourceReader();
	MetaSlangLexerFromAntlr lexer = new MetaSlangLexerFromAntlr(reader, r);

	// Create a parser that reads from the scanner
	MetaSlangParserFromAntlr parser = new MetaSlangParserFromAntlr(lexer, r);
	try {
	    // start parsing at the starts rule (theories, theory elems, terms)
	    r.notifyStart();
	    parser.starts();
	}
	catch (RecognitionException e) {
	    // handled by MetaSlangParserFromAntlr
	}
	catch (TokenStreamException e) {
	    // TODO: Better handling of token stream errors
	    edu.kestrel.netbeans.Util.trace("*** MetaSlangParserEngine.process(): caught "+e.getClass()+" in file "+r.getSourceFile());
	    if (e instanceof TokenStreamRecognitionException) {
		RecognitionException ex = ((TokenStreamRecognitionException) e).recog;
		r.pushError(ex.getLine(), ex.getColumn(), ex.getMessage());
	    } else {
		r.pushError(0, 0, e.getMessage());
	    }
	}
	r.notifyComplete();
    }
}
