/*
 * ParseObjectRequest.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.io.Reader;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;

import org.netbeans.modules.java.ErrConsumer;

/**
 * Request for parsing the Meta Slang source. This interface defines interactions
 * between the parsing engine and the request object.
 * Parser engine takes appropriate DataObject from the request and processes
 * its file. The engine consults the request about its validity from time to 
 * time so it can stop time-consuming processing as soon as possible.
 * The main purpose is to inform the Request about states of processing so it
 * can properly track its validity.
 *
 */
public interface ParseObjectRequest {
    /** Sets the number of syntax errors that occured during parsing.
    */
    public void setSyntaxErrors(int errors);
    
    /** Returns the number of syntax errors.
    */
    public int  getSyntaxErrors();
    
    /** 
     * Sets number of semantic errors.
     */
    public void setSemanticErrors(int errors);
    
    /** Returns Element implementation creation factory. The Engine asks for the
        factory after it finishes general text scan. The factory will be responsible
        for creating the source text representation and to bind it to the request.
    */
    public ElementFactory getFactory();
    
    /** 
     * Called to obtain data to be parsed. 
     * @throws IOException if the data can't be returned.
    */
    public char[] getSource() throws IOException;

    /** 
     * Called to obtain reader for the data to be parsed. 
     * @throws IOException if the reader can't be returned.
    */
    public Reader getSourceReader() throws IOException;

    /** Determines if the request is still valid.
        In general, request processing stops whenever this method returns false.
        It is <B>required</B> that implementation returns false, if the source contents
        changes during request processing.
        Implementation might return false whenever it decides to discard potential results
        from this request to provide hint to the Parser Engine.
    */
    public boolean isValid();

    public boolean needsProcessing();
    
    /** Notifies the request that the parser engine is about to process the request.
        Should any data passed to the parser engine change after this call, the
        parser request implementation should invalidate the request.
    */
    public void notifyStart();

    /** Notifies the request object that the engine has finished its processing.
        The request can then become completed (depending on its validity)
    */
    public void notifyComplete();
    
    public Object getParserType();
    
    public ErrConsumer getErrConsumer();
    
    public String getSourceName();
    
    public Collection getSourcePath();
}
