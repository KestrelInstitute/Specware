/*
 * ParserEngine.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:37  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.io.IOException;

import org.openide.filesystems.FileObject;

import edu.kestrel.netbeans.parser.ParseObjectRequest;

/** Simple interface to a parser engine
 *  The engine should process passed source file(s) and give out enough information
 *  to produce MetaSlang Hierarchy classes for the source. The engine should not only
 *  parse, but resolve identifiers as well; doing that, it is free to open other
 *  source files.
 */
public interface ParserEngine {
    /** Registers a new request with the parser engine.
        When a request is registered, it can be processed at any time. The engine
        can carry this task during processing of other requests.
     * @param r Request to be registered
     * @param fo FileObject that the request should be bound to. The request will
     * be processed if the parser/compiler touches `fo' during other processing.
    */
    public void register(ParseObjectRequest r, FileObject fo);

    /**
     * Unregisters a request filed for the given FileObject. 
     */
    public void unregister(FileObject fo);

    /** Determines if a parse request is already registered with the engine.
    */
    public boolean isRegistered(ParseObjectRequest r);

    /** Clears all requests in the parser engine.
    */
    public void unregisterAll();

    /** Process the request immediately. The method returns after the request is
        completed (either successfully or with some errors).
        If request was already completed, it is processed again yielding fresh
        results.
    */
    public void process(ParseObjectRequest r) throws IOException;
}
