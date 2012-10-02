/*
 * ProcessorObjectRequest
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

import org.openide.text.CloneableEditorSupport;
import edu.kestrel.netbeans.parser.MetaSlangParser;

public interface ProcessorObjectRequest {

    /** Notifies the request object that the engine has resheduled this request.
     * Internal request data should be cleared.
    */
    public void notifyReschedule();
    
    /**
     * Notifies the request that the source text has been changed. This causes
     * cancellation of the request in some cases.
    */
    public void sourceChanged();

    /**
     * Notifies the request that the model has been changed. This causes
     * cancellation of the request in some cases.
    */
    public void modelChanged();
    
    /**
     *
    */
    public DocumentModelUpdater getUpdater();     

    public void setEnvironment(MetaSlangParser.Env env);
    
    public void setEditorSupport(CloneableEditorSupport editor);
}

