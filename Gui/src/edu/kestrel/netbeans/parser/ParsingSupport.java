/*
 * ParsingSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:26  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.*;
import java.io.Reader;
import java.io.InputStream;
import java.io.IOException;

import javax.swing.event.ChangeListener;
import javax.swing.event.ChangeEvent;

import javax.swing.text.Segment;
import javax.swing.text.StyledDocument;
import javax.swing.text.BadLocationException;

import org.openide.filesystems.FileObject;
import org.openide.nodes.Node;
import org.openide.text.CloneableEditorSupport;
import org.openide.util.Task;
import org.openide.util.TaskListener;
import org.openide.util.RequestProcessor;
import org.openide.src.SourceException;
import org.netbeans.modules.java.model.CommitListener;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.SourceText;
import edu.kestrel.netbeans.ParserEngine;

/**
 * This class serves as a default implementation of MetaSlangParser interface and coordinates
 * one-way interaction between a LangModel and the underlying StyledDocument. The other
 * way is implemented through various bindings attached to individual model elements.
 * The parser is responsible for maintaining `dirty' status for the model data, with respect
 * to changes made to the document, parsing when the client asks to parse and updating
 * the model contents when appropriate.
 *
 */
public class ParsingSupport implements MetaSlangParser {
    
    private static final int READ_THRESHOLD = 2048;
    
    private PropertyChangeSupport  propSupport;
    
    public static final String PROP_STATUS = "status"; // NOI18N
    
    private static final boolean DEBUG = false;
    
    /** Initially true. Set to false when the Support is no longer valid.
     */
    private boolean valid;
    
    /**
     * True during the model update operation. When true, the refImplementation
     * cannot be cleared, otherwise the updater thread may lock up.
     */
    private boolean updating;

    /**
     * Creates a ParsingSupport and initializes it with an environment, binding,
     * updater interface and the model.
     */
    public ParsingSupport(Env parsingEnv, DocumentBinding docBinding,
			  LangModel.Updater updater, LangModel model) {
        initialize(parsingEnv, docBinding, updater, model);
    }
    
    private void initialize(Env parsingEnv, DocumentBinding docBinding,
			    LangModel.Updater updater, LangModel model) {
        this.docBinding = docBinding;
        this.parsingEnv = parsingEnv;
        this.updater = updater;
        this.model = model;
        this.valid = true;

        synchronized (ParsingSupport.class) {
            if (referenceSupportMap == null) {
                referenceSupportMap = new HashMap(17);
                refQueue = new ReferenceQueue();
            }
        }
    }
    
    public void addChangeListener(ChangeListener l) {
        if (changeList == null) {
            synchronized (this) {
                if (changeList == null) 
                    changeList = new LinkedList();
            }
        }
        synchronized (changeList) {
            changeList.add(l);
        }
    }
    
    public void removeChangeListener(ChangeListener l) {
        if (changeList == null)
            return;
        synchronized (changeList) {
            changeList.remove(l);
        }
    }

    /**
     * Adds a property change listener to this object.
     */
    public void addPropertyChangeListener(PropertyChangeListener l) {
        if (propSupport == null) {
            synchronized (this) {
                if (propSupport == null)
                    propSupport = new PropertyChangeSupport(this);
            }
        }
        propSupport.addPropertyChangeListener(l);
    }
    
    /**
     * Removes the change listener.
     */
    public void removePropertyChangeListener(PropertyChangeListener l) {
        if (propSupport == null)
            return;
        propSupport.removePropertyChangeListener(l);
    }
    
    /** Schedules a refresh/reparse of the associated document. The request is given
     * the passed priority. If there are some errors during parsing and acceptErrors
     * is false, the hierarchy is <B>not</B> updated. After the parsing task finishes,
     * the hiearchy will reflect the state of the document at the time parse() was called,
     * or a more recent state, if there were multiple parse() requests before the task
     * was processed.
     * @return Task that can be tested for completion or can be listened on
     */
    public org.openide.util.Task parse(int priority, boolean ignoreClean, boolean acceptErrors) {
        ParsableObjectRequest req=new ParseSourceRequest();
        return parse(priority, ignoreClean, acceptErrors, req);
    }

    public org.openide.util.Task parse(int priority, boolean ignoreClean, boolean acceptErrors, ParsableObjectRequest req) {
	if (DEBUG) {
	    Util.trace("*** ParsingSupport.parse()");
	}
        Processor immediate;
        SourceElement.Impl i = null;
        // #20100 - order locks properly: getEditorSupport() is likely to 
        // access/lock some CookieSet, and cookies tend to call/synchronize
        // on the parser support.
        CloneableEditorSupport editSupport = docBinding.getEditorSupport();
        synchronized (this) {
            if (DEBUG) {
                System.err.println("Got parse request, prio = " + priority + " ignoreClean = " + ignoreClean + " acceptErrs = " + acceptErrors); // NOI18N
                i = getSourceImpl();
                System.err.println("Data = " + i + " clean = " + this.clean); // NOI18N
                System.err.println("Parsing task = " + currentRequest + "/" + runningRequest); // NOI18N
            }
            if (currentRequest != null) {
                // if THIS is the parsing thread, then -- well, it's bad.
                // temporal resolution: take out the request IMMEDIATELY.
                if (PARSING_RP.isRequestProcessorThread()) {
                    if (DEBUG)
                        System.err.println("Running in parsing thread!"); // NOI18N
                    immediate = currentRequest;
                } else {                
                    currentRequest.enableErrors(acceptErrors);
                    currentRequest.setPriority(priority);
                    if (DEBUG)
                        System.err.println("Returning task from current request " + currentRequest); // NOI18N
                    return currentRequest.getClientTask();
                }
            } else {
                i = getSourceImpl();
                if (i != null && this.clean && !ignoreClean) {
                    if (DEBUG)
                        System.err.println("Returning finished task"); // NOI18N
                    return new FinishedTask(i);
                }
		/*
		if (req.getSourceName() != null) {
		    Util.trace("*** ParsingSupport.parse: sourceName="+req.getSourceName());
		}
		*/
                Processor proc = new Processor(priority, parsingEnv, editSupport,req);
                proc.enableErrors(acceptErrors);
                if (PARSING_RP != null && PARSING_RP.isRequestProcessorThread()) {
                    immediate = proc;
                } else {
                    addRequest(proc, priority);
                    return proc.getClientTask();
                }
            }
        }
        immediate.run();
        i = getSourceImpl();
	    
        return new FinishedTask(i);
    }    
    public synchronized org.openide.util.Task getCurrentTask() {
        if (currentRequest!=null)
            return currentRequest.getClientTask();
        return new FinishedTask(null);
    }

    private static class FinishedTask extends org.openide.util.Task {
        private Object hook;
        
        public FinishedTask(Object o) {
            super(null);
            hook = o;
        }
    }
    
    public void fireElementPropertyChange(Element source, PropertyChangeEvent evt) {
        if (source == getSource()) {
            proxy.propertyChange(evt);
        } else {
            updater.firePropertyChange(source, evt);
        }
    }
    
    /**
     * Returns the parser engine used by this Support.
     */
    public ParserEngine getParserEngine() {
        return this.engine;
    }
    
    /** Replaces the parser engine with the given implementation. All
     * parse requests issued from now on will use the new engine impl.
     */
    public void setParserEngine(ParserEngine eng) {
        this.engine = eng;
    }

    /**
     * Prepares data for the MetaSlang hierarchy from the source. If some data already
     * exists, they are not refreshed, and the Task is reaturned in already finished
     * state.
     * @return task object that is set to completed after the data is prepared.
     */
    public org.openide.util.Task prepare() {
        return parse(PRIORITY_BACKGROUND, false, false);
    }
    
    public SourceElement getSource() {
        if (this.src != null)
            return src;
        synchronized (this) {
            if (src != null)
                return src;
            return src = createSourceProxy();
        }
    }
    
    /**
     * Invalidates contents of the parser support. This method should be called
     * when the original data source is discarded. The parser support is not
     * expecting to be valid ever again after this call.
     */
    public void invalidate() {
        SourceElement.Impl impl;
        synchronized (this) {
            if (!valid)
                return;
            impl = getSourceImpl();
            if (impl == null)
                return;
            valid = false;
        }
        updater.invalidateModel(getSource());
        synchronized (this) {
            if (!updating)
                refImplementation = null;
        }
        changeStatus(SourceElement.STATUS_NOT);
    }
        
    
    protected void changeStatus(int newStatus) {
        int oldStatus = status;
        status = newStatus;
        if (propSupport != null && propSupport.hasListeners(null))
            propSupport.firePropertyChange(PROP_STATUS, oldStatus, newStatus);
        fireStateChange();
    }
    
    protected void fireStateChange() {
        if (changeList == null)
            return;
        Collection copy;
        
        synchronized (changeList) {
            if (changeList.isEmpty())
                return;
            copy = new ArrayList(changeList);
        }
        ChangeEvent e = new ChangeEvent(this);
        
        for (Iterator it = copy.iterator(); it.hasNext(); ) {
            try {
                ((ChangeListener)it.next()).stateChanged(e);
            } catch (RuntimeException x) {
                if (Boolean.getBoolean("netbeans.debug.exceptions")) // NOI18N
                    x.printStackTrace();
            }
        }
    }
    
    public SourceElement.Impl getSourceImpl() {
        Object impl = refImplementation == null ? null : refImplementation.get();
        return (SourceElement.Impl)impl;
    }
    
    public LangModel getModel() {
        return this.model;
    }
    
    public SourceElement.Impl findSourceImpl() throws SourceException {
        synchronized (this) {
            SourceElement.Impl impl = getSourceImpl();
            if (impl != null)
                return impl;
            //Util.log("impl = null"); // NOI18N
            if (savedException != null)
                throw savedException;
        }
        throw new SourceException("Cannot acquire source"); // NOI18N
    }
    
    /**
     * Invalidates the data in the specified region (bounds inclusive).
     * @return true, if validity pattern of the parsed data changes.
     */
  public void sourceChanged(int from, int to) {
    Processor req = currentRequest;    
    clean = false;
    if (req != null)
      req.sourceChanged();
  }
  
    /**
     * Retrieves the Throwable that caused the parsing to abort. This will be
     * mainly an IOException.
     * @return Throwable that aborted the last most recent parse request.
     */
    public SourceException getErrorCause() {
        return savedException;
    }

    /*--------------------------------------------------------------------------------*/
    private boolean clean;
    
    private Env parsingEnv;
    
    /**
     * Parser engine this support is working with.
     */
    private ParserEngine    engine;

    /** IOException saved (?) from the last parsing process. If no change is
     * reported to the underlying document, the exception is immediately
     * thrown without attempting to parse.
     */
    private SourceException     savedException;
    
    /**
     * SourceElement that is bound to the proxy. The proxy, if needed constructs the
     * real Impl. The element, once constructed, is not freed unless the ParsingSupport
     * dies as well.
     */
    private SourceElement   src;
    
    /**
     * The request object that is filed to the parsing queue. Since the request has not
     * yet touched by the RequestProcessor, it is safe to change paramterers for it.
     */
    private Processor       currentRequest;
    
    /** The request that is currently running, null if none. This request is currently
     * being serviced by the RequestProcessor.
     */
    private Processor       runningRequest;

    /**
     * Language model interface.
     */
    LangModel           model;

    /**
     * Extended interface for updating the language model.
     */
    LangModel.Updater   updater;

    /**
     * Proxy for SourceElement's implementation, can handle some requests.
     */
    private SourceImplProxy  proxy;
    
    /**
     * A Weak/Soft reference to the real implementation.
     */
    private Reference       refImplementation;
    
    /**
     * Parsing status of the source - it is one of SourceElement.STATUS_* symbolic
     * constatnts.
     */
    private int             status;
    
    /**
     * Collection of ChangeListeners registered with this Support.
     */
    Collection              changeList;
    
    /**
     * SourceImpl reference management
     */
    private static ReferenceQueue   refQueue;
    
    private static Map              referenceSupportMap;
    
    DocumentBinding         docBinding;
    
    private SourceElement createSourceProxy() {
        return new SourceElement(proxy = new SourceImplProxy(this));
    }
    
    Node.Cookie findCookieForSource(Class type) {
        if (src == null)
            return null;
        return parsingEnv.findCookie(getSource(), type);
    }
    
    /**
     * Retrieves the parsing status of the source. The value is one of the symbolic
     * SourceElement.STATUS_* constants.
     */
    public int getStatus() {
        int s = status;
        if (s != SourceElement.STATUS_OK)
            return s;
        SourceElement.Impl impl = getSourceImpl();
        if (impl == null)
            changeStatus(SourceElement.STATUS_NOT);
        return status;
    }
    
    /**
     * Called from within the RequestProcessor's Runnable to actually update
     * the model with gathered data. The update lock has been already acquired by the
     * caller.
     */
    private SourceElement.Impl updateSourceModel(DocumentModelUpdater builder) 
        throws SourceException {

	if (DEBUG) {
	    Util.log("*** ParsingSupport.updateSourceModel()");
	}
        SourceElement.Impl currentImpl = getSourceImpl();
        SourceElement.Impl finalImpl = currentImpl;
        boolean created;

        synchronized (this ) {
	    if (DEBUG) {
		Util.log("*** ParsingSupport.updateSourceModel(): entered synchronized block");
	    }
            if (!valid)
                throw new SourceException.IO("Source was deleted");
            updating = true;
	    if (DEBUG) {
		Util.log("updating"); // NOI18N
	    }
            if ((created = (currentImpl == null))) {
                currentImpl = updater.createSource();
            }
        }
        try {
            // this call lazy-initializes the proxy
            SourceElement s = getSource();

            docBinding.enableGenerator(false);
            proxy.notifyInProgress(Thread.currentThread(), currentImpl);

            if (created) {
                currentImpl.attachedToElement(s);
                ((ElementImpl)currentImpl).setBinding(docBinding.bindSource(s));
            }

            if (DEBUG) {
		Util.log("Trying to update the model"); // NOI18N
	    }
            builder.updateModel(updater, s, currentImpl);
            if (finalImpl == null)
                updater.activate(s);
            if (DEBUG) {
		Util.log("Update bindings"); // NOI18N
	    }
            builder.updateBindings(docBinding);
            finalImpl = currentImpl;
            synchronized (this) {
                updating = false;
                if (!valid) 
                    throw new SourceException.IO("Source was deleted");
            }
            //Util.log("register data = " + finalImpl); // NOI18N
            registerData(finalImpl);

        } finally {
            docBinding.enableGenerator(true);
            proxy.setModelDelegate(finalImpl, created);
        }
        return finalImpl;
    }
    
    public org.openide.util.Task addParsingRunnable(Runnable r, int priority) {
        return PARSING_RP.post(r, priority);
    }
    

    static final Runnable EMPTY_RUNNABLE = new Runnable() {
	    public void run() {}
	};
    
    /**
     * Helper class that is put to the parsing RequestProcessor to carry out 
     * a specific ParseRequest.
     */
    private class Processor extends Object implements
        Runnable, CommitListener, ParseObjectRequest {
        Processor             chained;
        int                   priority;
        RequestProcessor.Task ownTask;
        boolean               errorsOK;
        //SourceElement.Impl    implHook;
        int                   stage;
        int                   resultStatus;
        ParsableObjectRequest request;
        T                     task;
        
        Processor(int priority, Env env, CloneableEditorSupport supp,ParsableObjectRequest req) {
            request=req;
            task = new T();
            request.setEnvironment(env); 
            request.setEditorSupport(supp); 
        }
        
        /**
         * If run() is directly invoked on the request processor task, it means
         * that the request processor thread itself needs to complete the task before
         * executing. We have to evaluate the task at once.
         */
        protected void directRun() {
            do {
                run();
            } while (stage >= 0);
        }
        
        public void setPriority(int prior) {
            if (this.priority > prior)
                return;
            priority = prior;
            // if the task cannot be cancelled, it is being processed right now,
            // or it was already completed.
            if (ownTask.cancel()) {
                addRequest(this, prior); 
            }
        }
        
        public void enableErrors(boolean enable) {
            errorsOK |= enable;
        }
        
        public void chainRequest(Processor other) {
            chained = other;
        }
        
        public void setProcessorTask(RequestProcessor.Task t) {
            ownTask = t;
        }
                
        public void run() {
            //Util.log("processing request " + this + " stage " + stage); // NOI18N
            try {
                switch (stage++) {
		case 0:
		    if (DEBUG) {
			System.err.println("Starting request " + this); // NOI18N
		    }
		    parseLockModel();
		    break;
		case 1:
		    updateModel();
		    break;
                }
	    } catch (SourceException.IO e) {
		// the exception is expected - I/O in reading sources. Mark the source as errorenous.
		resultStatus = SourceElement.STATUS_ERROR;
            } catch (Throwable e) {
                savedException = new SourceException(e.getLocalizedMessage());
                parsingEnv.annotateThrowable(savedException, e);
                parsingEnv.annotateThrowable(savedException, "Parser error", false); // NOI18N
		org.openide.ErrorManager.getDefault().notify(e);
                resultStatus = SourceElement.STATUS_ERROR;
            } finally {
                stage--;
            }
            //Util.log("request " + this + " stage " + (stage + 1) + " end"); // NOI18N
            if (stage > 0)
                return;
            
            if (resultStatus != -1) {
                complete();
            } else {
                // it's a pity -- reschedule the request.
                request.notifyReschedule();
                //Util.log("Rescheduling request"); // NOI18N
                stage = 0;
                addRequest(this, priority);
            }
        }
        
        private void updateModel() throws SourceException {
            model.removePreCommitListener(this);
	    if (DEBUG) Util.log("*** ParsingSupport$Process.updateModel(): getSyntaxErrors()="+getSyntaxErrors()+", errorsOK="+errorsOK+", sourceImpl="+getSourceImpl()+", isValid()="+isValid());
            if (getSyntaxErrors() > 0 && !errorsOK && getSourceImpl() != null) {
                // don't update the model at all.
		if (DEBUG) Util.log("*** ParsingSupport$Process.updateModel(): model is not updated!!!");
                resultStatus = SourceElement.STATUS_PARTIAL;
                return;
            }
            if (isValid()) {
                // we have the write lock, noone changed the model
                // since we started.
                SourceElement.Impl i = null;
                
                DocumentModelUpdater updater = request.getUpdater();
                if (updater != null) 
                    i = updateSourceModel( updater );
                if (i == null) {
                    resultStatus = SourceElement.STATUS_NOT;
                } else {
                    // SUCCESS (?)
                    resultStatus = getSyntaxErrors() > 0 ?
                        SourceElement.STATUS_PARTIAL : SourceElement.STATUS_OK;
                }
                return;
            }
        }
        
        private void parseLockModel() throws SourceException {
	    if (DEBUG) Util.trace("*** ParsingSupport$Processor.parseLockModel()");
            model.addPreCommitListener(this);
            resultStatus = -1;
            synchronized (ParsingSupport.this) {
                runningRequest = this;
                if (DEBUG) {
		    Util.log("Running request = " + this); // NOI18N
		}
            }
            savedException = null;
            try {
                runningRequest = this;
                if (DEBUG) {
		    Util.log("Before calling parser engine"); // NOI18N
		}
                process(getParserEngine());
                if (DEBUG) {
		    Util.log("After calling parser engine"); // NOI18N
		}
                if (isValid()) {
		    if (DEBUG) {
			Util.log("Request " + this + " processed. Still valid"); // NOI18N
		    }
                    stage = 1;
                    if (DEBUG) {
			Util.log("trying to run update"); // NOI18N
		    }
                    ParsingSupport.this.updater.runUpdate(this, true);
                }
            } catch (IOException ex) {
                savedException = new SourceException.IO(ex);
                parsingEnv.annotateThrowable(savedException, ex);
                // notify listeners that we are finished.
                resultStatus = SourceElement.STATUS_ERROR;
            } catch (InternalError er) {
                // the parser sometimes issues this one -- just issue an error
                savedException = new SourceException(er.getMessage());
                parsingEnv.annotateThrowable(savedException, er);
                resultStatus = SourceElement.STATUS_ERROR;
            } finally {
                model.removePreCommitListener(this);
            }
            runningRequest = null;
        }
        
        public void complete() {
            synchronized (ParsingSupport.this) {
                if (currentRequest == this)
                    currentRequest = null;
            }
            changeStatus(resultStatus);
            task.complete();
            if (chained != null)
                chained.complete();
            // signal -- processing is finally over.
            stage = -1;
        }
        
        public void changesCommited(Set created, Set removed, Map changed) {
            request.modelChanged();
        }

        /**
         * Causes the request to be passed immediately to the parsing engine.
         * If the request is already processed, it returns immediately.
         */
        public void process(ParserEngine eng) throws IOException {
            eng.process(this);
        }

        /**
         * Returns a task clients can wait for. This is *NOT* a task which processes the
         * request, since the request can be rescheduled several times before it is
         * completed (if it is completed).
         */
        public org.openide.util.Task getClientTask() {
            return task;
        }

        /**
         * Notifies the request that the source text has been changed. This causes
         * cancellation of the request in some cases.
         */
        public void sourceChanged() {
            request.sourceChanged();
        }

        /* ParseObjectRequest method is delegated to request object */
        public void setSyntaxErrors(int errors) {
            request.setSyntaxErrors(errors);
        }

        public void setSemanticErrors(int errors) {
            request.setSemanticErrors(errors);
        }

        public void notifyStart() {
            request.notifyStart();
        }

        public void notifyComplete() {
            request.notifyComplete();
        }

        public boolean isValid() {
            return request.isValid();
        }

        public boolean needsProcessing() {
            return request.needsProcessing();
        }

        public int getSyntaxErrors() {
            return request.getSyntaxErrors();
        }

        public ElementFactory getFactory() {
            return request.getFactory();
        }

        public char[] getSource() throws java.io.IOException {
            clean = true;
            return request.getSource();
        }

	public Reader getSourceReader() throws java.io.IOException {
	    return request.getSourceReader();
	}

	public FileObject getSourceFile(){
	    return request.getSourceFile();
	}

        public Object getParserType() {
            return request.getParserType();
        }

        public void pushError(int line, int column, String message) {
            request.pushError(line, column, message);
        }
        
        public String getSourceName() {
            return request.getSourceName();
        }
        
        public Collection getSourcePath() {
            return request.getSourcePath();
        }
        
        /* --------------------------------------------------------------------*/

        /** The class is NOT static intentionally - it holds a hard reference
         * to the request, keeping its data alive.
         */
        private class T extends org.openide.util.Task {
            T() {
                super(EMPTY_RUNNABLE);
            }

            public void run() {
                Processor.this.directRun();
            }

            protected void complete() {
                super.notifyFinished();
            }
        }
    }
    
    /* --------------------------------------------------------------------*/
    static RequestProcessor    PARSING_RP;
    
    private void addRequest(Processor proc, int priority) {
	//edu.kestrel.netbeans.Util.trace("*** ParsingSupport.addRequest: proc="+proc+" priority="+priority);
        if (PARSING_RP == null) {
            synchronized(this) {
                if (PARSING_RP == null) {
		    //edu.kestrel.netbeans.Util.log("*** ParsingSupport.addRequest: creating new RequestProcessor for parsing");
                    PARSING_RP = new RequestProcessor("MetaSlang source parsing"); // NOI18N
		}
            }
        }
        synchronized (this) {
            if (currentRequest != proc) {
                if (currentRequest != null) 
                    proc.chainRequest(currentRequest);
                currentRequest = proc;
            }
            proc.setProcessorTask(PARSING_RP.post(proc, priority));
        }
    }
    
    protected static DataFinalizer finalizer;
    /**
     * Send finalization notices every 30s
     */
    private static final int FINALIZE_TIMEOUT   = 30000;
    
    protected void registerData(SourceElement.Impl data) {
        synchronized (ParsingSupport.class) {
            if (finalizer == null) {
                finalizer = new DataFinalizer();
                RequestProcessor.getDefault().post(finalizer, FINALIZE_TIMEOUT, Thread.MIN_PRIORITY);
            }
        }
        Reference r = finalizer.registerParsingInfo(this, data, refImplementation);
        synchronized (this) {
            refImplementation = r;
        }
    }
    
    protected void notifyFinalized(Reference refImpl) {
        int oldStatus;
        
        synchronized (this) {
            if (refImplementation != refImpl)
                return;
            refImplementation = null;
        }
        changeStatus(SourceElement.STATUS_NOT);
    }
    
    private static class DataFinalizer implements Runnable {
        private Map             mapSupportData;
        private ReferenceQueue  finalizedQueue;
        
        DataFinalizer() {
            mapSupportData = new HashMap(37);
            finalizedQueue = new ReferenceQueue();
        }
        
        public synchronized Reference registerParsingInfo(ParsingSupport supp, 
							  SourceElement.Impl data, Object oldRef) {
            if (oldRef != null)
                mapSupportData.remove(oldRef);
            Reference newRef = new WeakReference(data, finalizedQueue);
            mapSupportData.put(newRef, new WeakReference(supp));
            return newRef;
        }
        
        public void run() {
            Reference f;

            while ((f = finalizedQueue.poll()) != null) {
                Reference refSupp;
                
                synchronized (this) {
                    refSupp = (Reference)mapSupportData.get(f);
                }
                if (refSupp == null)
                    continue;
                ParsingSupport supp = (ParsingSupport)refSupp.get();
                if (supp == null)
                    continue;
                supp.notifyFinalized(f);
            }
            RequestProcessor.getDefault().post(this, FINALIZE_TIMEOUT, Thread.MIN_PRIORITY);
        }
    }
}
