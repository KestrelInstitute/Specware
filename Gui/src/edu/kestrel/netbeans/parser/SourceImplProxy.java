/*
 * SourceImplProxy.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/04/23 01:16:26  weilyn
 * DiagElemInfo.java
 *
 * Revision 1.4  2003/04/01 02:29:44  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.3  2003/03/29 03:14:03  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.2  2003/03/14 04:15:33  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:27  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.util.Iterator;
import java.util.Collection;
import java.util.List;
import java.util.LinkedList;
import javax.swing.text.StyledDocument;

import org.openide.nodes.Node;
import org.openide.src.SourceException;
import org.openide.text.NbDocument;
import org.openide.util.Task;
import org.openide.util.TaskListener;

import edu.kestrel.netbeans.model.*;
import org.openide.ErrorManager;

/*--------------------------------------------------------------------------------*/
/**
 * The class serves as a delegating proxy that forwards all model-related
 * requests to the actual implementation in the model while it processes
 * management functions that are (for historical reasons) available on
 * SourceElement.
 */
public class SourceImplProxy implements SourceElement.Impl, Node.Cookie,
PropertyChangeListener {
    
    private static final SpecElement[] NO_SPECS = new SpecElement[0];
    private static final ProofElement[] NO_PROOFS = new ProofElement[0];
    private static final MorphismElement[] NO_MORPHISMS = new MorphismElement[0];
    private static final DiagramElement[] NO_DIAGRAMS = new DiagramElement[0];
    private static final ColimitElement[] NO_COLIMITS = new ColimitElement[0];
    //private static final UIDElement[] NO_UIDS = new UIDElement[0];
    
    /**
     * PropertyChangeListeners attached to the SourceElement.
     */
    LinkedList              listeners;
    
    /**
     * The Element representing this proxy/impl. Once set, the element cannot be
     * changed.
     */
    SourceElement           srcElement;
    
    /**
     * The real parser core
     */
    ParsingSupport          supp;
    
    /**
     * Thread, that should not be blocked during data extraction. Instead of
     * blocking on parser's completion, this thread should be directed at
     * temporary implementation.
     */
    Thread                  dontBlockThread;
    
    /**
     * Task to wait for. If not null, all getters and setters need to be blocked
     * on that task; data are live until that task finishes.
     */
    Task                    waitTask;
    
    /**
     * Temporary delegate object to use during data extraction. The thread that
     * creates the data structure need to access the SourceElement, possibly through
     * the OpenAPI calls.
     */
    SourceElement.Impl      tempDelegate;
    
    private static final long serialVersionUID = 3120888788645227532L;
    
    /**
     * Constructs the Impl proxy object for the given ParsingSupport.
     */
    public SourceImplProxy(ParsingSupport parsingSupp) {
        this.supp = parsingSupp;
        supp.addPropertyChangeListener(this);
    }
    
    /**
     * Returns the SourceElement representing the hierarchy.
     */
    protected SourceElement getElement() {
        return this.srcElement;
    }
    
    /**
     * OpenAPI callback; called when the SourceElement is constructed. This implementation
     * only records the reference
     */
    public void attachedToElement(Element el) {
        this.srcElement = (SourceElement)el;
    }
    
    /**
     * Retrieves the status of the parsing operation. Delegates to ParsingSupport.
     */
    public int getStatus() {
        return supp.getStatus();
    }
    
    /**
     * Implementation of OpenAPI prepare() call. Delegates to ParsingSupport's
     * prepare(), ignores errors and does nothing if the source is up-to-date.
     */
    public Task prepare() {
        return supp.parse(ParsingSupport.PRIORITY_BACKGROUND, false, false);
    }
    
    public void changeSpecs(SpecElement[] elems, int action) throws SourceException {
        findModelDelegate().changeSpecs(elems, action);
    }
    
    public SpecElement[] getSpecs() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getSpecs(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getSpecs(): specs="+impl.getSpecs());
            return impl.getSpecs();
        }
        return NO_SPECS;
    }
    
    public SpecElement getSpec(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getSpec(name);
        return null;
    }
    
    public void changeProofs(ProofElement[] elems, int action) throws SourceException {
        findModelDelegate().changeProofs(elems, action);
    }
    
    public ProofElement[] getProofs() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getProofs(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getProofs(): specs="+impl.getProofs());
            return impl.getProofs();
        }
        return NO_PROOFS;
    }
    
    public ProofElement getProof(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getProof(name);
        return null;
    }
    
    public void changeMorphisms(MorphismElement[] elems, int action) throws SourceException {
        findModelDelegate().changeMorphisms(elems, action);
    }
    
    public MorphismElement[] getMorphisms() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getMorphisms(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getMorphisms(): specs="+impl.getMorphisms());
            return impl.getMorphisms();
        }
        return NO_MORPHISMS;
    }
    
    public MorphismElement getMorphism(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getMorphism(name);
        return null;
    }

    public void changeDiagrams(DiagramElement[] elems, int action) throws SourceException {
        findModelDelegate().changeDiagrams(elems, action);
    }
    
    public DiagramElement[] getDiagrams() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getDiagrams(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getDiagrams(): specs="+impl.getDiagrams());
            return impl.getDiagrams();
        }
        return NO_DIAGRAMS;
    }
    
    public DiagramElement getDiagram(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getDiagram(name);
        return null;
    }

    public void changeColimits(ColimitElement[] elems, int action) throws SourceException {
        findModelDelegate().changeColimits(elems, action);
    }
    
    public ColimitElement[] getColimits() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getColimits(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getColimits(): specs="+impl.getColimits());
            return impl.getColimits();
        }
        return NO_COLIMITS;
    }
    
    public ColimitElement getColimit(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getColimit(name);
        return null;
    }

   /* public void changeUIDs(UIDElement[] elems, int action) throws SourceException {
        findModelDelegate().changeUIDs(elems, action);
    }
    
    public UIDElement[] getUIDs() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null) {
	    System.err.println("*** SourceImplProxy.getUIDs(): impl="+impl);
	    System.err.println("*** SourceImplProxy.getUIDs(): specs="+impl.getUIDs());
            return impl.getUIDs();
        }
        return NO_UIDS;
    }
    
    public UIDElement getUID(String name) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getUID(name);
        return null;
    }*/
    
    public Collection getPropertyChangeListeners() {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            return impl.getPropertyChangeListeners();
        return null;
    }
    
    public void updateMemberOrder(Element[] orderedMembers) {
        SourceElement.Impl impl = safeFindModelDelegate();
        if (impl != null)
            impl.updateMemberOrder(orderedMembers);
    }
    
    /**
     * Implementation of getCookie(). The implementation fakes cookies of all interfaces
     * on this object; if the cookie is not available, it asks the environment to
     * provide the cookie and IF the cookie descends from the implementation hierarchy
     * passes the request on to the real SourceElement's implementation, optionally
     * parsing it from the source.
     */
    public Node.Cookie getCookie(Class type) {
        if (type.isAssignableFrom(getClass()))
            return this;
        SourceElement.Impl impl = supp.getSourceImpl();
        if (impl != null)
            return impl.getCookie(type);
        // PENDING: ask the environment about cookies.
        if (!edu.kestrel.netbeans.model.ElementImpl.class.isAssignableFrom(type))
            return this.supp.findCookieForSource(type);
        impl = safeFindModelDelegate();
        if (impl == null)
            return null;
        return impl.getCookie(type);
    }
    
    /**
     * No effect on SourceElements, there's only one of them in a source :-)
     */
    public void markCurrent(boolean beforeAfter) {
    }
    
    /**
     * Exclusively locks the model for the execution of the Runnable object. Note that
     * the implementation does *NOT* lock the document! Also, do *NOT* call the
     * method if you have already locked the document for writing unless you
     * _REALLY_ know what you are doing.
     */
    public void runAtomic(final Runnable run) {
        final StyledDocument doc;
        try {
            doc = supp.docBinding.getEditorSupport().openDocument();
        } catch (java.io.IOException ex) {
            return;
        }
        try {
            supp.model.runAtomic(new Runnable() {
                public void run() {
                    try {
                        supp.docBinding.enableAtomicAsUser(true);
                        NbDocument.runAtomic(doc, run);
                    } finally {
                        supp.docBinding.enableAtomicAsUser(false);
                    }
                }
            });
        } catch (SourceException ex) {
        }
    }
    /**
     * Creates an atomic transaction, that respects the guarded sections inside
     * the document, over the model. Again, this does *NOT* lock the document.
     */
    public void runAtomicAsUser(final Runnable run) throws SourceException {
        final StyledDocument doc;
        try {
            doc = supp.docBinding.getEditorSupport().openDocument();
        } catch (java.io.IOException ex) {
            throw new SourceException.IO(ex);
        }
        supp.model.runAtomic(new Runnable() {
            public void run() {
                try {
                    supp.docBinding.enableAtomicAsUser(true);
                    NbDocument.runAtomic(doc, run);
                } finally {
                    supp.docBinding.enableAtomicAsUser(false);
                }
            }
        });
    }
    
    /**
     * Adds a PropertyChangeListener
     */
    public synchronized void addPropertyChangeListener(PropertyChangeListener l) {
        if (listeners == null) {
            listeners = new LinkedList();
        }
        boolean attach = listeners.isEmpty();
        listeners.add(l);
        SourceElement.Impl impl = supp.getSourceImpl();
        if (impl != null && attach)
            impl.addPropertyChangeListener(this);
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener l) {
        if (listeners == null)
            return;
        listeners.remove(l);
        // does not remove (this) listener from the SourceElement.Impl
    }
    
    public Object readResolve() {
        return null;
    }
    
    /**
     * Attempts to locate the Impl object provided by the "real" model. If the object
     * cannot be acquired (for example missing or unparseable source), it throws a
     * SourceException.
     */
    protected SourceElement.Impl findModelDelegate() throws SourceException {
        /* This is a gate for the INITIALIZING thread to get through the
         * proxy. All other threads will fail miserably waiting on te
         * parsing task. */
        if (dontBlockThread == Thread.currentThread()) {
            return tempDelegate;
        }
        
        // optionally throws a SourceException, if the error cause is known.
        SourceElement.Impl candidate = supp.getSourceImpl();
        if (candidate != null)
            return candidate;
        
        Task t;
        t = supp.parse(ParsingSupport.PRIORITY_DEMAND, false, false);
        t.waitFinished();
        SourceElement.Impl i = supp.findSourceImpl();
        t.isFinished();
        return i;
    }
    
    /**
     * Safe variant of the method above -- does not throw any exceptions, but rather
     * returns null, if the source element cannot be created.
     */
    protected SourceElement.Impl safeFindModelDelegate() {
        try {
            return findModelDelegate();
        } catch (SourceException ex) {
            return null;
        }
    }
    
    /**
     * PropertyChangeListener implementation that refires all property changes
     * to the listeners attached to a SourceElement.
     */
    public void propertyChange(PropertyChangeEvent evt) {
        List l;
        synchronized (this) {
            if (listeners == null)
                return;
            l = new java.util.ArrayList(listeners);
        }
        // remap the event so that it appears to be fired from the source element.
        evt = new PropertyChangeEvent(
        srcElement, evt.getPropertyName(),
        evt.getOldValue(), evt.getNewValue());
        
        for (Iterator it = l.iterator(); it.hasNext(); ) {
            PropertyChangeListener ll = (PropertyChangeListener)it.next();
            ll.propertyChange(evt);
        }
    }
    
    /**
     * Called by the ParsingSupport to notify the proxy, that data extraction is
     * in progress; the call also informs about the thread that performs updates
     * and therefore should not be blocked.
     * @param t thread updating the model
     * @param tempDelegate temporary delegate that is being updated with fresh data and
     * should be delegated to during the update cycle.
     */
    void notifyInProgress(Thread t, SourceElement.Impl tempDelegate) {
        this.dontBlockThread = t;
        this.tempDelegate = tempDelegate;
    }
    
    /**
     * This method is called by the ParsingSupport when it finally constructs
     * the implementation object. Temp delegate is not needed any more and
     * non-blocking thread is obsolete, too.
     * @param delegate the final delegate to use, may be null if the update fails.
     * @param created true, if the delegate was created rather than refreshed. In that
     * case, a listener is attached to watch PropertyChangeEvents.
     */
    protected synchronized void setModelDelegate(SourceElement.Impl delegate, boolean created) {
        List ls = listeners;
        synchronized (this) {
            // clear blocking/task information
            dontBlockThread = null;
            tempDelegate = null;
            waitTask = null;
        }
        if (!created || ls == null || delegate == null)
            return;
        // add ONE property change listener:
        // The listener is *NOT* Weak intentionally; the implementation object prevents
        // the Proxy from being GCed.
        delegate.addPropertyChangeListener(this);
    }
    
    
}
