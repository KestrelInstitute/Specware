/*
 * DefaultLangModel.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.10  2003/07/05 07:46:37  lambert
 * *** empty log message ***
 *
 * Revision 1.9  2003/06/23 18:00:15  weilyn
 * internal release version
 *
 * Revision 1.8  2003/04/23 01:14:38  weilyn
 * BindingFactory.java
 *
 * Revision 1.7  2003/04/01 02:29:36  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.6  2003/03/29 03:13:55  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:14:00  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:12:54  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:14:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:54  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.beans.PropertyChangeEvent;
import java.lang.reflect.Modifier;
import java.util.*;

import org.openide.src.SourceException;
import org.netbeans.modules.java.model.CommitListener;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.codegen.ExceptionRunnable;

/**
 * This is the root point of the source text model. This object creates individual
 * model's elements and performs model-related tasks. All elements in the model have
 * (indirect) references to this object so they can contact it.
 */
public class DefaultLangModel implements LangModel, LangModel.Updater, Runnable {
    private static boolean  initialized;
    
    private static Class    MEMBER_IMPL;
    
    static final Positioner DEFAULT_POSITIONER = new DefaultInsertStrategy();
    
    /** Mutex object for the whole model. The lock is obtained during model updates so
     * change detection and property changes are really atomic.
     */
    private Object      locked;
    
    private Env         env;
    
    private Object      writerNotify;
    
    private Thread      writingThread;
    
    private int         readerCount;
    
    private Thread      reader;
    
    // derived attributes:
    private BindingFactory  bindingFactory;
    
    private WrapperFactory  wrapperFactory;
    
    /** Event queue map for individual elements in the model. The map is keyed by
     * element instances, values maps <property_name> -> <property change event>
     */
    private EventQueue  eventQueue;
    
    /** Number of nested atomic locks.
     */
    private int         writeLocks;
    
    private int         masterLocks;
    
    /**
     * True, if all changes made in the transaction should be commited upon lock
     * release.
     */
    private boolean     transactionCommited;
    
    /**
     * True, if the transaction is constrained - changes are consulted with
     * VetoableChangeListeners and checked for consistency.
     */
    private boolean     transactionConstrained;
    
    /**
     * True, if the model is currently dispatching events.
     */
    private boolean     eventDispatch;

    /**
     * List of currently registered pre-commit listners.
     */
    Collection          preCommitListeners;
    
    /**
     * List of currently registered post-commit listeners.
     */
    Collection          postCommitListeners;
    
    /**
     * Holds top-level EventQueues in the order of dispatching. New queues are appened
     * during unlock to preserve the order of event generation.
     */
    LinkedList           outputQueue;
    
    boolean              firingEvents;
    
    public DefaultLangModel(Env env) {
        this.env = env;
        writerNotify = new Object();
        this.eventQueue = new EventQueue(null);
    }
    
    private static void initializeClasses() {
        if (initialized)
            return;
        try {
            MEMBER_IMPL = Class.forName("edu.kestrel.netbeans.model.MemberElementImpl"); // NOI18N
        } catch (ClassNotFoundException ex) {
            // warn -- the class was not found.
        }
        initialized = true;
    }
    
    /** Clone the model object; the method does not clone the whole model, it rather clones
     * the management object so that objects created by the clone are compatible with
     * the original one. Usable mainly for paralel analysis of two sources and matching
     * them up.
     */
    public Object clone() {
        return null;
    }
    
    /*----------------------------------------------------------------  
     * Factory methods for creating implementations of 
     * model pieces
     *----------------------------------------------------------------*/
    public SpecElementImpl createSpec(Element src) {
	SpecElementImpl c = new SpecElementImpl(this);
        getWrapper().wrapSpec(c, src);
        c.setParent(src);
        return c;
    }
    
    public SortElementImpl createSort(SpecElement parent) {
        SortElementImpl impl = new SortElementImpl(this);
        getWrapper().wrapSort(impl, parent);
        impl.setParent(parent);
        return impl;
    }
    
    public OpElementImpl createOp(SpecElement parent) {
        OpElementImpl impl = new OpElementImpl(this);
        getWrapper().wrapOp(impl, parent);
        impl.setParent(parent);
        return impl;
    }
    
    public DefElementImpl createDef(SpecElement parent) {
        DefElementImpl impl = new DefElementImpl(this);
        getWrapper().wrapDef(impl, parent);
        impl.setParent(parent);
        return impl;
    }
    
    public ClaimElementImpl createClaim(SpecElement parent) {
        ClaimElementImpl impl = new ClaimElementImpl(this);
        getWrapper().wrapClaim(impl, parent);
        impl.setParent(parent);
        return impl;
    }    
    
    public ImportElementImpl createImport(SpecElement parent) {
        ImportElementImpl impl = new ImportElementImpl(this);
        getWrapper().wrapImport(impl, parent);
        impl.setParent(parent);
        return impl;
    }
    
    public DiagElemElementImpl createDiagElem(DiagramElement parent) {
        DiagElemElementImpl impl = new DiagElemElementImpl(this);
        getWrapper().wrapDiagElem(impl, parent);
        impl.setParent(parent);
        return impl;
    }

    public ProofElementImpl createProof(Element src) {
        ProofElementImpl c = new ProofElementImpl(this);
        getWrapper().wrapProof(c, src);
        c.setParent(src);
        return c;
    }
    
    public MorphismElementImpl createMorphism(Element src) {
        MorphismElementImpl c = new MorphismElementImpl(this);
        getWrapper().wrapMorphism(c, src);
        c.setParent(src);
        return c;
    }

    public DiagramElementImpl createDiagram(Element src) {
        DiagramElementImpl c = new DiagramElementImpl(this);
        getWrapper().wrapDiagram(c, src);
        c.setParent(src);
        return c;
    }

    public ColimitElementImpl createColimit(Element src) {
        ColimitElementImpl c = new ColimitElementImpl(this);
        getWrapper().wrapColimit(c, src);
        c.setParent(src);
        return c;
    }    

    /*public UIDElementImpl createUID(Element src) {
        UIDElementImpl c = new UIDElementImpl(this);
        getWrapper().wrapUID(c, src);
        c.setParent(src);
        return c;
    }*/

    public SourceElementImpl createSource() {
        return new SourceElementImpl(this);
    }
        
    public void addPreCommitListener(CommitListener l) {
        synchronized (this) {
            if (preCommitListeners == null)
                preCommitListeners = new LinkedList();
        }
        synchronized (preCommitListeners) {
            preCommitListeners.add(l);
        }
    }
    
    public void addPostCommitListener(CommitListener l) {
        synchronized (this) {
            if (postCommitListeners == null)
                postCommitListeners = new LinkedList();
        }
        synchronized (postCommitListeners) {
            postCommitListeners.add(l);
        }
    }
    
    public void removePreCommitListener(CommitListener l) {
        if (preCommitListeners == null)
            return;
        synchronized (preCommitListeners) {
            preCommitListeners.remove(l);
        }
    }
    
    public void removePostCommitListener(CommitListener l) {
        if (postCommitListeners == null)
            return;
        synchronized (postCommitListeners) {
            postCommitListeners.remove(l);
        }
    }
    
    final void notifyEventsDispatched(boolean dispatchOn) {
        this.eventDispatch = dispatchOn;
    }
    
    public final Object writeLock() {
        Object l = doWriteLock();
        if (masterLocks == -1) 
            createEventQueue();
        return l;
    }
    
    private void createEventQueue() {
        eventQueue = new EventQueue(eventQueue);
    }
    
    /**
     * The method obtains a write lock, but integrates all messages to the outside
     * queue instead of creating a local one.
     */
    final Object masterWriteLock() {
        Object l = doWriteLock();
        if (masterLocks > 0) {
            try {
                releaseWriteLock(l);
            } catch (SourceException ex) {
                // should NOT happen.
            }
            throw new IllegalStateException("Nested master locks!!"); // NOI18N
        }
        masterLocks = writeLocks;
        eventQueue = new EventQueue(eventQueue);
        return l;
    }
    
    public Object tryWriteLock() {
        return tryWriteLock(false);
    }
    
    private Object tryWriteLock(boolean master) {
        synchronized (writerNotify) {
            if (locked == null ||
                writingThread == Thread.currentThread())
                return master ?
                    masterWriteLock() :
                    writeLock();
        }
        return null;
    }
    
    public final Object doWriteLock() {
	//Util.log("DefaultLangModel doWriteLock requesting lock "+writingThread +" Locked "+locked);
        synchronized (writerNotify) {
            if (writingThread == Thread.currentThread()) {
                if (eventDispatch) {
                    throw new IllegalStateException(
                        "Modification from inside the event handler are banned"); // NOI18N
                }
                writeLocks++;
                return locked;
            }
            if (locked != null) {
                try {
		    //Util.log("DefaultLangModel doWriteLock requesting lock "+writingThread +" Locked "+locked+" Thread waiting");
                    writerNotify.wait();
                } catch (InterruptedException ex) {
                    throw new IllegalStateException("Interrupted"); // NOI18N
                }
            }
            // new lock - constrain the transaction.
            transactionConstrained = true;
            writeLocks++;
            locked = writerNotify;
            this.writingThread = Thread.currentThread();
            return locked;
        }
    }
    
    /**
     * Releases the write lock held on the model. If there are any outstanding
     * events, the CommitListener events are fired prior to releasing the lock.
     * If the operation is not aborted, write lock is released and queued 
     * PropertyChangeEvents are fired out. 
     */
    public final void releaseWriteLock(Object handle) throws SourceException {
        releaseWriteLock(handle, false);
    }
    
    final void releaseWriteLock(Object handle, boolean forkThread) throws SourceException {
        if (handle == null)
            throw new IllegalArgumentException("Invalid lock: " + handle); // NOI18N
        if (locked == null)
            throw new IllegalStateException("Model not locked."); // NOI18N
        synchronized (writerNotify) {
            if (handle != locked)
                throw new IllegalArgumentException("Invalid unlock attempt."); // NOI18N
        }
        
        EventQueue result = null;
        
        if (masterLocks == -1)
            result = mergeEventQueues();
        else if (masterLocks >= writeLocks) {
            result = mergeEventQueues();
            masterLocks = -1;
        }
        if (--writeLocks > 0) {
            return;
        }
        eventQueue = null;

        // fix change events so they contain snapshots of
        // new state in addition to the live reference.        
        result.fixupChanges();
        // can throw SourceException
        firePreCommitEvents(result);
        enqueue(result);
        synchronized (writerNotify) {
	    //Util.log("DefaultLangModel releaseWriteLock releasing  lock Locked "+locked);
            this.writingThread = null;
            locked = null;
            writerNotify.notifyAll();
        }
        if (forkThread) {
            org.openide.util.RequestProcessor.getDefault().post(this);
        } else {
            processOutputQueue();
        }
    }
    
    /**
     * This method operates under a write lock -- nobody else can modify or create the queue,
     * but somebody may be reading it.
     */
    private void enqueue(EventQueue q) {
        if (outputQueue == null)
            outputQueue = new LinkedList();
        synchronized (outputQueue) {
            outputQueue.addLast(q);
        }
    }
    
    public void run() {
        processOutputQueue();
    }
    
    private void processOutputQueue() {
        if (this.outputQueue == null)
            return;
        
        EventQueue bit;
        synchronized (outputQueue) {
            if (firingEvents)
                return;
            firingEvents = true;
        }
        try {
            while (true) {
                synchronized (outputQueue) {
                    if (outputQueue.isEmpty()) {
                        return;
                    }
                    bit = (EventQueue)outputQueue.removeFirst();
                }
                bit.fireEvents();
                firePostCommitEvents(bit);
            }
        } finally {
            synchronized (outputQueue) {
                firingEvents = false;
            }
        }
    }
    
    private void firePreCommitEvents(EventQueue q) {
        fireCommitEvents(preCommitListeners, q);
    }
    
    private void firePostCommitEvents(EventQueue what) {
        fireCommitEvents(postCommitListeners, what);
    }

    private void fireCommitEvents(Collection origListeners, EventQueue data) {
        if (origListeners == null || data == null || data.isEmpty())
            return;
        
        Collection listeners;
        
        synchronized (origListeners) {
            listeners = new Vector(origListeners);
        }
        
        Set removed = data.getRemovedElements();
        Set created = data.getCreatedElements();
        Map changed = data.getChangedElements();

        /*
         * Removed - for now. A cleaner spec of the veto semantic needed.
        if (isConstrained()) {
            for (Iterator it = listeners.iterator(); it.hasNext(); ) {
                CommitListener l = (CommitListener)it.next();
                l.queryCommitChanges(created, removed, changed, writeLocks);
            }
        }
         */

        // if the lock will be released after this operation, fire summary events
        // to watchers as well.
        for (Iterator it = listeners.iterator(); it.hasNext(); ) {
            CommitListener l = (CommitListener)it.next();
	    Util.log("DefaultLangModel.fireCommitEvents listener = "+l);
            l.changesCommited(created, removed, changed);
        }
    }
    
    private EventQueue mergeEventQueues() {
        EventQueue parent = eventQueue.getParent();
        if (parent != null) {
            if (transactionCommited) {
                eventQueue.mergeToParent();
            } else {
                // PENDING: cancel ordinary events in the queue,
                // backfire all vetoable changes.
            }
            eventQueue = parent;
        }
        transactionCommited = false;
        return eventQueue;
    }
    
    public void commitChanges() {
        if (locked == null || this.writingThread != Thread.currentThread()) {
            throw new IllegalStateException("Sanity check: commit outside lock"); // NOI18N
        }
        if (masterLocks > 0 && masterLocks < writeLocks)
            return;
        this.transactionCommited = true;
    }
    
    public void runAtomic(Runnable r) throws SourceException {
        Object token = writeLock();
        try {
            r.run();
            commitChanges();
        } finally {
            releaseWriteLock(token);
        }
    }
    
    protected boolean isConstrained() {
        return this.transactionConstrained;
    }
    
    protected final org.openide.nodes.Node.Cookie findElementCookie(Element el, Class clazz) {
        return env.findCookie(el, clazz);
    }

    /**
     * Enters a special locked mode with disabled constraint and veto
     * checking.
     */
    public boolean runUpdate(Runnable r, boolean disableConstraints) 
    throws SourceException {
        Object token = tryWriteLock(true);
        if (token == null)
            return false;
        boolean saveConstraint = this.transactionConstrained;
        
        try {
            this.transactionConstrained = !disableConstraints;
            r.run();
            /*
        } catch (SourceException ex) {
            throw ex;
             */
            commitChanges();
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new SourceException("Unexpected implementation error"); // NOI18N
        } finally {
            this.transactionConstrained = saveConstraint;
            releaseWriteLock(token, true);
            return true;
        }
    }
    
    private void doRunAtomic(ExceptionRunnable r) throws SourceException {
        // nothing done here (for now).
        try {
            r.run();
        } catch (SourceException ex) {
            throw ex;
        } catch (Exception ex) {
            throw new SourceException("Unexpected implementation error."); // NOI18N
        }
    }
    
    public void runAtomic(ExceptionRunnable r) throws SourceException {
        boolean fire = false;
        boolean ok = false;
        Object token = null;

        token = writeLock();
        try {
            doRunAtomic(r);
            commitChanges();
        } finally {
            releaseWriteLock(token);
        }
    }
    
    public Object getManagementLock() {
        return writerNotify;
    }
    
    public final void readLock() {
        synchronized (writerNotify) {
            if (writingThread != null) {
                if (writingThread == Thread.currentThread()) {
                    readerCount++;
                    return;
                }
            }
            try {
                writerNotify.wait();
            } catch (InterruptedException ex) {
                // PENDING: rethrow another (Runtime) exception.
            }
            if (locked == null) {
                locked = Thread.currentThread();
            }
            readerCount++;
        }
    }

    public final void releaseReadLock() {
        synchronized (writerNotify) {
            if (--readerCount == 0) {
                if (writingThread == null) {
                    locked = null;
                    writerNotify.notifyAll();
                }
            }
        }
    }
    
    protected EventQueue getEventQueue() {
        return this.eventQueue;
    }
    
    public boolean isWriteLocked() {
        return this.writingThread != null;
    }
    
    public void notifyElementChanged(Element ref, Element old) {
        eventQueue.elementChanged(ref, old);
    }
    
    public void notifyElementCreated(Element ref) {
        eventQueue.elementCreated(ref);
    }
    
    public void notifyElementRemoved(Element ref) {
        eventQueue.elementRemoved(ref);
    }
    
    public void fireModelElementChange(ElementImpl bean, PropertyChangeEvent evt) {
        queuePropertyChange(bean, evt.getPropertyName(), evt);
    }
    
    public void fireModelElementChange(Element.Impl bean, PropertyChangeEvent evt) {
        queuePropertyChange((ElementImpl)bean, evt.getPropertyName(), evt);
    }
    
    // Model-private protocol
    ///////////////////////////////////////////////////////////////////////////////

    protected BindingFactory getBindingFactory() {
        if (this.bindingFactory != null) {
            return this.bindingFactory;
        }
        return this.bindingFactory = env.getBindingFactory();
    }
    
    public WrapperFactory getWrapper() {
        if (this.wrapperFactory != null) {
            return this.wrapperFactory;
        }
        synchronized (this) {
            if (this.wrapperFactory == null) {
                this.wrapperFactory = env.getWrapperFactory();
            }
            return this.wrapperFactory;
        }
    }
    
    // Implementation:
    ///////////////////////////////////////////////////////////////////////////////
    private void queuePropertyChange(ElementImpl bean, String name, PropertyChangeEvent evt) {
        eventQueue.addPropertyChange(bean, evt);
    }
    
    private ElementImpl getElementImpl(Element el) {
        return (ElementImpl)el.getCookie(ElementImpl.class);
    }
    
    public void updateMembers(Element target, String propertyName, Element[] els, 
        int[] orderIndices,
        int[] optMap) {
        if (target instanceof SpecElement) {
            SpecElementImpl impl = (SpecElementImpl)getElementImpl(target);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        } else if (target instanceof ProofElement) {
            ProofElementImpl impl = (ProofElementImpl)getElementImpl(target);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        } else if (target instanceof MorphismElement) {
            MorphismElementImpl impl = (MorphismElementImpl)getElementImpl(target);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        } else if (target instanceof DiagramElement) {
            DiagramElementImpl impl = (DiagramElementImpl)getElementImpl(target);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        } else if (target instanceof ColimitElement) {
            ColimitElementImpl impl = (ColimitElementImpl)getElementImpl(target);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        } else {
	    //Util.log("DefaultLangModel.updateMembers() : "+propertyName+" els = "+els.length);
	    //Util.log("DefaultLangModel.updateMembers() orderIndices = "+Util.print(orderIndices)+" optMap = "+Util.print(optMap));
            SourceElementImpl impl = (SourceElementImpl)getElementImpl(target);
	    //Util.log("DefaultLangModel.updateMembers() impl = "+impl);
            impl.updateMembers(propertyName, els, orderIndices, optMap);
        }
    }
    
    public void updateMemberOrder(Element target, String id, 
        Element[] orderedMembers) {
        if (target instanceof SourceElement) {
	    SourceElement.Impl impl = (SourceElement.Impl)getElementImpl(target);
	    impl.updateMemberOrder(orderedMembers);
	} else if (target instanceof SpecElement) {
	    SpecElementImpl impl = (SpecElementImpl)getElementImpl(target);
	    impl.updateMemberOrder(orderedMembers);
	} else if (target instanceof ProofElement) {
            ProofElementImpl impl = (ProofElementImpl)getElementImpl(target);
            impl.updateMemberOrder(orderedMembers);
        } else if (target instanceof MorphismElement) {
            MorphismElementImpl impl = (MorphismElementImpl)getElementImpl(target);
            impl.updateMemberOrder(orderedMembers);
        } else if (target instanceof DiagramElement) {
            DiagramElementImpl impl = (DiagramElementImpl)getElementImpl(target);
            impl.updateMemberOrder(orderedMembers);
        } else if (target instanceof ColimitElement) {
            ColimitElementImpl impl = (ColimitElementImpl)getElementImpl(target);
            impl.updateMemberOrder(orderedMembers);
        }
    }
    
    public void activate(Element target) {
        ElementImpl impl = getElementImpl(target);
        impl.notifyCreate();
    }
    
    public Binding getElementBinding(Element target) {
        ElementImpl impl = getElementImpl(target);
        return impl.getRawBinding();
    }
    
    public boolean isSameContext(Element context, String id) {
        ElementImpl impl = getElementImpl(context);
        if (impl == null)
            return false;
        return true;
    }
    
    public Element findElement(Element.Impl impl) {
        if (!(impl instanceof ElementImpl))
            return null;
        return ((ElementImpl)impl).getElement();
    }
    
    public void firePropertyChange(Element el, PropertyChangeEvent evt) {
        ElementImpl impl = getElementImpl(el);
        if (impl == null)
            return;
        impl.firePropertyChangeEvent(evt);
    }

    public void invalidateModel(SourceElement el) {
        SourceElementImpl impl = (SourceElementImpl)getElementImpl(el);
        Object token = writeLock();
        try {
            if (impl == null) return;
	    Util.log("DefaultLangModel.invalidateModel calling notifyRemove");
            impl.notifyRemove();
            commitChanges();
        } finally {
            try {
                releaseWriteLock(token);
            } catch (SourceException x) {
            }
        }
    }
    
}
