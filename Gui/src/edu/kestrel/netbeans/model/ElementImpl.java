/*
 * ElementImpl.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.beans.*;
import java.util.*;
import javax.swing.undo.UndoableEdit;
import javax.swing.undo.CannotRedoException;
import javax.swing.undo.CannotUndoException;

import org.openide.nodes.Node;
import org.openide.nodes.CookieSet;
import org.openide.src.SourceException;
import org.openide.src.SourceVetoException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.codegen.ExceptionRunnable;

/**
 * Abstract base class that implements a single element in the source hierarchy.
 * This class contains the base services as event listening support, per-element
 * and per-model locking and various utility functions.
 *
 */
public abstract class ElementImpl implements 
    Element.Impl, Element.Impl2, ElementProperties, Node.Cookie, ElementEvents {

    /** The element for this class.
     */
    private transient Element               element;

    /**
     * Collection of registered PropertyChangeListeners.
     */
    private transient Collection	    propListeners;
        
    /** Vetoable change support.
     * PENDING: Need to create special VetoableChangeSupport, as the standard one
     * is not sufficient for the fine-grained events.
     */
    private transient VetoableChangeSupport vetoSupport;

    /**
     * Binding to the underlying source/whatever.
     */
    private transient Binding               binding;
    
    /**
     * True, if the element has been already created and was not destroyed.
     */
    private transient boolean               valid;

    /**
     * Set of cookies for this element. The set conveniently contains only cookies for
     * the implementation class hierarchy.
     */
    private CookieSet                       cookieSet;

    /**
     * Model that has created this element and that is used to manage the element.
     * The element delegates management functions like locking and event queueing to
     * its model.
     */
    private transient DefaultLangModel      model;

    /**
     * Flag that is used to signal that the element is being created. Some processing
     * is reduced to minimum during this mode and event firing is supressed.
     */
    private transient boolean               inCreation;
    
    /**
     * Enables debug trace messages for event generation
     */
    private static final boolean DEBUG_EVENTS = false;

    private static final long serialVersionUID = -6337836874152020892L;
    
    /**
     * Initializes model and sets the mode of the element to inCreation
     */
    protected ElementImpl(DefaultLangModel model) {
        this.model = model;
        this.inCreation = true;
    }

    /**
     * Attaches the abstract layer to the element; since the all properties required
     * for the Binding to operate are available, the binding is created as well.
     */
    public void attachedToElement(Element el) {
        this.element = el;
    }
    
    /**
     * Binds the element to a particular underlying Binding. The function does nothing
     * if the binding was already establised; it is impossible to rebind an element once
     * the binding was established (this constraint may be overriden by descendants)
     *
     * @param b binding to use for element i/o operations.
     */
    public void setBinding(Binding b) {
        if (this.binding != null)
            return;
        if (b instanceof Node.Cookie) {
            getCookieSet().add((Node.Cookie)b);
        }
        binding = b;
    }
    
    // Listener interface functions
    ///////////////////////////////////////////////////////////////////////////////////
    
    private String describeEvent(PropertyChangeEvent evt) {
        StringBuffer sb = new StringBuffer();
        sb.append(evt.getPropertyName());
        Object oldV = evt.getOldValue();        
        sb.append(" old = " + describeValue(evt.getOldValue())); // NOI18N
        sb.append(" new = " + describeValue(evt.getNewValue())); // NOI18N
        return sb.toString();
    }
    
    private String describeValue(Object o) {
        if (o instanceof String) {
            String id = (String)o;
            return id;
        } else if (o instanceof String[]) {
            StringBuffer sb = new StringBuffer();
            sb.append("[ ");
            String[] ids = (String[])o;
            for (int i = 0; i < ids.length; i++) {
                if (i > 0)
                    sb.append(", ");
                sb.append(describeValue(ids[i]));
            }
            sb.append(" ]");
            return sb.toString();
        } else if (o != null) {
            return o.toString();
        } else return "null"; // NOI18N
    }

    public Collection getPropertyChangeListeners() { 
        return propListeners; 
    }
    
    /** Adds property listener. 
     */
    public void addPropertyChangeListener (PropertyChangeListener l) {
        if (DEBUG_EVENTS) {
            System.err.println("[" + this + "] attaching listener " + l); // NOI18N
        }
    	//Util.log("ElementImpl.addPropertyChangeListener [" + this + "] attaching listener " + l); // NOI18N
        if (propListeners == null) {
            synchronized (this) {
                // new test under synchronized block
                if (propListeners == null) {
                    propListeners = new LinkedList();
                    initializeListenerSupport();
                }
            }
        }
	synchronized (propListeners) {
	    propListeners.add(l);
	}
    }

    /**
     * Returns true, if the element is fully created. This yes/no test is used for supression
     * of some event firing and lightweight operations.
     */
    protected boolean isCreated() {
        return this.inCreation;
    }
    
    /** Removes property listener */
    public void removePropertyChangeListener (PropertyChangeListener l) {
        if (DEBUG_EVENTS) {
            System.err.println("[" + this + "] removing listener " + l); // NOI18N
        }
	if (propListeners != null) {
	    synchronized (propListeners) {
		propListeners.remove(l);
	    }
	}
    }

    /** Adds property vetoable listener */
    public void addVetoableChangeListener (VetoableChangeListener l) {
        if (DEBUG_EVENTS) {
            System.err.println("[" + this + "] attaching veto listener " + l); // NOI18N
        }
	Util.log("ElementImpl.addVetoableChangeListener [" + this + "] attaching listener " + l); // NOI18N
        if (vetoSupport == null) {
            synchronized (this) {
                // new test under synchronized block
                if (vetoSupport == null) {
                    vetoSupport = new VetoableChangeSupport (element);
                    initializeListenerSupport();
                }
            }
        }
        vetoSupport.addVetoableChangeListener (l);
    }
    
    /** Removes property vetoable listener */
    public void removeVetoableChangeListener (VetoableChangeListener l) {
        if (DEBUG_EVENTS) {
            System.err.println("[" + this + "] removing veto listener " + l); // NOI18N
        }
        if (vetoSupport != null) {
            vetoSupport.removeVetoableChangeListener (l);
        }
    }

    /** Base method for marking the current insertion point.
     */
    public void markCurrent(boolean beforeAfter) {
        // PENDING: redirect to the new facilities for element ordering.
    }
    
    /** Returns the abstract wrapper for this implementation.
     */
    public final Element getElement() {
        return element;
    }
    
    /**
     * Returns the cookie set so that extension objects can plug in and
     * extend the element implementation.
     * @return r/w cookie set instance.
     */
    public final CookieSet getCookieSet() {
        if (cookieSet == null) {
            synchronized (this) {
                if (cookieSet == null) {
                    cookieSet = new CookieSet();
                    initializeCookies(cookieSet);
                }
            }
        }
        return cookieSet;
    }
    
    protected void initializeCookies(CookieSet set) {
        set.add(this);
    }
    
    /**
     * Returns true, if the element is still valid - that is present in the model.
     * @return true, iff the element is still valid.
     */
    public boolean isValid() {
        return this.valid;
    }
    
    // Support functions 
    /////////////////////////////////////////////////////////////////////////////////
    
    /** Fires property change event. The event is fired as "own" property change event,
     * so it is captured in the queue and counted for the summary information.
    * @param name property name
    * @param o old value
    * @param n new value
    */
    protected final void firePropertyChange(String name, Object o, Object n) {
        fireOwnPropertyChange(new PropertyChangeEvent(getElement(), name, o, n));
    }
    
    /**
     * Fires a PropertyChangeEvent to the listeners, if there's a listener.
     */
    protected final void firePropertyChangeEvent(PropertyChangeEvent evt) {
        if (DEBUG_EVENTS) {
            StringBuffer sb = new StringBuffer();
            sb.append('[');
            sb.append(toString());
            sb.append("] Dispatching change: "); // NOI18N
            sb.append(describeEvent(evt));
            System.err.println(sb.toString());
        }
	if (propListeners == null)
	    return;
	
	Vector listeners;
	synchronized (propListeners) {
	    listeners = new Vector(propListeners);
	}
	for (int i = 0; i < listeners.size(); i++) {
	    PropertyChangeListener l = (PropertyChangeListener)listeners.elementAt(i);
	    //Util.log("ElementImpl.firePropertyChangeEvent -- sending property change event to " + l); 
	    //System.err.println("ElementImpl.firePropertyChangeEvent -- sending property change event to " + l); 
	    l.propertyChange(evt);
	}
    }
    
    /**
     * Fires an arbitrary property change event about intrinsic property change.
     * Events fired though this method will show up in the change summary events
     * fired after the model's lock is released. The method does nothing if the element
     * is in the creation phase.<P>
     * <B>Important note:<B> since the implementation will record the current element's
     * state by creating a copy/clone, it is <B>required</B> that the change is fired
     * before the element updates its internal state so that the clone contains the
     * old one.
     */
    protected final void fireOwnPropertyChange(PropertyChangeEvent evt) {
        if (isCreated())
            return;
        EventQueue q = getModelImpl().getEventQueue();
        q.elementChanged(this);
        addPropertyChange(evt);
    }
    
    protected Element cloneSelf() {
        throw new UnsupportedOperationException("clone unsupported on "  // NOI18N
            + getClass());
    }

    /**
     * Creates a suitable binding for the element. The binding is created with the
     * help of BindingFactory available from the element's model object; descendants 
     * are required to route the request to the most appropriate factory's method.
     */
    protected abstract Binding createBinding(Element el);

    /**
     * Adds an extrinsic property change event to the final event queue.
     * Events channeled through this method do not contribute to the summary events,
     * for example properties that contain children sub-elements should use
     * this method to avoid unnecessary element cloning.
     */
    public final void addPropertyChange(PropertyChangeEvent evt) {
        if (isCreated())
            return;
        getModelImpl().getEventQueue().addPropertyChange(this, evt);
    }
    
    /** Fires a vetoable change on property `name' from old value `o' to new value `n'.
     * @param name name of the property that is being changed.
     * @param o old value of the property; can be null.
     * @param n new value of the property; can be null.
     */
    protected final void fireVetoableChange(String name, Object o, Object n) throws PropertyVetoException {
        if (isCreated())
            return;
        if (vetoSupport != null) {
            try {
                getModelImpl().notifyEventsDispatched(true);
                vetoSupport.fireVetoableChange(name, o, n);
            } finally {
                getModelImpl().notifyEventsDispatched(false);
            }
        }
    }
    
    /**
     * Fires arbitrary pre-constructed vetoable change event.
     * @param evt vetoable event that should be fired.
     */
    public final void fireVetoableChange(PropertyChangeEvent evt) throws SourceException {
        if (isCreated())
            return;
         checkVetoablePropertyChange(evt);
    }
    
    private void doFireVetoableChange(PropertyChangeEvent evt) throws PropertyVetoException {
        if (DEBUG_EVENTS) {
            StringBuffer sb = new StringBuffer();
            sb.append('[');
            sb.append(toString());
            sb.append("] Dispatching veto: "); // NOI18N
            sb.append(describeEvent(evt));
            System.err.println(sb.toString());
        }
        if (vetoSupport != null) {
            try {
                getModelImpl().notifyEventsDispatched(true);
                vetoSupport.fireVetoableChange(evt);
            } finally {
                getModelImpl().notifyEventsDispatched(false);
            }
        }
    }
    
    /** The method tries to fire a Vetoable Change event; if (one of) listener throws 
     * PropertyVetoException, the exception is examined whether it holds a wrapped SourceException.
     * If so, that inner SourceException is rethrown, otherwise, the PropertyVetoException is
     * wrapped into a SourceException and thrown to the caller.
     */
    protected void checkVetoablePropertyChange(PropertyChangeEvent evt) throws SourceException {
        if (isCreated() || !isConstrained())
            return;
        
        try {
            doFireVetoableChange(evt);
        } catch (SourceVetoException ex) {
            // rethrow the original exception.
            throw ex.getNestedException();
        } catch (PropertyVetoException ex) {
            // rethrow the veto as a general SourceException.
            // PENDING: use model's environment to annotate/log the exception(s).
            throw new SourceException(ex.getMessage());
        }
    }
    
    /**
     * Returns the storage binding for this element. The element must be 
     * backed up by a text file/document, but the changes themselves and the binding
     * to the underlying document are performed by other delegate object.
     * If the element is just being created, the function returns NULL_BINDING that accepts
     * all requests, but does nothing. This way the element is blocked from altering the
     * storage until it is fully created.
     *
     * @return The binding for this element, or, if the element has inCreation flag,
     * it returns the default NULL_BINDING.
     */
    public final Binding getBinding() {
        if (isCreated())
            return null;
        return this.binding;
    }

    /**
     * Returns the actual binding without any shielding for elements that are not yet
     * created.
     */
    public final Binding getRawBinding() {
        return this.binding;
    }
    
    /** Invalidates the element. The element will be no longer valid and may refuse some
     * operations that would depend on other objects in the model - since it will be no
     * longer considered to be a part of a model.
     */
    protected void invalidate() {
        setValid(false);
    }
    
    private void setValid(boolean valid) {
        boolean old = this.valid;
        if (old == valid)
            return;
        this.valid = valid;
        if (old)
            // do not clone the element upon THIS property change.
            addPropertyChange(new PropertyChangeEvent(getEventSource(),
                PROP_VALID, 
                valid ? Boolean.FALSE : Boolean.TRUE,
                valid ? Boolean.TRUE : Boolean.FALSE 
            ));
    }

    /**
     * Checks whether the element is still valid. If not, throws a SourceException
     * to indicate that the calling operation cannot be completed.
     * @throw SourceException if the element is not valid/present in the model.
     */
    protected void checkValid(Object lockToken) throws SourceException {
        if (isValid()) {
            return;
        }
        releaseLock(lockToken);
        Util.throwException("Element was deleted", "EXC_ElementInvalid"); // NOI18N
    }

    /** Retrieves cookie supported by the Element. In general, implementation
     * classes are ALWAYS available as cookies, so they can be extracted from both ElementImpls
     * and the abstract counterparts.
     */
    public Node.Cookie getCookie(Class desired) {
        // return this instance, if the cookie is directly supported.
        if (desired.isAssignableFrom(getClass()))
            return this;
        // ask the CookieSet
        Node.Cookie ret = getCookieSet().getCookie(desired);
        if (ret != null)
            return ret;
        return getModelImpl().findElementCookie(getElement(), desired);
    }
    
    
    /** Finds the source element - the root for the hierarchy this element are part of.
     */
    protected abstract SourceElementImpl findSource();
    
    // Package-private protocol
    ////////////////////////////////////////////////////////////////////////
    protected void createAfter(Binding.Container cb, Binding refBinding) 
    throws SourceException {
        inCreation = false;
        cb.insert(binding, refBinding);
        setValid(true);
    }
    
    protected abstract boolean parentValid();
    
    protected void notifyCreate() {
        inCreation = false;
        setValid(true);
        if (parentValid())
            notifyElementCreated();
    }
    
    protected void notifyElementCreated() {
        getModelImpl().getEventQueue().elementCreated(getElement());
    }
    
    /**
     * Notifies the element that it has been removed.
     */
    protected void notifyRemove() {
        invalidate();
        getModelImpl().getEventQueue().elementRemoved(getElement());
    }
    
    /**
     * Checks whether the element can be removed. Fires a Vetoable property change
     * event on PROP_VALID from true to false.
     */
    protected void checkRemove() throws SourceException {
        if (isCreated() || !isConstrained())
            return;
        PropertyChangeEvent evt = new PropertyChangeEvent(getElement(),
            PROP_VALID, Boolean.TRUE, Boolean.FALSE);
        checkVetoablePropertyChange(evt);
    }
    
    /** Determines whether there's somebody interested in the property. Subclasses may
     * then optimize whether they should ever generate PropertyChangeEvent.
     */
    protected boolean hasListeners(String propName) {
	if (vetoSupport.hasListeners(propName))
	    return true;
	if (propListeners == null)
	    return false;
	synchronized (propListeners) {
	    return !propListeners.isEmpty();
	}
    }
    
    /**
     * Attempts to run atommically an operation. Throws SourceException if the runnable
     * throws any kind of exception
     * @deprecated use {@link #takeLock}/{@link #releaseLock} instead.
     */
    protected void runAtomic(ExceptionRunnable r) throws SourceException {
        model.runAtomic(r);
    }
    
    protected void initializeListenerSupport() {
    }

    /** 
     * Implementation of {@link ElementEvents} interface; returns the element to
     * be reported as the source of events.
     */
    public final Object getEventSource() {
        return getElement();
    }
    
    /**
     *  Implementation of {@link ElementEvents} interface; returns the implementation
     * object paired with the event source (this object).
     */
    public final ElementImpl getElementImpl() {
        return this;
    }
    
    protected abstract void setParent(ElementImpl parent);
    
    protected void setParent(Element parent) {
        setParent((ElementImpl)parent.getCookie(ElementImpl.class));
        setBinding(createBinding(this.element));
    }
    
    /**
     * Convenience method that retrieves reference to the model that had created
     * the element.
     */
    protected final DefaultLangModel getModelImpl() {
        return this.model;
    }
    
    /**
     * Attempts to obtain model's write lock preventing other threads from modifying
     * the model. Before it returns, the method also checks whether the element
     * is still valid. If not, it releases the lock and throws a SourceException
     * @return token object that should be later used to free the lock.
     */
    protected final Object takeLock() throws SourceException {
        if (isCreated())
            return null;
        Object o = getModelImpl().writeLock();
        checkValid(o);
        return o;
    }

    /**
     * Releases write lock on the model. If an invalid token object is passed,
     * the model will throw IllegalArgumentException
     * @param o token object for lock release operation.
     */
    protected final void releaseLock(Object o) throws SourceException {
        if (isCreated())
            return;
        getModelImpl().releaseWriteLock(o);
    }

    /**
     * Takes a <B>master</B> lock. This lock differs from the ordinary in that it
     * does not create nested event queue, but merges all events to the current one.
     * Until the master lock is in effect, all events will be routed to the current
     * event queue. The master lock is used when the model's implementation is about
     * to issue nested model operations.
     */
    protected final Object takeMasterLock() throws SourceException {
        if (isCreated())
            return null;
        Object l =  getModelImpl().masterWriteLock();
        checkValid(l);
        return l;
    }
    
    protected abstract void createFromModel(Element model) throws SourceException;
    
    /**
     * Causes changes made by the last locked operation to be confirmed and,
     * upon lock release, merged into the higher operation.
     */
    protected final void commit() {
        if (!isValid())
            return;
        getModelImpl().commitChanges();
    }
    
    /**
     * Returns true, if constraints on elements should be checked. This can
     * be disabled during some special operations (like external model updates).
     * If the method returns false, no VetoableChangeListeners should be informed.
     * @return true, if constraints are enabled, false otherwise.
     */
    protected final boolean isConstrained() {
        return getModelImpl().isConstrained();
    }
    
    /*
    public void undoPropertyChange(PropertyChangeEvent change) throws CannotUndoException {
        try {
            undoRedoActive = true;
            applyPropertyChange(change, true);
        } catch (CannotRedoException ex) {
            throw new InternalError("Redo exception in undo operation"); // NOI18N
        } finally {
            undoRedoActive = false;
        }
    }
    
    public void redoPropertyChange(PropertyChangeEvent change) throws CannotRedoException {
        try {
            undoRedoActive = true;
            applyPropertyChange(change, true);
        } catch (CannotUndoException ex) {
            throw new InternalError("UndoException in redo operation"); // NOI18N
        } finally {
            undoRedoActive = false;
        }
    }
    
    public void addUndoableEdit(UndoableEdit edit) {
    }
     */
}
