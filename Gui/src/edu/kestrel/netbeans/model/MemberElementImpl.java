/*
 * MemberElementImpl.java
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

import java.beans.PropertyChangeEvent;
import java.lang.reflect.Modifier;
import javax.swing.undo.CannotRedoException;
import javax.swing.undo.CannotUndoException;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/** Describes a main elements of meta-slang source.
 * Provides support
 * for associating this element with the parent element. Adds `name' property
 * implementation for descendant elements as well as some utility methods.
 */
abstract class MemberElementImpl extends ElementImpl {
    /** Name of this element. 
     */
    protected String  name;

    /** Implementation of the parent element. It is just a shorthand for acquiring
     * a cookie from the Element.
     */
    protected ElementImpl    parentImpl;
    
    static final long serialVersionUID =6388377681336329844L;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////

	/** Construction of MemberElement from externally supplied data.
	 * @param name the name of the Element.
	 protected MemberElementImpl(String name) {
	 super(null);
	 this.name = name;
	 }
	*/
    
    protected MemberElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    // Public operations
    ///////////////////////////////////////////////////////////////////////////////////

	protected void setParent(ElementImpl impl) {
	    this.parentImpl = impl;
	}
    
    protected boolean parentValid() {
        return parentImpl != null && parentImpl.isValid();
    }

    protected void createFromModel(Element model) throws SourceException {
        MemberElement other = (MemberElement)model;
        setName(other.getName());
    }
    
    // Getters
    ///////////////////////////////////////////////////////////////////////////////////

	/** Getter for name of the field.
	 * @return the name
	 */
    public String getName() {
        return name;
    }

    /**
     * Extends the basic isValid with a check, whether the parent is valid.
     * @return true, if both the element and its parent are valid.
     */
    public boolean isValid() {
        if (!super.isValid())
            return false;
        
        ElementImpl impl = getParentImpl();
        return impl == null || impl.isValid();
    }
    
    // Setters/changers
    ///////////////////////////////////////////////////////////////////////////////////
	/** Overload to impose constraint over the member's name. The default implementation
	 * does nothing.
	 */
	protected void checkNameConstraints(String name) throws SourceException {
	}

    /** Retrieves the binding object.
     */
    protected final Binding.Member getMemberBinding() {
        return (Binding.Member)getBinding();
    }

    protected Element getParent() {
        return parentImpl.getElement();
    }
    
    protected void doSetName(String id) throws SourceException {
        PropertyChangeEvent evt;
        if (!isCreated()) {
            String old = this.name;
            if (isConstrained())
                checkNameConstraints(id);
            if (old != null &&
                old.equals(id))
                return;
            evt = new PropertyChangeEvent(getElement(), PROP_NAME, old, id);
            checkVetoablePropertyChange(evt);
            changeName(id);
            fireOwnPropertyChange(evt);
        }
        this.name = id;
    }

    /**
     * Actually handles out the name change. 
     */
    protected void changeName(String id) throws SourceException {
        getMemberBinding().changeName(id);
    }
    
    /**
     * Implementation of name change for an Element. The implementation will:<UL>
     * <LI>check for model constraints on the name
     * <LI>check vetoable listener acknowledges of the change
     * <LI>ask the Binding for performing the change
     * <LI>fire the PropertyChangedEvent.
     * @param id new name to use with the element.
     */
    public void setName(String id) throws SourceException {
        Object token = takeLock();
        try {
            doSetName(id);
            commit();
        } finally {
            releaseLock(token);
        }
    }
    
    // Utility methods
    ///////////////////////////////////////////////////////////////////////////////////

	protected SourceElementImpl findSource() {
	    ElementImpl parentImpl = getParentImpl();
	    if (parentImpl == null) {
		return null;
	    }
	    if (parentImpl instanceof SpecElementImpl) {
		return ((SpecElementImpl)parentImpl).findSourceImpl();
	    } else if (parentImpl instanceof MemberElementImpl) {
		return ((MemberElementImpl)parentImpl).findSource();
	    }
	    return null;
	}

    /**
     * Returns the implementation of the parent element.
     */
    protected ElementImpl getParentImpl() {
        return this.parentImpl;
    }
    
    /**
     * Access method to the Element's isValid, may be used by subclasses for overriding
     * isValid semantics.
     */
    protected boolean isElementValid() {
        return super.isValid();
    }
    
    // Support classes
    ///////////////////////////////////////////////////////////////////////////////////
}
