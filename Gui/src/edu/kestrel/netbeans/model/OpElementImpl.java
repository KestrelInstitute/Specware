/*
 * Opelementimpl.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:01  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.beans.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/**
 * Implements properties specific to a Op declared in a mode.
 *
 */
final class OpElementImpl extends MemberElementImpl implements OpElement.Impl {
    /** Sort of the op.
     */
    private String sort;

    private static final long serialVersionUID = 6799964214013985830L;
    
    OpElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindOp((OpElement)el);
    }

    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        OpElement element = (OpElement)el;
        setSort(element.getSort());
    }

    public Object readResolve() {
        return null;
    }
    
    /** Getter for the sort.
    * @return sort for the op 
    */
    public String getSort() {
        return this.sort;
    }

    /** Setter for the sort.
    * @param value sort for the op
    */
    public void setSort(String sort) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (sort == this.sort)
                    return;
                evt = new PropertyChangeEvent(getElement(), PROP_SORT, this.sort, sort);
                // no constraings on the Initializer... only check vetoable listeners.
                checkVetoablePropertyChange(evt);
                getOpBinding().changeSort(sort);
                addPropertyChange(evt);
            }
            this.sort = sort;
            commit();
        } finally {
            releaseLock(token);
        }
    }

    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.Op getOpBinding() {
        return (Binding.Op)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "OpElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((OpElement)getElement()).clone();
    }
}
