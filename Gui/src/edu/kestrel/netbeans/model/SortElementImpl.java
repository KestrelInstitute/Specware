/*
 * SortElementImpl.java
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

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/**
 * Implements properties specific to a Sort declared in a spec.
 *
 */
final class SortElementImpl extends MemberElementImpl implements SortElement.Impl {
    private static final long serialVersionUID = 6799964214013985830L;
    
    /** Parameters of the sort.
     */
    private String[] parameters;

    SortElementImpl(DefaultLangModel model) {
        super(model);
        parameters = null;
    }
    
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindSort((SortElement)el);
    }

    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        SortElement element = (SortElement)el;
        setParameters(element.getParameters());
	//edu.kestrel.netbeans.Util.log("SortElementImpl.createFromModel: name="+element.getName());
    }

    public Object readResolve() {
        return null;
    }
    
    /** Getter for the initial value.
    * @return initial value for the variable or empty string if it is not initialized
    */
    public String[] getParameters() {
        return this.parameters;
    }

    /** Setter for the initial value.
    * @param value initial value for the variable
    */
    public void setParameters(String[] parameters) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (parameters == this.parameters)
                    return;
                evt = new PropertyChangeEvent(getElement(), PROP_PARAMETERS, this.parameters, parameters);
                // no constraings on the Initializer... only check vetoable listeners.
                checkVetoablePropertyChange(evt);
                getSortBinding().changeParameters(parameters);
                addPropertyChange(evt);
            }
            this.parameters = parameters;
            commit();
        } finally {
            releaseLock(token);
        }
    }

    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.Sort getSortBinding() {
        return (Binding.Sort)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "SortElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((SortElement)getElement()).clone();
    }
}
