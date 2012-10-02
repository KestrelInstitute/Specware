/*
 * DefElementImpl.java
 *
 * Created on February 15, 2003, 4:22 PM
 */

package edu.kestrel.netbeans.model;

import java.beans.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/**
 *
 * @author  weilyn
 */
/**
 * Implements properties specific to a Def defined in a spec.
 *
 */
final class DefElementImpl extends MemberElementImpl implements DefElement.Impl {
    private static final long serialVersionUID = 6799964214013985830L;
    
    /** Parameters of the def.
     */
    private String[] parameters;
    
    private String expression;

    DefElementImpl(DefaultLangModel model) {
        super(model);
        parameters = null;
        expression = null;
    }
    
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindDef((DefElement)el);
    }

    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        DefElement element = (DefElement)el;
        setParameters(element.getParameters());
        setExpression(element.getExpression());
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
                getDefBinding().changeParameters(parameters);
                addPropertyChange(evt);
            }
            this.parameters = parameters;
            commit();
        } finally {
            releaseLock(token);
        }
    }
    
    /** Getter for the initial value.
    * @return initial value for the variable or empty string if it is not initialized
    */
    public String getExpression() {
        return this.expression;
    }

    /** Setter for the initial value.
    * @param value initial value for the variable
    */
    public void setExpression(String expression) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (expression == this.expression)
                    return;
                evt = new PropertyChangeEvent(getElement(), PROP_EXPRESSION, this.expression, expression);
                // no constraings on the Initializer... only check vetoable listeners.
                checkVetoablePropertyChange(evt);
                getDefBinding().changeExpression(expression);
                addPropertyChange(evt);
            }
            this.expression = expression;
            commit();
        } finally {
            releaseLock(token);
        }
    }

    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.Def getDefBinding() {
        return (Binding.Def)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "DefElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((DefElement)getElement()).clone();
    }
}
