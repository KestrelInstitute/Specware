/*
 * ElementBeanModel.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.*;
import java.lang.reflect.InvocationTargetException;

import org.openide.explorer.propertysheet.PropertyModel;
import org.openide.explorer.propertysheet.DefaultPropertyModel;
import org.openide.src.SourceException;
import org.openide.*;

import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.SourceElement;

/** The class wraps another PropertyModel's setXXX calls into runAtomicAsUser
 * to provide guarded block cheking.
 * 
 */
class ElementBeanModel extends java.lang.Object implements PropertyModel {
    private PropertyModel original;
    private Element bean;

    public ElementBeanModel(Element bean, String propertyName) {
        this(bean, new DefaultPropertyModel(bean, propertyName));
    }
    
    /** Creates new ElementBeanModel */
    public ElementBeanModel(Element bean, PropertyModel original) {
        this.bean = bean;
        this.original = original;
    }
    
    /** The class of the property editor or <CODE>null</CODE>
     * if default property editor should be used.
     */
    public Class getPropertyEditorClass() {
        return original.getPropertyEditorClass();
    }
    
    /** Remove listener to change of the value.
     */
    public void removePropertyChangeListener(PropertyChangeListener l) {
        original.removePropertyChangeListener(l);
    }
    
    /** The class of the property.
     */
    public Class getPropertyType() {
        return original.getPropertyType();
    }
    
    /** Getter for current value of a property.
     */
    public Object getValue() throws InvocationTargetException {
        return original.getValue();
    }

    /** Setter for a value of a property.
     * @param v the value
     * @exeception InvocationTargetException
     */
    public void setValue(final Object v) throws InvocationTargetException {
        final InvocationTargetException[] ex = new InvocationTargetException[1];
	final Throwable[] ex2 = { null };
        SourceElement srcel = SourceEditSupport.findSource(bean);
        if (srcel == null) {
            original.setValue(v);
            return;
        }
        try {
            srcel.runAtomicAsUser(new Runnable() {
                public void run() {
                    try {
                        original.setValue(v);
                    } catch (InvocationTargetException e) {
                        ex[0] = e;
			ErrorManager.getDefault().annotate(
			    e, e.getTargetException()
			);
                    }
                }
            });
        } catch (SourceException e) {
            ex[0] = new InvocationTargetException(e);
	    ErrorManager.getDefault().annotate(ex[0], e);
        }
        if (ex[0] == null)
            return;
        throw ex[0];
    }

    /** Add listener to change of the value.
    */
    public void addPropertyChangeListener(PropertyChangeListener l) {
        original.addPropertyChangeListener(l);
    }    
}
