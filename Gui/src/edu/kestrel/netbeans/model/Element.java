/*
 * Element.java
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
import java.io.*;
import java.util.StringTokenizer;

import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.StyledDocument;

import org.openide.TopManager;
import org.openide.ErrorManager;
import org.openide.nodes.Node;
import org.openide.text.IndentEngine;
import org.openide.filesystems.FileUtil;
import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.codegen.ElementPrinter;
import edu.kestrel.netbeans.codegen.DefaultElementPrinter;
import java.util.*;

/** Base class for representations of elements in the
 * MetaSlang language.
 */
public abstract class Element extends Object
    implements Serializable, ElementProperties, Node.Cookie {

    /** Implementation */
    protected Impl impl;
    
    /** Implementation extension #2 */
    protected Impl2 impl2;

    static final long serialVersionUID =967040188302141522L;
    /** Create a new element with the provided implementation. The implementation is
     * responsible for storing all properties of the object.
     *
     * @param impl the implementation to use
     */
    protected Element(Impl impl) {
        this.impl = impl;
        if (impl instanceof Impl2) {
            this.impl2 = (Impl2)impl;
        }
        impl.attachedToElement (this);
    }

    public Collection getPropertyChangeListeners() { 
        return impl.getPropertyChangeListeners(); 
    }
    
    /** Add a property change listener.
     * @param l the listener to add
     * @see ElementProperties
     */
    public final void addPropertyChangeListener (PropertyChangeListener l) {
        impl.addPropertyChangeListener (l);
    }

    /** Remove a property change listener.
     * @param l the listener to remove
     * @see ElementProperties
     */
    public final void removePropertyChangeListener (PropertyChangeListener l) {
        impl.removePropertyChangeListener (l);
    }
    
    /**
     * Attaches a VetoableChange listener to the element.
     * The Listener will be notified about changes being done before the change is
     * actually done.
     * @param l instance of listener to attach.
     */
    public final void addVetoableChangeListener(VetoableChangeListener l) {
        if (impl2 != null)
            impl2.addVetoableChangeListener(l);
    }

    /**
     * Removes the vetoable listener from the element.
     * @param l listener to remove.
     */
    public final void removeVetoableChangeListener(VetoableChangeListener l) {
        if (impl2 != null)
            impl2.removeVetoableChangeListener(l);
    }

    /** Mark the current element in the context of this element.
     * The current element means the position for inserting new elements.
     * @param beforeAfter <CODE>true</CODE> means that new element is inserted before
     *        the specified element, <CODE>false</CODE> means after.
     */
    public void markCurrent(boolean beforeAfter) {
        impl.markCurrent(beforeAfter);
    }

    /** Look for a cookie providing added behavior for this element.
     * The request is {@link Impl#getCookie delegated} to the current implementation.
     * Also note that <code>Element</code> implements <code>Node.Cookie</code>, and that
     * if the implementation does not provide a cookie, but the requested cookie class is
     * actually a superclass/interface of this element type, then the element itself may be
     * returned as the cookie.
     * @param type the cookie class to look for
     * @return a cookie assignable to that class, or <code>null</code> if the cookie
     *    is not supported
     */
    public Node.Cookie getCookie(Class type) {
        Node.Cookie c = impl.getCookie(type);
        if ((c == null) && type.isAssignableFrom(getClass()))
            c = this;

        return c;
    }

    protected Object writeReplace() {
        return impl;
    }

    /** Print this element (and all its subelements) into an element printer.
     * @param printer the element printer
     * @exception ElementPrinterInterruptException if the printer canceled the printing
     */
    public abstract void print(ElementPrinter printer) throws ElementPrinterInterruptException;

    /** Prints array of elements.
     * @param el the elements
     * @param printer The printer where to write
     * @return true if at least one element was printed
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    static boolean print(Element[] el, ElementPrinter printer) throws ElementPrinterInterruptException {
	return print(el, printer, "\n\n");
    }

    /** Prints array of elements.
     * @param el the elements
     * @param printer The printer where to write
     * @param delimiter The delimiter between elements
     * @return true if at least one element was printed
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    static boolean print(Element[] el, ElementPrinter printer, String delimiter) throws ElementPrinterInterruptException {
        for (int i = 0; i < el.length; i++) {
            if (i > 0) {
                printer.print(delimiter); // NOI18N
            }
            el[i].print(printer);
        }
        return (el.length > 0);
    }

    /** Helper method. User for creating document that perform better formatting if there's an
     *  EditorKit registered for the MetaSlang MIME type and supports indentation engine.
     *  @return document that can be used for MetaSlang code generation
     */    
    StyledDocument createDocument() {
	javax.swing.text.EditorKit kit = javax.swing.JEditorPane.createEditorKitForContentType("x-meta-slang"); // NOI18N
	if (kit == null) {
	    kit = new javax.swing.text.DefaultEditorKit();
	}
	javax.swing.text.Document doc = kit.createDefaultDocument();
	if (doc instanceof StyledDocument) {
	    return (StyledDocument)doc;
	}
	return new org.openide.text.FilterDocument(doc);
    }
    
    /** Helper method that properly annotates an exception.
     *  @param message used for human-readable explanation of the exception.
     */
	void throwSourceException(String message) throws SourceException {
	    SourceException ex = new SourceException(message);
	    ErrorManager.getDefault().annotate(ex, ErrorManager.USER, null, message, null, null);
	    throw ex;    
	}
    
    void throwSourceException(Throwable nested) throws SourceException {
	SourceException ex = new SourceException(nested.getMessage());
	ErrorManager.getDefault().annotate(ex, nested);
	throw ex;    
    }	

    /** Get a string representation of the element.
     * @return the string
     * @see #print
     * @see DefaultElementPrinter
     */
    public String toString() {
        StringWriter sw = new StringWriter();
	StyledDocument doc = createDocument();
        IndentEngine indentator = IndentEngine.find(doc); 
        PrintWriter pw = new PrintWriter(indentator.createWriter(doc, 0, sw));
        //    PrintWriter pw = new PrintWriter(sw);
        try {
            print(new DefaultElementPrinter(pw));
        }
        catch (ElementPrinterInterruptException e) {
            // could not happen.
        }
        pw.close();
        return sw.toString();
    }

    /** Pluggable implementation of the storage of element properties.
     * @see Element#Element
     */
    public interface Impl extends Serializable {
        /** @deprecated Only public by accident. */
        /* public static final */ long serialVersionUID = -3246061193296761293L;
        /** Called to attach the implementation to a specific
	 * element. Will be called in the element's constructor.
	 * Allows implementors
	 * of this interface to store a reference to the holder class,
	 * useful for implementing the property change listeners.
	 *
	 * @param element the element to attach to
	 */
        public void attachedToElement (Element el);

        /** Returns the collection of all PropertyChangeListeners
	 * listening to this element
	 */
        public Collection getPropertyChangeListeners();
        
        /** Add a property change listener.
	 * @param l the listener to add
	 */
        public void addPropertyChangeListener (PropertyChangeListener l);

        /** Remove a property change listener.
	 * @param l the listener to remove
	 */
        public void removePropertyChangeListener (PropertyChangeListener l);
        
        /** Implementations must be resolvable.
	 * I.e., upon deserialization they must be able to recreate the
	 * holder class.
	 * @return an instance of the proper subclass of {@link Element}
	 * @see Serializable
	 */
        //public Object readResolve();

        /** Get the support for a cookie, if any.
	 * Changes of supported cookies are <em>not</em> fired.
	 *
	 * @param type the cookie class to look for
	 * @return an instance assignable to that class, or <code>null</code> if the cookie
	 *    is not supported
	 */
        public Node.Cookie getCookie(Class type);

        /** Mark the current element in the context of this element.
	 * The current element means the position for inserting new elements.
	 * @param beforeAfter <CODE>true</CODE> means that new element is inserted before
	 *        the specified element, <CODE>false</CODE> means after.
	 */
        public void markCurrent(boolean beforeAfter);
    }

    /**
     * Extended version of the implementation interface. The new version contains
     * support for vetoable listeners for all Elements and some more for specialized
     * ones.
     */
    public interface Impl2 extends Impl {
        /** Adds a vetoable listener.
         * @param l instener instance to add.
         */
        public void addVetoableChangeListener(VetoableChangeListener l);
        
        /** Removes a vetoable listener.
         * @param l instener instance to remove.
         */
        public void removeVetoableChangeListener(VetoableChangeListener l);

        /**
         * Determines whether the element is still valid - if it is a part of its original model.
         * The Element should be invalidated during its removal from the model so further 
         * operations may notice that and fail in appropriate cases.
         * @return true, if the element is still valid and a part of a model.
         */
        public boolean isValid();
    }

    /** Default implementation of the Impl interface.
     * It just holds the property values.
     */
    static abstract class Memory implements Element.Impl2, Node.Cookie {
        /** the element for this implementation */
        protected Element element;

        /** Property change support */
        private PropertyChangeSupport support;
        
        /**
         * VetoableChange Support.
         */
        private VetoableChangeSupport vetoSupport;

        static final long serialVersionUID =7734412320645883859L;
        /** Attaches to element */
        public void attachedToElement (Element element) {
            this.element = element;
        }

        /** Fires property change event.
	 * @param name property name
	 * @param o old value
	 * @param n new value
	 */
        protected final void firePropertyChange (String name, Object o, Object n) {
            if (support != null) {
                support.firePropertyChange (name, o, n);
            }
        }
        
        protected final void firePropertyChange(PropertyChangeEvent evt) {
            if (support != null)
                support.firePropertyChange(evt);
        }

        public Collection getPropertyChangeListeners() { 
            return Arrays.asList(support.getPropertyChangeListeners());
        }
        
        /** Adds property listener */
        public synchronized void addPropertyChangeListener (PropertyChangeListener l) {
            if (support == null) {
                synchronized (this) {
                    // new test under synchronized block
                    if (support == null) {
                        support = new PropertyChangeSupport (element);
                    }
                }
            }
            support.addPropertyChangeListener (l);
        }

        /** Removes property listener */
        public void removePropertyChangeListener (PropertyChangeListener l) {
            if (support != null) {
                support.removePropertyChangeListener (l);
            }
        }

        public void addVetoableChangeListener(VetoableChangeListener l) {
            if (vetoSupport == null) {
                synchronized (this) {
                    if (vetoSupport == null)
                        vetoSupport = new VetoableChangeSupport(this);
                }
            }
            vetoSupport.addVetoableChangeListener(l);
        }

        public void removeVetoableChangeListener(VetoableChangeListener l) {
            if (vetoSupport != null)
                vetoSupport.removeVetoableChangeListener(l);
        }
        
        protected void fireVetoableChange(String name, Object o, Object v) throws PropertyVetoException {
            if (vetoSupport != null)
                vetoSupport.fireVetoableChange(name, o, v);
        }
        
        protected void fireVetoableChange(PropertyChangeEvent evt) throws PropertyVetoException {
            if (vetoSupport != null)
                vetoSupport.fireVetoableChange(evt);
        }

        /** This implementation returns always null.
	 * @param type the class to look for
	 * @return null.
	 */
        public Node.Cookie getCookie(Class type) {
            if (type.isAssignableFrom(getClass())) {
		return this;
            } else {
		return null;
            }
        }

        /** Mark the current element in the context of this element.
	 * The current element means the position for inserting new elements.
	 * @param beforeAfter <CODE>true</CODE> means that new element is inserted before
	 *        the specified element, <CODE>false</CODE> means after.
	 */
        public void markCurrent(boolean beforeAfter) {
            //PENDING
        }
        
        public boolean isValid() {
            return true;
        }
    }
}
