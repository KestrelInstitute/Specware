/*
 * MemberElement.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:58  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.io.*;

import org.openide.src.SourceException;

/** Superclass for containable MetaSlang source members
 * (e.g. specs). Provides support
 * for associating this element with a declaring class.
 */
public abstract class MemberElement extends Element implements Cloneable {
    /** the element this element belongs to */
    private Element parent;

    static final long serialVersionUID =7896378970641663987L;

    /** Create a member element.
     * @param impl the pluggable implementation
     * @param parent the element this element belongs to, or <code>null</code> if unattached
     */
    protected MemberElement(MemberElement.Impl impl, Element parent) {
        super(impl);
        this.parent = parent;
    }

    /** @return the current implementation. */
    final MemberElement.Impl getMemberImpl() {
        return (MemberElement.Impl) impl;
    }

    /** Get the name of this member.
     * @return the name
     */
    public final String getName() {
        return getMemberImpl().getName();
    }

    /** Set the name of this member.
     * @param name the name
     * @throws SourceException if impossible
     */
    public void setName(String name) throws SourceException {
        getMemberImpl().setName(name);
    }

    public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }

    /* This field is automaticly sychnronized
     * when a MemberElement is added to the parent. */
    /** Get the parent element.
     *
     * @return the element that owns this member element, or <code>null</code> if the element is not
     *    attached to any element
     */
    public final Element getParent () {
        return parent;
    }

    public final SpecElement getTopLevelSpec() {
	Element parent = getParent();
	if ((this instanceof SpecElement) && (parent instanceof SourceElement)) {
	    return (SpecElement)this;
	}
	if (parent instanceof MemberElement) {
	    return ((MemberElement)parent).getTopLevelSpec();
	}
	return null;
    }


    public final SourceElement findSource() {
	Element parent = getParent();
	if (parent != null) {
	    if (parent instanceof SourceElement) {
		return (SourceElement)parent;
	    }
	    if (parent instanceof MemberElement) {
		return ((MemberElement)parent).findSource();
	    }
	}
	return null;
    }


    /** Pluggable implementation of member elements.
     * @see MemberElement
     */
    public interface Impl extends Element.Impl {
        /** @deprecated Only public by accident. */
        /* public static final */ long serialVersionUID = 2037286733482347462L;

        /** Get the name of this member.
         * @return the name
         */
        public String getName();

        /** Set the name of this member.
         * @param name the name
         * @throws SourceException if impossible
         */
        public void setName(String name) throws SourceException;
    }

    /** Default implementation of the Impl interface.
     * It just holds the property values.
     */
    static abstract class Memory extends Element.Memory implements MemberElement.Impl {
        /** Name of this element */
        protected String name;

        static final long serialVersionUID =1876531129266668488L;
        /** Default */
        public Memory () {
        }

        /** Copy */
        public Memory (MemberElement el) {
            name = el.getName ();
        }

        /** Getter for name of the field.
	 * @return the name
	 */
        public synchronized String getName() {
            if (name == null) {
                // lazy initialization !?
                name = "";
            }
            return name;
        }

        /** Setter for name of the field.
	 * @param name the name of the field
	 */
        public synchronized void setName(String name) {
            String old = this.name;
            this.name = name;
            firePropertyChange (PROP_NAME, old, name);
        }
    
        public void markCurrent(boolean after) {
            Element parent = ((MemberElement)element).getParent();
           ((SpecElement.Memory)parent.getCookie(SpecElement.Memory.class)).markCurrent(element, after);
        }
    }
}
