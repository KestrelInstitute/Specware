/*
 * SpecElement.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:05  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.io.*;
import java.util.*;

import org.openide.TopManager;
import org.openide.cookies.SourceCookie;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataObjectNotFoundException;
import org.openide.filesystems.Repository;
import org.openide.filesystems.FileObject;
import org.openide.util.NbBundle;
import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;

/** Element that describes one spec.
 * Note that this is a member element.<P>
 * <B>Note:</B> If you add an element to a SpecElement, the SpecElement
 * crates its own copy of the passed element. If you perform subsequent
 * modifications to the object passed to addParameter (addMode, addWhatever),
 * the original element will be updated, <B>not</B> the one created as a result
 * of the add() operation.
 *
 */
public final class SpecElement extends MemberElement {
    /** Formats for the header - used in code generator */
    private static final ElementFormat HEADER_FORMAT = 
        new ElementFormat("spec {n}"); // NOI18N

    /** source element we are attached to */
    private SourceElement source;
    private boolean topLevel;

    //================ Constructors of SpecElement =================

    /** Create a new spec element in memory.
     */
    public SpecElement() {
        this(new Memory(), null);
    }

    /** Factory constructor for defining top level specs.
     * @param impl implementation of functionality
     * @param source the source element this spec is contained in, or <code>null</code>
     */
    public SpecElement(MemberElement.Impl impl, Element parent) {
        super(impl, parent);
	if (parent instanceof SourceElement) {
	    this.source = (SourceElement) parent;
	    this.topLevel = true;
	} else {
	    this.topLevel = false;
	}
    }

    /** Clone this element.
     * @return new element with the same values as the original,
     *   but represented in memory
     */
    public Object clone() {
        Memory mem = new Memory(this);
        SpecElement el = new SpecElement(mem, null);
        mem.copyFrom(this);
        return el;
    }

    /** @return implemetation factory for this spec
     */
    final Impl getSpecImpl() {
        return(Impl)impl;
    }
 
    //================ Main properties ==============================

    /** Get the source element of this spec.
     * @return the source, or <code>null</code> if the spec is not attached to any source
     */
    public SourceElement getSource() {
        return source;
    }
    
    public void setSource(SourceElement source) {
        this.source = source;
    }
    
    //================== Sorts ===============================

    /** Add a new sort to the spec.
     *  @param el the sort to add
     * @throws SourceException if impossible
     */
    public void addSort(SortElement el) throws SourceException {
        if (getSort(el.getName()) != null)
            throwAddException("FMT_EXC_AddSort", el); // NOI18N
        getSpecImpl().changeSorts(new SortElement[] { el }, Impl.ADD);
    }

    /** Add some new sorts to the spec.
     *  @param els the sorts to add
     * @throws SourceException if impossible
     */
    public void addSorts(final SortElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getSort(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddSort", els[i]); // NOI18N
        getSpecImpl().changeSorts(els, Impl.ADD);
    }

    /** Remove a sort from the spec.
     *  @param el the sort to remove
     * @throws SourceException if impossible
     */
    public void removeSort(SortElement el) throws SourceException {
        getSpecImpl().changeSorts(
						 new SortElement[] { el }, Impl.REMOVE
						 );
    }

    /** Remove some sorts from the spec.
     *  @param els the sorts to remove
     * @throws SourceException if impossible
     */
    public void removeSorts(final SortElement[] els) throws SourceException {
        getSpecImpl().changeSorts(els, Impl.REMOVE);
    }

    /** Set the sorts for this spec.
     * Previous sorts are removed.
     * @param els the new sorts
     * @throws SourceException if impossible
     */
    public void setSorts(SortElement[] els) throws SourceException {
        getSpecImpl().changeSorts(els, Impl.SET);
    }

    /** Get all sorts in this spec.
     * @return the sorts
     */
    public SortElement[] getSorts() {
        return getSpecImpl().getSorts();
    }

    /** Find a sort by name.
     * @param name the name of the sort to look for
     * @return the element or <code>null</code> if not found
     */
    public SortElement getSort(String name) {
        return getSpecImpl().getSort(name);
    }

    //================== Ops ===============================

    /** Add a new op to the spec.
     *  @param el the op to add
     * @throws SourceException if impossible
     */
    public void addOp(OpElement el) throws SourceException {
        if (getOp(el.getName()) != null)
            throwAddException("FMT_EXC_AddOp", el); // NOI18N
        getSpecImpl().changeOps(new OpElement[] { el }, Impl.ADD);
    }

    /** Add some new ops to the spec.
     *  @param els the ops to add
     * @throws SourceException if impossible
     */
    public void addOps(final OpElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getOp(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddOp", els[i]); // NOI18N
        getSpecImpl().changeOps(els, Impl.ADD);
    }

    /** Remove a op from the spec.
     *  @param el the op to remove
     * @throws SourceException if impossible
     */
    public void removeOp(OpElement el) throws SourceException {
        getSpecImpl().changeOps(
						 new OpElement[] { el }, Impl.REMOVE
						 );
    }

    /** Remove some ops from the spec.
     *  @param els the ops to remove
     * @throws SourceException if impossible
     */
    public void removeOps(final OpElement[] els) throws SourceException {
        getSpecImpl().changeOps(els, Impl.REMOVE);
    }

    /** Set the ops for this spec.
     * Previous ops are removed.
     * @param els the new ops
     * @throws SourceException if impossible
     */
    public void setOps(OpElement[] els) throws SourceException {
        getSpecImpl().changeOps(els, Impl.SET);
    }

    /** Get all ops in this spec.
     * @return the ops
     */
    public OpElement[] getOps() {
        return getSpecImpl().getOps();
    }

    /** Find a op by name.
     * @param name the name of the op to look for
     * @return the element or <code>null</code> if not found
     */
    public OpElement getOp(String name) {
        return getSpecImpl().getOp(name);
    }

    //================== Claims ===============================

    /** Add a new claim to the spec.
     *  @param el the claim to add
     * @throws SourceException if impossible
     */
    public void addClaim(ClaimElement el) throws SourceException {
        if (getClaim(el.getName()) != null)
            throwAddException("FMT_EXC_AddClaim", el); // NOI18N
        getSpecImpl().changeClaims(new ClaimElement[] { el }, Impl.ADD);
    }

    /** Add some new claims to the spec.
     *  @param els the claims to add
     * @throws SourceException if impossible
     */
    public void addClaims(final ClaimElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getClaim(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddClaim", els[i]); // NOI18N
        getSpecImpl().changeClaims(els, Impl.ADD);
    }

    /** Remove a claim from the spec.
     *  @param el the claim to remove
     * @throws SourceException if impossible
     */
    public void removeClaim(ClaimElement el) throws SourceException {
        getSpecImpl().changeClaims(
						 new ClaimElement[] { el }, Impl.REMOVE
						 );
    }

    /** Remove some claims from the spec.
     *  @param els the claims to remove
     * @throws SourceException if impossible
     */
    public void removeClaims(final ClaimElement[] els) throws SourceException {
        getSpecImpl().changeClaims(els, Impl.REMOVE);
    }

    /** Set the claims for this spec.
     * Previous claims are removed.
     * @param els the new claims
     * @throws SourceException if impossible
     */
    public void setClaims(ClaimElement[] els) throws SourceException {
        getSpecImpl().changeClaims(els, Impl.SET);
    }

    /** Get all claims in this spec.
     * @return the claims
     */
    public ClaimElement[] getClaims() {
        return getSpecImpl().getClaims();
    }

    /** Find a claim by name.
     * @param name the name of the claim to look for
     * @return the element or <code>null</code> if not found
     */
    public ClaimElement getClaim(String name) {
        return getSpecImpl().getClaim(name);
    }

    // ================ printing =========================================

    /* Print this element to an element printer.
     * @param printer the printer to print to
     * @exception ElementPrinterInterruptException if the printer cancels the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
	boolean topLevel = (source != null);

        printer.markSpec(this, printer.ELEMENT_BEGIN);

        printer.markSpec(this, printer.HEADER_BEGIN); // HEADER begin
        if (topLevel) {
	    printer.println(getName()+" =");
	}
	printer.print(HEADER_FORMAT.format(this));

        printer.markSpec(this, printer.HEADER_END); // HEADER end

        printer.markSpec(this, printer.BODY_BEGIN); // BODY begin
        printer.println(""); // NOI18N

        if (print(getSorts(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N
        }

        if (print(getOps(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N
        }
        
        if (print(getClaims(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N            
        }

        printer.println(""); // NOI18N
        printer.markSpec(this, printer.BODY_END); // BODY end
        printer.print("endspec"); // NOI18N

        if (topLevel) {
	    printer.println("");
	    printer.println("");
	}

        printer.markSpec(this, printer.ELEMENT_END);
    }

    // ================ misc =========================================

    /** This mode just throws localized exception. It is used during
     * adding some element, which already exists in the spec.
     * @param formatKey The message format key to localized bundle.
     * @param element The element which can't be added
     * @exception SourceException is alway thrown from this mode.
     */
    private void throwAddException(String formatKey, MemberElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					  getName(), element.getName());
	throwSourceException(msg);
    }

    // ================ finders =======================================

    /** List of finders */
    private static List finders = new LinkedList();

    /** Register a new finder for locating spec elements.
     * @param f the finder to add
     */
    public static void register(Finder f) {
        synchronized(finders) {
            finders.add(f);
        }
    }

    /** Unregister a finder for locating spec elements.
     * @param f the finder to remove
     */
    public static void unregister(Finder f) {
        synchronized(finders) {
            finders.remove(f);
        }
    }

    /** Provides a "finder" for spec elements.
     * A module can provide its own finder to enhance the ability
     * of the IDE to locate a valid spec element description for different specs.
     * @see SpecElement#forName
     * @see SpecElement#register
     * @see SpecElement#unregister
     */
    public static interface Finder {
        /** Find a spec element description for a spec.
	 *
	 * @param spec the spec to find
	 * @return the spec element, or <code>null</code> if not found
	 */
        //public SpecElement find(Spec spec);

        /** Find a spec element description for a spec name.
	 *
	 * @param name the name of a spec to find
	 * @return the spec element, or <code>null</code> if not found
	 */
        public SpecElement find(String name);
    }

    // ================ implementation ===================================

    /** Pluggable behavior for spec elements.
     * @see SpecElement
     */
    public static interface Impl extends MemberElement.Impl {
        /** Add some items. */
        public static final int ADD = 1;
        /** Remove some items. */
        public static final int REMOVE = -1;
        /** Set some items, replacing the old ones. */
        public static final int SET = 0;

        /** Change the set of sorts.
	 * @param elems the new sorts
	 * @param action {@link #ADD}, {@link #REMOVE}, or {@link #SET}
	 * @exception SourceException if impossible
	 */
        public void changeSorts(SortElement[] elems, int action) throws SourceException;

        /** Get all sorts.
	 * @return the sorts
	 */
        public SortElement[] getSorts();

        /** Find a sort by signature.
	 * @param arguments the argument types to look for
	 * @return the sort, or <code>null</code> if it does not exist
	 */
        public SortElement getSort(String name);

        /** Change the set of ops.
	 * @param elems the new ops
	 * @param action {@link #ADD}, {@link #REMOVE}, or {@link #SET}
	 * @exception SourceException if impossible
	 */
        public void changeOps(OpElement[] elems, int action) throws SourceException;

        /** Get all ops.
	 * @return the ops
	 */
        public OpElement[] getOps();

        /** Find a op by content.
	 * @param str the content to look for
	 * @return the op, or <code>null</code> if it does not exist
	 */
        public OpElement getOp(String name);
        
        /** Change the set of claims.
	 * @param elems the new claims
	 * @param action {@link #ADD}, {@link #REMOVE}, or {@link #SET}
	 * @exception SourceException if impossible
	 */
        public void changeClaims(ClaimElement[] elems, int action) throws SourceException;

        /** Get all claims.
	 * @return the claims
	 */
        public ClaimElement[] getClaims();

        /** Find a claim by signature.
	 * @param arguments the argument types to look for
	 * @return the claim, or <code>null</code> if it does not exist
	 */
        public ClaimElement getClaim(String name);
        
    }

    /** Memory based implementation of the element factory.
     */
    static final class Memory extends MemberElement.Memory implements Impl {
        /** collection of sorts */
        private MemoryCollection.Sort sorts;
        /** collection of ops */
        private MemoryCollection.Op ops;
        /** collection of claims */
        private MemoryCollection.Claim claims;

        public Memory() {
        }

        /** Copy constructor.
	 * @param el element to copy from
	 */
        public Memory(SpecElement el) {
            super(el);
        }

        /** Late initialization of initialization of copy elements.
        */
        public void copyFrom (SpecElement copyFrom) {
            changeSorts (copyFrom.getSorts (), SET);
            changeOps (copyFrom.getOps (), SET);
            changeClaims(copyFrom.getClaims (), SET);
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
        public synchronized void changeSorts(SortElement[] elems, int action) {
            initSorts();
            sorts.change(elems, action);
        }

        public synchronized SortElement[] getSorts() {
            initSorts();
            return(SortElement[])sorts.toArray();
        }

        /** Finds a sort with given name and argument types.
	 * @param source the name of source mode
	 * @param target the name of target mode
	 * @return the element or null if such sort does not exist
	 */
        public synchronized SortElement getSort(String name) {
            initSorts();
            return(SortElement)sorts.find(name);
        }

        void initSorts() {
            if (sorts == null) {
                sorts = new MemoryCollection.Sort(this);
            }
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
        public synchronized void changeOps(OpElement[] elems, int action) {
            initOps();
            ops.change(elems, action);
        }

        public synchronized OpElement[] getOps() {
            initOps();
            return(OpElement[])ops.toArray();
        }

        public synchronized OpElement getOp(String name) {
            initOps();
            return(OpElement)ops.find(name);
        }

        void initOps() {
            if (ops == null) {
                ops = new MemoryCollection.Op(this);
            }
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
        public synchronized void changeClaims(ClaimElement[] elems, int action) {
            initClaims();
            claims.change(elems, action);
        }

        public synchronized ClaimElement[] getClaims() {
            initClaims();
            return(ClaimElement[])claims.toArray();
        }

        public synchronized ClaimElement getClaim(String name) {
            initClaims();
            return(ClaimElement)claims.find(name);
        }

        void initClaims() {
            if (claims == null) {
                claims = new MemoryCollection.Claim(this);
            }
        }

        void markCurrent(Element marker, boolean after) {
            MemoryCollection col;
      
            if (marker instanceof SortElement) {
                col = sorts;
	    } else if (marker instanceof OpElement) {
                col = ops;
            } else if (marker instanceof ClaimElement) {
                col = claims;
            } else {
                throw new IllegalArgumentException();
            }
            col.markCurrent(marker, after);
        }

	/** Getter for the associated spec
        * @return the spec element for this impl
        */
        final SpecElement getSpecElement () {
            return (SpecElement)element;
        }

    }
}
