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

/** Element that describes one colimit.
 * Note that this is a member element.<P>
 * <B>Note:</B> If you add an element to a ColimitElement, the ColimitElement
 * crates its own copy of the passed element. If you perform subsequent
 * modifications to the object passed to addParameter (addMode, addWhatever),
 * the original element will be updated, <B>not</B> the one created as a result
 * of the add() operation.
 *
 */
public final class ColimitElement extends MemberElement {
    /** Formats for the header - used in code generator */
    private static final ElementFormat HEADER_FORMAT = 
        new ElementFormat("colimit"); // NOI18N

    /** source element we are attached to */
    private SourceElement source;
    private boolean topLevel;

    //================ Constructors of ColimitElement =================

    /** Create a new colimit element in memory.
     */
    public ColimitElement() {
        this(new Memory(), null);
    }

    /** Factory constructor for defining top level colimits.
     * @param impl implementation of functionality
     * @param source the source element this colimit is contained in, or <code>null</code>
     */
    public ColimitElement(MemberElement.Impl impl, Element parent) {
        super(impl, parent);
	if (parent instanceof SourceElement) {
	    this.source = (SourceElement) parent;
	    this.topLevel = true;
	} else {
            this.source = null;
	    this.topLevel = false;
	}
    }

    /** Clone this element.
     * @return new element with the same values as the original,
     *   but represented in memory
     */
    public Object clone() {
        Memory mem = new Memory(this);
        ColimitElement el = new ColimitElement(mem, null);
        mem.copyFrom(this);
        return el;
    }

    /** @return implemetation factory for this colimit
     */
    final Impl getColimitImpl() {
        return(Impl)impl;
    }
 
    //================ Main properties ==============================

    /** Get the source element of this colimit.
     * @return the source, or <code>null</code> if the colimit is not attached to any source
     */
    public SourceElement getSource() {
        return source;
    }
    
    public void setSource(SourceElement source) {
        this.source = source;
    }
    
//================== Diagrams ===============================

    /** Add a new diagram to the colimit.
     *  @param el the diagram to add
     * @throws SourceException if impossible
     */
    public void addDiagram(DiagramElement el) throws SourceException {
        if (getDiagram(el.getName()) != null)
            throwAddException("FMT_EXC_AddDiagram", el); // NOI18N
        getColimitImpl().changeDiagrams(new DiagramElement[] { el }, Impl.ADD);
    }

    /** Add some new diagrams to the colimit.
     *  @param els the diagrams to add
     * @throws SourceException if impossible
     */
    public void addDiagrams(final DiagramElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getDiagram(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddDiagram", els[i]); // NOI18N
        getColimitImpl().changeDiagrams(els, Impl.ADD);
    }

    /** Remove a diagram from the colimit.
     *  @param el the diagram to remove
     * @throws SourceException if impossible
     */
    public void removeDiagram(DiagramElement el) throws SourceException {
        getColimitImpl().changeDiagrams(new DiagramElement[] { el }, Impl.REMOVE);
    }

    /** Remove some diagrams from the colimit.
     *  @param els the diagrams to remove
     * @throws SourceException if impossible
     */
    public void removeDiagrams(final DiagramElement[] els) throws SourceException {
        getColimitImpl().changeDiagrams(els, Impl.REMOVE);
    }

    /** Set the diagrams for this colimit.
     * Previous diagrams are removed.
     * @param els the new diagrams
     * @throws SourceException if impossible
     */
    public void setDiagrams(DiagramElement[] els) throws SourceException {
        getColimitImpl().changeDiagrams(els, Impl.SET);
    }

    /** Get all diagrams in this colimit.
     * @return the diagrams
     */
    public DiagramElement[] getDiagrams() {
        return getColimitImpl().getDiagrams();
    }

    /** Find a diagram by name.
     * @param name the name of the diagram to look for
     * @return the element or <code>null</code> if not found
     */
    public DiagramElement getDiagram(String name) {
        return getColimitImpl().getDiagram(name);
    }


    // ================ printing =========================================

    /* Print this element to an element printer.
     * @param printer the printer to print to
     * @exception ElementPrinterInterruptException if the printer cancels the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
	boolean topLevel = (source != null);

        printer.markColimit(this, printer.ELEMENT_BEGIN);

        printer.markColimit(this, printer.HEADER_BEGIN); // HEADER begin
        if (topLevel) {
	    printer.println(getName()+" =");
	}
	printer.print(HEADER_FORMAT.format(this));

        printer.markColimit(this, printer.HEADER_END); // HEADER end

        printer.markColimit(this, printer.BODY_BEGIN); // BODY begin
        printer.println(""); // NOI18N

        if (print(getDiagrams(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N
        }

        printer.println(""); // NOI18N
        printer.markColimit(this, printer.BODY_END); // BODY end
//        printer.print("endspec"); // NOI18N

        if (topLevel) {
	    printer.println("");
	    printer.println("");
	}

        printer.markColimit(this, printer.ELEMENT_END);
    }

    // ================ misc =========================================

    /** This mode just throws localized exception. It is used during
     * adding some element, which already exists in the colimit.
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

    /** Register a new finder for locating colimit elements.
     * @param f the finder to add
     */
    public static void register(Finder f) {
        synchronized(finders) {
            finders.add(f);
        }
    }

    /** Unregister a finder for locating colimit elements.
     * @param f the finder to remove
     */
    public static void unregister(Finder f) {
        synchronized(finders) {
            finders.remove(f);
        }
    }

    /** Provides a "finder" for colimit elements.
     * A module can provide its own finder to enhance the ability
     * of the IDE to locate a valid colimit element description for different colimits.
     * @see ColimitElement#forName
     * @see ColimitElement#register
     * @see ColimitElement#unregister
     */
    public static interface Finder {
        /** Find a colimit element description for a colimit.
	 *
	 * @param colimit the colimit to find
	 * @return the colimit element, or <code>null</code> if not found
	 */
        //public ColimitElement find(Colimit colimit);

        /** Find a colimit element description for a colimit name.
	 *
	 * @param name the name of a colimit to find
	 * @return the colimit element, or <code>null</code> if not found
	 */
        public ColimitElement find(String name);
    }

    // ================ implementation ===================================

    /** Pluggable behavior for colimit elements.
     * @see ColimitElement
     */
    public static interface Impl extends MemberElement.Impl {

        //============== Diagrams ======================
        /** Change the set of diagrams.
         * @param elems the new diagrams
         * @param action {@link #ADD}, {@link #REMOVE}, or {@link #SET}
         * @exception SourceException if impossible
         */
        public void changeDiagrams(DiagramElement[] elems, int action) throws SourceException;

        /** Get all diagrams.
         * @return the diagrams
         */
        public DiagramElement[] getDiagrams();

        /** Find a diagram by signature.
         * @param arguments the argument types to look for
         * @return the diagram, or <code>null</code> if it does not exist
         */
        public DiagramElement getDiagram(String name);

    }
        

    /** Memory based implementation of the element factory.
     */
    static final class Memory extends MemberElement.Memory implements Impl {
        /** collection of diagrams */
        private MemoryCollection.Diagram diagrams;       

        public Memory() {
        }

        /** Copy constructor.
	 * @param el element to copy from
	 */
        public Memory(ColimitElement el) {
            super(el);
        }

        /** Late initialization of initialization of copy elements.
        */
        public void copyFrom (ColimitElement copyFrom) {
            changeDiagrams (copyFrom.getDiagrams (), SET);
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
        public synchronized void changeDiagrams(DiagramElement[] elems, int action) {
            initDiagrams();
            diagrams.change(elems, action);
        }

        public synchronized DiagramElement[] getDiagrams() {
            initDiagrams();
            return(DiagramElement[])diagrams.toArray();
        }

        /** Finds a diagram with given name and argument types.
	 * @param source the name of source mode
	 * @param target the name of target mode
	 * @return the element or null if such diagram does not exist
	 */
        public synchronized DiagramElement getDiagram(String name) {
            initDiagrams();
            return(DiagramElement)diagrams.find(name);
        }

        void initDiagrams() {
            if (diagrams == null) {
                diagrams = new MemoryCollection.Diagram(this);
            }
        }

        void markCurrent(Element marker, boolean after) {
            MemoryCollection col = null;
      
            if (marker instanceof DiagramElement) {
                col = diagrams;
            } else {
                throw new IllegalArgumentException();
            }
          if (col != null) 
                col.markCurrent(marker, after);
        }

	/** Getter for the associated colimit
        * @return the colimit element for this impl
        */
        final ColimitElement getColimitElement () {
            return (ColimitElement)element;
        }

    }
} 