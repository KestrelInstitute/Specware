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

/** Element that describes one diagram.
 * Note that this is a member element.<P>
 * <B>Note:</B> If you add an element to a DiagramElement, the DiagramElement
 * crates its own copy of the passed element. If you perform subsequent
 * modifications to the object passed to addParameter (addMode, addWhatever),
 * the original element will be updated, <B>not</B> the one created as a result
 * of the add() operation.
 *
 */
public final class DiagramElement extends MemberElement {
    /** Formats for the header - used in code generator */
    private static final ElementFormat HEADER_FORMAT = 
        new ElementFormat("diagram"); // NOI18N

    /** source element we are attached to */
    private SourceElement source;
    private boolean topLevel;

    //================ Constructors of DiagramElement =================

    /** Create a new diagram element in memory.
     */
    public DiagramElement() {
        this(new Memory(), null);
    }

    /** Factory constructor for defining top level diagrams.
     * @param impl implementation of functionality
     * @param source the source element this diagram is contained in, or <code>null</code>
     */
    public DiagramElement(MemberElement.Impl impl, Element parent) {
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
        DiagramElement el = new DiagramElement(mem, null);
        mem.copyFrom(this);
        return el;
    }

    /** @return implemetation factory for this diagram
     */
    final Impl getDiagramImpl() {
        return(Impl)impl;
    }
 
    //================ Main properties ==============================

    /** Get the source element of this diagram.
     * @return the source, or <code>null</code> if the diagram is not attached to any source
     */
    public SourceElement getSource() {
        return source;
    }
    
    public void setSource(SourceElement source) {
        this.source = source;
    }
    
    //================== DIAGELEMS ===============================

    public void addDiagElem(DiagElemElement el) throws SourceException {
        if (getDiagElem(el.getName()) != null)
            throwAddException("FMT_EXC_AddDiagElem", el); // NOI18N
        getDiagramImpl().changeDiagElems(new DiagElemElement[] { el }, Impl.ADD);
    }

    public void addDiagElems(final DiagElemElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getDiagElem(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddDiagElem", els[i]); // NOI18N
        getDiagramImpl().changeDiagElems(els, Impl.ADD);
    }

    public void removeDiagElem(DiagElemElement el) throws SourceException {
        getDiagramImpl().changeDiagElems(new DiagElemElement[] { el }, Impl.REMOVE
                                     );
    }

    public void removeDiagElems(final DiagElemElement[] els) throws SourceException {
        getDiagramImpl().changeDiagElems(els, Impl.REMOVE);
    }

    public void setDiagElems(DiagElemElement[] els) throws SourceException {
        getDiagramImpl().changeDiagElems(els, Impl.SET);
    }

    public DiagElemElement[] getDiagElems() {
        return getDiagramImpl().getDiagElems();
    }

    public DiagElemElement getDiagElem(String name) {
        return getDiagramImpl().getDiagElem(name);
    }


    // ================ printing =========================================

    /* Print this element to an element printer.
     * @param printer the printer to print to
     * @exception ElementPrinterInterruptException if the printer cancels the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
	boolean topLevel = (source != null);

        printer.markDiagram(this, printer.ELEMENT_BEGIN);

        printer.markDiagram(this, printer.HEADER_BEGIN); // HEADER begin
        if (topLevel) {
	    printer.print(getName()+" = ");
	}
	printer.print(HEADER_FORMAT.format(this));

        printer.markDiagram(this, printer.HEADER_END); // HEADER end

        printer.markDiagram(this, printer.BODY_BEGIN); // BODY begin
        printer.print(" {"); // NOI18N

        if (print(getDiagElems(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N
        }

        printer.println("}"); // NOI18N
        printer.markDiagram(this, printer.BODY_END); // BODY end

        if (topLevel) {
	    printer.println("");
	}

        printer.markDiagram(this, printer.ELEMENT_END);
    }

    // ================ misc =========================================

    /** This mode just throws localized exception. It is used during
     * adding some element, which already exists in the diagram.
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

    /** Register a new finder for locating diagram elements.
     * @param f the finder to add
     */
    public static void register(Finder f) {
        synchronized(finders) {
            finders.add(f);
        }
    }

    /** Unregister a finder for locating diagram elements.
     * @param f the finder to remove
     */
    public static void unregister(Finder f) {
        synchronized(finders) {
            finders.remove(f);
        }
    }

    /** Provides a "finder" for diagram elements.
     * A module can provide its own finder to enhance the ability
     * of the IDE to locate a valid diagram element description for different diagrams.
     * @see DiagramElement#forName
     * @see DiagramElement#register
     * @see DiagramElement#unregister
     */
    public static interface Finder {
        /** Find a diagram element description for a diagram.
	 *
	 * @param diagram the diagram to find
	 * @return the diagram element, or <code>null</code> if not found
	 */
        //public DiagramElement find(Diagram diagram);

        /** Find a diagram element description for a diagram name.
	 *
	 * @param name the name of a diagram to find
	 * @return the diagram element, or <code>null</code> if not found
	 */
        public DiagramElement find(String name);
    }

    // ================ implementation ===================================

    /** Pluggable behavior for diagram elements.
     * @see DiagramElement
     */
    public static interface Impl extends MemberElement.Impl {

        //============== DIAGELEMS ======================
        public void changeDiagElems(DiagElemElement[] elems, int action) throws SourceException;

        public DiagElemElement[] getDiagElems();

        public DiagElemElement getDiagElem(String name);

    }
        

    /** Memory based implementation of the element factory.
     */
    static final class Memory extends MemberElement.Memory implements Impl {
        /** collection of diagElems */
        private MemoryCollection.DiagElem diagElems;       

        public Memory() {
        }

        /** Copy constructor.
	 * @param el element to copy from
	 */
        public Memory(DiagramElement el) {
            super(el);
        }

        /** Late initialization of initialization of copy elements.
        */
        public void copyFrom (DiagramElement copyFrom) {
            changeDiagElems (copyFrom.getDiagElems (), SET);
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
        public synchronized void changeDiagElems(DiagElemElement[] elems, int action) {
            initDiagElems();
            diagElems.change(elems, action);
        }

        public synchronized DiagElemElement[] getDiagElems() {
            initDiagElems();
            return(DiagElemElement[])diagElems.toArray();
        }

        /** Finds a diagElem with given name and argument types.
	 * @param source the name of source mode
	 * @param target the name of target mode
	 * @return the element or null if such diagElem does not exist
	 */
        public synchronized DiagElemElement getDiagElem(String name) {
            initDiagElems();
            return(DiagElemElement)diagElems.find(name);
        }

        void initDiagElems() {
            if (diagElems == null) {
                diagElems = new MemoryCollection.DiagElem(this);
            }
        }


        void markCurrent(Element marker, boolean after) {
            MemoryCollection col = null;
      
            if (marker instanceof DiagElemElement) {
                col = diagElems;
            } else {
                throw new IllegalArgumentException();
            }
          if (col != null) 
                col.markCurrent(marker, after);
        }

	/** Getter for the associated diagram
        * @return the diagram element for this impl
        */
        final DiagramElement getDiagramElement () {
            return (DiagramElement)element;
        }

    }
} 
