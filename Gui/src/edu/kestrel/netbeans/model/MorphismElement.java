/*
 * MorphismElement.java
 *
 * Created on March 28, 2003, 3:22 PM
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

/**
 *
 * @author  weilyn
 */
public class MorphismElement extends MemberElement {
    
    /** Formats for the header - used in code generator */
    private static final ElementFormat HEADER_FORMAT = 
        new ElementFormat("morphism"); // NOI18N

    /** source element we are attached to */
    private SourceElement source;
    private boolean topLevel;

    //================ Constructors of MorphismElement =================

    /** Create a new morphism element in memory.
     */
    public MorphismElement() {
        this(new Memory(), null);
    }

    /** Factory constructor for defining top level morphisms.
     * @param impl implementation of functionality
     * @param source the source element this morphism is contained in, or <code>null</code>
     */
    public MorphismElement(MemberElement.Impl impl, Element parent) {
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
        MorphismElement el = new MorphismElement(mem, null);
        mem.copyFrom(this);
        return el;
    }

    /** @return implemetation factory for this morphism
     */
    final Impl getMorphismImpl() {
        return(Impl)impl;
    }
 
    //================ Main properties ==============================

    /** Get the source element of this morphism.
     * @return the source, or <code>null</code> if the morphism is not attached to any source
     */
    public SourceElement getSource() {
        return source;
    }
    
    public void setSource(SourceElement source) {
        this.source = source;
    }
    
    //================== TODO: ADD THESE METHODS FOR EACH SUB-ELEMENT ===============================

    /** Add a new import to the spec.
     *  @param el the import to add
     * @throws SourceException if impossible
     */
/*    public void addImport(ImportElement el) throws SourceException {
        if (getImport(el.getName()) != null)
            throwAddException("FMT_EXC_AddImport", el); // NOI18N
        getSpecImpl().changeImports(new ImportElement[] { el }, Impl.ADD);
    }
*/
    /** Add some new imports to the spec.
     *  @param els the imports to add
     * @throws SourceException if impossible
     */
/*    public void addImports(final ImportElement[] els) throws SourceException {
        for (int i = 0; i < els.length; i++)
            if (getImport(els[i].getName()) != null)
                throwAddException("FMT_EXC_AddImport", els[i]); // NOI18N
        getSpecImpl().changeImports(els, Impl.ADD);
    }
*/
    /** Remove a import from the spec.
     *  @param el the import to remove
     * @throws SourceException if impossible
     */
/*    public void removeImport(ImportElement el) throws SourceException {
        getSpecImpl().changeImports(
						 new ImportElement[] { el }, Impl.REMOVE
						 );
    }
*/
    /** Remove some imports from the spec.
     *  @param els the imports to remove
     * @throws SourceException if impossible
     */
/*    public void removeImports(final ImportElement[] els) throws SourceException {
        getSpecImpl().changeImports(els, Impl.REMOVE);
    }
*/
    /** Set the imports for this spec.
     * Previous imports are removed.
     * @param els the new imports
     * @throws SourceException if impossible
     */
/*    public void setImports(ImportElement[] els) throws SourceException {
        getSpecImpl().changeImports(els, Impl.SET);
    }
*/
    /** Get all imports in this spec.
     * @return the imports
     */
/*    public ImportElement[] getImports() {
        return getSpecImpl().getImports();
    }
*/
    /** Find a import by name.
     * @param name the name of the import to look for
     * @return the element or <code>null</code> if not found
     */
/*    public ImportElement getImport(String name) {
        return getSpecImpl().getImport(name);
    }
*/

    // ================ printing =========================================

    /* Print this element to an element printer.
     * @param printer the printer to print to
     * @exception ElementPrinterInterruptException if the printer cancels the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
	boolean topLevel = (source != null);

        printer.markMorphism(this, printer.ELEMENT_BEGIN);

        printer.markMorphism(this, printer.HEADER_BEGIN); // HEADER begin
        if (topLevel) {
	    printer.println(getName()+" =");
	}
	printer.print(HEADER_FORMAT.format(this));

        printer.markMorphism(this, printer.HEADER_END); // HEADER end

        printer.markMorphism(this, printer.BODY_BEGIN); // BODY begin
        printer.println(""); // NOI18N

/*        if (print(getImports(), printer)) {
            printer.println(""); // NOI18N
            printer.println(""); // NOI18N
        }
*/
        printer.println(""); // NOI18N
        printer.markMorphism(this, printer.BODY_END); // BODY end
//        printer.print("endspec"); // NOI18N

        if (topLevel) {
	    printer.println("");
	    printer.println("");
	}

        printer.markMorphism(this, printer.ELEMENT_END);
    }

    // ================ misc =========================================

    /** This mode just throws localized exception. It is used during
     * adding some element, which already exists in the morphism.
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

    /** Register a new finder for locating morphism elements.
     * @param f the finder to add
     */
    public static void register(Finder f) {
        synchronized(finders) {
            finders.add(f);
        }
    }

    /** Unregister a finder for locating morphism elements.
     * @param f the finder to remove
     */
    public static void unregister(Finder f) {
        synchronized(finders) {
            finders.remove(f);
        }
    }

    /** Provides a "finder" for morphism elements.
     * A module can provide its own finder to enhance the ability
     * of the IDE to locate a valid morphism element description for different morphisms.
     * @see MorphismElement#forName
     * @see MorphismElement#register
     * @see MorphismElement#unregister
     */
    public static interface Finder {
        /** Find a morphism element description for a morphism.
	 *
	 * @param morphism the morphism to find
	 * @return the morphism element, or <code>null</code> if not found
	 */
        //public MorphismElement find(Morphism morphism);

        /** Find a morphism element description for a morphism name.
	 *
	 * @param name the name of a morphism to find
	 * @return the morphism element, or <code>null</code> if not found
	 */
        public MorphismElement find(String name);
    }

    // ================ implementation ===================================

    /** Pluggable behavior for morphism elements.
     * @see MorphismElement
     */
    public static interface Impl extends MemberElement.Impl {
        /** Add some items. */
        public static final int ADD = SpecElement.Impl.ADD;//1;
        /** Remove some items. */
        public static final int REMOVE = SpecElement.Impl.REMOVE;//-1;
        /** Set some items, replacing the old ones. */
        public static final int SET = SpecElement.Impl.SET;//0;

        //==============TODO======================
        /** Change the set of imports.
         * @param elems the new imports
         * @param action {@link #ADD}, {@link #REMOVE}, or {@link #SET}
         * @exception SourceException if impossible
         */
        //public void changeImports(ImportElement[] elems, int action) throws SourceException;

        /** Get all imports.
         * @return the imports
         */
        //public ImportElement[] getImports();

        /** Find a import by signature.
         * @param arguments the argument types to look for
         * @return the import, or <code>null</code> if it does not exist
         */
        //public ImportElement getImport(String name);

    }
        

    /** Memory based implementation of the element factory.
     */
    static final class Memory extends MemberElement.Memory implements Impl {
        /** collection of imports */
//        private MemoryCollection.Import imports;       

        public Memory() {
        }

        /** Copy constructor.
	 * @param el element to copy from
	 */
        public Memory(MorphismElement el) {
            super(el);
        }

        /** Late initialization of initialization of copy elements.
        */
        public void copyFrom (MorphismElement copyFrom) {
//            changeImports (copyFrom.getImports (), SET);
        }

        /** Changes set of elements.
	 * @param elems elements to change
	 * @param action the action to do(ADD, REMOVE, SET)
	 * @exception SourceException if the action cannot be handled
	 */
/*        public synchronized void changeImports(ImportElement[] elems, int action) {
            initImports();
            imports.change(elems, action);
        }

        public synchronized ImportElement[] getImports() {
            initImports();
            return(ImportElement[])imports.toArray();
        }
*/
        /** Finds a import with given name and argument types.
	 * @param source the name of source mode
	 * @param target the name of target mode
	 * @return the element or null if such import does not exist
	 */
/*        public synchronized ImportElement getImport(String name) {
            initImports();
            return(ImportElement)imports.find(name);
        }

        void initImports() {
            if (imports == null) {
                imports = new MemoryCollection.Import(this);
            }
        }
*/

        void markCurrent(Element marker, boolean after) {
            MemoryCollection col = null;
      
/*            if (marker instanceof ImportElement) {
                col = imports;
            } else {
                throw new IllegalArgumentException();
            }
*/          if (col != null) 
                col.markCurrent(marker, after);
        }

	/** Getter for the associated morphism
        * @return the morphism element for this impl
        */
        final MorphismElement getMorphismElement () {
            return (MorphismElement)element;
        }

    }
} 