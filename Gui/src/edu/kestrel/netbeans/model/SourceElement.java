/*
 * SourceElement.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/04/23 01:14:40  weilyn
 * BindingFactory.java
 *
 * Revision 1.4  2003/04/01 02:29:37  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.3  2003/03/29 03:13:57  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.2  2003/03/14 04:14:01  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:03  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.io.IOException;
import java.io.Reader;
import java.io.PrintWriter;
import java.util.Enumeration;
import java.util.Vector;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.StyledDocument;
import java.util.*;
import org.openide.text.IndentEngine;
import java.io.*;

import org.openide.util.Task;
import org.openide.util.NbBundle;
import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;
import edu.kestrel.netbeans.codegen.DefaultElementPrinter;

/** Describes an entire MetaSlang source file.
* Note that there is no standard in-memory implementation of this element;
* every user of the class is expected to have a reasonable
* implementation according to where the source file resides.
* <p>The source element should be parsed in the background using
* {@link #prepare} before any attempts are made to access its properties
* to read or to write, or to call {@link #print};
* otherwise such accesses will block until the parse is finished.
*/
public final class SourceElement extends Element {
    /** Status when the source element is not yet prepared.
    */
    public static final int STATUS_NOT = 0;
    /** Status when the source element contains unrecoverable errors.
    */
    public static final int STATUS_ERROR = 1;
    /** Status when the source element contains minor errors.
    */
    public static final int STATUS_PARTIAL = 2;
    /** Status when the source element has been parsed and is error-free.
    */
    public static final int STATUS_OK = 3;

    static final long serialVersionUID =-1439690719608070114L;

    /** Create a new source element.
    * @param impl the pluggable implementation
    */
    public SourceElement(Impl impl) {
        super (impl);
    }

    /** @return implementation for the source
    */
    final Impl getSourceImpl() {
        return (Impl)impl;
    }

    /** Get the parsing status of the element.
    * This is a non-blocking operation.
    * @return one of {@link #STATUS_NOT}, {@link #STATUS_ERROR}, {@link #STATUS_PARTIAL}, or {@link #STATUS_OK}
    */
    public int getStatus() {
        return getSourceImpl().getStatus ();
    }

    /** Begin parsing this source element.
    * This method is non-blocking; it only returns
    * a task that can be used to control the ongoing parse.
    * Initially the {@link #getStatus} should be {@link #STATUS_NOT}, and change
    * to one of the other three when parsing is complete, according to whether
    * or not errors were encountered, and their severity.
    *
    * @return a task to control the preparation of the element
    */
    public Task prepare() {
        return getSourceImpl().prepare ();
    }

    public String toString() {
        StringWriter sw = new StringWriter();
	StyledDocument doc = createDocument();
        System.err.println("*** Source.toString() doc="+doc);
        IndentEngine indentator = IndentEngine.find(doc); 
        System.err.println("*** Source.toString() indentator="+indentator);
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

    //================== specs ==========================

    /** Add a new spec.
    * @param el the spec to add
    * @throws SourceException if impossible
    */
    public void addSpec (SpecElement el) throws SourceException {
      //Util.log("SourceElement.addSpec -- adding spec "+el.getName());
        String id = el.getName();
        if (getSpec(id) != null)
            throwAddException("FMT_EXC_AddSpecToSource", el); // NOI18N
        getSourceImpl().changeSpecs(new SpecElement[] { el }, Impl.ADD);
    }

    /** Add some new specs.
    * @param el the specs to add
    * @throws SourceException if impossible
    */
    public void addSpecs(final SpecElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getName();
            if (getSpec(id) != null)
                throwAddException("FMT_EXC_AddSpecToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeSpecs(els, Impl.ADD);
    }

    /** This method just throws localized exception. It is used during
    * adding spec element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
    private void throwAddException(String formatKey, SpecElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getName());
        throwSourceException(msg);
    }

    /** Remove an spec.
    * @param el the spec to remove
    * @throws SourceException if impossible
    */
    public void removeSpec(SpecElement el) throws SourceException {
        getSourceImpl().changeSpecs(new SpecElement[] { el }, Impl.REMOVE);
    }

    /** Remove some specs.
    * @param els the specs to remove
    * @throws SourceException if impossible
    */
    public void removeSpecs (final SpecElement[] els) throws SourceException {
        getSourceImpl().changeSpecs(els, Impl.REMOVE);
    }

    /** Set the specs.
    * The old ones will be replaced.
    * @param els the new specs
    * @throws SourceException if impossible
    */
    public void setSpecs (SpecElement[] els) throws SourceException {
        getSourceImpl().changeSpecs(els, Impl.SET);
    }

    /** Get the specs.
    * @return all specs
    */
    public SpecElement[] getSpecs() {
        System.err.println("*** getSpecs(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getSpecs();
    }

    /** Find a spec by name.
    * @param name the name to look for
    * @return the spec, or <code>null</code> if it does not exist
    */
    public SpecElement getSpec(String name) {
        return getSourceImpl().getSpec(name);
    }

  //================== proofs ==========================

    /** Add a new proof.
    * @param el the proof to add
    * @throws SourceException if impossible
    */
    public void addProof (ProofElement el) throws SourceException {
      //Util.log("SourceElement.addProof -- adding proof "+el.getName());
        String id = el.getName();
        if (getProof(id) != null)
            throwAddException("FMT_EXC_AddProofToSource", el); // NOI18N
        getSourceImpl().changeProofs(new ProofElement[] { el }, Impl.ADD);
    }

    /** Add some new proofs.
    * @param el the proofs to add
    * @throws SourceException if impossible
    */
    public void addProofs(final ProofElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getName();
            if (getProof(id) != null)
                throwAddException("FMT_EXC_AddProofToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeProofs(els, Impl.ADD);
    }

    /** This method just throws localized exception. It is used during
    * adding proof element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
    private void throwAddException(String formatKey, ProofElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getName());
        throwSourceException(msg);
    }

    /** Remove a proof.
    * @param el the proof to remove
    * @throws SourceException if impossible
    */
    public void removeProof(ProofElement el) throws SourceException {
        getSourceImpl().changeProofs(new ProofElement[] { el }, Impl.REMOVE);
    }

    /** Remove some proofs.
    * @param els the proofs to remove
    * @throws SourceException if impossible
    */
    public void removeProofs (final ProofElement[] els) throws SourceException {
        getSourceImpl().changeProofs(els, Impl.REMOVE);
    }

    /** Set the proofs.
    * The old ones will be replaced.
    * @param els the new proofs
    * @throws SourceException if impossible
    */
    public void setProofs (ProofElement[] els) throws SourceException {
        getSourceImpl().changeProofs(els, Impl.SET);
    }

    /** Get the proofs.
    * @return all proofs
    */
    public ProofElement[] getProofs() {
        System.err.println("*** getProofs(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getProofs();
    }

    /** Find a proof by name.
    * @param name the name to look for
    * @return the proof, or <code>null</code> if it does not exist
    */
    public ProofElement getProof(String name) {
        return getSourceImpl().getProof(name);
    }

  //================== morphisms ==========================

    /** Add a new morphism.
    * @param el the morphism to add
    * @throws SourceException if impossible
    */
    public void addMorphism (MorphismElement el) throws SourceException {
      //Util.log("SourceElement.addMorphism -- adding morphism "+el.getName());
        String id = el.getName();
        if (getMorphism(id) != null)
            throwAddException("FMT_EXC_AddMorphismToSource", el); // NOI18N
        getSourceImpl().changeMorphisms(new MorphismElement[] { el }, Impl.ADD);
    }

    /** Add some new morphisms.
    * @param el the morphisms to add
    * @throws SourceException if impossible
    */
    public void addMorphisms(final MorphismElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getName();
            if (getMorphism(id) != null)
                throwAddException("FMT_EXC_AddMorphismToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeMorphisms(els, Impl.ADD);
    }

    /** This method just throws localized exception. It is used during
    * adding morphism element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
    private void throwAddException(String formatKey, MorphismElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getName());
        throwSourceException(msg);
    }

    /** Remove a morphism.
    * @param el the morphism to remove
    * @throws SourceException if impossible
    */
    public void removeMorphism(MorphismElement el) throws SourceException {
        getSourceImpl().changeMorphisms(new MorphismElement[] { el }, Impl.REMOVE);
    }

    /** Remove some morphisms.
    * @param els the morphisms to remove
    * @throws SourceException if impossible
    */
    public void removeMorphisms (final MorphismElement[] els) throws SourceException {
        getSourceImpl().changeMorphisms(els, Impl.REMOVE);
    }

    /** Set the morphisms.
    * The old ones will be replaced.
    * @param els the new morphisms
    * @throws SourceException if impossible
    */
    public void setMorphisms (MorphismElement[] els) throws SourceException {
        getSourceImpl().changeMorphisms(els, Impl.SET);
    }

    /** Get the morphisms.
    * @return all morphisms
    */
    public MorphismElement[] getMorphisms() {
        System.err.println("*** getMorphisms(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getMorphisms();
    }

    /** Find a morphism by name.
    * @param name the name to look for
    * @return the morphism, or <code>null</code> if it does not exist
    */
    public MorphismElement getMorphism(String name) {
        return getSourceImpl().getMorphism(name);
    }

  //================== diagrams ==========================

    /** Add a new diagram.
    * @param el the diagram to add
    * @throws SourceException if impossible
    */
    public void addDiagram (DiagramElement el) throws SourceException {
      //Util.log("SourceElement.addDiagram -- adding diagram "+el.getName());
        String id = el.getName();
        if (getDiagram(id) != null)
            throwAddException("FMT_EXC_AddDiagramToSource", el); // NOI18N
        getSourceImpl().changeDiagrams(new DiagramElement[] { el }, Impl.ADD);
    }

    /** Add some new diagrams.
    * @param el the diagrams to add
    * @throws SourceException if impossible
    */
    public void addDiagrams(final DiagramElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getName();
            if (getDiagram(id) != null)
                throwAddException("FMT_EXC_AddDiagramToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeDiagrams(els, Impl.ADD);
    }

    /** This method just throws localized exception. It is used during
    * adding diagram element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
    private void throwAddException(String formatKey, DiagramElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getName());
        throwSourceException(msg);
    }

    /** Remove a diagram.
    * @param el the diagram to remove
    * @throws SourceException if impossible
    */
    public void removeDiagram(DiagramElement el) throws SourceException {
        getSourceImpl().changeDiagrams(new DiagramElement[] { el }, Impl.REMOVE);
    }

    /** Remove some diagrams.
    * @param els the diagrams to remove
    * @throws SourceException if impossible
    */
    public void removeDiagrams (final DiagramElement[] els) throws SourceException {
        getSourceImpl().changeDiagrams(els, Impl.REMOVE);
    }

    /** Set the diagrams.
    * The old ones will be replaced.
    * @param els the new diagrams
    * @throws SourceException if impossible
    */
    public void setDiagrams (DiagramElement[] els) throws SourceException {
        getSourceImpl().changeDiagrams(els, Impl.SET);
    }

    /** Get the diagrams.
    * @return all diagrams
    */
    public DiagramElement[] getDiagrams() {
        System.err.println("*** getDiagrams(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getDiagrams();
    }

    /** Find a diagram by name.
    * @param name the name to look for
    * @return the diagram, or <code>null</code> if it does not exist
    */
    public DiagramElement getDiagram(String name) {
        return getSourceImpl().getDiagram(name);
    }

  //================== colimits ==========================

    /** Add a new colimit.
    * @param el the colimit to add
    * @throws SourceException if impossible
    */
    public void addColimit (ColimitElement el) throws SourceException {
      //Util.log("SourceElement.addColimit -- adding colimit "+el.getName());
        String id = el.getName();
        if (getColimit(id) != null)
            throwAddException("FMT_EXC_AddColimitToSource", el); // NOI18N
        getSourceImpl().changeColimits(new ColimitElement[] { el }, Impl.ADD);
    }

    /** Add some new colimits.
    * @param el the colimits to add
    * @throws SourceException if impossible
    */
    public void addColimits(final ColimitElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getName();
            if (getColimit(id) != null)
                throwAddException("FMT_EXC_AddColimitToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeColimits(els, Impl.ADD);
    }

    /** This method just throws localized exception. It is used during
    * adding colimit element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
    private void throwAddException(String formatKey, ColimitElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getName());
        throwSourceException(msg);
    }

    /** Remove a colimit.
    * @param el the colimit to remove
    * @throws SourceException if impossible
    */
    public void removeColimit(ColimitElement el) throws SourceException {
        getSourceImpl().changeColimits(new ColimitElement[] { el }, Impl.REMOVE);
    }

    /** Remove some colimits.
    * @param els the colimits to remove
    * @throws SourceException if impossible
    */
    public void removeColimits (final ColimitElement[] els) throws SourceException {
        getSourceImpl().changeColimits(els, Impl.REMOVE);
    }

    /** Set the colimits.
    * The old ones will be replaced.
    * @param els the new colimits
    * @throws SourceException if impossible
    */
    public void setColimits (ColimitElement[] els) throws SourceException {
        getSourceImpl().changeColimits(els, Impl.SET);
    }

    /** Get the colimits.
    * @return all colimits
    */
    public ColimitElement[] getColimits() {
        System.err.println("*** getColimits(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getColimits();
    }

    /** Find a colimit by name.
    * @param name the name to look for
    * @return the colimit, or <code>null</code> if it does not exist
    */
    public ColimitElement getColimit(String name) {
        return getSourceImpl().getColimit(name);
    }

  //================== UIDs ==========================

    /** Add a new unitId.
    * @param el the unitId to add
    * @throws SourceException if impossible
    */
/*    public void addUID (UIDElement el) throws SourceException {
      //Util.log("SourceElement.addUID -- adding unitId "+el.getName());
        String id = el.getPath();
        if (getUID(id) != null)
            throwAddException("FMT_EXC_AddUIDToSource", el); // NOI18N
        getSourceImpl().changeUIDs(new UIDElement[] { el }, Impl.ADD);
    }*/

    /** Add some new uids.
    * @param el the uids to add
    * @throws SourceException if impossible
    */
    /*public void addUIDs(final UIDElement[] els) throws SourceException {
        String id;
        
        for (int i = 0; i < els.length; i++) {
            id = els[i].getPath();
            if (getUID(id) != null)
                throwAddException("FMT_EXC_AddUIDToSource", els[i]); // NOI18N
        }
        getSourceImpl().changeUIDs(els, Impl.ADD);
    }*/

    /** This method just throws localized exception. It is used during
    * adding unitId element, which already exists in source.
    * @param formatKey The message format key to localized bundle.
    * @param element The element which can't be added
    * @exception SourceException is alway thrown from this method.
    */
/*    private void throwAddException(String formatKey, UIDElement element) throws SourceException {
	String msg = NbBundle.getMessage(ElementFormat.class, formatKey,
					 element.getPath());
        throwSourceException(msg);
    }*/

    /** Remove a unitId.
    * @param el the unitId to remove
    * @throws SourceException if impossible
    */
/*    public void removeUID(UIDElement el) throws SourceException {
        getSourceImpl().changeUIDs(new UIDElement[] { el }, Impl.REMOVE);
    }*/

    /** Remove some uids.
    * @param els the uids to remove
    * @throws SourceException if impossible
    */
/*    public void removeUIDs (final UIDElement[] els) throws SourceException {
        getSourceImpl().changeUIDs(els, Impl.REMOVE);
    }*/

    /** Set the uids.
    * The old ones will be replaced.
    * @param els the new uids
    * @throws SourceException if impossible
    */
/*    public void setUIDs (UIDElement[] els) throws SourceException {
        getSourceImpl().changeUIDs(els, Impl.SET);
    }*/

    /** Get the uids.
    * @return all uids
    */
/*    public UIDElement[] getUIDs() {
        System.err.println("*** getUIDs(): SourceImpl="+ getSourceImpl());
        return getSourceImpl().getUIDs();
    }*/

    /** Find a unitId by path.
    * @param path the path to look for
    * @return the unitId, or <code>null</code> if it does not exist
    */
/*    public UIDElement getUID(String path) {
        return getSourceImpl().getUID(path);
    }*/

    //-------------------------------------------------------------
    
    /* Prints the element into the element printer.
    * @param printer The element printer where to print to
    * @exception ElementPrinterInterruptException if printer cancel the printing
    */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        print(getSpecs(), printer);
        print(getProofs(), printer);
        print(getMorphisms(), printer);
        print(getDiagrams(), printer);
        print(getColimits(), printer);
        //print(getUIDs(), printer);
    }
    
    /** Lock the underlaing document to have exclusive access to it and could make changes
    * on this SourceElement.
    *
    * @param run the action to run
    */
    public void runAtomic(Runnable run) {
        getSourceImpl().runAtomic(run);
    }

    /** Executes given runnable in "user mode" does not allowing any modifications
    * to parts of text marked as guarded. The actions should be run as "atomic" so
    * either happen all at once or none at all (if a guarded block should be modified).
    *
    * @param run the action to run
    * @exception SourceException if a modification of guarded text occured
    *   and that is why no changes to the document has been done.
    */
    public void runAtomicAsUser(Runnable run) throws SourceException {
        getSourceImpl ().runAtomicAsUser(run);
    }

    /** Pluggable behaviour for source elements.
    * @see SourceElement
    */
    public static interface Impl extends Element.Impl {

        /** @deprecated Only public by accident. */
        /* public static final */ long serialVersionUID = -2181228658756563166L;

        /** Get the parsing status of the element.
         * This is a non-blocking operation.
         * @return one of {@link #STATUS_NOT}, {@link #STATUS_ERROR}, {@link #STATUS_PARTIAL}, or {@link #STATUS_OK}
         */
        public int getStatus();


        /** Begin parsing this source element.
         * This method is non-blocking; it only returns
         * a task that can be used to control the ongoing parse.
         * Initially the {@link #getStatus} should be {@link #STATUS_NOT}, and change
         * to one of the other three when parsing is complete, according to whether
         * or not errors were encountered, and their severity.
         *
         * @return a task to control the preparation of the element
         */
        public Task prepare ();

        /** Change the set of specs.
        * @param elems the specs to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
        public void changeSpecs (SpecElement[] elems, int action) throws SourceException;

        /** Get all specs.
        * @return the specs
        */
        public SpecElement[] getSpecs ();

        /** Find a spec by name.
        * @param name the name to look for
        * @return the spec, or <code>null</code> if it does not exist
        */
        public SpecElement getSpec (String name);

        /** Change the set of proofs.
        * @param elems the proofs to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
        public void changeProofs (ProofElement[] elems, int action) throws SourceException;

        /** Get all proofs.
        * @return the proofs
        */
        public ProofElement[] getProofs ();

        /** Find a proof by name.
        * @param name the name to look for
        * @return the proof, or <code>null</code> if it does not exist
        */
        public ProofElement getProof (String name);

        /** Change the set of specs.
        * @param elems the specs to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
        public void changeMorphisms (MorphismElement[] elems, int action) throws SourceException;

        /** Get all Morphisms.
        * @return the Morphisms
        */
        public MorphismElement[] getMorphisms ();

        /** Find a Morphism by name.
        * @param name the name to look for
        * @return the Morphism, or <code>null</code> if it does not exist
        */
        public MorphismElement getMorphism (String name);

        /** Change the set of diagrams.
        * @param elems the diagrams to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
        public void changeDiagrams (DiagramElement[] elems, int action) throws SourceException;

        /** Get all diagrams.
        * @return the diagrams
        */
        public DiagramElement[] getDiagrams ();

        /** Find a diagram by name.
        * @param name the name to look for
        * @return the diagram, or <code>null</code> if it does not exist
        */
        public DiagramElement getDiagram (String name);

        /** Change the set of colimits.
        * @param elems the colimits to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
        public void changeColimits (ColimitElement[] elems, int action) throws SourceException;

        /** Get all colimits.
        * @return the colimits
        */
        public ColimitElement[] getColimits ();

        /** Find a colimit by name.
        * @param name the name to look for
        * @return the colimit, or <code>null</code> if it does not exist
        */
        public ColimitElement getColimit (String name);

        /** Change the set of uids.
        * @param elems the uids to change
        * @param action one of {@link #ADD}, {@link #REMOVE}, or {@link #SET}
        * @exception SourceException if the action cannot be handled
        */
       // public void changeUIDs (UIDElement[] elems, int action) throws SourceException;

        /** Get all uids.
        * @return the uids
        */
        //public UIDElement[] getUIDs ();

        /** Find a unitId by path.
        * @param path the path to look for
        * @return the unitId, or <code>null</code> if it does not exist
        */
        //public UIDElement getUID (String path);

        /** Lock the underlaing document to have exclusive access to it and could make changes
        * on this SourceElement.
        *
        * @param run the action to run
        */
        public void runAtomic(Runnable run);

        /** Executes given runnable in "user mode" does not allowing any modifications
        * to parts of text marked as guarded. The actions should be run as "atomic" so
        * either happen all at once or none at all (if a guarded block should be modified).
        *
        * @param run the action to run
        * @exception SourceException if a modification of guarded text occured
        *   and that is why no changes to the document has been done.
        */
        public void runAtomicAsUser(Runnable run) throws SourceException;

	public void updateMemberOrder(Element[] orderedMembers);

    }

}
