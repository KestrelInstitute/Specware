/*
 * SourceEditSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.7  2003/03/29 03:13:59  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:14:22  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:06:42  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:33:56  weilyn
 * Created claim customizer.
 *
 * Revision 1.3  2003/02/16 02:15:04  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:42:09  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:12  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;


import java.awt.Component;
import java.awt.datatransfer.Transferable;
import java.beans.*;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.*;

import org.openide.*;
import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.filesystems.FileObject;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataFolder;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;
import org.openide.util.datatransfer.NewType;
import org.openide.util.datatransfer.PasteType;
import org.openide.util.datatransfer.ExTransferable;

import edu.kestrel.netbeans.MetaSlangDataLoader;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.cookies.SourceCookie;

/** This class defines utilities for editing source using hierarchy API,
 * e.g. creation new types for spec elements, runAtomicAsUser support, ...
 *
 */
class SourceEditSupport {

    static final ResourceBundle bundle = NbBundle.getBundle(SourceEditSupport.class);

    static final String[] SPEC_MENU_NAMES = {
        bundle.getString("MENU_CREATE_IMPORT"),
	bundle.getString("MENU_CREATE_SORT"),
	bundle.getString("MENU_CREATE_OP"),
	bundle.getString("MENU_CREATE_DEF"),
        bundle.getString("MENU_CREATE_CLAIM")
    };

    static final String[] PROOF_MENU_NAMES = {
    
    };
        
    static final String[] MORPHISM_MENU_NAMES = {
    
    };
    
    static final String[] DIAGRAM_MENU_NAMES = {
    
    };
    
    static final String[] COLIMIT_MENU_NAMES = {
    
    };    

    /* Get the new types that can be created in this node.
     * For example, a node representing a Java package will permit classes to be added.
     * @return array of new type operations that are allowed
     */
    public static NewType[] createNewTypes(SpecElement element) {
	return new NewType[] {
	    new SpecElementNewType(element, (byte) 0),
            new SpecElementNewType(element, (byte) 1),
            new SpecElementNewType(element, (byte) 2),
            new SpecElementNewType(element, (byte) 3),
            new SpecElementNewType(element, (byte) 4),
        };
    }

    /* Get the new types that can be created in this node.
     * For example, a node representing a Java package will permit classes to be added.
     * @return array of new type operations that are allowed
     */
    public static NewType[] createNewTypes(ProofElement element) {
	return new NewType[] {
/*	    new SpecElementNewType(element, (byte) 0),
            new SpecElementNewType(element, (byte) 1),
            new SpecElementNewType(element, (byte) 2),
            new SpecElementNewType(element, (byte) 3),
            new SpecElementNewType(element, (byte) 4),*/
        };
    }
    
    /* Get the new types that can be created in this node.
     * For example, a node representing a Java package will permit classes to be added.
     * @return array of new type operations that are allowed
     */
    public static NewType[] createNewTypes(MorphismElement element) {
	return new NewType[] {
/*	    new SpecElementNewType(element, (byte) 0),
            new SpecElementNewType(element, (byte) 1),
            new SpecElementNewType(element, (byte) 2),
            new SpecElementNewType(element, (byte) 3),
            new SpecElementNewType(element, (byte) 4),*/
        };
    }

    /* Get the new types that can be created in this node.
     * For example, a node representing a Java package will permit classes to be added.
     * @return array of new type operations that are allowed
     */
    public static NewType[] createNewTypes(DiagramElement element) {
	return new NewType[] {
/*	    new SpecElementNewType(element, (byte) 0),
            new SpecElementNewType(element, (byte) 1),
            new SpecElementNewType(element, (byte) 2),
            new SpecElementNewType(element, (byte) 3),
            new SpecElementNewType(element, (byte) 4),*/
        };
    }

    /* Get the new types that can be created in this node.
     * For example, a node representing a Java package will permit classes to be added.
     * @return array of new type operations that are allowed
     */
    public static NewType[] createNewTypes(ColimitElement element) {
	return new NewType[] {
/*	    new SpecElementNewType(element, (byte) 0),
            new SpecElementNewType(element, (byte) 1),
            new SpecElementNewType(element, (byte) 2),
            new SpecElementNewType(element, (byte) 3),
            new SpecElementNewType(element, (byte) 4),*/
        };
    }
    
    /** New types for spec element */
    static class SpecElementNewType extends NewType {
	/** Spec element where to create new element */
	SpecElement element;

	/** The kind of element to create */
	byte kind;
        
	/** Creates new type
	 * @param element Where to create new element.
	 * @param kind The kind of the element to create
	 */
	public SpecElementNewType(SpecElement element, byte kind) {
	    this.element = element;
	    this.kind = kind;
	}

	/** Get the name of the new type.
	 * @return localized name.
	 */
	public String getName() {
	    return SPEC_MENU_NAMES[kind];
	}

	/** Help context */
	public org.openide.util.HelpCtx getHelpCtx() {
	    return new org.openide.util.HelpCtx (SourceEditSupport.class.getName () + ".newElement" + kind); // NOI18N
	}

	/** Creates new element */
	public void create () throws IOException {
	    final String name = element.getName();

	    Element newElement = null;

	    try {
		switch (kind) {
		case 0:
		    {
			// Adding import
			ImportElement e = new ImportElement();
			e.setName("<name of unit to import>");
			MemberCustomizer cust = new MemberCustomizer(e, "Import");
			if (openCustomizer(cust, "TIT_NewImport") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 1:
		    {
			// Adding sort
			SortElement e = new SortElement();
			e.setName("newSort");
			MemberCustomizer cust = new MemberCustomizer(e, "Sort");
			if (openCustomizer(cust, "TIT_NewSort") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 2:
		    {
			// Adding op
			OpElement e = new OpElement();
			e.setName("newOp"); // NOI18N
			OpCustomizer cust = new OpCustomizer(e);
			if (openCustomizer(cust, "TIT_NewOp") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 3:
		    {
			// Adding def
			DefElement e = new DefElement();
			e.setName("newDef");
			DefCustomizer cust = new DefCustomizer(e);
			if (openCustomizer(cust, "TIT_NewDef") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 4:
		    {
			// Adding claim
			ClaimElement e = new ClaimElement();
			e.setName("newClaim"); // NOI18N
                        ClaimCustomizer cust = new ClaimCustomizer(e);
			if (openCustomizer(cust, "TIT_NewClaim") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		}
                
	    }
	    catch (SourceException exc) {
		// shouldn't happen - memory implementation
		// is not based on java source.
	    }

	    if (newElement == null)
		return;

	    final Element addingElement = newElement;
	    SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			switch (kind) {
			case 0:
			    ((SpecElement)element).addImport((ImportElement)addingElement);
			    return;
			case 1:
			    ((SpecElement)element).addSort((SortElement)addingElement);
			    return;
			case 2:
			    ((SpecElement)element).addOp((OpElement)addingElement);
			    return;
			case 3:
			    ((SpecElement)element).addDef((DefElement)addingElement);
			    return;
			case 4:
			    ((SpecElement)element).addClaim((ClaimElement)addingElement);
			    return;
			}
                        
		    }
		});
	}
	}

    /** New types for proof element */
    static class ProofElementNewType extends NewType {
	/** Proof element where to create new element */
        ProofElement element;

	/** The kind of element to create */
	byte kind;
        
	/** Creates new type
	 * @param element Where to create new element.
	 * @param kind The kind of the element to create
	 */
	public ProofElementNewType(ProofElement element, byte kind) {
	    this.element = element;
	    this.kind = kind;
	}

	/** Get the name of the new type.
	 * @return localized name.
	 */
	public String getName() {
	    return PROOF_MENU_NAMES[kind];
	}

	/** Help context */
	public org.openide.util.HelpCtx getHelpCtx() {
	    return new org.openide.util.HelpCtx (SourceEditSupport.class.getName () + ".newElement" + kind); // NOI18N
	}

	/** Creates new element */
	public void create () throws IOException {
	    final String name = element.getName();

	    Element newElement = null;

/*	    try {
		switch (kind) {
		case 0:
		    {
			// Adding import
			ImportElement e = new ImportElement();
			e.setName("<name of unit to import>");
			MemberCustomizer cust = new MemberCustomizer(e, "Import");
			if (openCustomizer(cust, "TIT_NewImport") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		}
                
	    }
	    catch (SourceException exc) {
		// shouldn't happen - memory implementation
		// is not based on java source.
	    }*/

	    if (newElement == null)
		return;

	    final Element addingElement = newElement;
	    SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			switch (kind) {
/*			case 0:
			    ((SpecElement)element).addImport((ImportElement)addingElement);
			    return;*/
			}
                        
		    }
		});
	}
	}
    
    /** New types for morphism element */
    static class MorphismElementNewType extends NewType {
	/** Morphism element where to create new element */
        MorphismElement element;

	/** The kind of element to create */
	byte kind;
        
	/** Creates new type
	 * @param element Where to create new element.
	 * @param kind The kind of the element to create
	 */
	public MorphismElementNewType(MorphismElement element, byte kind) {
	    this.element = element;
	    this.kind = kind;
	}

	/** Get the name of the new type.
	 * @return localized name.
	 */
	public String getName() {
	    return MORPHISM_MENU_NAMES[kind];
	}

	/** Help context */
	public org.openide.util.HelpCtx getHelpCtx() {
	    return new org.openide.util.HelpCtx (SourceEditSupport.class.getName () + ".newElement" + kind); // NOI18N
	}

	/** Creates new element */
	public void create () throws IOException {
	    final String name = element.getName();

	    Element newElement = null;

/*	    try {
		switch (kind) {
		case 0:
		    {
			// Adding import
			ImportElement e = new ImportElement();
			e.setName("<name of unit to import>");
			MemberCustomizer cust = new MemberCustomizer(e, "Import");
			if (openCustomizer(cust, "TIT_NewImport") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		}
                
	    }
	    catch (SourceException exc) {
		// shouldn't happen - memory implementation
		// is not based on java source.
	    }*/

	    if (newElement == null)
		return;

	    final Element addingElement = newElement;
	    SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			switch (kind) {
/*			case 0:
			    ((SpecElement)element).addImport((ImportElement)addingElement);
			    return;*/
			}
                        
		    }
		});
	}
	}

    /** New types for diagram element */
    static class DiagramElementNewType extends NewType {
	/** Diagram element where to create new element */
        DiagramElement element;

	/** The kind of element to create */
	byte kind;
        
	/** Creates new type
	 * @param element Where to create new element.
	 * @param kind The kind of the element to create
	 */
	public DiagramElementNewType(DiagramElement element, byte kind) {
	    this.element = element;
	    this.kind = kind;
	}

	/** Get the name of the new type.
	 * @return localized name.
	 */
	public String getName() {
	    return PROOF_MENU_NAMES[kind];
	}

	/** Help context */
	public org.openide.util.HelpCtx getHelpCtx() {
	    return new org.openide.util.HelpCtx (SourceEditSupport.class.getName () + ".newElement" + kind); // NOI18N
	}

	/** Creates new element */
	public void create () throws IOException {
	    final String name = element.getName();

	    Element newElement = null;

/*	    try {
		switch (kind) {
		case 0:
		    {
			// Adding import
			ImportElement e = new ImportElement();
			e.setName("<name of unit to import>");
			MemberCustomizer cust = new MemberCustomizer(e, "Import");
			if (openCustomizer(cust, "TIT_NewImport") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		}
                
	    }
	    catch (SourceException exc) {
		// shouldn't happen - memory implementation
		// is not based on java source.
	    }*/

	    if (newElement == null)
		return;

	    final Element addingElement = newElement;
	    SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			switch (kind) {
/*			case 0:
			    ((SpecElement)element).addImport((ImportElement)addingElement);
			    return;*/
			}
                        
		    }
		});
	}
	}

    /** New types for colimit element */
    static class ColimitElementNewType extends NewType {
	/** Colimit element where to create new element */
        ColimitElement element;

	/** The kind of element to create */
	byte kind;
        
	/** Creates new type
	 * @param element Where to create new element.
	 * @param kind The kind of the element to create
	 */
	public ColimitElementNewType(ColimitElement element, byte kind) {
	    this.element = element;
	    this.kind = kind;
	}

	/** Get the name of the new type.
	 * @return localized name.
	 */
	public String getName() {
	    return COLIMIT_MENU_NAMES[kind];
	}

	/** Help context */
	public org.openide.util.HelpCtx getHelpCtx() {
	    return new org.openide.util.HelpCtx (SourceEditSupport.class.getName () + ".newElement" + kind); // NOI18N
	}

	/** Creates new element */
	public void create () throws IOException {
	    final String name = element.getName();

	    Element newElement = null;

/*	    try {
		switch (kind) {
		case 0:
		    {
			// Adding import
			ImportElement e = new ImportElement();
			e.setName("<name of unit to import>");
			MemberCustomizer cust = new MemberCustomizer(e, "Import");
			if (openCustomizer(cust, "TIT_NewImport") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		}
                
	    }
	    catch (SourceException exc) {
		// shouldn't happen - memory implementation
		// is not based on java source.
	    }*/

	    if (newElement == null)
		return;

	    final Element addingElement = newElement;
	    SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			switch (kind) {
/*			case 0:
			    ((SpecElement)element).addImport((ImportElement)addingElement);
			    return;*/
			}
                        
		    }
		});
	}
	}

    /** Show dialog and allow user to modify new element.
     * @param customizer The component to be displayed
     * @param titleKey the key to resource bundle for the title of dialog
     * @return <CODE>true</CODE> if user pressed OK button,
     *     otherwise <CODE>false</CODE> (for CANCEL)
     */
    static boolean openCustomizer(Component customizer, String titleKey) {
	NotifyDescriptor desriptor = new NotifyDescriptor(
							  customizer,
							  ElementNode.bundle.getString(titleKey),
							  NotifyDescriptor.OK_CANCEL_OPTION,
							  NotifyDescriptor.PLAIN_MESSAGE,
							  null, null);

	Object ret = TopManager.getDefault().notify(desriptor);
	return (ret == NotifyDescriptor.OK_OPTION);
    }

    /** Invokes the runnable using SourceElement.runAtomicAsUser, if it can find
     * a source element for the given hierarchy element. If the SourceElement can't
     * be found, the runnable is executed without any protection.
     * @exception IOException If SourceException occured inside the runnable.
     */
    static void invokeAtomicAsUser(Element element, final ExceptionalRunnable exRun) throws IOException {
	final SourceException[] ex = { null };
	try {
	    SourceElement source = SourceEditSupport.findSource(element);
	    if (source == null) {
		exRun.run();
	    } else {
		Runnable run = new Runnable() {
			public void run() {
			    try {
				exRun.run();
			    }
			    catch (SourceException e) {
				ex[0] = e;
			    }
			}
		    };
		source.runAtomicAsUser(run);
	    }
	}
	catch (SourceException e) {
	    ex[0] = e;
	}
	if (ex[0] != null) {
	    if (Boolean.getBoolean("netbeans.debug.exceptions")) // NOI18N
		ex[0].printStackTrace();
	    IOException x = new IOException(ex[0].getMessage());
	    // #9512 -- this exception is expected, so lower its priority to "user".
	    ErrorManager.getDefault().annotate(x, 
					       ErrorManager.USER, null, null, ex[0], null);
	    throw x;
	}
    }
    
    static void runAsUser(Element ref, final ExceptionalRunnable exRun) throws SourceException {
	final SourceException ex[] = { null };
	SourceElement src = findSource(ref);
	if (src == null) {
	    exRun.run();
	} else {
	    src.runAtomicAsUser(new Runnable() {
		    public void run() {
			try {
			    exRun.run();
			} catch (SourceException e) {
			    ex[0] = e;
			}
		    }
		});
	}
	if (ex[0] != null) 
	    throw ex[0];
    }

    /** This interface is used like runnable, but its method run
     * could throw BadLocationException.
     * @exception SourceException
     */
    static interface ExceptionalRunnable {
	public void run() throws SourceException;
    }

    static boolean isWriteable(Element element) {
	SourceElement el = findSource(element);
	DataObject d = el == null ? null : (DataObject)el.getCookie(DataObject.class);
	if (d == null) {
	    return true;
	}
	return !d.getPrimaryFile().isReadOnly();
    }

    /** Find the source for the specifier element. 
     * @return instance of SourceElement or null, if the source can't be found.
     */
    static SourceElement findSource(Element element) {
	if (element instanceof SourceElement) {
	    return (SourceElement) element;
        }
	if (element instanceof SpecElement) {
	    SpecElement mm = (SpecElement) element;
	    SourceElement source = mm.getSource();
	    if (source != null) {
		return source;
	    } else {
		return findSource(mm.getParent());
	    }
	}
        if (element instanceof DiagramElement) {
            DiagramElement mm = (DiagramElement) element;
 	    SourceElement source = mm.getSource();
	    if (source != null) {
		return source;
	    } else {
		return findSource(mm.getParent());
	    }           
        }
        if (element instanceof MorphismElement) {
            MorphismElement mm = (MorphismElement) element;
 	    SourceElement source = mm.getSource();
	    if (source != null) {
		return source;
	    } else {
		return findSource(mm.getParent());
	    }           
        }
        if (element instanceof MemberElement) {
	    return findSource(((MemberElement) element).getParent());
	}
	return null;
    }
    
    static void createMetaSlangFile(MemberElement elem, FileObject target) throws SourceException, IOException {
	DataObject targetObject;
	String name = elem.getName();
	FileObject newFile;
	String newName;
        
	newName = org.openide.filesystems.FileUtil.findFreeFileName(target, name, MetaSlangDataLoader.META_SLANG_EXTENSION); // NOI18N
	newFile = target.createData(name, MetaSlangDataLoader.META_SLANG_EXTENSION); // NOI18N
	SourceElement newSrc;
	SourceCookie cookie;
	try {
	    targetObject = DataObject.find(newFile);
	} catch (org.openide.loaders.DataObjectNotFoundException e) {
	    throw (IOException)ErrorManager.getDefault().annotate(
								  new IOException(e.getMessage()), 
								  ErrorManager.EXCEPTION, "Data object can't be created", // NOI18N
								  bundle.getString("EXC_CREATE_SOURCE_FILE"),
								  e, null
								  );
	}
	cookie = (SourceCookie)targetObject.getCookie(SourceCookie.class);
	if (cookie == null) {
	    // perhaps meta-slang sources not installed ?
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Source element cannot be found"), // NOI18N
								      bundle.getString("EXC_CREATE_SOURCE_FILE")
								      );
	}
        if (elem instanceof SpecElement) {
            cookie.getSource().addSpec((SpecElement)elem);
        } else if (elem instanceof DiagramElement) {
            cookie.getSource().addDiagram((DiagramElement)elem);
        } else if (elem instanceof MorphismElement) {
            cookie.getSource().addMorphism((MorphismElement)elem);
        }
	
    }
    
    static void removeSpec(SpecElement spec) throws SourceException {
	SourceElement src = SourceEditSupport.findSource(spec);
	if (src == null) {
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Element has no source"), // NOI18N
								      bundle.getString("EXC_NO_SOURCE")
								      );
	}
	src.removeSpec(spec);
    }

    static void removeProof(ProofElement proof) throws SourceException {
	SourceElement src = SourceEditSupport.findSource(proof);
	if (src == null) {
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Element has no source"), // NOI18N
								      bundle.getString("EXC_NO_SOURCE")
								      );
	}
	src.removeProof(proof);
    }
    
    static void removeMorphism(MorphismElement morphism) throws SourceException {
	SourceElement src = SourceEditSupport.findSource(morphism);
	if (src == null) {
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Element has no source"), // NOI18N
								      bundle.getString("EXC_NO_SOURCE")
								      );
	}
	src.removeMorphism(morphism);
    }

    static void removeDiagram(DiagramElement diagram) throws SourceException {
	SourceElement src = SourceEditSupport.findSource(diagram);
	if (src == null) {
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Element has no source"), // NOI18N
								      bundle.getString("EXC_NO_SOURCE")
								      );
	}
	src.removeDiagram(diagram);
    }

    static void removeColimit(ColimitElement colimit) throws SourceException {
	SourceElement src = SourceEditSupport.findSource(colimit);
	if (src == null) {
	    throw (SourceException)ErrorManager.getDefault().annotate(
								      new SourceException("Element has no source"), // NOI18N
								      bundle.getString("EXC_NO_SOURCE")
								      );
	}
	src.removeColimit(colimit);
    }

    /* default */static class PackagePaste implements NodeTransfer.Paste {
	private static PasteType[] EMPTY_TYPES = new PasteType[0];                         
	/** True, if the paste should remove the original class element.
	 */
	private boolean deleteSelf;

	/** Spec element to paste.
	 */        
	//private SpecElement element;
        
        private MemberElement element;
        
	PackagePaste(SpecElement element, boolean deleteSelf) {
	    this.deleteSelf = deleteSelf;
	    this.element = element;
	}
        
        PackagePaste(ProofElement element, boolean deleteSelf) {
	    this.deleteSelf = deleteSelf;
	    this.element = element;
	}
        
        PackagePaste(MorphismElement element, boolean deleteSelf) {
	    this.deleteSelf = deleteSelf;
	    this.element = element;
	}

        PackagePaste(DiagramElement element, boolean deleteSelf) {
	    this.deleteSelf = deleteSelf;
	    this.element = element;
	}
        
        PackagePaste(ColimitElement element, boolean deleteSelf) {
	    this.deleteSelf = deleteSelf;
	    this.element = element;
	}

        public PasteType[] types(Node target) {
	    DataObject obj = (DataObject)target.getCookie(DataObject.class);
	    if (element == null || obj == null) 
		return EMPTY_TYPES;
	    FileObject fob = obj.getPrimaryFile();
	    if (!fob.isFolder()) {
		return EMPTY_TYPES;
	    }
	    return new PasteType[] {
		new Type(fob)
		    };
	}

	private class Type extends PasteType {
	    /** Target file folder
	     */
	    private FileObject target;

	    Type(FileObject target) {
		this.target = target;
	    }

	    public String getName() {
		return bundle.getString("MENU_PASTE_AS_FILE");
	    }

	    public org.openide.util.HelpCtx getHelpCtx() {
		return super.getHelpCtx();
	    }

	    public Transferable paste() throws IOException {
		final MemberElement elem = PackagePaste.this.element;
		final boolean del = PackagePaste.this.deleteSelf;

		try {                
		    createMetaSlangFile(elem, target);
		} catch (SourceException ex) {
		    IOException x = new IOException(ex.getMessage());
		    ErrorManager.getDefault().annotate(x, ex);
		    throw x;
		}
		if (del) {
		    final SourceException ex[] = { null };
		    SourceEditSupport.invokeAtomicAsUser(elem, new SourceEditSupport.ExceptionalRunnable() {
			    public void run() throws SourceException {
				try {
                                    if (elem instanceof SpecElement) {
                                        removeSpec((SpecElement)elem);
                                    } else if (elem instanceof ProofElement) {
                                        removeProof((ProofElement)elem);
                                    } else if (elem instanceof MorphismElement) {
                                        removeMorphism((MorphismElement)elem);
                                    } else if (elem instanceof DiagramElement) {
                                        removeDiagram((DiagramElement)elem);
                                    } else if (elem instanceof ColimitElement) {
                                        removeColimit((ColimitElement)elem);
                                    }
 				} catch (SourceException e) {
				    ex[0] = e;
				} 
			    }
			});
		    if (ex[0] != null) {
			IOException x = new IOException(ex[0].getMessage());
			ErrorManager.getDefault().annotate(x, ex[0]);
			throw x;
		    }
		    PackagePaste.this.element = null;
		    return ExTransferable.EMPTY;
		} else {
		    return null;
		}
	    }
	}
    }
    
    static class SpecMultiPasteType extends PasteType {
	SpecElementNode target;
	Collection members;
	boolean delete;

	SpecMultiPasteType(SpecElementNode target, Collection members, boolean delete) {
	    this.target = target;
	    this.members = members;
	    this.delete = delete;
	}

	public Transferable paste() throws IOException {
	    for (Iterator it = members.iterator(); it.hasNext(); ) {
		target.pasteElement((Element)it.next(), delete);
	    }
	    if (delete) 
		return ExTransferable.EMPTY;
	    else
		return null;
	}
    }

    static class ProofMultiPasteType extends PasteType {
	ProofElementNode target;
	Collection members;
	boolean delete;

	ProofMultiPasteType(ProofElementNode target, Collection members, boolean delete) {
	    this.target = target;
	    this.members = members;
	    this.delete = delete;
	}

	public Transferable paste() throws IOException {
	    for (Iterator it = members.iterator(); it.hasNext(); ) {
		target.pasteElement((Element)it.next(), delete);
	    }
	    if (delete) 
		return ExTransferable.EMPTY;
	    else
		return null;
	}
    }    

    static class MorphismMultiPasteType extends PasteType {
	MorphismElementNode target;
	Collection members;
	boolean delete;

	MorphismMultiPasteType(MorphismElementNode target, Collection members, boolean delete) {
	    this.target = target;
	    this.members = members;
	    this.delete = delete;
	}

	public Transferable paste() throws IOException {
	    for (Iterator it = members.iterator(); it.hasNext(); ) {
		target.pasteElement((Element)it.next(), delete);
	    }
	    if (delete) 
		return ExTransferable.EMPTY;
	    else
		return null;
	}
    }    

    static class DiagramMultiPasteType extends PasteType {
	DiagramElementNode target;
	Collection members;
	boolean delete;

	DiagramMultiPasteType(DiagramElementNode target, Collection members, boolean delete) {
	    this.target = target;
	    this.members = members;
	    this.delete = delete;
	}

	public Transferable paste() throws IOException {
	    for (Iterator it = members.iterator(); it.hasNext(); ) {
		target.pasteElement((Element)it.next(), delete);
	    }
	    if (delete) 
		return ExTransferable.EMPTY;
	    else
		return null;
	}
    }    

    static class ColimitMultiPasteType extends PasteType {
	ColimitElementNode target;
	Collection members;
	boolean delete;

	ColimitMultiPasteType(ColimitElementNode target, Collection members, boolean delete) {
	    this.target = target;
	    this.members = members;
	    this.delete = delete;
	}

	public Transferable paste() throws IOException {
	    for (Iterator it = members.iterator(); it.hasNext(); ) {
		target.pasteElement((Element)it.next(), delete);
	    }
	    if (delete) 
		return ExTransferable.EMPTY;
	    else
		return null;
	}
    }    
    
}
