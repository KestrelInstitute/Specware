/*
 * SourceEditSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
	bundle.getString("MENU_CREATE_SORT"),
	bundle.getString("MENU_CREATE_OP"),
	bundle.getString("MENU_CREATE_DEF"),
        bundle.getString("MENU_CREATE_CLAIM")
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
            new SpecElementNewType(element, (byte) 3)
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
			// Adding sort
			SortElement e = new SortElement();
			e.setName("newSort");
			MemberCustomizer cust = new MemberCustomizer(e, "Sort");
			if (openCustomizer(cust, "TIT_NewSort") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 1:
		    {
			// Adding op
			OpElement e = new OpElement();
			e.setName("newOp"); // NOI18N
			OpCustomizer cust = new OpCustomizer(e);
			if (openCustomizer(cust, "TIT_NewOp") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 2:
		    {
			// Adding def
			DefElement e = new DefElement();
			e.setName("newDef");
			DefCustomizer cust = new DefCustomizer(e);
			if (openCustomizer(cust, "TIT_NewDef") && cust.isOK()) // NOI18N
			    newElement = e;
			break;
		    }
		case 3:
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
			    ((SpecElement)element).addSort((SortElement)addingElement);
			    return;
			case 1:
			    ((SpecElement)element).addOp((OpElement)addingElement);
			    return;
			case 2:
			    ((SpecElement)element).addDef((DefElement)addingElement);
			    return;
			case 3:
			    ((SpecElement)element).addClaim((ClaimElement)addingElement);
			    return;
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
	if (element instanceof MemberElement) {
	    return findSource(((MemberElement) element).getParent());
	}
	return null;
    }
    
    static void createMetaSlangFile(SpecElement spec, FileObject target) throws SourceException, IOException {
	DataObject targetObject;
	String name = spec.getName();
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
	cookie.getSource().addSpec(spec);
	
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

    /* default */static class PackagePaste implements NodeTransfer.Paste {
	private static PasteType[] EMPTY_TYPES = new PasteType[0];                         
	/** True, if the paste should remove the original class element.
	 */
	private boolean deleteSelf;

	/** Spec element to paste.
	 */        
	private SpecElement element;
        
	PackagePaste(SpecElement element, boolean deleteSelf) {
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
		final SpecElement spec = PackagePaste.this.element;
		final boolean del = PackagePaste.this.deleteSelf;

		try {                
		    createMetaSlangFile(spec, target);
		} catch (SourceException ex) {
		    IOException x = new IOException(ex.getMessage());
		    ErrorManager.getDefault().annotate(x, ex);
		    throw x;
		}
		if (del) {
		    final SourceException ex[] = { null };
		    SourceEditSupport.invokeAtomicAsUser(spec, new SourceEditSupport.ExceptionalRunnable() {
			    public void run() throws SourceException {
				try {
				    removeSpec(spec);
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

}
