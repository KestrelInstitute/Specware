/*
 * SourceText.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.7  2003/04/01 02:29:35  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.6  2003/03/29 03:13:54  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:12:31  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 17:59:38  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:12:14  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:37:44  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:45  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.lang.ref.*;
import java.io.IOException;
import java.util.*;

import javax.swing.text.BadLocationException;
import javax.swing.text.Position;
import javax.swing.text.StyledDocument;
import javax.swing.undo.UndoableEdit;

import org.openide.awt.UndoRedo;
import org.openide.text.CloneableEditorSupport;
import org.openide.text.NbDocument;
import org.openide.text.PositionBounds;
import org.openide.text.PositionRef;
import org.openide.ErrorManager;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.Util;

/**
 * Source is not, in fact, a Binding, but provides context to the editing operations.
 * It should manage locking, interactions with the outside environment and protection
 * management.<P>
 *
 */
public class SourceText implements DocumentBinding {
    /** True, if runAtomics should be, in fact, runAtomicAsUser.
     */
    int                     isAtomicAsUser;

    /** Support for editing documents.
     */
    CloneableEditorSupport  editSupport;
    
    /**
     * Undo manager to register undo events with.
     */
    Env                     environment;
    
    /**
     * Yes/no flag whether the whole generator is enabled. Parser updater, for example,
     * disables the code generator while it updates the source model, so the discovered
     * changes are not reflected back to the text.
     */
    boolean                 generatorEnabled;
    
    /**
     * An object used to lock tree of javax.swing.text.Elements or Bindings during
     * updates & reads.
     */
    Object                  treeLock;
    
    /**
     * Binding of the SourceElement, held by a WeakReference. Since the binding
     * is held exclusively by SourceElement.Impl implementation, it may be freed along
     * with the implementation (or according to the implementation memory policy).
     */
    Reference               refSourceRoot;

    Map                     bindingMap;
    
    
    public SourceText(Env sourceEnvironment) {
        this.environment = sourceEnvironment;
        treeLock = new Object();
    }
    
    public Element getElement() {
        return null;
    }
    
    protected SourceB getRoot() {
        synchronized (this) {
            if (refSourceRoot == null)
                return null;
            Object r = refSourceRoot.get();
            if (r == null) 
                refSourceRoot = null;
            return (SourceB)r;
        }            
    }
    
    public CloneableEditorSupport getEditorSupport() {
        if (editSupport == null)
            editSupport = environment.findEditorSupport();
        return editSupport;
    }
    
    protected synchronized void registerBinding(Element el, ElementBinding b) {
        if (bindingMap == null) {
            bindingMap = new WeakHashMap(37);
        }
        bindingMap.put(el, new WeakReference(b));
    }

    /**
     * Enters or leaves user-mode of document editing. If the document contains
     * some user-protected text, all changes to the text will be disallowed in
     * the user mode.
     */
    public void enableAtomicAsUser(boolean enable) {
        if (enable)
            isAtomicAsUser++;
        else
            isAtomicAsUser--;
    }
    
    public void enableGenerator(boolean enable) {
        generatorEnabled = enable;
    }
    
    public boolean isGeneratorEnabled() {
        return generatorEnabled;
    }
    
    
    /**
     * Retrieves a document for the I/O operations. The method can throw
     * IOException wrapped into a SourceException, if the operation fails.
     */
    public StyledDocument getDocument() throws SourceException {
        try {
            return getEditorSupport().openDocument();
        } catch (IOException ex) {
            rethrowException(ex);
        }
        return null;
    }
    
    public Element findElement(int position) {
        SourceB sb = getRoot();
        if (sb == null)
            return null;
        synchronized (getTreeLock()) {
            ElementBinding b = sb.findBindingAt(position);
            if (b == null)
                return null;
            return b.getElement();
        }
    }
    
    public boolean isAtomicAsUser() {
        return this.isAtomicAsUser > 0;
    }
    
    public void runAtomic(final Runnable r) throws SourceException {
        runAtomic(null, r);
    }
    
    private void runAtomic(Element el, final Runnable r) throws SourceException {
       final Exception[] exc = new Exception[1];
       try {
           if (isAtomicAsUser()) {
               NbDocument.runAtomicAsUser(getDocument(), r);
           } else {
               NbDocument.runAtomic(getDocument(), r);
           }
       } catch (RuntimeException ex) {
           throw ex;
       } catch (Exception ex) {
           exc[0] = ex;
       }
       rethrowException(el, exc[0]);
    }
    
    public void updateBindings(Runnable r) {
        synchronized (getTreeLock()) {
            r.run();
        }
    }
    
    protected Object getTreeLock() {
        return treeLock;
    }

    protected static void rethrowException(Exception ex) throws SourceException {
        rethrowException(null, ex);
    }
    
    protected static void rethrowException(Element el, Exception ex) throws SourceException {
        if (ex == null)
            return;

        ErrorManager man = ErrorManager.getDefault();
        SourceException x;
        
        if (ex instanceof IOException) {
           x =  new SourceException.IO((IOException)ex);
           man.annotate(x, ex);
        } else if (ex instanceof SourceException) {
           x = (SourceException)ex;
        } else {
           // PENDING: annotate the exception with the old one!
           x = new SourceException();
           man.annotate(x, ex);
        }
        throw x;
    }
    
    public void runAtomic(Element el, final ExceptionRunnable r) throws SourceException {
        final Exception[] exc = new Exception[1];
        Runnable r2 = new Runnable() {
            public void run() {
                //environment.notifyBeginEdit();
                try {
                    r.run();
                } catch (Exception ex) {
                    exc[0] = ex;
                    Util.log("SourceText.runAtomic Runnable r2 IllegalState Exception thrown "+ex);
                    throw new IllegalStateException();
                } finally {
                    //environment.notifyEndEdit();
                }
            }
       };
       StyledDocument doc = getDocument();
       if (isAtomicAsUser()) {
           try {
                NbDocument.runAtomicAsUser(doc, r2);
           } catch (BadLocationException ex) {
               exc[0] = ex;
           } catch (IllegalStateException ex) {
           }
       } else {
           try {
                NbDocument.runAtomic(doc, r2);
           } catch (IllegalStateException ex) {
               // swallow - rethrow the runnable's exception instead.
           }
       }
       rethrowException(el, exc[0]);
    }
    
    protected PositionRef createPos(int offset, Position.Bias bias) {
        return getEditorSupport().createPositionRef(offset, bias);
    }
    
    protected synchronized ElementBinding findBinding(Element e) {
        if (bindingMap == null)
            return null;
        Reference r = (Reference)bindingMap.get(e);
        if (r == null)
            return null;
        return (ElementBinding)r.get();
    }
    
    protected boolean canWriteInside(PositionBounds bounds) {
        return environment.findFreePosition(bounds) != null;
    }
    
    protected PositionRef findFreePosition(PositionBounds bounds) {
        return environment.findFreePosition(bounds);
    }

    public Binding.Source bindSource(SourceElement impl) {
        SourceB b = new SourceB(impl, this);
        this.refSourceRoot = new WeakReference(b);
        return b;
    }
    
    public Binding.Spec bindSpec(SpecElement impl) {
        SpecB b = new SpecB(impl, this);
        return b;
    }
    
    public Binding.Sort bindSort(SortElement impl) {
        SortB b = new SortB(impl, this);
        return b;
    }
    
    public Binding.Op bindOp(OpElement impl) {
        OpB b = new OpB(impl, this);
        return b;
    }
    
    public Binding.Def bindDef(DefElement impl) {
        DefB b = new DefB(impl, this);
        return b;
    }
    
    public Binding.Claim bindClaim(ClaimElement impl) {
        ClaimB b = new ClaimB(impl, this);
        return b;
    }

    public Binding.Import bindImport(ImportElement impl) {
        ImportB b = new ImportB(impl, this);
        return b;
    }
    
    public Binding.Proof bindProof(ProofElement impl) {
        ProofB b = new ProofB(impl, this);
        return b;
    }

    public Binding.Morphism bindMorphism(MorphismElement impl) {
        MorphismB b = new MorphismB(impl, this);
        return b;
    }
    
    public Binding.DiagElem bindDiagElem(DiagElemElement impl) {
        DiagElemB b = new DiagElemB(impl, this);
        return b;
    }

    public Binding.Diagram bindDiagram(DiagramElement impl) {
        DiagramB b = new DiagramB(impl, this);
        return b;
    }

    public Binding.Colimit bindColimit(ColimitElement impl) {
        ColimitB b = new ColimitB(impl, this);
        return b;
    }
    
/*    public Binding.URI bindURI(URIElement impl) {
        URIB b = new URIB(impl, this);
        return b;
    }   
*/
    public void dumpDocument() {
        System.err.println("Document dump:"); // NOI18N
        final StyledDocument doc = getEditorSupport().getDocument();
        doc.render(new Runnable() {
            public void run() {
                try {
                    String s = doc.getText(0, doc.getLength());
                    System.err.println(s);
                } catch (Exception ex) {
                }
            }
        });
    }
}
