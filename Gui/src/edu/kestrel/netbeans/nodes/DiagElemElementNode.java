package edu.kestrel.netbeans.nodes;

import java.awt.Component;
import java.beans.*;
import java.io.IOException;
import java.lang.reflect.Modifier;
import java.lang.reflect.InvocationTargetException;
import java.util.ResourceBundle;

import org.openide.TopManager;
import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.ElementFormat;

/**
 *
 * @author  weilyn
 */
public class DiagElemElementNode extends MemberElementNode {
    /** Create a new diagElem node.
    * @param element diagElem element to represent
    * @param writeable <code>true</code> to be writable
    */
    public DiagElemElementNode(DiagElemElement element, boolean writeable) {
        super(element, Children.LEAF, writeable);
        setElementFormat0(sourceOptions.getDiagElemElementFormat());
    }

    public org.openide.util.HelpCtx getHelpCtx () {
        return new org.openide.util.HelpCtx ("org.openide.src.nodes.DiagElemNode"); // NOI18N
    }

    /* Resolve the current icon base.
    * @return icon base string.
    */
    protected String resolveIconBase() {
	return DIAG_ELEM;
    }

    /* This method resolve the appropriate hint format for the type
    * of the element. It defines the short description.
    */
    protected ElementFormat getHintElementFormat() {
        return sourceOptions.getDiagElemElementLongFormat();
    }

    /* Creates property set for this node */
    protected Sheet createSheet () {
        Sheet sheet = Sheet.createDefault();
        Sheet.Set ps = sheet.get(Sheet.PROPERTIES);
        ps.put(createNameProperty(isWriteable()));
        //ps.put(createCategoryProperty(isWriteable()));
        return sheet;
    }

    /* Removes the element from the class and calls superclass.
    *
    * @exception IOException if SourceException is thrown
    *            from the underlayed Element.
    */
    public void destroy() throws IOException {
        SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
                                                 public void run() throws SourceException {
                                                     DiagElemElement el = (DiagElemElement) element;
                                                     ((DiagramElement) el.getParent()).removeDiagElem(el);
                                                 }
                                             });
        super.destroy();
    }

    public Component getCustomizer() {
        return null;   // new DiagElemCustomizer((DiagElemElement)element);
    }

    public boolean hasCustomizer() {
        return false;  // isWriteable();
    }
    
}
