/*
 * DefElementNode.java
 *
 * Created on February 15, 2003, 5:08 PM
 */

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

public class DefElementNode extends MemberElementNode {
    /** Create a new def node.
    * @param element def element to represent
    * @param writeable <code>true</code> to be writable
    */
    public DefElementNode(DefElement element, boolean writeable) {
        super(element, Children.LEAF, writeable);
        setElementFormat0(sourceOptions.getDefElementFormat());
    }

    public org.openide.util.HelpCtx getHelpCtx () {
        return new org.openide.util.HelpCtx ("org.openide.src.nodes.DefNode"); // NOI18N
    }

    /* Resolve the current icon base.
    * @return icon base string.
    */
    protected String resolveIconBase() {
	return DEF;
    }

    /* This method resolve the appropriate hint format for the type
    * of the element. It defines the short description.
    */
    protected ElementFormat getHintElementFormat() {
        return sourceOptions.getDefElementLongFormat();
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
                                                     DefElement el = (DefElement) element;
                                                     ((SpecElement) el.getParent()).removeDef(el);
                                                 }
                                             });
        super.destroy();
    }

    public Component getCustomizer() {
        return null;   // new DefCustomizer((DefElement)element);
    }

    public boolean hasCustomizer() {
        return false;  // isWriteable();
    }
    
}
