/*
 * OpElementNode.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.awt.Component;
import java.beans.*;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.ResourceBundle;

import org.openide.TopManager;
import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.ElementFormat;

/** Node representing a op.
* @see OpElement
*/
public class OpElementNode extends MemberElementNode {
    /** Create a new op node.
    * @param element op element to represent
    * @param writeable <code>true</code> to be writable
    */
    public OpElementNode(OpElement element, boolean writeable) {
        super(element, Children.LEAF, writeable);
        setElementFormat0(sourceOptions.getOpElementFormat());
    }

    public org.openide.util.HelpCtx getHelpCtx () {
        return new org.openide.util.HelpCtx ("org.openide.src.nodes.OpNode"); // NOI18N
    }

    /* Resolve the current icon base.
    * @return icon base string.
    */
    protected String resolveIconBase() {
	return OP;
    }

    /* This method resolve the appropriate hint format for the type
    * of the element. It defines the short description.
    */
    protected ElementFormat getHintElementFormat() {
        return sourceOptions.getOpElementLongFormat();
    }

    /* Creates property set for this node */
    protected Sheet createSheet () {
        Sheet sheet = Sheet.createDefault();
        Sheet.Set ps = sheet.get(Sheet.PROPERTIES);
        ps.put(createNameProperty(isWriteable()));
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
                                                     OpElement el = (OpElement) element;
                                                     ((SpecElement) el.getParent()).removeOp(el);
                                                 }
                                             });
        super.destroy();
    }

    public Component getCustomizer() {
        return null;   // new OpCustomizer((OpElement)element);
    }

    public boolean hasCustomizer() {
        return false;  // isWriteable();
    }

}
