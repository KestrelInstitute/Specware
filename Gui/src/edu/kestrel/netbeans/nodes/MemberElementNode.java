/*
 * MemberElementNode.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:09  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.io.IOException;
import java.beans.*;
import java.lang.reflect.Modifier;
import java.lang.reflect.InvocationTargetException;
import java.text.MessageFormat;
import java.util.ResourceBundle;

import org.openide.TopManager;
import org.openide.ErrorManager;
import org.openide.NotifyDescriptor;
import org.openide.explorer.propertysheet.editors.ModifierEditor;
import org.openide.explorer.propertysheet.PropertyEnv;
import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.util.Lookup;
import org.openide.util.NbBundle;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.*;

/** Node representing some type of member element.
*/
public abstract class MemberElementNode extends ElementNode {
    /** Create a new node.
    *
    * @param element member element to represent
    * @param children list of children
    * @param writeable <code>true</code> to be writable
    */
    public MemberElementNode(MemberElement element, Children children, boolean writeable) {
        super(element, children, writeable);
        superSetName(element.getName());
    }

    /** Set the node's (system) name.
    * Attempts to change the element's name as well using {@link MemberElement#setName}.
    * Read-only elements cannot have their name set.
    * The display name will also be updated according to the proper format,
    * if necessary (typically it will be).
    *
    * @param str the new element and node name
    */
    public void setName(final String str) {
        try {
            if (testMetaSlangId(str)) {
                SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
                                                         public void run() throws SourceException {
                                                             ((MemberElement)element).setName(str);
                                                             superSetName(str);
                                                         }
                                                     });
            }
        }
        catch (IOException e) {
            MessageFormat fmt = new MessageFormat(bundle.getString("MSG_ElementCantRename"));
            String[] params = new String[] { ((MemberElement)element).getName(), e.getMessage() };
            if (params[1] == null)
                params[1] = ""; // NOI18N
	    
	    IllegalArgumentException ex = new IllegalArgumentException("Invalid name"); // NOI18N
	    ErrorManager.getDefault().annotate(ex, ErrorManager.USER,
		    null, fmt.format(params), e, null);
	    throw ex;
        }
    }

    /** Tests if the given string is meta-slang identifier and if not, notifies
    * the user.
    * @return true if it is ok.
    */
    boolean testMetaSlangId(String str) throws IllegalArgumentException {
        boolean ok = MetaSlangSyntax.isMetaSlangIdentifier(str);
        if (!ok) {
	    IllegalArgumentException ex = new IllegalArgumentException("Invalid identifier");
	    ErrorManager.getDefault().annotate(ex, ErrorManager.USER,
		null, bundle.getString("MSG_Not_Valid_Identifier"), null, null);
            throw ex;
        }
        return ok;
    }

    /** Create a node property representing the element's name.
    * @param canW if <code>false</code>, property will be read-only
    * @return the property.
    */
    protected Node.Property createNameProperty(boolean canW) {
        return new ElementProp(ElementProperties.PROP_NAME, String.class, canW) {
                   /** Gets the value */
                   public Object getValue () {
                       return ((MemberElement)element).getName();
                   }

                   /** Sets the value */
                   public void setValue(final Object val) throws IllegalArgumentException,
                       IllegalAccessException, InvocationTargetException {
                       super.setValue(val);
                       if (!(val instanceof String))
                           throw new IllegalArgumentException();

                       runAtomic(element, new SourceEditSupport.ExceptionalRunnable() {
                                     public void run() throws SourceException {
                                         String name = ((String) val).trim();
                                         //String prevName = ((MemberElement)element).getName();
                                         if (testMetaSlangId(name)) {
                                             ((MemberElement)element).setName(name);
                                         }
                                     }
                                 });
                   }
               };
    }
}
