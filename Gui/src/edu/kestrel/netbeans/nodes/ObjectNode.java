package edu.kestrel.netbeans.nodes;

import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.DataFlavor;
import java.beans.*;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.ResourceBundle;

import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.util.Lookup;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;
import org.openide.util.WeakListener;
import org.openide.util.actions.SystemAction;
import org.openide.util.datatransfer.ExTransferable;

import edu.kestrel.netbeans.model.*;

public class ObjectNode extends AbstractNode implements IconStrings {
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(ObjectNode.class);
    
    /** Associated object. */
    protected Object object;

    /** Create a new object node.
    *
    * @param object Object to represent
    */
    public ObjectNode(Object object) {
	super(Children.LEAF);
        this.object = object;
        setIconBase(resolveIconBase());
        setDisplayName(object.toString());
    }

    public String getName() {
        return object.toString();
    }
    
    /** Get the currently appropriate icon base.
    * Subclasses should make this sensitive to the state of the object--for example,
    * a private variable may have a different icon than a public one.
    * @return icon base
    * @see AbstractNode#setIconBase
    */
    protected String resolveIconBase() {
	return OBJECT;
    }

    public HelpCtx getHelpCtx () {
        return new HelpCtx (ObjectNode.class);
    }

    /** Test whether this node can be renamed.
    * The default implementation assumes it can if this node is {@link #writeable}.
    *
    * @return <code>true</code> if this node can be renamed
    */
    public boolean canRename() {
        return false;
    }

    /** Test whether this node can be deleted.
    * The default implementation assumes it can if this node is {@link #writeable}.
    *
    * @return <code>true</code> if this node can be renamed
    */
    public boolean canDestroy () {
        return false;
    }

    /** Test whether this node can be copied.
    * The default implementation returns <code>true</code>.
    * @return <code>true</code> if it can
    */
    public boolean canCopy () {
        return true;
    }

    /** Test whether this node can be cut.
    * The default implementation assumes it can if this node is {@link #writeable}.
    * @return <code>true</code> if it can
    */
    public boolean canCut () {
        return false;
    }

    /** Set all actions for this node.
    * @param actions new list of actions
    */
    public void setActions(SystemAction[] actions) {
        systemActions = actions;
    }

    /** Calls super.fireCookieChange. The reason why is redefined
    * is only to allow the access from this package.
    */
    void superFireCookieChange() {
        fireCookieChange();
    }

    /** Test for equality.
    * @return <code>true</code> if the represented {@link Object}s are equal
    */
    public boolean equals (Object o) {
        return (o instanceof ObjectNode) && (object.equals (((ObjectNode)o).object));
    }

    /** Get a hash code.
    * @return the hash code from the represented {@link Element}
    */
    public int hashCode () {
        return object.hashCode ();
    }


}
