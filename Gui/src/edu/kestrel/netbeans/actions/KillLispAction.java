package edu.kestrel.netbeans.actions;

import org.openide.filesystems.FileObject;
import org.openide.loaders.DataObject;
import org.openide.TopManager;
import org.openide.util.HelpCtx;
import org.openide.util.actions.NodeAction;
import org.openide.nodes.Node;
import org.openide.util.NbBundle;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.lisp.LispSocketManager;
import org.openide.filesystems.FileStateInvalidException;

/**
 *
 * @author  weilyn
 */
public class KillLispAction extends NodeAction {
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008826L;

    /* execute code for the nodes */
    protected void performAction (Node[] activatedNodes) {
        killLisp();
    }
    
    protected boolean enable(Node[] arr) {
        if (arr.length == 0) {
	    return false;
	}
	for (int i = 0; i < arr.length; i++) {
            Node node = arr[i];
	    if (!enable(node)) {
		return false;
	    }
        }
        return true;
    }

    private boolean enable (Node node) {
	DataObject dataObj = (DataObject) node.getCookie(DataObject.class);
	return (dataObj instanceof MetaSlangDataObject);	
    }

    /** Message to display when the action is looking for
    * object that should be processed.
    *
    * @return text to display at status line
    */
    protected String message () {
        return NbBundle.getMessage(StartLispAction.class, "CTL_KillingLisp");
    }

    /** Execute code for a node.
    * @param node the node
    */
    void killLisp () {
        TopManager.getDefault ().setStatusText (message ());
	LispSocketManager.destroyLispProcess();
        TopManager.getDefault ().setStatusText ("");
    }
    
    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(KillLispAction.class, "KillLisp");
    }

    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(KillLispAction.class);
    }
    
}
