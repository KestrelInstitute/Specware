/*
 * GenerateCodeAction.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

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

/**
 * GenerateCode action -- generate code for MetaSlangDataNode.
 */
public class GenerateCodeAction extends NodeAction {
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008824L;

    /* generate code for the nodes */
    protected void performAction (Node[] activatedNodes) {
        generateCodeForNodes(activatedNodes);
    }

    protected boolean enable (Node[] arr) {
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
        return NbBundle.getMessage(GenerateCodeAction.class, "CTL_CodeGenerationStarted");
    }

    /** Generate code for a set of nodes.
    * @param nodes the nodes
    */
    void generateCodeForNodes (Node[] nodes) {
        TopManager.getDefault ().setStatusText (message ());
        try {
            for (int i = 0; i < nodes.length; i++) {
		generateCodeForNode(nodes[i]);
            }
        } finally { 
            TopManager.getDefault ().setStatusText (""); // NOI18N
        }

    }

    /** Generate code for a node.
    * @param node the node
    */
    void generateCodeForNode (Node node) {
	MetaSlangDataObject dataObj = (MetaSlangDataObject) node.getCookie(DataObject.class);
	FileObject fileObj = dataObj.getPrimaryFile();
	String fileName = fileObj.getNameExt();
	SourceElement source = dataObj.getSource();
	// TODO
    }


    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(GenerateCodeAction.class, "GenerateCode");
    }

    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(GenerateCodeAction.class);
    }


}
