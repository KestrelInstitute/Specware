package edu.kestrel.netbeans.actions;

import org.openide.TopManager;
import org.openide.cookies.FilterCookie;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.actions.NodeAction;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.lisp.LispSocketManager;
import edu.kestrel.netbeans.model.SourceElement;



/**
 *
 * @author  weilyn
 */
public class CompileSpecAction extends NodeAction {
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008824L;
    
    /** Creates a new instance of ProcessUnitAction */
    protected void performAction(org.openide.nodes.Node[] activatedNodes) {
        compileSpecForNodes(activatedNodes);
    }

    
    protected boolean enable(org.openide.nodes.Node[] arr) {
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
        return NbBundle.getMessage(CompileSpecAction.class, "CTL_SpecCompilationStarted");
    }
    
    /** Incremental compile for selected spec nodes
    * @param nodes the nodes
    */
    void compileSpecForNodes (Node[] nodes) {
        TopManager.getDefault ().setStatusText (message ());
        try {
            for (int i = 0; i < nodes.length; i++) {
		compileSpecForNode(nodes[i]);
            }
        } finally { 
            TopManager.getDefault ().setStatusText (""); // NOI18N
        }

    }

    /** compile a spec node.
    * @param node the node
    */
    void compileSpecForNode (Node node) {
	MetaSlangDataObject dataObj = (MetaSlangDataObject) node.getCookie(DataObject.class);
	FileObject fileObj = dataObj.getPrimaryFile();
        String pathName = "";
        try {
            pathName = fileObj.getFileSystem().getSystemName();
        } catch (FileStateInvalidException e) {}
        String fileName = fileObj.getPackageName('/'); 
        String specName = node.getName();
        LispSocketManager.compileSpec(pathName, fileName, specName);
    }

    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(CompileSpecAction.class);
    }
    
    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(CompileSpecAction.class, "CompileSpec");
    }
}
