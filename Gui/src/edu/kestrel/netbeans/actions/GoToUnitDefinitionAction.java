package edu.kestrel.netbeans.actions;


import edu.kestrel.netbeans.MetaSlangDataNode;
import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.MemberElement;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.model.SpecElement;
import edu.kestrel.netbeans.nodes.MemberElementNode;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ResourceBundle;

import org.openide.ErrorManager;
import org.openide.TopManager;
import org.openide.cookies.EditCookie;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.filesystems.Repository;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileSystem;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataObjectNotFoundException;
import org.openide.nodes.Children;
import org.openide.nodes.Node;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.actions.NodeAction;

/**
 *
 * @author  weilyn
 */
public class GoToUnitDefinitionAction extends NodeAction {
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(GoToUnitDefinitionAction.class);
    
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008826L;

    /* execute code for the nodes */
    protected void performAction (Node[] activatedNodes) {
        goToUnitDefinition(activatedNodes);
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
	/*DataObject dataObj = (DataObject) node.getCookie(DataObject.class);
	return (dataObj instanceof MetaSlangDataObject);*/
        return true;
    }

    /** Message to display when the action is looking for
    * object that should be processed.
    *
    * @return text to display at status line
    */
    protected String message () {
        return NbBundle.getMessage(StartLispAction.class, "CTL_SearchingForUnitDefinition");
    }

    /** Find and open unit definition
    */
    void goToUnitDefinition (Node[] nodes) {
        TopManager.getDefault ().setStatusText (message ());
        for (int i =0; i< nodes.length; i++) {
            MetaSlangDataObject dataObj;
            Node currNode = nodes[i];
            while (currNode.getParentNode().getCookie(DataObject.class) == null) {
                currNode = currNode.getParentNode();
            }
            dataObj = (MetaSlangDataObject)currNode.getParentNode().getCookie(DataObject.class);
            FileObject fileObj = dataObj.getPrimaryFile();
            //fullMountedPath is the path from the mounted file system, including hte file name itself
            String fullMountedPath = fileObj.getPackageName('/');
            String packageName, currFileName;
            int lastSlashIndex = fullMountedPath.lastIndexOf('/');
            if (lastSlashIndex != -1) {
                currFileName = fullMountedPath.substring(lastSlashIndex+1);
                packageName = fullMountedPath.substring(0, lastSlashIndex);
            } else {
                currFileName = fullMountedPath;
                packageName = "";
            }
            MemberElementNode node = dereference(nodes[i].getName(), packageName, currFileName);
        }
        TopManager.getDefault ().setStatusText (""); // NOI18N
    }
    
    /**
     * This method follows the documented algorithm for resolving unit identifiers at
     * http://www.specware.org/documentation/4.0/user-manual/x293.html
     */
    public MemberElementNode dereference(String unitID, String packageName, String currFileName) {        
        String innerUnitName = "";
        String fileName = "";
        String partialPathName = "";
        
        FileObject fo = null;
        MemberElementNode node = null;
        
        int innerRefIndex = unitID.indexOf('#');
        int lastSlashIndex = unitID.lastIndexOf('/');
        
        boolean alreadyFoundNode = false;
        
        // Case 1: SWPATH-based path
        if (unitID.startsWith("/")) {
            // Case 1a: with #<unit>
            if (innerRefIndex != -1) {
                innerUnitName = unitID.substring(innerRefIndex+1);
                fileName = unitID.substring(lastSlashIndex+1, innerRefIndex);
            } else { // Case 1b: without a #
                fileName = unitID.substring(lastSlashIndex+1);
            }
            partialPathName = unitID.substring(0, lastSlashIndex);
            fo = findSWPATHbasedUnit(partialPathName, fileName);
        } else { // Case 2: relative path
            // Case 2a: with #<unit>
            if (innerRefIndex != -1) {
                innerUnitName = unitID.substring(innerRefIndex+1);
                // Case 2a.i: with at least one '/'
                if (lastSlashIndex != -1) {
                    fileName = unitID.substring(lastSlashIndex+1, innerRefIndex);
                    // TODO: error check that the file <partialPathName/fileName> exists
                    partialPathName = packageName + unitID.substring(0, lastSlashIndex);
                } else { // Case 2a.ii: no '/'
                    fileName = unitID.substring(0, innerRefIndex);
                    partialPathName = packageName;
                }
            } else { // Case 2b: with no #
                // Case 2b.i: with at least one '/'
                if (lastSlashIndex != -1) {
                    fileName = unitID.substring(lastSlashIndex+1);
                    partialPathName = packageName + unitID.substring(0, lastSlashIndex);
                } else { // Case 2b.ii: no '/' - just a single identifier
                    // First, consider id to be an innerRef to current file
                    // TODO: error check that it's a multi-unit file
                    innerUnitName = unitID;
                    fo = findRelativeUnit(packageName, currFileName);
                    node = findNode(fo, innerUnitName);
                    if (node != null) {
                        return node;
                    } else {
                        partialPathName = packageName;
                        fileName = innerUnitName;
                    }
                }
            }
            fo = findRelativeUnit(partialPathName, fileName);
        }
        
        node = findNode(fo, innerUnitName);
        return node;
    }
        
    MemberElementNode findNode(FileObject fo, String innerUnitName) {
        if (fo == null) {
            FileNotFoundException ex = new FileNotFoundException();
            ErrorManager.getDefault().annotate(
                ex, ErrorManager.USER, null, 
                bundle.getString("MSG_DefinitionFileNotFound"),
                null, null);
        } else {
            MetaSlangDataNode dataNode = null;
            try {
                MetaSlangDataObject obj = (MetaSlangDataObject)(DataObject.find(fo));
                dataNode = (MetaSlangDataNode)obj.getNodeDelegate();
            } catch (DataObjectNotFoundException ex) {}

            Children kids = dataNode.getChildren();
            MemberElementNode innerUnitNode = (MemberElementNode)kids.findChild(innerUnitName);
            if (innerUnitNode == null) {
                IOException ex = new IOException();
                ErrorManager.getDefault().annotate(
                    ex, ErrorManager.USER, null, 
                    bundle.getString("MSG_DefinitionNotFound"),
                    null, null);
                return null;
            }
            EditCookie es = (EditCookie)innerUnitNode.getCookie(EditCookie.class);
            if (es != null) {
                es.edit ();
            }
            return innerUnitNode;
        }
        return null;
    }    
    
    FileObject findSWPATHbasedUnit(String partialPathName, String fileName) {
        String fullSWPATH = System.getProperty("Env-SWPATH");
        String[] SWPATHarr = fullSWPATH.split(";");
        FileObject fo = null;
                
        Repository rep = Repository.getDefault();

        for (int i=0; i<SWPATHarr.length; i++) {
            FileSystem fs = rep.findFileSystem(SWPATHarr[i]);
            fo = rep.find(partialPathName, fileName, "sw");
            if (fo != null) return fo;
        }
        return null;
    }
    
    FileObject findRelativeUnit(String partialPathName, String fileName) {
        Repository rep = Repository.getDefault();
        FileObject fo = null;
        fo = rep.find(partialPathName, fileName, "sw");
        return fo;
    }
    
    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(GoToUnitDefinitionAction.class, "GoToUnitDefinition");
    }

    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(GoToUnitDefinitionAction.class);
    }
    
}
