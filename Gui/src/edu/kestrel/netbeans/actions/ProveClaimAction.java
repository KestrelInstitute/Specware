/*
 * ProveClaimAction.java
 *
 * Created on February 19, 2003, 11:23 AM
 */

package edu.kestrel.netbeans.actions;

import org.openide.NotifyDescriptor;
import org.openide.TopManager;
import org.openide.filesystems.FileLock;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.filesystems.FileUtil;
import org.openide.filesystems.Repository;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.src.SourceException;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.actions.NodeAction;

import java.io.OutputStream;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.model.ClaimElement;
import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.model.SpecElement;
import edu.kestrel.netbeans.nodes.SpecElementNode;
import edu.kestrel.netbeans.nodes.MemberCustomizer;
import edu.kestrel.netbeans.nodes.ProveCustomizer;

/**
 *
 * @author  weilyn
 */
public class ProveClaimAction extends NodeAction {
    
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008824L;
    
    /** Creates a new instance of ProveClaimAction */
    protected void performAction(org.openide.nodes.Node[] activatedNodes) {
       proveClaimForNodes(activatedNodes);
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
        return NbBundle.getMessage(ProveClaimAction.class, "CTL_CreatingProveStarted");
    }
    
    /** Process a set of nodes.
    * @param nodes the nodes
    */
    void proveClaimForNodes (Node[] nodes) {
        TopManager.getDefault ().setStatusText (message ());
        try {
            for (int i = 0; i < nodes.length; i++) {
		proveClaimForNode(nodes[i]);
            }
        } finally { 
            TopManager.getDefault ().setStatusText (""); // NOI18N
        }

    }

    /** Prove a claim for a node.
    * @param node the node
    */
    void proveClaimForNode (Node node) {
        // TODO: Ask user whether to only display proof results in Specware Output window -or-
        // generate a .sw file with the proof command, call the prover with the .sw file, and display the results

        // Open ProveClaimWizard and present node's info
        
        Element el = (Element)node.getCookie(Element.class);
        ClaimElement claimElement = null;
        SpecElement parentSpecElement = null;
        if (el instanceof ClaimElement) {
            claimElement = (ClaimElement)el;
            parentSpecElement = (SpecElement)claimElement.getParent();
        }
        /*Prove*/SpecElement newProveElem = new SpecElement();
        try {
            newProveElem.setName("newProof");
        } catch (SourceException exc) {}
        ProveCustomizer cust = new ProveCustomizer(newProveElem, parentSpecElement, claimElement);
	NotifyDescriptor descriptor = new NotifyDescriptor(
							  cust,
							  "Create new proof",
							  NotifyDescriptor.OK_CANCEL_OPTION,
							  NotifyDescriptor.PLAIN_MESSAGE,
							  null, null);

	Object ret = TopManager.getDefault().notify(descriptor);

        if ((ret == NotifyDescriptor.OK_OPTION) && cust.isOK()) {
            createProofFile(newProveElem, node, cust);
        }
    }

    private void createProofFile(/*Prove*/SpecElement e, Node node, ProveCustomizer cust) {
       
        String qualifiedSpecName;
        Node parentSpecNode = node.getParentNode().getParentNode();
        String specName = parentSpecNode.getName();
        if (specName.equals("")) {
            qualifiedSpecName = parentSpecNode.getParentNode().getName();
        } else {
            qualifiedSpecName = parentSpecNode.getParentNode().getName();
            qualifiedSpecName += "#" + specName;
        }
        String proveCommand = "";
        proveCommand += e.getName();
        proveCommand += " = prove " + node.getName();
        proveCommand += " in " + qualifiedSpecName;
        
        String usingClaim = cust.getSelectedUsingClaim();
        String useResolution = cust.getSelectedUseResolution();
        String timeLimit = cust.getTimeLimit();
        if (!usingClaim.equals(ProveCustomizer.USE_ALL_CLAIMS) &&
            !usingClaim.equals(ProveCustomizer.USE_NO_CLAIMS)) {
            proveCommand += " using " + cust.getSelectedUsingClaim();
        }
        if (!(useResolution.equals(ProveCustomizer.USE_RESOLUTION_DEFAULT) &&
              timeLimit.equals("0"))) {
              proveCommand += " options \"";
              if (useResolution.equals(ProveCustomizer.USE_RESOLUTION_YES)) {
                  proveCommand += "(USE-RESOLUTION T)";
              } else if (useResolution.equals(ProveCustomizer.USE_RESOLUTION_NO)) {
                  proveCommand += "(USE-RESOLUTION NIL)";
              }
              if (!timeLimit.equals("0")) {
                  proveCommand += "(RUN-TIME-LIMIT " + timeLimit + ")";
              }
              proveCommand += "\"";
        }


	/*MetaSlangDataObject dataObj = (MetaSlangDataObject) (parentSpecNode.getParentNode()).getCookie(DataObject.class);
	FileObject fileObj = dataObj.getPrimaryFile();
        String pathName = "";
        try {
            pathName = fileObj.getFileSystem().getSystemName();
        } catch (FileStateInvalidException fsie) {
            Util.log("ProveClaimAction.createProofFile caught FileStateInvalidException: "+fsie.getMessage());
        }
        String fileName = fileObj.getPackageName('/');
        */
        
 
        FileObject folder = Repository.getDefault().find("Demo_Examples", null, null);
        FileObject proofFile = null;
        try {
            proofFile = FileUtil.createData(folder, e.getName()+"-proofs.sw");
        } catch (java.io.IOException exc) {}

        if (proofFile != null) {
            try {
                FileLock lock = proofFile.lock();
                OutputStream out = proofFile.getOutputStream(lock);
                out.write(proveCommand.getBytes());
                out.flush();
                out.close();
            } catch (java.io.IOException exc) {}

            // Process (TODO: proof command or ) new foo-proofs.sw file
            String pathName = "";
            try {
                pathName = proofFile.getFileSystem().getSystemName();
            } catch (FileStateInvalidException exc) {}
            String fileName = proofFile.getPackageName('/'); 
            LispProcessManager.processUnit(pathName, fileName);                
        }
        
    }
    
    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(ProcessUnitAction.class);
    }
    
    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(ProveClaimAction.class, "ProveClaim");
    }
    
}
