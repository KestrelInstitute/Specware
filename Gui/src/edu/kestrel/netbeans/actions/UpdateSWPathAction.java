package edu.kestrel.netbeans.actions;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.lisp.LispSocketManager;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.nodes.SWPathCustomizer;

import java.awt.BorderLayout;
import java.awt.HeadlessException;
import java.awt.event.*;
import java.awt.TextArea;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;

import org.openide.TopManager;
import org.openide.DialogDisplayer;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.DialogDescriptor;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;
import org.openide.util.actions.NodeAction;



/**
 *
 * @author  weilyn
 */
public class UpdateSWPathAction extends NodeAction {
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008824L;
    
    /** Creates a new instance of ProcessUnitAction */
    protected void performAction(org.openide.nodes.Node[] activatedNodes) {
        LispSocketManager.getSWPath();
    }
    
    static public void finishPerformAction(String currSWPath) {
        JPanel innerPane = new JPanel();
        innerPane.setLayout(new BorderLayout());
        innerPane.setBorder(BorderFactory.createEmptyBorder(12, 12, 0, 11));
        JLabel label1;
        if (Utilities.isWindows()) {
            label1 = new JLabel("Edit the SWPATH (semicolon-separated list of absolute directory paths):");
        } else {
            label1 = new JLabel("Edit the SWPATH (colon-separated list of absolute directory paths):");
        }
        try {
            TextArea text = new TextArea(currSWPath, 1, 50, TextArea.SCROLLBARS_HORIZONTAL_ONLY);
            innerPane.add(text, BorderLayout.CENTER);
            innerPane.add(label1, BorderLayout.NORTH);

            DialogDescriptor dd = new DialogDescriptor(
                                    innerPane,
                                    "Edit SWPATH",
                                    true,
                                    DialogDescriptor.OK_CANCEL_OPTION,
                                    DialogDescriptor.OK_OPTION,
                                    null);

            if (DialogDisplayer.getDefault().notify(dd) == DialogDescriptor.OK_OPTION) {
                LispSocketManager.updateSWPath(text.getText());
            }
        } catch (HeadlessException he) {
            Util.log("UpdateSWPathAction.finishPerformAction caught HeadlessException "+he.getMessage());
        }
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
        return NbBundle.getMessage(UpdateSWPathAction.class, "CTL_RetrievingSWPath");
    }

    /* Help context where to find more about the action.
    * @return the help context for this action
    */
    public HelpCtx getHelpCtx() {
        return new HelpCtx(UpdateSWPathAction.class);
    }
    
    /* Human presentable name of the action. This should be
    * presented as an item in a menu.
    * @return the name of the action
    */
    public String getName() {
        return NbBundle.getMessage(UpdateSWPathAction.class, "UpdateSWPath");
    }
}
