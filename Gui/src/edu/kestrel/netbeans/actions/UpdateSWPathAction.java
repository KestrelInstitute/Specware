package edu.kestrel.netbeans.actions;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.nodes.SWPathCustomizer;

import java.awt.BorderLayout;
import java.awt.event.*;
import java.awt.TextArea;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;

import org.openide.TopManager;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
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
/*        final JDialog d = new JDialog();
        d.getContentPane().setLayout(new BorderLayout());
        JPanel p = new JPanel();
        p.setLayout(new BorderLayout());
        p.setBorder(BorderFactory.createEmptyBorder(12, 12, 0, 11));
        
        final TextArea text = new TextArea(2, 80);
        text.setText(System.getProperty("Env-SWPATH"));
        p.add(text, BorderLayout.CENTER);
        
        JButton b = new JButton("Update SWPATH");
        b.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent ev) {
                System.setProperty("Env-SWPATH", text.getText());
                d.setVisible(false);
                d.dispose();
            }
        });
        p.add(b, BorderLayout.SOUTH);
        
        d.getContentPane().add(p, BorderLayout.CENTER);
        d.pack();
        d.show();
        //d.dispose();*/
        
        final JDialog d = new JDialog();
        d.getContentPane().setLayout(new BorderLayout());
        JPanel p = new JPanel();
        p.setLayout(new BorderLayout());
        p.setBorder(BorderFactory.createEmptyBorder(12, 12, 0, 11));
        p.add(new SWPathCustomizer(), BorderLayout.CENTER);
        JButton b = new JButton("Close View");
        b.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent ev) {
                d.setVisible(false);
                d.dispose();
            }
        });
        p.add(b, BorderLayout.SOUTH);
        d.getContentPane().add(p, BorderLayout.CENTER);
        d.pack();
        d.show();
  //      d.dispose();
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
