/*
 * GenerateCodeAction.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.4  2003/06/21 00:57:11  weilyn
 * specware.jar
 *
 * Revision 1.3  2003/02/19 18:52:47  weilyn
 * Added calls to LispProcessManager to generate lisp and java.
 *
 * Revision 1.2  2003/02/19 15:46:20  gilham
 * Added submenu for GenerateCodeAction.
 *
 * Revision 1.1  2003/01/30 02:01:38  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.actions;

import java.awt.MenuShortcut;
import java.io.IOException;
import javax.swing.event.*;

import org.openide.actions.*;
import org.openide.cookies.EditorCookie;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileStateInvalidException;
import org.openide.loaders.DataObject;
import org.openide.util.enum.ArrayEnumeration;
import org.openide.util.HelpCtx;
import org.openide.util.actions.*;
import org.openide.awt.*;
import org.openide.nodes.Node;
import org.openide.TopManager;
import org.openide.NotifyDescriptor;
import org.openide.explorer.ExplorerManager;
import org.openide.util.NbBundle;
import org.openide.windows.WindowManager;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangEditorSupport;
import edu.kestrel.netbeans.lisp.LispProcessManager;
import edu.kestrel.netbeans.lisp.LispSocketManager;
import edu.kestrel.netbeans.model.SourceElement;

/**
 * GenerateCode action -- generate code for MetaSlangDataNode.
 */
public class GenerateCodeAction extends NodeAction {
    /** generated Serialized Version UID */
    static final long serialVersionUID = 5089785814030008824L;

    /** Imlementation of ActSubMenuInt */
    private static ActSubMenuModel model = new ActSubMenuModel();

    protected void performAction (Node[] activatedNodes) {
        performAction (activatedNodes, 0);
    }

    /** Performs action on index.
    */
    private void performAction (int indx) {
        performAction (
            WindowManager.getDefault().getRegistry ().getCurrentNodes (),
            indx
        );
    }


    /** Performs action on index and nodes.
    */
    private void performAction (Node[] nodes, int indx) {
	/*
        PasteAction.NodeSelector sel = null;
        try {
            ExplorerManager em = PasteAction.findExplorerManager();
            if (em != null) {
                sel = new PasteAction.NodeSelector (em, nodes);
            }
	    generateCodeForNodes(nodes, indx);
        } catch (java.io.IOException e) {
            TopManager.getDefault().notify(new NotifyDescriptor.Message(e.getMessage(), NotifyDescriptor.ERROR_MESSAGE));
        } finally {
            if (sel != null) {
                sel.select ();
            }
        }
	*/
	generateCodeForNodes(nodes, indx);
    }

    /** Generate code for a set of nodes.
    * @param nodes the nodes
    */
    void generateCodeForNodes (Node[] nodes, int target) {
        TopManager.getDefault ().setStatusText (message ());
        try {
            for (int i = 0; i < nodes.length; i++) {
		generateCodeForNode(nodes[i], target);
            }
        } finally { 
            TopManager.getDefault ().setStatusText (""); // NOI18N
        }

    }

    /** Generate code for a node.
    * @param node the node
    */
    void generateCodeForNode (Node node, int target) {
	MetaSlangDataObject dataObj = (MetaSlangDataObject) node.getCookie(DataObject.class);
        if (dataObj.isModified()) {
            MetaSlangEditorSupport editor = (MetaSlangEditorSupport)node.getCookie(EditorCookie.class);
            try {
                editor.saveDocument();
            } catch (IOException ioe) {
                Util.log("GenerateCodeAction.generateCodeForNode got IOException: "+ioe.getMessage());
            }
        }
	FileObject fileObj = dataObj.getPrimaryFile();
        String pathName = "";
        try {
            pathName = fileObj.getFileSystem().getSystemName();
        } catch (FileStateInvalidException e) {}
        String fileName = fileObj.getPackageName('/');

	switch (target) {
	case ActSubMenuModel.LISP_TARGET:
	    //Util.log("*** Generating Lisp code: fileName ="+fileName);
	    LispSocketManager.generateLispCode(pathName, fileName);
	    break;
	case ActSubMenuModel.JAVA_TARGET: 
	    //Util.log("*** Generating Java code: fileName ="+fileName);
	    LispSocketManager.generateJavaCode(pathName, fileName);
	    break;
        }
    }


    protected boolean enable (Node[] nodes) {
        // notify listeners
        Object[] listeners = model.getListenerList();
        if (listeners.length > 0) {
            ChangeEvent ev = new ChangeEvent (model);
            for (int i = listeners.length-1; i>=0; i-=2) {
                ((ChangeListener)listeners[i]).stateChanged (ev);
            }
        }

        if (nodes.length == 0) {
	    return false;
	}

	for (int i = 0; i < nodes.length; i++) {
            Node node = nodes[i];
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


    /* Returns a JMenuItem that presents the Action, that implements this
    * interface, in a MenuBar.
    * @return the JMenuItem representation for the Action
    */
    public javax.swing.JMenuItem getMenuPresenter() {
        return new Actions.SubMenu(this, model, false);
    }

    /* Returns a JMenuItem that presents the Action, that implements this
    * interface, in a PopuMenu.
    * @return the JMenuItem representation for the Action
    */
    public javax.swing.JMenuItem getPopupPresenter() {
        return new Actions.SubMenu(this, model, true);
    }

    /** Implementation of ActSubMenuInt */
    private static class ActSubMenuModel extends EventListenerList implements Actions.SubMenuModel {
        static final long serialVersionUID =-4273674308662494596L;

	static final int JAVA_TARGET = 0;
	static final int LISP_TARGET = 1;
	static final String[] MUNU_ITEM_STRINGS = new String[]{"Java", "Lisp"};

	ActSubMenuModel() {}
	
        public int getCount() {
            return MUNU_ITEM_STRINGS.length;
        }

        public String getLabel(int index) {
            return MUNU_ITEM_STRINGS[index];
        }

        public HelpCtx getHelpCtx (int index) {
	    return null;
        }

        public void performActionAt(int index) {
            GenerateCodeAction a = (GenerateCodeAction)findObject (GenerateCodeAction.class);
            if (a == null) return;
            a.performAction(index);
        }

        /** Adds change listener for changes of the model.
        */
        public void addChangeListener (ChangeListener l) {
            add (ChangeListener.class, l);
        }

        /** Removes change listener for changes of the model.
        */
        public void removeChangeListener (ChangeListener l) {
            remove (ChangeListener.class, l);
        }

    }
}
