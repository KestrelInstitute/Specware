/*
 * RootContainerNode.java
 *
 * Created on December 2, 2002, 7:31 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.*;
import javax.swing.tree.*;
/**
 * Instances of this class represent the root node of the application model
 * @author  ma
 */
public class RootContainerNode extends Folder {
    
    protected XGraphApplication appl;
    
    /** Creates a new instance of RootContainerNode */
    public RootContainerNode(XGraphApplication appl, Object label) {
        super(label);
        this.appl = appl;
    }
    
    /** returns the path of the node, which is the empty path for the root container node.
     */
    public TreePath getPath() {
        return new TreePath(this);
    }
    
    /** forwards the event to the application tree model.
     */
    protected void fireModelChange(XTreeModelEvent e) {
        if (e != null) {
            e.fireEvent(appl);
        } else {
            //appl.reloadTreeModel();
        }
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        initModelElement();
        initModelNode();
        initModelContainerNode();
        super.initFromElementProperties(rwop,props);
    }
    
    
}
