/*
 * Folder.java
 *
 * Created on December 3, 2002, 6:02 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import javax.swing.tree.*;
import java.util.*;

/**
 * Instances of this class represent folders in the model tree
 * @author  ma
 */
public class Folder extends ModelContainerNode {
    
    protected static String newFolderPrefix = "newfolder";
    
    /** Creates a new instance of Folder */
    public Folder(Object label) {
        super();
        setValue(label);
        setUniqueValue();
    }
    
    public Folder(Folder parent) {
        this(newFolderPrefix);
        try {
            setParent(parent);
        } catch (Exception e) {}
        setUniqueValue();
    }
    
    public Folder() {
        this("");
    }
    
    public boolean existsWithoutRepresentation() {
        return true;
    }
    
    
    /** sets a unique value for this folder.
     */
    public void setUniqueValue() {
        int cnt = 0;
        TreeNode parent = getParent();
        String name = (String) getValue();
        String prefix = name;
        if (parent == null) return;
        for(;;) {
            boolean alreadyUsed = false;
            Enumeration iter = parent.children();
            while (iter.hasMoreElements() && (!alreadyUsed)) {
                Object obj = iter.nextElement();
                if (!equals(obj)) {
                    if (obj instanceof Folder) {
                        String fname = (String) ((Folder)obj).getValue();
                        if (fname.equals(name))
                            alreadyUsed = true;
                    }
                }
            }
            if (alreadyUsed) {
                name = prefix + String.valueOf(cnt++);
            } else {
                if (!prefix.equals(name))
                    setValue(name);
                return;
            }
        }
    }
    
    public void addRepr(XGraphElement elem) {
    }
    
    /** adds a sub folder.
     */
    public void addSubfolder(Folder sub) {
        int index = getChildCount();
        insert(sub,index);
        fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_INSERTED,this,new int[]{index},new Object[]{sub}));
    }
    
    /** its only possible to add a child that had a folder parent before.
     */
    public void addChild(ModelNode mnode) throws ModelException {
        TreeNode mnodeParent = mnode.getParent();
        boolean addChildOk = true;
        if (mnodeParent == null) {
            addChildOk = true;
        }
        else if (mnodeParent instanceof Folder) {
            addChildOk = true;
        }
        if (addChildOk) {
            super.addChild(mnode);
        } else {
            throw new ModelException("node \""+mnode+"\" cannot become a child of \""+this+"\", because it is an inner node.");
        }
    }
}
