/*
 * EspecModelNode.java
 *
 * Created on December 5, 2002, 9:47 PM
 */

package edu.kestrel.especs.graphs.spec;

import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.util.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.*;
import java.util.*;
/**
 *
 * @author  ma
 */
public class EspecModelNode extends ModelContainerNode {
    
    protected java.util.List importedEspecs;
    protected java.util.List importedByEspecs;
    
    protected boolean firstImport = true;
    
    /** Creates a new instance of EspecModelNode */
    public EspecModelNode() {
        super();
    }
    
    public void addImportedEspec(EspecModelNode espec) {
        importedEspecs = ListUtils.addToList(importedEspecs,espec);
        if (espec != null) {
            espec.addImportedByEspec(this);
        }
    }
    
    public void removeImportedEspec(EspecModelNode espec) {
        ListUtils.removeFromList(importedEspecs,espec);
        if (espec != null) {
            espec.removeImportedByEspec(this);
        }
    }
    
    public void removeAllImportedEspecs() {
        ListUtils.doForall(importedEspecs,new ListUtils.ListAction() {
            public boolean execute(Object obj) {
                if (obj instanceof EspecModelNode) {
                    ((EspecModelNode)obj).removeImportedByEspec(EspecModelNode.this);
                }
                return true;
            }
        });
        importedEspecs = null;
    }
    
    public java.util.List getImportedEspecs() {
        return importedEspecs;
    }
    
    /** returns true, if the given espec is in the list
     * of imported especs of this node.
     */
    public boolean importsEspec(EspecModelNode espec) {
        return importsEspec(espec,false);
    }
    
    public boolean importsEspec(EspecModelNode espec, boolean recursive) {
        if (importedEspecs == null) return false;
        if (importedEspecs.contains(espec)) {
            return true;
        }
        if (!recursive) return false;
        Iterator iter = importedEspecs.iterator();
        while(iter.hasNext()) {
            EspecModelNode impEspec = (EspecModelNode)iter.next();
            if (impEspec.importsEspec(espec,recursive)) return true;
        }
        return false;
    }
    
    public void addImportedByEspec(EspecModelNode espec) {
        importedByEspecs = ListUtils.addToList(importedByEspecs,espec);
        if (firstImport) {
            saveReprToBackupStore();
            firstImport = false;
        }
    }
    
    public void removeImportedByEspec(EspecModelNode espec) {
        ListUtils.removeFromList(importedByEspecs,espec);
    }
    
    public java.util.List getImportedByEspecs() {
        return importedByEspecs;
    }
    
    public boolean removeOk(boolean throwVeto) throws VetoException {
        if (super.removeOk(throwVeto)) {
            if (importedByEspecs != null) {
                if (importedByEspecs.size() > 0) {
                    if (throwVeto) {
                        throw new VetoException("espec is imported by other especs");
                    } else {
                        return false;
                    }
                }
            }
        } else {
            return false;
        }
        return true;
    }
    
    public boolean dragAndDropOk() {
        return true;
    }
    
    public void importHook(EspecModelNode orig) {
        copyHook(orig);
        //addImportedEspec(orig);
    }
    
    public void postImportAction(Map modelElementMap, EspecModelNode orig) {
        removeAllImportedEspecs();
        addImportedEspec(orig);
    }
    
    /** called after a copy action. */
    public void postCopyAction(final Map modelElementMap, ModelElement original) {
        Dbg.pr("postCopyAction: EspecModelNode "+getShortName()+"...");
        EspecModelNode mnode0 = (EspecModelNode)original;
        java.util.List imported0 = mnode0.getImportedEspecs();
        if (imported0 != null) {
            ListUtils.doForall(imported0, new ListUtils.ListAction() {
                public boolean execute(Object obj0) {
                    EspecModelNode importedEspec0 = (EspecModelNode)obj0;
                    Object obj = modelElementMap.get(importedEspec0);
                    if (obj instanceof EspecModelNode) {
                        Dbg.pr("imported espec has also been copied.");
                        addImportedEspec((EspecModelNode)obj);
                    } else {
                        Dbg.pr("imported espec has not been copied, adding the same one...");
                        addImportedEspec(importedEspec0);
                    }
                    return true;
                }
            });
        }
    }
    
    /*
    protected void createImportEdgesForReprs() {
        doForallReprs(new ReprAction() {
           public void execute(XGraphElement elem) {
               if (elem instanceof EspecNode) {
                   ((EspecNode)elem).createImportEdgeInGraph();
               }
           }
        });
    }
     */
    
    protected static String ImportedEspecs = "ImportedEspecs";
    
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        props.setStorableListProperty(ImportedEspecs, getImportedEspecs());
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        importedEspecs = props.getStorableListProperty(ImportedEspecs);
    }
    
    
}
