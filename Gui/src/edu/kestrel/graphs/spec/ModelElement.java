/*
 * ModelElement.java
 *
 * Created on November 26, 2002, 5:55 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import java.util.*;
import java.awt.datatransfer.*;

/**
 * Superclass for ModelNode and ModelEdge.
 * @author  ma
 */
public abstract class ModelElement implements Storable, Transferable {
    
    /** counter for model elements; mainly used for debugging purposes.
     */
    static protected int elementCnt = 0;
    
    /** unique id for this model element; mainly used for debugging purposes.
     */
    protected int id;
    
    /** the parent of this element
     */
    protected ModelContainerNode parent;
    
    /** vector containing all representation objects currently existing for this model node.
     * The elements of this vector are of type XNode for ModelNode and XEdge for ModelEdge
     */
    protected Vector reprs;
    
    /** the value of the node/edge; this is the only "builtin" property for all model elements.
     */
    protected Object value;
    
    /** this is a graph display which is used as backup store in case this model element cannot be removed and
     * the user removes the last representation object.
     */
    protected XGraphDisplay backupStore;
    
    /** the backup representation stored in the backup store.
     */
    protected XGraphElement backupRepr;
    
    /** interface use in doForallReprs */
    protected interface ReprAction {
        public void execute(XGraphElement elem);
    }
    
    public ModelElement() {
        this.value = null;
        initModelElement();
    }
    
    protected void initModelElement() {
        reprs = new Vector();
        id = elementCnt++;
        backupStore = null;
        backupRepr = null;
        Dbg.pr("initModelElement: new model element \""+this+"\" created");
    }
    
    /** this method determines whether the model element must have at least one representation element or not;
     * subclassers can overwrite this method to control the behaviour in case the last representation element
     * of this model element is removed: if this method returns true, it will exist without having a representation;
     * if it returns false, the node/edge will be removed, if no representation element for it exists.
     */
    public boolean existsWithoutRepresentation() {
        return false;
    }
    
    /** adds the first representation object, which is used to initialize the element's value.
     */
    public void addFirstRepr(XGraphElement xelem) {
        if (xelem != null) {
            addRepr(xelem);
            setValue(xelem.getUserObject());
        }
    }
    
    /** adds a new representation element to the list of representations.
     */
    public void addRepr(XGraphElement repr) {
        if (!reprs.contains(repr)) {
            //clearBackupStore();
            reprs.add(repr);
            Dbg.pr("new representation node added to "+value);
        }
        else Dbg.pr("'new' representation already exists for element "+this);
    }
    
    
    /** returns the number of representation objects for this model element.
     */
    public int getReprCnt() {
        if (reprs == null) return 0;
        return reprs.size();
    }
    
    /** returns the "accessible" representations of this model element, i.e. those elements that are
     * not in the graph's clipboard.
     */
    public int getAccessibleReprCnt(XGraphDisplay graph) {
        if (graph == null) return getReprCnt();
        int cnt = 0;
        XGraphDisplay clipboard = graph.getClipboard();
        if (clipboard == null) return getReprCnt();
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof XGraphElement) {
                XGraphElement elem = (XGraphElement)obj;
                if (!clipboard.equals(elem.getGraph())) {
                    cnt++;
                }
            }
        }
        Dbg.pr("ModelElement "+this+" has "+cnt+" accessible representation objects.");
        return cnt;
    }
    
    /** iterates over all representation elements and performs the given action.
     */
    public void doForallReprs(ReprAction action) {
        if (reprs == null) return;
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof XGraphElement) {
                action.execute((XGraphElement)obj);
            }
        }
    }
    
    /** sets this element as model element of all representations.
     */
    protected abstract void setModelElementOfReprs();
    
    
    /** removes the given representation element from the list of representations.
     */
    public void removeRepr(XGraphDisplay graph, XGraphElement repr) {
        reprs.remove(repr);
        Dbg.pr("repr of "+this+" removed.");
        if (reprs.size() == 0) {
            if (!existsWithoutRepresentation()) {
                // throw away if no representation element is left
                try {
                    if (removeOk(false)) {
                        Dbg.pr("removing model element \""+this+"\", because the last representation object has been removed...");
                        removeModelElement();
                    } else {
                        Dbg.pr("model element "+this+" will not be removed.");
                        //saveReprToBackupStore(graph,repr);
                    }
                } catch (VetoException ve) {/*ignore*/}
            }
        }
    }
    
    /** if representations currently exist in one of the graph displays of the application, this method returns an
     * enumeration of those (the ones that are store in the reprs field);
     * if no such representations exist, the reprExemplar field is checked, and -- if != null -- the enumeration jst
     * consisting of reprExemplar is returned;
     * if reprExemplar is null, this method returns null.
     */
    protected Enumeration getReprs() {
        if (reprs.size()>0)
            return reprs.elements();
        return null;
    }
    
    /** returns a representation object or null.
     */
    public XGraphElement getARepr() {
        if (reprs != null) {
            if (reprs.size() > 0) {
                return (XGraphElement) reprs.elementAt(0);
            }
        }
        return null;
    }
    
    /** returns the saved representation exemplar. */
    public XGraphElement getBackupRepr() {
        return backupRepr;
    }
    
    /** creates an instance of XGraphDisplay for storing the "last" representation object in case the user deletes it.
     */
    protected XGraphDisplay createXGraphDisplayForBackupStore() {
        XGraphDisplay res = new XGraphDisplay();
        return res;
    }
    
    /** returns the backupStore XGraphDisplay, which is initially created using createXgraphDisplayForBackupStore().
     */
    protected XGraphDisplay getBackupStore() {
        if (backupStore == null) {
            backupStore = createXGraphDisplayForBackupStore();
        }
        return backupStore;
    }
    
    /** this saves the representation object elem which is displayed in graph into the backup store of the model element.
     * Before this is done, the backup store is cleared.
     */
    public void saveReprToBackupStore(XGraphDisplay graph, XGraphElement elem) {
        clearBackupStore();
        XGraphDisplay bgraph = getBackupStore();
        bgraph.setIsClipboard(true);
        if (graph != null) {
            Dbg.pr("cloning representation object of model element "+this+" into its backStore...");
            Map cellMap = graph.cloneCells(new Object[]{elem},bgraph);
            if (cellMap.containsKey(elem)) {
                Object obj = cellMap.get(elem);
                if (obj instanceof XGraphElement) {
                    Dbg.pr("setting backup Repr of model element "+this+"...");
                    backupRepr = (XGraphElement)obj;
                }
            }
        }
    }
    
    public void saveReprToBackupStore() {
        XGraphElement elem = getARepr();
        if (elem != null) {
            saveReprToBackupStore(elem.getGraph(),elem);
        }
    }
    
    /** clears the backup store.
     */
    public void clearBackupStore() {
        backupRepr = null;
        if (backupStore == null) return;
        Dbg.pr("clearing the backup store of model element "+this+"...");
        backupStore.clear();
    }
    
    public abstract void removeModelElement();
    
    /** method used to give the model element a chance to veto its removal.
     * $param throwVetoException if set to true, it will throw a VetoException explaining the reason
     * why the remove operation is not ok; if set to false, a boolean value is returned in any case.
     */
    public boolean removeOk(boolean throwVetoException) throws VetoException {
        return true;
    }
    
    /** method used to give the model element a chance to veto its renaming.
     * $param throwVetoException if set to true, it will throw a VetoException explaining the reason
     * why the rename operation is not ok; if set to false, a boolean value is returned in any case.
     */
    public boolean renameOk(boolean throwVetoException) throws VetoException {
        return true;
    }
    
    /** removes the model element and all representations in all graph displays of the application.
     */
    public void removeModelElement(XGraphApplication appl) {
        removeModelElement();
        Vector rem = new Vector();
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XGraphElement elem = (XGraphElement)iter.nextElement();
            rem.add(elem);
        }
        Enumeration iter0 = rem.elements();
        while(iter0.hasMoreElements()) {
            XGraphElement elem = (XGraphElement) iter0.nextElement();
            appl.removeXGraphElement(elem);
        }
    }
    
    /** for those applications which use drag and drop, this can be used to signal whether this model element
     * is ok for dragging and dropping.
     */
    public boolean dragAndDropOk() {
        return false;
    }
    
    
    
    /** returns the value field of this model element. */
    public Object getValue() {
        return value;
    }
    
    /** sets the value field of this model element. */
    public void setValue(Object value) {
        //Dbg.pr("setValue("+value+")");
        this.value = value;
    }
    
    /** returns a short representation of the element's value as string to be used in popup windows etc.
     */
    public String getShortName() {
        if (getValue() == null) return "";
        String name = getValue().toString();
        if (name.length() > XGraphConstants.maxShortNameLength) {
            name = name.substring(0,XGraphConstants.maxShortNameLength) + "...";
        }
        return name;
    }
    
    
    
    /** inserts a freshly created representation element into the given graph.
     * @paran elem the graph element that is used as representation element
     * @param elemReprMap data structure mapping model elements to representations in the context of this
     * insertion operation
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem, Map elemReprMap) {
        if (elem == null)
            throw new IllegalArgumentException("displaying this element failed; no representation information found.");
        return elem;
    }
    
    /** inserts the model element into graph using elem as representation object
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem) {
        return insertIntoGraph(graph,elem,new Hashtable());
    }
    
    /** insert the model element into the graph using a copy of reprExemplar as representation object; elemReprMap contains
     * mappings from ModelElements to XGraphElement in the context of a insertion operation.
     */
    //public XGraphElement insertIntoGraph(XGraphDisplay graph, Map elemReprMap) {
    //XGraphElement repr = reprExemplar.cloneGraphElement();
    //return insertIntoGraph(graph,repr,elemReprMap);
    //}
    
    /** inserts the model element into the graph using a copy of reprExemplar as representation object.
     */
    //public XGraphElement insertIntoGraph(XGraphDisplay graph) {
    //    XGraphElement repr = reprExemplar.cloneGraphElement();
    //    return insertIntoGraph(graph,repr);
    //}
    
    /** synchronize this model element with all its representation objects by updating the representation objects
     * according to changed properties.
     */
    public void sync() {
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XGraphElement n = (XGraphElement) iter.nextElement();
            sync(n);
            n.repaintGraph();
        }
    }
    
    /** fires a model change to all listeners of this model element.
     */
    protected abstract void fireModelChange(XTreeModelEvent e);
    
    /** synchronizes this model element with the given representation element, which is part of the reprs. This method is called
     * from within sync() and can be used by subclassers to implement customized synch operations without iterating over the
     * list of representations.
     */
    protected void sync(XGraphElement n) {
        n.setFullUserObject(getValue());
    }
    
    protected static String Representation = "Representation";
    
    /** returns the instance of <code>ElementProperties</code> that is used in io operations as a representation of this
     * element.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = wop.createElementProperties(this);
        Enumeration iter = getReprs();
        if (iter != null) {
            while(iter.hasMoreElements()) {
                Storable obj = (Storable)iter.nextElement();
                props.addChildObject(Representation,obj);
            }
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        initModelElement();
        Dbg.pr("{adding representations for model element "+this+"...");
        Dbg.pr(" #existing reprs: "+reprs.size());
        Enumeration iter = props.getChildObjectEnumeration(Representation);
        while(iter.hasMoreElements()) {
            ElementProperties cprops = (ElementProperties)iter.nextElement();
            XGraphElement elem = (XGraphElement) rwop.getObjectForId(cprops.getId());
            addRepr(elem);
        }
        //setModelElementOfReprs();
        Dbg.pr("}");
    }
    
    /** returns the string representation of this model elment, which is the string representation of the model element's value.
     */
    public String toString() {
        String res;
        if (value != null) {
            res = value.toString();
        } else {
            String cname = getClass().getName();
            int index = cname.lastIndexOf('.');
            String name;
            if (index<0)
                name = cname;
            else
                name = cname.substring(index+1);
            res = name+id;
        }
        int cnt = reprs.size();
        return res;// + "("+ String.valueOf(cnt) + ")";
    }
    
    
    /** called when a new copy of the model element is created. Subclasses that introduce new fields can overwrite this method
     * to make sure that the new fields are copied to the new instance. This is called during a copy operation.
     */
    public void copyHook(ModelElement original) {
    }
    
    /** called after completion of a copy operation in order to let the model element perform tasks to update certain structure.
     * For instance, if A and B are copied to A' and B' respectively, and A and B have some relation R, this method can be used
     * to establish this relation also for A' and B'
     */
    public void postCopyAction(Map modelElementMap, ModelElement original) {
    }
    
    // methods implementing the transferable interface needed for dnd
    
    final public static DataFlavor MODEL_ELEMENT_FLAVOR =
    new DataFlavor(ModelElement.class, "Model Element");
    
    static DataFlavor flavors[] = {MODEL_ELEMENT_FLAVOR};
    
    
    
    public boolean isDataFlavorSupported(DataFlavor df) {
        return df.equals(MODEL_ELEMENT_FLAVOR);
    }
    
    /** implements Transferable interface */
    public Object getTransferData(DataFlavor df)
    throws UnsupportedFlavorException, java.io.IOException {
        if (df.equals(MODEL_ELEMENT_FLAVOR)) {
            return this;
        }
        else throw new UnsupportedFlavorException(df);
    }
    
    /** implements Transferable interface */
    public DataFlavor[] getTransferDataFlavors() {
        return flavors;
    }
    
    
    
}
