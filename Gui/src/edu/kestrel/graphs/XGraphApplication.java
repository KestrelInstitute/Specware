/*
 * XGraphApplication.java
 *
 * Created on November 25, 2002, 11:51 AM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import javax.swing.tree.*;
import javax.swing.event.*;
import javax.swing.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;

/**
 * This class represents the toplevel class for an xgraph application. It contains all the information that constituted the application;
 * for instance which XGraphDisplay instances are currently existent, which logical model element exists etc.
 * @author  ma
 */
public class XGraphApplication {
    
    protected Vector registeredGraphs = null;
    protected XGraphDisplay clipboard = null;
    
    /** the desktop instance associated with this application.
     */
    protected XGraphDesktop desktop;
    
    /** the name of the top-level node of the model hierarchy as it appears in the tree view.
     */
    protected String applicationModelTitleString = "Application Model";
    
    protected String graphDisplayDefaultPrefix = "Graph Display";
    
    protected String graphDisplayTreeRootString = graphDisplayDefaultPrefix+"s";
    
    /** the object that serves as root node for the graphDisplay tree */
    protected ToplevelTreeModel treeModel;
    
    protected ToplevelTreeNode toplevelTreeNode;
    
    /** the modelNode associated with this application.
     */
    protected RootContainerNode modelNode = null;
    
    /** the current file name of the application */
    protected String currentFilename;
    
    protected ReadWriteOperation rwop;
    
    /** map from String -> Objects mapping class names to their singleton instance as they appear in this application.
     * This information is used in read/write operation to prevent generation of new object of classes which are supposed to
     * have exactly one instance in the application, like e.g. the toplevel tree node.
     */
    protected Map classExemplars;
    
    /** Creates a new instance of XGraphApplication */
    public XGraphApplication() {
        registeredGraphs = new Vector();
        clipboard = createXGraphDisplay("Clipboard");
        clipboard.setRemoveAllOnClosing(false);
        //clipboard.setTitleString("Clipboard");
        clipboard.setApplication(this);
        if (Dbg.isDebug()) {
            //setCurrentFilename("/tmp/test.xml");
            setCurrentFilename(null);
        }
        setCurrentFilename(null);
        classExemplars = new Hashtable();
        getToplevelTreeNode();
        //registerGraph(clipboard);
    }
    
    /** sets the desktop that is associated with this application.
     */
    public void setDesktop(XGraphDesktop desktop) {
        this.desktop = desktop;
    }
    
    /** returns the desktop that is associated with this application.
     */
    public XGraphDesktop getDesktop() {
        return desktop;
    }
    
    protected void registerGraph(XGraphDisplay graph) {
        if (!registeredGraphs.contains(graph)) {
            registeredGraphs.add(graph);
            getToplevelTreeNode().addGraphDisplay(graph);
        }
    }
    
    public void unregisterGraph(XGraphDisplay graph) {
        registeredGraphs.remove(graph);
        getToplevelTreeNode().removeGraphDisplay(graph);
    }
    
    public Enumeration graphDisplays() {
        return registeredGraphs.elements();
    }
    
    /** returns a new unique name for a graph display frame.
     */
    protected String generateGraphDisplayName() {
        int cnt = 0;
        for(;;cnt++) {
            String cand = graphDisplayDefaultPrefix+cnt;
            boolean alreadyUsed = false;
            //Dbg.pr("trying \""+cand+"\"...");
            Enumeration iter = registeredGraphs.elements();
            while(iter.hasMoreElements() && (!alreadyUsed)) {
                XGraphDisplay graph = (XGraphDisplay)iter.nextElement();
                Object val = graph.getValue();
                if (val.toString().equals(cand))
                    alreadyUsed = true;
            }
            if (!alreadyUsed)
                return cand;
        }
    }
    
    /** returns the (invisible) graph display that is used as clipboard.
     */
    public XGraphDisplay getClipboard() {
        return clipboard;
    }
    
    /** clears the application's clipboard.
     */
    public void clearClipboard() {
        getClipboard().getXGraphModel().removeAll();
    }
    
    /** inserts the given model elements into the given graph; the elemReprMap determines which XGraphElement is
     * the representation that is used for inserting the ModelElement.
     */
    public void insertModelElementsIntoGraph(XGraphDisplay graph, ModelElement[] elems, Map elemReprMap) {
        graph.disableListener();
        Map map = elemReprMap;
        if (map == null)
            map = new Hashtable();
        for(int i=0;i<elems.length;i++) {
            if (elems[i] instanceof ModelNode) {
                if (map.containsKey(elems[i])) {
                    XGraphElement elem = (XGraphElement) map.get(elems[i]);
                    ((ModelNode)elems[i]).insertIntoGraph(graph,elem,map);
                } else {
                    ((ModelNode)elems[i]).insertIntoGraph(graph,map);
                }
            }
        }
        Vector mnodes = new Vector();
        Iterator iter = map.keySet().iterator();
        while(iter.hasNext()) {
            ModelElement elem = (ModelElement) iter.next();
            Dbg.pr("--------------> inserted into graph: "+elem);
            if (elem instanceof ModelNode) {
                mnodes.add(elem);
            }
        }
        Enumeration iter1 = mnodes.elements();
        while(iter1.hasMoreElements()) {
            ModelNode mnode = (ModelNode)iter1.nextElement();
            XNode node = (XNode) map.get(mnode);
            mnode.insertEdgesIntoGraph(graph,node,map);
        }
        Enumeration iter2 = mnodes.elements();
        while(iter2.hasMoreElements()) {
            Object obj = iter2.nextElement();
            if (obj instanceof ModelContainerNode) {
                ModelContainerNode mnode = (ModelContainerNode)obj;
                XContainerNode node = (XContainerNode) map.get(mnode);
                mnode.restoreIsExpandedState(graph,node,map);
            }
        }
        graph.enableListener();
    }
    
    /** inserts the given model elements into the given graph; the reprExemplar fields of the model elements are
     * used as representation XGraphElements.
     */
    public void insertModelElementsIntoGraph(XGraphDisplay graph, ModelElement[] elements) {
        insertModelElementsIntoGraph(graph,elements,null);
    }
    
    /** creates a new graph display; this method should also be overwritten by sub-classers to return
     * an instance of a customized sub-class of XGraphDisplay.
     */
    protected XGraphDisplay createXGraphDisplay(Object value) {
        XGraphSpec spec = createXGraphSpec();
        XGraphDisplay graph = new XGraphDisplay(value,spec);
        return graph;
    }
    
    protected XGraphDisplay createXGraphDisplay() {
        String title = generateGraphDisplayName();
        XGraphDisplay graph = createXGraphDisplay(title);
        graph.addGraphDisplayValueListener(getToplevelTreeModel());
        return graph;
    }
    
    /** removes the XGraphElement in all registered graph displays.
     */
    public void removeXGraphElement(XGraphElement elem) {
        Enumeration iter = registeredGraphs.elements();
        while(iter.hasMoreElements()) {
            XGraphDisplay graph = (XGraphDisplay)iter.nextElement();
            elem.remove(graph.getModel());
        }
        Dbg.pr("removing "+elem+" from clipboard...");
        elem.remove(getClipboard().getModel());
    }
    
    /** initializes a new modelTree frame for the application.
     */
    public void initModelTree(XModelTree t) {
        Enumeration iter = registeredGraphs.elements();
        while(iter.hasMoreElements()) {
            XGraphDisplay graph = (XGraphDisplay)iter.nextElement();
            graph.addGraphDisplayValueListener(t);
        }
    }
    
    /** method called when the model tree frame is closed
     */
    public void finalizeModelTree(XModelTree t) {
        Enumeration iter = registeredGraphs.elements();
        while(iter.hasMoreElements()) {
            XGraphDisplay graph = (XGraphDisplay)iter.nextElement();
            graph.removeGraphDisplayValueListener(t);
        }
    }
    
    /** creates the model nodes for this application; subclassers should overwrite this method to
     * create instances of subclasses of RootContainerNode that is suitable for the customized application.
     */
    protected RootContainerNode createModelNode() {
        return new RootContainerNode(this,applicationModelTitleString);
    }
    
    /** returns the model node for the application. This method should
     * not be overwritten; overwrite <code>createModelNode()</code> instead.
     */
    public RootContainerNode getModelNode() {
        if (modelNode == null) {
            Dbg.pr("creating new toplevel model node...");
            modelNode = createModelNode();
            putClassExemplar(modelNode.getClass().getName(),modelNode);
        }
        return modelNode;
    }
    
    /** the toplevel tree model is the root node that has the graph displays and the application model as its children.
     */
    public ToplevelTreeModel getToplevelTreeModel() {
        if (treeModel == null) {
            treeModel = new ToplevelTreeModel(getToplevelTreeNode());
            getToplevelTreeNode().addTreeModel(treeModel);
        }
        return treeModel;
    }
    
    /** reloads the tree model after a change.
     */
    public void reloadTreeModel() {
        if (desktop == null) return;
        XModelTree mtree = desktop.getModelTree();
        mtree.saveExpandedPaths();
        getToplevelTreeModel().reload();
        mtree.restoreExpandedPaths();
        Dbg.pr("reload done.");
    }
    
    public void treeNodesChanged(ModelNode n, int[] childIndices, Object[] children) {
        reloadTreeModel();
        //getToplevelTreeModel().treeNodesChanged(this,n,childIndices,children);
    }
    public void treeNodesInserted(ModelNode n, int[] childIndices, Object[] children) {
        reloadTreeModel();
        //getToplevelTreeModel().treeNodesInserted(this,n,childIndices,children);
    }
    public void treeNodesRemoved(ModelNode n, int[] childIndices, Object[] children) {
        reloadTreeModel();
        //getToplevelTreeModel().treeNodesRemoved(this,n,childIndices,children);
    }
    public void treeStructureChanged(ModelNode n, int[] childIndices, Object[] children) {
        reloadTreeModel();
        //getToplevelTreeModel().treeStructureChanged(this,n,childIndices,children);
    }
    
    /** returns the toplevel tree node of this application; its children are the root node for the graph displays and the
     * root node for the application model.
     */
    public ToplevelTreeNode getToplevelTreeNode() {
        if (toplevelTreeNode == null) {
            Dbg.pr("creating new toplevel tree node...");
            toplevelTreeNode = new ToplevelTreeNode(graphDisplayTreeRootString);
        }
        return toplevelTreeNode;
    }
    
    /** the action to be performed to create a new XGraphDisplay; calls the createXGraphDisplay method and registers
     * the new graph instance.
     */
    final public XGraphDisplay newGraphAction() {
        XGraphDisplay graph = createXGraphDisplay();
        graph.setApplication(this);
        registerGraph(graph);
        return graph;
    }
    
    /** the action to be performed when a graph display is closed.
     */
    public void closeGraphAction(XGraphDisplay graph) {
        unregisterGraph(graph);
    }
    
    /** cleans up the graph list by removing those graph displays that are empty and currently not open.
     */
    public void cleanupGraphDisplays() {
        Dbg.pr("cleanupGraphDisplays...");
        Enumeration iter = graphDisplays();
        while(iter.hasMoreElements()) {
            XGraphDisplay graph = (XGraphDisplay) iter.nextElement();
            Dbg.pr("  graph \""+graph+"\" "+(graph.isEmpty()?"is empty":"is not empty"));
            if (desktop != null) {
                desktop.closeGraphIfEmptyAction(graph);
            }
        }
        reloadTreeModel();
    }
    
    /** deletes everything stored in the current application: all model nodes and all graph displays.
     */
    public void deleteAllAction() {
        // delete the model elements
        RootContainerNode modelroot = getModelNode();
        modelroot.removeModelElement(this,true);
        deleteAllGraphDisplays();
    }
    
    /** deletes all graph displays registered in the application.
     */
    protected void deleteAllGraphDisplays() {
        ArrayList glist = new ArrayList();
        Enumeration iter = graphDisplays();
        while (iter.hasMoreElements())
            glist.add(iter.nextElement());
        Iterator iter1 = glist.iterator();
        while(iter1.hasNext()) {
            XGraphDisplay graph = (XGraphDisplay)iter1.next();
            graph.deleteAction();
        }
    }
    
    /** store the given object as the singleton instance of the class in this application. This information is
     * used in io operation to prevent creation of new instances for these classes, like e.g. the ToplevelTreeNode class.
     */
    public void putClassExemplar(String classname, Object obj) {
        Dbg.pr("putClassExemplar("+classname+")");
        classExemplars.put(classname,obj);
    }
    
    /** returns the object that represents the singleton instance of the given class name in the application.
     */
    public Object getClassExemplar(String classname) {
        return classExemplars.get(classname);
    }
    
    /** returns true, if the application doesn't contain any items, i.e. graph displays and/or model elements that
     * are worth saving.
     */
    public boolean isEmpty() {
        RootContainerNode modelRoot = getModelNode();
        return (modelRoot.getChildCount() == 0);
    }
    
    /** this might be overwritten by sub-classers for providing a suitable instance of XGraphSpec that
     * represents the data model of the application.
     */
    public XGraphSpec createXGraphSpec() {
        return XGraphSpec.getDefaultSpec();
    }
    
    /** returns the XML representation of the given object together with all its dependent objects.
     */
    public String toXml(Storable obj) {
        return getReadWriteOperation(obj).toXml();
    }
    
    /** returns the ReadWriteOperation object that holds all information for the given obj
     * in form of ElementProperties
     */
    public ReadWriteOperation getReadWriteOperation(Storable obj) {
        ReadWriteOperation rwop = new ReadWriteOperation(this,obj);
        rwop.computeAllElementProperties();
        return rwop;
    }
    
    /** returns an instance of ReadWriteOperation for the toplevel tree node. The data structures returned
     * can be used to save the current state of the entire application.
     */
    public ReadWriteOperation getToplevelReadWriteOperation() {
        return getReadWriteOperation(getToplevelTreeNode());
    }
    
    /** returns the XML representation of the entire application. This method calls <code>toXml(getToplevelTreeNode())</code>.
     */
    public String allToXml() {
        rwop = getReadWriteOperation(getToplevelTreeNode());
        return rwop.toXml();
    }
    
    public void loadFromReadWriteOperation(ReadWriteOperation rwop) {
        if (rwop != null) {
            Dbg.pr("creating object from read-write-operation...");
            Storable obj = rwop.createObject();
            if (obj == null) {
                Dbg.pr("created object is null!?");
            } else {
                Dbg.pr("created object has class "+obj.getClass().getName());
            }
        }
        else Dbg.pr("rwop is null.");
        reloadTreeModel();
    }
    
    /** returns the file name that is used to save the application elements.
     */
    public String getCurrentFilename() {
        return currentFilename;
    }
    
    /** sets the file name that will be used to save the application elements.
     */
    public void setCurrentFilename(String filename) {
        currentFilename = filename;
        String title = filename;
        if (filename == null) {
            title = "No File";
        }
        if (desktop != null)
            desktop.setFrameTitle(title);
    }
    
    /** inner class for a storable tree node; used for the root node of graph displays, for instance.
     */
    protected class DefaultStorableTreeNode extends DefaultMutableTreeNode implements Storable {
        
        public boolean xmlHideToplevel = false;
        public String childTag = "ChildNode";
        
        public DefaultStorableTreeNode() {
            this(null);
        }
        
        public DefaultStorableTreeNode(Object label) {
            super(label);
        }
        
        public ElementProperties getElementProperties(ReadWriteOperation wop) {
            ElementProperties props = wop.createElementProperties(this);
            Enumeration iter = children();
            //props.setXmlHideToplevel(xmlHideToplevel);
            props.setValueProperty(getUserObject());
            while (iter.hasMoreElements()) {
                Object obj = iter.nextElement();
                if (obj instanceof Storable) {
                    props.addChildObject(childTag,(Storable)obj);
                }
            }
            return props;
        }
        
        public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
            Object value = props.getValueProperty();
            setUserObject(value);
            Dbg.pr("initFromElementProperties: "+this+"...");
            removeAllChildren();
            Enumeration iter = props.getChildObjectEnumeration(childTag);
            while(iter.hasMoreElements()) {
                ElementProperties childProps = (ElementProperties) iter.nextElement();
                Storable childObj = rwop.getObjectForId(childProps.getId());
                //Dbg.pr("childObj has class "+childObj.getClass().getName());
                if (childObj instanceof MutableTreeNode) {
                    Dbg.pr("   adding child "+childObj);
                    add((MutableTreeNode)childObj);
                }
            }
        }
        
    }
    
    /** inner class for the toplevel tree node of the application.
     */
    protected class ToplevelTreeNode extends DefaultStorableTreeNode {
        
        /** the root node for graph displays.
         */
        protected DefaultStorableTreeNode graphDisplayRoot;
        
        /** the tree models (of type DefaultTreeModel) which display this node.
         */
        protected Vector treeModels;
        
        public ToplevelTreeNode(String graphDisplayRootLabel) {
            super("ToplevelTreeNode");
            graphDisplayRoot = new DefaultStorableTreeNode(graphDisplayRootLabel) {
                public boolean isLeaf() {
                    return false;
                }
                public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
                    Object value = props.getValueProperty();
                    setUserObject(value);
                    Dbg.pr("initFromElementProperties: "+this+"...");
                    removeAllChildren();
                    // don't add children, they will be added with registerGraphDisplay()
                    Enumeration iter = props.getChildObjectEnumeration(childTag);
                    while(iter.hasMoreElements()) {
                        ElementProperties childProps = (ElementProperties) iter.nextElement();
                        Storable childObj = rwop.getObjectForId(childProps.getId());
                    }
                }
            };
            //graphDisplayRoot.xmlHideToplevel = true;
            graphDisplayRoot.childTag = "GraphDisplay";
            treeModels = new Vector();
            insert(graphDisplayRoot,0);
            insert(getModelNode(),1);
            //xmlHideToplevel = true;
            putClassExemplar(getClass().getName(),this);
            putClassExemplar(graphDisplayRoot.getClass().getName(),graphDisplayRoot);
        }
        
        public DefaultMutableTreeNode getGraphDisplayRoot() {
            return graphDisplayRoot;
        }
        
        /** adds a DefaultTreeModel to the list of tree models that display this node.
         */
        public void addTreeModel(DefaultTreeModel tm) {
            if (!treeModels.contains(tm)) {
                treeModels.add(tm);
            }
        }
        
        public void removeTreeModel(DefaultTreeModel tm) {
            treeModels.remove(tm);
        }
        
        public void addGraphDisplay(XGraphDisplay graph, int index) {
            Dbg.pr("adding XGraphDisplay "+graph+"...");
            int index0 = (index<0?graphDisplayRoot.getChildCount():index);
            XGraphDisplayTreeNode n = new XGraphDisplayTreeNode(XGraphApplication.this,graph);
            graphDisplayRoot.insert(n,index0);
            reloadTreeModel();
            //Enumeration iter = treeModels.elements();
            //while(iter.hasMoreElements()) {
            //    ((DefaultTreeModel)iter.nextElement()).nodesWereInserted(graphDisplayRoot,new int[]{index0});
            //}
        }
        
        public void addGraphDisplay(XGraphDisplay graph) {
            addGraphDisplay(graph,-1);
        }
        
        /** removes the graph display from the tree, returns the index where is has been found, -1, if it hasn't been found.
         */
        public void removeGraphDisplay(XGraphDisplay graph) {
            Enumeration iter = graphDisplayRoot.children();
            int index = 0;
            XGraphDisplayTreeNode n = null;
            while(iter.hasMoreElements() && (n == null)) {
                n = (XGraphDisplayTreeNode)iter.nextElement();
                if (!n.showsGraph(graph)) {
                    n = null;
                }
            }
            if (n != null) {
                n.removeFromParent();
                desktop.removeXGraphDisplay(graph);
                reloadTreeModel();
            }
        }
        
        public int getIndexOfGraphDisplay(XGraphDisplay graph) {
            Enumeration iter = graphDisplayRoot.children();
            int index = 0;
            boolean nothingRemoved = true;
            while(iter.hasMoreElements() && (nothingRemoved)) {
                XGraphDisplayTreeNode n = (XGraphDisplayTreeNode)iter.nextElement();
                if (n.showsGraph(graph)) {
                    return index;
                }
                index++;
            }
            return -1;
        }
        
        protected String ShowModelTree = "ShowModelTree";
        protected String ModelTree = "ModelTree";
        protected String RegisteredGraph = "RegisteredGraph";
        
        public ElementProperties getElementProperties(ReadWriteOperation rwop) {
            ElementProperties props = super.getElementProperties(rwop);
            Rectangle b = getDesktop().getModelTreeBounds();
            props.setBooleanProperty(ShowModelTree,(b!=null));
            if (b != null) {
                props.setRectangleProperty(ModelTree,b);
            }
            Enumeration iter = registeredGraphs.elements();
            while(iter.hasMoreElements()) {
                XGraphDisplay graph = (XGraphDisplay)iter.nextElement();
                props.addChildObjectAsReference(RegisteredGraph,graph);
            }
            return props;
        }
        public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
            super.initFromElementProperties(rwop,props);
            if (props.getBooleanProperty(ShowModelTree)) {
                Rectangle b = props.getRectangleProperty(ModelTree);
                getDesktop().showModelTree(b);
            }
            Enumeration iter = props.getChildObjectAsReferenceEnumeration(RegisteredGraph);
            while(iter.hasMoreElements()) {
                String id = (String) iter.nextElement();
                Storable obj = rwop.getObjectForId(id);
                if (obj instanceof XGraphDisplay) {
                    registerGraph((XGraphDisplay)obj);
                }
            }
            //reloadTreeModel();
        }
        
        
    }
    
    protected class ToplevelTreeModel extends DefaultTreeModel implements XGraphDisplayValueListener {
        
        protected ToplevelTreeNode treeNode;
        
        public ToplevelTreeModel(ToplevelTreeNode n) {
            super(n);
            treeNode = n;
        }
        
        public void treeNodesChanged(Object source, ModelNode n, int[] childIndices, Object[] children) {
            Object[] path = getPathInTreeModel(n).getPath();
            fireTreeNodesChanged(source,path,childIndices,children);
        }
        
        public void treeNodesInserted(Object source, ModelNode n, int[] childIndices, Object[] children) {
            Object[] path = getPathInTreeModel(n).getPath();
            fireTreeNodesInserted(source,path,childIndices,children);
        }
        
        public void treeNodesRemoved(Object source, ModelNode n, int[] childIndices, Object[] children) {
            Object[] path = getPathInTreeModel(n).getPath();
            fireTreeNodesRemoved(source,path,childIndices,children);
        }
        
        public void treeStructureChanged(Object source, ModelNode n, int[] childIndices, Object[] children) {
            Object[] path = getPathInTreeModel(n).getPath();
            fireTreeStructureChanged(source,path,childIndices,children);
        }
        
        /** retunrs the path of the model node wrt. to the tree model of the application.
         */
        public TreePath getPathInTreeModel(ModelNode n) {
            TreePath p0 = n.getPath();
            Object[] p = new Object[p0.getPathCount()+1];
            p[0] = getToplevelTreeNode();
            Object[] path0 = p0.getPath();
            for(int i=0;i<path0.length;i++) {
                p[i+1] = path0[i];
            }
            return new TreePath(p);
        }
        
        public void graphValueChanged(XGraphDisplay graph, Object oldValue, Object newValue) {
            int index = treeNode.getIndexOfGraphDisplay(graph);
            //Dbg.pr("index of graph: "+index);
            if (index>=0) {
                nodesChanged(treeNode.getGraphDisplayRoot(), new int[] {index});
            }
            //reload(treeNode);
            //int index = treeNode.removeGraphDisplay(graph);
            //treeNode.addGraphDisplay(graph,index);
        }
        
    }
    
    /** processes the arguments given at the command line.
     */
    protected static void processCommandLineArgs(String[] args, XGraphDesktop dt) {
        String loadfile = null;
        for(int i=0;i<args.length;i++) {
            Dbg.pr("command line argument: "+args[i]);
            if (args[i].equals("-d0")) {
                Dbg.setDebugLevel(0);
            }
            else if (args[i].equals("-d1")) {
                Dbg.setDebugLevel(1);
            }
            else if (args[i].equals("-d2")) {
                Dbg.setDebugLevel(2);
            }
            else {
                loadfile = args[i];
            }
        }
        if (loadfile != null) {
            dt.openAction(loadfile);
        }
    }
    
    /** static method that starts the application.
     */
    public static void startApplication(String[] args, String frameTitle, final XGraphDesktop dt) {
        JFrame frame = new JFrame(frameTitle);
        frame.getContentPane().setLayout(new BorderLayout());
        Dbg.setDebugLevel(0);
        
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                dt.exitAction(false);
                System.exit(0);
            }
        });
        dt.setFrame(frame);
        processCommandLineArgs(args,dt);
        frame.getContentPane().add(new JScrollPane(dt));
        frame.setSize(750,750);
        frame.show();
        
    }
    
    public static void main(String[] args) {
        XGraphApplication appl = new XGraphApplication();
        XGraphDesktop dt = new XGraphDesktop(appl);
        startApplication(args,"XGraphApplication Test",dt);
    }
    
}
