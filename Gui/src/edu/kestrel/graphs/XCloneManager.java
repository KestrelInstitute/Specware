/*
 * XCloneManager.java
 *
 * Created on November 27, 2002, 2:27 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import com.jgraph.graph.*;
import javax.swing.tree.*;
import java.util.*;
/**
 * This class encapsulates a clone/copy operation of cells in a graph display to either the same or another graph display.
 * Instances of this class represent one clone/copy operation.
 * @author  ma
 */
public class XCloneManager {
    
    /** the graph displaying the cells to be cloned. */
    protected XGraphDisplay graph;
    
    /** the graph display for the cloned cells. */
    protected XGraphDisplay destGraph;
    
    /** the cells to be cloned. */
    protected Object[] cells;
    
    /** flag signaling whether or not the clone should be readonly */
    protected boolean createReadOnlyClone;
    
    /** flag controlling whether this operation is a clone or a copy: if set to true, new model elements will
     * be created for the new cells, which means that this operation is a copy operation. Otherwise, the new cells
     * get the same model elements as their original counterpart, which means that this operation is a clone operation.
     */
    protected boolean createNewModelElements;

    /** the cellMap that is computed in the process of cloning/copying */
    protected Map cellMap;
    
    /** the modelElementMap is set during the copy operation and contains mappings
     * from original model elements to their copies.
     */
    protected Map modelElementMap;
    
    /** Creates a new instance of XCloneManager */
    public XCloneManager(XGraphDisplay graph, Object[] cells, XGraphDisplay destGraph, boolean readonly, boolean isCopy) {
        this.graph = graph;
        this.cells = cells;
        this.destGraph = destGraph;
        this.createReadOnlyClone = readonly;
        this.createNewModelElements = isCopy;
        this.modelElementMap = new Hashtable();
    }
    
    public XCloneManager(XGraphDisplay graph, Object[] cells, XGraphDisplay destGraph) {
        this(graph,cells,destGraph,false,false);
    }

    /** sets the flag that determines whether or not the resulting clones shall be readonly or not.
     */
    public void setCreateReadOnlyClone(boolean b) {
        createReadOnlyClone = b;
    }
    
    /** returns true, if this operation represents a real cloning and not a copy.
     */
    public boolean isCloneOperation() {
        return !createNewModelElements;
    }

    /** returns true, if this operation is a copy operation, i.e. new model elements are created for the cells.
     */
    public boolean isCopyOperation() {
        return createNewModelElements;
    }
    
    /** returns true, if the source and destination graphs are the same.
     */
    public boolean isSameGraphOperation() {
        return graph.equals(destGraph);
    }
    
    /** sets the flag controlling whether this operation is a clone or a copy: if set to true, new model elements will
     * be created for the new cells, which means that this operation is a copy operation. Otherwise, the new cells
     * get the same model elements as their original counterpart, which means that this operation is a clone operation.
     */
    public void setCreateNewModelElements(boolean b) {
        createNewModelElements = b;
    }


    /** updated version of cells cloning; in addition to the standard cloning operation it takes care of cloning container nodes
     * that are collapsed.
     */
    public Map cloneCells() {
        Dbg.pr("start cloning cells...");
        graph.busy();
        if (!destGraph.equals(graph)) destGraph.busy();
        XContainerView.enableAddingOfContainedNodes(false);
        //step 1: collect all inner nodes and edges including detached ones
        ArrayList clist = new ArrayList();
        for(int i=0;i<cells.length;i++) {
            if (!clist.contains(cells[i]))
                clist.add(cells[i]);
            if (cells[i] instanceof XContainerNode) {
                java.util.List chlist = ((XContainerNode)cells[i]).getInnerNodesAndEdges();
                if (chlist != null) {
                    clist.addAll(chlist);
                    Dbg.pr("added "+chlist.size()+" children of container node "+cells[i]);
                }
            }
        }
        // step 2: do the cloning of the cells (copied from original cloneCells)
        Object[] allcells = clist.toArray();
        Dbg.pr("allcells: "+clist);
        CellView[] allviews = graph.getView().getMapping(allcells);
        ConnectionSet cs = ConnectionSet.create(graph.getModel(),allcells,false);
        cs.addConnections(allviews);
        Map propertyMapOrig = GraphConstants.createPropertyMap(allviews,null);
        Map propertyMap = propertyMapOrig;
        // if readonly, change the editable and disconnectable flags
        if (createReadOnlyClone) {
            propertyMap = new Hashtable();
            Iterator iter1 = propertyMapOrig.keySet().iterator();
            while(iter1.hasNext()) {
                Object key = iter1.next();
                Object obj = propertyMapOrig.get(key);
                Dbg.pr("obj has class "+obj.getClass().getName());
                if (obj instanceof Map) {
                    Map newmap = new Hashtable((Map)obj);
                    Dbg.pr("setting editable to false.");
                    GraphConstants.setEditable(newmap,false);
                    GraphConstants.setDisconnectable(newmap,false);
                    propertyMap.put(key,newmap);
                } else {
                    propertyMap.put(key,obj);
                }
            }
        }
        //step 3: remove multiple occurences of the same element, which may also
        //        occur somewhat hidden, namely when a cell is a descendant of another
        //        cell in the allcells array and is at the same time itself contained.
        //        in the array.
        Object[] cells0 = makeCellsUnique(allcells);//clist0.toArray();
        Object[] insert;
        cellMap = graph.cloneCells(cells0);
        propertyMap = GraphConstants.replaceKeys(cellMap, propertyMap);
        //GraphView.translateViews(allviews, dx, dy);
        boolean createLink = true;
        cs = cs.clone(cellMap);
        //insert = new Object[cells0.length];
        // step 4: construct the list of elements that are actually inserted; take care of
        //         cells the parents of which are already contained in the list; don't insert those.
        ArrayList insertAL = new ArrayList();
        for (int i = 0; i < cells0.length; i++) {
            boolean insertOk = true;
            Object insertCand = cellMap.get(cells0[i]);
            if (cells0[i] instanceof XNode) {
                TreeNode parent = ((XNode)cells0[i]).getVirtualParentNode();
                if (parent != null) {
                    if (clist.contains(parent)) {
                        Dbg.pr("skipping insertion of "+insertCand+", because parent will be inserted.");
                        insertOk = false;
                    }
                }
            }
            if (insertOk) {
                insertAL.add(insertCand);
            }
            //insert[i] = cellMap.get(cells0[i]);
        }
        insert = insertAL.toArray();
        //((XGraphDisplay) graph).getXGraphModel().insert(insert, cs, null, propertyMap);
        destGraph.getXGraphModel().insert(insert, cs, null, propertyMap);
        if (Dbg.isDebug()) {
            Set keyset = cellMap.keySet();
            Iterator iter = keyset.iterator();
            while (iter.hasNext()) {
                Object obj = iter.next();
                /*
                if (obj instanceof XNode) {
                    Dbg.pr("xnode: "+obj+" -> "+cellMap.get(obj));
                }
                else if (obj instanceof XEdge) {
                    Dbg.pr("xedge: "+obj+" -> "+cellMap.get(obj));
                }
                 */
            }
        }
        //getXGraphView().updateAllPorts();
        destGraph.getXGraphView().updateAllPorts();
        // step 5: call the cloneHook of cloned graph elements; first the nodes, then the edges
        Iterator iter = cellMap.keySet().iterator();
        while(iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof XGraphElement) {
                Object clone = cellMap.get(obj);
                if (clone instanceof XNode) {
                    //((XGraphElement)clone).cloneHook(this,obj);
                    cloneXGraphElement(obj,(XGraphElement)clone);
                }
            }
        }
        //getXGraphView().updateAllPorts();
        destGraph.getXGraphView().updateAllPorts();
        iter = cellMap.keySet().iterator();
        while(iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof XEdge) {
                Object clone = cellMap.get(obj);
                if (clone instanceof XGraphElement) {
                    //((XGraphElement)clone).cloneHook(this,obj);
                    cloneXGraphElement(obj,(XGraphElement)clone);
                }
            }
        }
        //((XGraphDisplay)graph).getXGraphView().updateAllPorts();
        // update the model nodes
        for(int i=0;i<allcells.length;i++) {
            Object obj = cellMap.get(allcells[i]);
            if (obj instanceof XNode) {
                XNode node = (XNode) obj;
                //Dbg.pr("*********** creating new model element for node "+node+"...");
                if (createNewModelElements) {
                    node.setModelNode(null);
                    if (allcells[i] instanceof XNode) {
                        ModelNode mnode0 = ((XNode)allcells[i]).getModelNode();
                        //node.getModelNode(destGraph).copyHook(mnode0);
                        ModelNode mnode1 = node.getModelNode(destGraph);
                        modelElementMap.put(mnode0, mnode1);
                        copyModelNode(mnode0,mnode1);
                    }
                }
                node.getModelNode(destGraph).addRepr(node);
            }
            if (obj instanceof XEdge) {
                XEdge edge = (XEdge) obj;
                if (createNewModelElements) {
                    edge.setModelEdge(null);
                    if (allcells[i] instanceof XEdge) {
                        ModelEdge medge0 = ((XEdge)allcells[i]).getModelEdge();
                        //edge.getModelEdge().copyHook(medge0);
                        ModelEdge medge1 = edge.getModelEdge();
                        modelElementMap.put(medge0,medge1);
                        copyModelEdge(medge0,medge1);
                    }
                }
                edge.getModelEdge().addRepr(edge);
            }
        }
        XContainerView.enableAddingOfContainedNodes(true);
        updateModelElements();
        Dbg.pr("cloning cells done.");
        graph.done();
        if (!destGraph.equals(graph)) destGraph.done();
        return cellMap;
    }
    
    /** calls ModelElement.potCopyAction() for each copied model element
     */
    protected void updateModelElements() {
        Iterator iter = modelElementMap.keySet().iterator();
        while(iter.hasNext()) {
            ModelElement elem0 = (ModelElement)iter.next();
            ModelElement elem1 = (ModelElement)modelElementMap.get(elem0);
            //elem1.postCopyAction(modelElementMap,elem0);
            modelElementPostCopyAction(modelElementMap,elem0,elem1);
        }
    }
    
    /** returns the cell map of this clone operation. */
    public Map getCellMap() {
        return cellMap;
    }
    
    /** returns the destination graph */
    public XGraphDisplay getDestGraph() {
        return destGraph;
    }
    
    /** clones the views of the cells original and clone and returns the view of the clone.
     * @param destGraph the target graph display, i.e. the graph display where the cloned views are contained
     */
    public CellView cloneCellViews(Object original, Object clone) {
        CellView oview = graph.getView().getMapping(original,false);
        CellView view = null;
        if (oview != null) {
            //if (Dbg.isDebug()) {
            //    Dbg.pr("attributes of original view:");
            //    XGraphDisplay.showAttributes(oview);
            //}
            Map omap = oview.getAttributes();
            view = destGraph.getView().getMapping(clone,true);
            if (view != null && omap != null) {
                Map viewMap = new Hashtable();
                viewMap.put(view,omap);
                //getView().edit(viewMap);
                destGraph.getView().edit(viewMap);
                //if (Dbg.isDebug()) {
                //    Dbg.pr("attributes of cloned view:");
                //    XGraphDisplay.showAttributes(view);
                //}
                if ((oview instanceof XContainerView) && (view instanceof XContainerView)) {
                    ((XContainerView)view).setCollapsedBounds(((XContainerView)oview).getCollapsedBounds());
                }
                if ((oview instanceof XEdgeView) && (view instanceof XEdgeView)) {
                }
            }
        }
        return view;
    }
    
    /** this method first collects all descendants of the given cells and returns the resulting array of cells with multiple
     * occurences of cells removed.
     */
    static public Object[] makeCellsUnique(Object[] cells) {
        ArrayList remove = new ArrayList();
        for(int i=0;i<cells.length;i++) {
            if (cells[i] instanceof XNode) {
                XNode node = (XNode) cells[i];
                boolean removeIt = false;
                for(int j=0;j<cells.length && !removeIt;j++) {
                    if (j!=i) {
                        if (cells[j] instanceof XContainerNode) {
                            XContainerNode cnode = (XContainerNode) cells[j];
                            if (cnode.isNodeDescendant(node)) {
                                removeIt = true;
                                remove.add(cells[i]);
                                Dbg.pr("  node "+cells[i]+" removed from cells list, because it's descendant of some other node.");
                            }
                        }
                    }
                }
            }
        }
        Object[] res = new Object[cells.length-remove.size()];
        int j = 0;
        for(int i=0;i<cells.length;i++) {
            if (!remove.contains(cells[i]))
                res[j++] = cells[i];
        }
        return res;
    }
    
    /** called when a graph element is copied/cloned; subclasser should always call <code>super.cloneXGraphElement()</code>.
     */
    protected void cloneXGraphElement(Object orig, XGraphElement copy) {
        copy.cloneHook(this,orig);
    }
    
    /** called when model nodes are copied; calls <copy>copy.copyHook(orig)</code> by default.
     */
    protected void copyModelNode(ModelNode orig, ModelNode copy) {
        copy.copyHook(orig);
    }
    
    /** called when model edges are copied; calls <copy>copy.copyHook(orig)</code> by default.
     */
    protected void copyModelEdge(ModelEdge orig, ModelEdge copy) {
        copy.copyHook(orig);
    }
    
    /** called after completion of a copy operation for all copied model elements.
     */
    protected void modelElementPostCopyAction(Map modeElementMap, ModelElement orig, ModelElement copy) {
        copy.postCopyAction(modelElementMap, orig);
    }
    
}
