/*
 * XGraphModelListener.java
 *
 * Created on November 26, 2002, 11:21 PM
 */

package edu.kestrel.graphs.event;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.spec.*;
import com.jgraph.event.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.util.*;
/**
 *
 * @author  ma
 */
public class XGraphModelListener implements GraphModelListener {
    
    protected XGraphDisplay graph;
    
    protected boolean enabled = true;
    
    /** Creates a new instance of XGraphModelListener */
    public XGraphModelListener(XGraphDisplay graph) {
        this.graph = graph;
    }
    
    public void disable() {
        enabled = false;
    }
    
    public void enable() {
        enabled = true;
    }
    
    public void graphChanged(GraphModelEvent graphModelEvent) {
        if (!enabled) return;
        processChange(graphModelEvent.getChange());
    }
    
    protected void processChange(GraphModelEvent.GraphModelChange change) {
        //Dbg.pr("processing model change of type "+change.getClass().getName());
        processInserted(change.getInserted());
        processRemoved(change.getRemoved());
        Map attrMap = (!graph.getModel().isAttributeStore()?change.getStoredAttributeMap():change.getAttributeMap());
        processChanged(change.getChanged(),attrMap);
    }
    
    protected void processInserted(Object[] objs) {
        if (objs == null) return;
        for(int i=0;i<objs.length;i++) {
            if (objs[i] instanceof XNode) {
                XNode node = (XNode) objs[i];
                Dbg.pr("listener: inserted node: "+node);
                ModelNode mnode = node.getModelNode();
                try {
                    graph.getModelNode().addChild(mnode);
                } catch (ModelException me) {
                    JOptionPane.showMessageDialog(graph,me.getMessage());
                    disable();
                    graph.getModel().remove(new Object[]{node});
                    enable();
                }
                //graph.getModelNode().addChild(mnode);
            }
            if (objs[i] instanceof XEdge) {
                XEdge edge = (XEdge) objs[i];
                Dbg.pr("listener: inserted edge: "+edge);
            }
        }
    }
    
    protected void processRemoved(Object[] objs) {
        if (objs == null) return;
        for(int i=0;i<objs.length;i++) {
            if (objs[i] instanceof XNode) {
                XNode node = (XNode) objs[i];
                Dbg.pr("listener: removed node: "+node);
                ModelNode mnode = node.getModelNode();
                mnode.removeRepr(node);
            }
            if (objs[i] instanceof XEdge) {
                XEdge edge = (XEdge) objs[i];
                Dbg.pr("listener: removed edge: "+edge);
                ModelEdge medge = edge.getModelEdge();
                medge.removeRepr(edge);
            }
        }
        if (graph.isEmpty()) {
            if (graph.getApplication() != null) {
                graph.getApplication().cleanupGraphDisplays();
            }
        }
    }
    
    protected void processChanged(Object[] objs, Map attrMap) {
        if (objs == null) return;
        for(int i=0;i<objs.length;i++) {
            if (objs[i] instanceof XNode) {
                XNode node = (XNode) objs[i];
                Dbg.pr("listener: changed node: "+node);
                Map map = null;
                if (attrMap != null) map = (Map)attrMap.get(node);
                processXNodeChange(node,map);
            }
            if (objs[i] instanceof XEdge) {
                XEdge edge = (XEdge) objs[i];
                Map map = null;
                if (attrMap != null) map = (Map)attrMap.get(edge);
                processXEdgeChange(edge,map);
            }
        }
    }
    
    /** processes the changes of the given node. */
    protected void processXNodeChange(XNode node, Map changes) {
        ModelNode mnode = node.getModelNode();
        if (changes != null) {
            Iterator iter = changes.keySet().iterator();
            while(iter.hasNext()) {
                Object key = iter.next();
                Dbg.pr("   changed: "+key);
                if (key.equals(GraphConstants.VALUE)) {
                    Object value = GraphConstants.getValue(changes);
                    mnode.setValue(value);
                    mnode.sync();
                }
            }
        }
        ModelContainerNode pnode = node.getModelParent(graph);
        try {
            mnode.setParent(pnode);
        } catch (ModelException me) {
            JOptionPane.showMessageDialog(graph,me.getMessage());
            disable();
            graph.getModel().remove(new Object[]{node});
            enable();
        }
    }
    
    /** processes the changes of the given edge. */
    protected void processXEdgeChange(XEdge edge, Map changes) {
        Dbg.pr("listener: changed edge: "+edge);
        ModelEdge medge = edge.getModelEdge();
        if (changes != null) {
            Iterator iter = changes.keySet().iterator();
            while(iter.hasNext()) {
                Object key = iter.next();
                Dbg.pr("   changed: "+key);
                if (key.equals(GraphConstants.VALUE)) {
                    Object value = GraphConstants.getValue(changes);
                    medge.setValue(value);
                    medge.sync();
                }
            }
        }
        try {
            ModelNode src = edge.getModelSource();
            medge.setSource(src);
        } catch (ModelException me) {
            JOptionPane.showConfirmDialog(graph,me.getMessage());
        }
        try {
            ModelNode trg = edge.getModelTarget();
            medge.setTarget(trg);
        } catch (ModelException me) {
            JOptionPane.showMessageDialog(graph,me.getMessage());
        }
        CellView cv = graph.getView().getMapping(edge,false);
        if (cv instanceof XGraphElementView)
            edge.updateViewData((XGraphElementView)cv);
    }
    
}
