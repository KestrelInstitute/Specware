/*
 * XGraphView.java
 *
 * Created on October 31, 2002, 1:15 AM
 */

package edu.kestrel.graphs;

import com.jgraph.event.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class XGraphView extends GraphView {
    
    /** Creates a new instance of XGraphView */
    public XGraphView(XGraphModel m, XGraphDisplay graph) {
        super(m,graph);
        addObserver(graph);
    }
    
    /** calls super.getPorts() and throws away all <code>null</code> port views
     */
    public PortView[] getPorts() {
        //Dbg.pr("getPorts...");
        PortView[] pv = super.getPorts();
        ArrayList res = new ArrayList();
        int j = 0;
        for(int i=0;i<pv.length;i++) {
            if (pv[i] != null)
                res.add(pv[i]);
        }
        PortView[] newpv = new PortView[res.size()];
        res.toArray(newpv);
        return newpv;
    }
    
    private boolean inGroupTranslate = false;
    private ArrayList edgesToBeUpdated = null;
    
    /** see {@link #translateViewsInGroup(CellView[],int,int)}
     */
    
    public void startGroupTranslate() {
        Dbg.pr2("starting group translate...");
        inGroupTranslate = true;
        edgesToBeUpdated = new ArrayList();
    }

    /** see {@link #translateViewsInGroup(CellView[],int,int)}
     */
    public void endGroupTranslate() {
        Dbg.pr2("ending group translate...");
        inGroupTranslate = false;
        updatePorts();
        ArrayList processed = new ArrayList();
        if (edgesToBeUpdated != null) {
            Iterator iter = edgesToBeUpdated.iterator();
            while(iter.hasNext()) {
                Object obj = iter.next();
                if (!processed.contains(obj)) {
                    processed.add(obj);
                    if (obj instanceof XEdgeView) {
                        Dbg.pr("*** updating edge "+((XEdgeView)obj).getCell()+"...");
                        ((XEdgeView)obj).update();
                    }
                }
            }
        }
        if (Dbg.isDebug2()) {
            Dbg.pr2("group translate done; updated edges:");
            Iterator iter = processed.iterator();
            while(iter.hasNext()) {
                Object obj = iter.next();
                if (obj instanceof XEdgeView) {
                    Dbg.pr2("  "+((XEdgeView)obj).getCell());
                }
            }
        }
    }
    
    /** translates the views for (dx,dy) using <code>GraphView.translateViews()</code>;
     * if <code>startGroupTranslate()</code> has been invoked before, the connecting edges
     * of all node views contained in the views are collected to be updated when the group
     * translation is finished, which is signaled by calling <code>endGroupTranslate</code>.
     * This makes sure, that the edges are updated even if they aren't contained in the views
     * that are translated.
     */
    public void translateViewsInGroup(CellView[] views, int dx, int dy) {
        GraphView.translateViews(views,dx,dy);
        if (Dbg.isDebug()) {
            for (int i=0;i<views.length;i++) {
                Dbg.pr("translating view of "+views[i].getCell()+": ("+dx+","+dy+")");
                Dbg.pr("  bounds after translation: "+views[i].getBounds());
            }
        }
        if (inGroupTranslate) {
            // collect the edges that might require to be updated:
            for (int i=0;i<views.length;i++) {
                if (views[i] instanceof XNodeView) {
                    CellView[] edgeviews = ((XNodeView)views[i]).getConnectedEdgeViews();
                    for(int j=0;j<edgeviews.length;j++) {
                        Dbg.pr2("--> connected edge: "+edgeviews[j].getCell());
                        edgesToBeUpdated.add(edgeviews[j]);
                    }
                }
                if (views[i] instanceof XContainerView) {
                    CellView[] edgeviews = ((XContainerView)views[i]).getInnerEdgeViews();
                    for(int j=0;j<edgeviews.length;j++) {
                        Dbg.pr2("--> inner edge: "+edgeviews[j].getCell());
                        edgesToBeUpdated.add(edgeviews[j]);
                    }
                    edgeviews = ((XContainerView)views[i]).getInnerConnToOuterEdgeViews();
                    for(int j=0;j<edgeviews.length;j++) {
                        Dbg.pr2("--> inner to outer edge: "+edgeviews[j].getCell());
                        edgesToBeUpdated.add(edgeviews[j]);
                    }
                }
            }
        }
        else Dbg.pr("not in group translate.");
    }
    
    public CellView[] getAllDescendants_(CellView[] views) {
        Dbg.pr("getAllDescendants...");
        CellView[] sres = super.getAllDescendants(views);
        ArrayList res = new ArrayList();
        for(int i=0;i<sres.length;i++) {
            res.add(sres[i]);
            if (sres[i] != null)
                if (sres[i] instanceof XContainerView) {
                    XEdgeView[] edges = ((XContainerView)sres[i]).getInnerEdgeViews();
                    for(int j=0;j<edges.length;j++)
                        if (!res.contains(edges[j])) {
                            Dbg.pr("adding edge to descendant views...");
                            res.add(edges[j]);
                        }
                }
        }
        CellView[] rviews = new CellView[res.size()];
        res.toArray(rviews);
        return rviews;
    }
    
    /** returns all toplevel XNodeView instances.
     */
    public XNodeView[] getRootNodeViews() {
        CellView[] views = getRoots();
        ArrayList nv = new ArrayList();
        for(int i=0;i<views.length;i++) {
            if (views[i] instanceof XNodeView) {
                nv.add(views[i]);
            }
        }
        XNodeView[] res = new XNodeView[nv.size()];
        nv.toArray(res);
        return res;
    }
    
    /** returns all selected XNodeView instances.
     */
    public XNodeView[] getSelectedNodeViews(XGraphDisplay graph) {
        XNode[] snodes = graph.getSelectedNodes();
        CellView[] views = getMapping(snodes);
        ArrayList nv = new ArrayList();
        for(int i=0;i<views.length;i++) {
            if (views[i] instanceof XNodeView) {
                nv.add(views[i]);
            }
        }
        XNodeView[] res = new XNodeView[nv.size()];
        nv.toArray(res);
        return res;
    }
    
    public void updateAllPorts() {
        super.updatePorts();
    }
    
    
    public void graphChanged(GraphModelEvent.GraphModelChange event) {
        super.graphChanged(event);
        //Dbg.pr("in XGraphView: graphChanged.");
    }
    
}
