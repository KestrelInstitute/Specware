/*
 * StepEdge.java
 *
 * Created on November 15, 2002, 1:32 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.especs.graphs.editor.*;
import edu.kestrel.especs.lang.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.editor.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class StepEdge extends XStraightEdge {
    
    /** Creates a new instance of StepEdge */
    public StepEdge() {
        super();
        setCollapseLabel(true);
    }
    
    public StepEdge(String name) {
        super(name);
        setCollapseLabel(true);
    }
    
    public ModelEdge createModelEdge() {
        return new StepModelEdge();
    }
    
    
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        super.insertHook(graph,viewObject);
        if (viewObject instanceof XEdgeView) {
            XEdgeView ev = (XEdgeView) viewObject;
            Map viewMap = new Hashtable();
            Map map = GraphConstants.createMap();
            ev.setFont(new Font("Courier", Font.PLAIN, 14),map);
            viewMap.put(ev, map);
            graph.getView().edit(viewMap);
        }
    }
    
    public void initialConnectHook(XEdgeView ev) {
        ev.editInNewFrame();
    }
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XEdgeView ev = new XEdgeView(this,graph,cm) {
            protected void initPopupMenu() {
                super.initPopupMenu();
                popupMenu.removeMenuItem("edit");
                JMenuItem item = popupMenu.getMenuItem("edit in new frame");
                if (item != null) {
                    item.setText("edit");
                }
            }
        };
        ev.setUseMultiLineEditor(true);
        ev.setShowMultiLineLabel(true);
        ev.setFillLabelBackground(false);
        return ev;
    }
    
    public XElementEditor createEditorPane() {
        return new StepEditor(this);
    }
    
    protected StepModelEdge getStepModelEdge() {
        return (StepModelEdge)getModelEdge();
    }
    
    public String getCollapsedLabel(String fullLabel) {
        if (getStepModelEdge().getStepName() == null) return "";
        return getStepModelEdge().getStepName();
    }
    
    
    public String getStepName() {
        return getStepModelEdge().getStepName();
    }
    
    public void setStepName(String stepName) {
        getStepModelEdge().setStepName(stepName);
    }
    
    public String getStepParams() {
        return getStepModelEdge().getStepParams();
    }
    
    public void setStepParams(String params) {
        getStepModelEdge().setStepParams(params);
    }
    
    public void setConditionTerms(java.util.List conditionTerms) {
        getStepModelEdge().setConditionTerms(conditionTerms);
    }
    
    public java.util.List getConditionTerms() {
        return getStepModelEdge().getConditionTerms();
    }
    
    public void setUpdates(java.util.List updates) {
        getStepModelEdge().setUpdates(updates);
    }
    
    public java.util.List getUpdates() {
        return getStepModelEdge().getUpdates();
    }
    
    public boolean isDerived() {
        return getStepModelEdge().isDerived();
    }
    
}
