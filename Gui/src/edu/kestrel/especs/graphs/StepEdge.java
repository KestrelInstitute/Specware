/*
 * StepEdge.java
 *
 * Created on November 15, 2002, 1:32 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.especs.graphs.editor.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.editor.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class StepEdge extends XStraightEdge {
    
    protected String stepName;
    protected String stepParams;
    /** holds the condition given as list of conjuntive terms, element type: Term (see below) */
    protected java.util.List conditionTerms;
    
    /** holds the list of updates; element type: Term (see below) */
    protected java.util.List updates;
    
    /** inner class used to represent the constituents of the step's condition. */
    public static class Term {
        public String term;
        public boolean isReadonly = false;
        public Term(String term) {
            this.term = term;
        }
        public String toString() {
            return term;
        }
    }
    
    protected boolean isGeneratedFromImportedStep = false;
    
    /** Creates a new instance of StepEdge */
    public StepEdge() {
        super();
    }
    
    public StepEdge(String name) {
        super(name);
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
        ev.edit();
    }
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XEdgeView ev = new XEdgeView(this,graph,cm);
        ev.setUseMultiLineEditor(true);
        ev.setShowMultiLineLabel(true);
        ev.setFillLabelBackground(false);
        return ev;
    }
    
    public XElementEditor createEditorPane() {
        return new StepEditor(this);
    }
    
    public String getCollapsedLabel(String fullLabel) {
        if (stepName == null) return "";
        return stepName;
    }
    
    
    public String getStepName() {
        return stepName;
    }
    
    public void setStepName(String stepName) {
        this.stepName = stepName;
        refreshUserObject();
    }
    
    public String getStepParams() {
        return stepParams;
    }
    
    public void setStepParams(String params) {
        this.stepParams = stepParams;
        refreshUserObject();
    }
    
    public void setConditionTerms(java.util.List conditionTerms) {
        this.conditionTerms = conditionTerms;
        refreshUserObject();
    }
    
    public java.util.List getConditionTerms() {
        return conditionTerms;
    }
    
    public void setUpdates(java.util.List updates) {
        this.updates = updates;
        refreshUserObject();
    }
    
    public java.util.List getUpdates() {
        return updates;
    }
    
    protected void refreshUserObject() {
        StringBuffer buf = new StringBuffer();
        buf.append(getStepName()+":"+"\n");
        String sep = "";
        if (conditionTerms != null) {
            Iterator iter = conditionTerms.iterator();
            while(iter.hasNext()) {
                Term t = (Term) iter.next();
                buf.append(sep+" "+t.term+"\n");
                sep = "&";
            }
        }
        sep = "";
        if (updates != null) {
            Iterator iter = updates.iterator();
            while(iter.hasNext()) {
                Term t = (Term) iter.next();
                buf.append(sep+" "+t.term+"\n");
                sep = ",";
            }
        }
        setFullUserObject(buf.toString());
    }
    
}
