/*
 * StepEdge.java
 *
 * Created on November 15, 2002, 1:32 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
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
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XEdgeView ev = new XEdgeView(this,graph,cm);
        ev.setUseMultiLineEditor(true);
        ev.setShowMultiLineLabel(true);
        ev.setFillLabelBackground(false);
        return ev;
    }
    
    
    
}
