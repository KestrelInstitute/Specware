/*
 * XStraightEdge.java
 *
 * Created on October 31, 2002, 1:55 AM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XStraightEdge extends XEdge {
    
    /** Creates a new instance of XStraightEdge */
    public XStraightEdge() {
        super();
    }
    
    public XStraightEdge(String name) {
        super(name);
    }
    
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setBendable(map,true);
        GraphConstants.setLineEnd(map, GraphConstants.TECHNICAL);
        //GraphConstants.setLineBegin(map,GraphConstants.DIAMOND);
        GraphConstants.setEndFill(map, true);
        viewMap.put(this, map);
        model.edit(null,viewMap,null,null);
        if (viewObject instanceof XEdgeView) {
            XEdgeView ev = (XEdgeView) viewObject;
            viewMap = new Hashtable();
            map = GraphConstants.createMap();
            ev.setFont(new Font("Courier", Font.PLAIN, 14),map);
            ev.setUseMultiLineEditor(true);
            viewMap.put(ev, map);
            graph.getView().edit(viewMap);
        }
    }
    
}
