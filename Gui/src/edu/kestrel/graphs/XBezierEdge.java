/*
 * XBezierEdge.java
 *
 * Created on October 31, 2002, 2:02 AM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class XBezierEdge extends XEdge {
    
    /** Creates a new instance of XBezierEdge */
    public XBezierEdge() {
        super();
    }
    
    /** method for initializing the graph element, when it is inserted in an XGraphDisplay
     * with the given model.
     *
     */
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setBendable(map,true);
        GraphConstants.setLineStyle(map,GraphConstants.BEZIER);
        GraphConstants.setLineWidth(map,1);
        GraphConstants.setLineEnd(map, GraphConstants.TECHNICAL);
        //GraphConstants.setLineBegin(map,GraphConstants.DIAMOND);
        GraphConstants.setEndFill(map, true);
        viewMap.put(this, map);
        model.edit(null,viewMap,null,null);
    }
    
}
