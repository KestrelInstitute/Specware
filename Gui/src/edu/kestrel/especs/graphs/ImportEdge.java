/*
 * ImportEdge.java
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
public class ImportEdge extends XBezierEdge {
    
    /** Creates a new instance of StepEdge */
    public ImportEdge() {
        super();
        setUserObject("import");
    }

    public ModelEdge createModelEdge() {
        return new StepModelEdge();
    }
    
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        super.insertHook(graph,viewObject);
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setEditable(map,false);
        //GraphConstants.setValue(map,"import");
        GraphConstants.setDisconnectable(map,false);
        GraphConstants.setFontStyle(map,Font.BOLD);
        GraphConstants.setLineWidth(map,1);
        GraphConstants.setLineBegin(map,GraphConstants.DIAMOND);
        GraphConstants.setBeginFill(map, false);
        GraphConstants.setEndFill(map, true);
        viewMap.put(this, map);
        model.edit(null,viewMap,null,null);
    }
    
    public void cloneHook(XCloneManager mgr, Object orig) {
        super.cloneHook(mgr,orig);
        setUserObject("import");
    }
    
}
