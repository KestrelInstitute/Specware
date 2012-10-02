/*
 * XGraphContext.java
 *
 * Created on November 4, 2002, 5:40 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class XGraphContext extends GraphContext {
    
    /** Creates a new instance of XGraphContext */
    public XGraphContext(XGraphDisplay graph, Object[] cells) {
        super(graph,cells);
        //System.out.println("xgraph context created.");
    }

    public CellView[] createTemporaryCellViews() {
        //Dbg.pr("creating temporary cell views...");
        CellView[] cellViews = new CellView[cells.length];
        for (int i = 0; i < cells.length; i++) {
            // Get View For Cell
            cellViews[i] = getMapping(cells[i], true);
            if (cellViews[i] instanceof XGraphElementView) {
                ((XGraphElementView)cellViews[i]).setTemporaryView(true);
                Dbg.pr("creating temporary view for "+cells[i]);
            }
            //if (Dbg.isDebug()) {
            //    CellView[] cvs = graphView.getMapping(new Object[]{cellViews[i]});
            //    Dbg.pr("cell has "+cvs.length+" views after creating temporary view.");
            //}
        }
        return cellViews;
    }
    
}
