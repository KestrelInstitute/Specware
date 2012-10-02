/*
 * DrawingModeAddNode.java
 *
 * Created on October 23, 2002, 3:31 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.ImageIcon;
import java.awt.event.*;

/**
 * @author  ma
 */
public class DrawingModeBasic extends DrawingModeWithMarqueeHandler {

    protected String id;
    
    /** Creates a new instance of DrawingModeAddNode */
    public DrawingModeBasic() {
        super();
        id = "Basic";
    }
    
    public void enter(XGraphDisplay graph) {
        super.enter(graph);
    }
    
    public void exit(XGraphDisplay graph) {
        super.exit(graph);
    }
    
    public String getMenuString() {
        return "Edit/Select";
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.edit24Icon;
    }

    public String getId() {
        return id;
    }
    
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        //Dbg.pr("creating new mhandler for mode basic...");
        return new MarqueeHandler(graph);
    }
    
    protected class MarqueeHandler extends XMarqueeHandler {
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
        }
        
    }

}
