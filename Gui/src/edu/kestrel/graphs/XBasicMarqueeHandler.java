/*
 * XMarqueeHandler.java
 *
 * Created on October 23, 2002, 4:28 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.util.Map;
import java.awt.event.*;
import java.awt.*;

/**
 * The base class for all marquee handlers used in the GUI . It introduces a field for the XGraphDisplay
 * representing the "owner" of the marquee handler.
 * @author  ma
 */
public abstract class XBasicMarqueeHandler extends BasicMarqueeHandler implements java.io.Serializable {
    
    protected XGraphDisplay graph;
    
    /** Creates a new instance of XMarqueeHandler */
    
    public XBasicMarqueeHandler(XGraphDisplay graph) {
        this.graph = graph;
    }
    
    /** convenience method to determine which mouse button has been pressed. */
    protected int getMouseButton(MouseEvent e) {
        if (e == null) return 0;
        return
        ((e.getModifiers() & InputEvent.BUTTON3_MASK) == InputEvent.BUTTON3_MASK?3:
            (e.getModifiers() & InputEvent.BUTTON2_MASK) == InputEvent.BUTTON2_MASK?2:
                (e.getModifiers() & InputEvent.BUTTON1_MASK) == InputEvent.BUTTON1_MASK?1:0);
    }
    
    
    /** convenience method to convert a mouse event's coordinates according to the
     * current scale (in place conversion!) */
    protected MouseEvent fromScreenSnap(MouseEvent e0) {
        Point p = graph.snap(graph.fromScreen(new Point(e0.getX(),e0.getY())));
        MouseEvent e = new MouseEvent(e0.getComponent(), e0.getID(), e0.getWhen(), e0.getModifiers(),
        p.x, p.y, e0.getClickCount(), e0.isPopupTrigger());
        return e;
    }
    
    protected void highlightPort(MouseEvent e0) {
        MouseEvent e = fromScreenSnap(e0);
        //graph.updateViews(graph.getView().getAllDescendants(graph.getView().getRoots()));
        try {
            PortView pv = graph.getPortViewAt(e.getX(),e.getY());
            if (pv == null) {
                graph.unsetHighlightedPortView();
            } else {
                Map map = pv.getParentView().getAttributes();
                if (GraphConstants.isVisible(map))
                    graph.setHighlightedPortView(pv);
                else
                    graph.unsetHighlightedPortView();
            }
            graph.repaint();
        } catch (Exception e1) {
            System.err.println("uncaught exception: "+e1.getMessage());
            e1.printStackTrace();
        }
        //Graphics g = graph.getGraphics();
        //graph.getUI().paintPorts(g, new PortView[]{pv});
        //graph.getUI().paintCell(g, pv, graph.toScreen(pv.getBounds()),  true);
        //graph.repaint();
    }
    
    private void showAttribsOfCellUnderMouse(MouseEvent e0) {
        MouseEvent e = fromScreenSnap(e0);
        Object cell = graph.getFirstCellForLocation(e.getX(),e.getY());
        if (cell != null) {
            if (cell instanceof GraphCell) {
                GraphCell c = (GraphCell) cell;
                XGraphDisplay.showAttributes(c);
                CellView cv = graph.getView().getMapping(c,false);
                if (cv != null)
                    XGraphDisplay.showAttributes(cv);
            }
        }
    }
    
    public void mouseMoved(MouseEvent e0) {
        //showAttribsOfCellUnderMouse(e0);
        highlightPort(e0);
        super.mouseMoved(e0);
    }
    
    public void mouseDragged(MouseEvent e0) {
        super.mouseDragged(e0);
    }
    
    public void mousePressed(MouseEvent e0) {
        super.mousePressed(e0);
    }
    
    public void mouseReleased(MouseEvent e0) {
        super.mouseReleased(e0);
    }
    
}
