/*
 * XGraphUI.java
 *
 * Created on November 3, 2002, 12:08 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.util.*;
import com.jgraph.graph.*;
import com.jgraph.plaf.basic.*;
import javax.swing.*;
import javax.swing.tree.*;
import java.util.*;
import java.awt.event.*;
import java.awt.dnd.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XGraphUI extends BasicGraphUI {
    
    /** flag set by the mouse handler signaling that the mouse is currently dragged. */
    protected boolean isMouseDragging;
    
    /** Creates a new instance of XGraphUI */
    public XGraphUI() {
        super();
        if (marquee == null) {
            Dbg.pr("XGraphUI: setting new XMarqueeHandler...");
            setMarquee(new XMarqueeHandler((XGraphDisplay)graph));
        }
    }
    
    protected MouseListener createMouseListener() {
        return new XGraphUI.MouseHandler();
    }
    /**
     * Update the handle using createHandle.
     */
    protected void updateHandle() {
        //System.out.println("updateHandle...");
        if (graphView != null) {
            Object[] cells = graphView.order(graph.getSelectionCells());
            if (cells != null && cells.length > 0) {
                if (graph instanceof XGraphDisplay)
                    handle = createHandle(new XGraphContext(((XGraphDisplay)graph), cells));
                else
                    handle = createHandle(new GraphContext(graph, cells));
            }
            else
                handle = null;
        }
    }
    
    public boolean isMouseDragging() {
        return isMouseDragging;
    }
    
    
    
    public class MouseHandler extends BasicGraphUI.MouseHandler {
        
        public MouseHandler() {
            super();
            //System.out.println("creating new mouse handler");
        }
        
        /** convenience method to convert a mouse event's coordinates according to the
         * current scale (in place conversion!) */
        protected MouseEvent fromScreenSnap(MouseEvent e0) {
            Point p = graph.snap(graph.fromScreen(new Point(e0.getX(),e0.getY())));
            MouseEvent e = new MouseEvent(e0.getComponent(), e0.getID(), e0.getWhen(), e0.getModifiers(),
            p.x, p.y, e0.getClickCount(), e0.isPopupTrigger());
            return e;
        }
        
        
        
        public void mousePressed(MouseEvent e0) {
            //System.out.println("mouse pressed!");
            if (e0.getClickCount() == 2) {
                MouseEvent e = fromScreenSnap(e0);
                Object cell = graph.getFirstCellForLocation(e.getX(),e.getY());
                if (cell != null)
                    if (cell instanceof XContainerNode) {
                        Dbg.pr2("double click over container");
                        XContainerView cview = ((XContainerNode)cell).getXContainerView(graph.getView());
                        cview.doubleClickAction();
                        e0.consume();
                        return;
                    }
            }
            super.mousePressed(e0);
            if (!e0.isConsumed()) {
                //Dbg.pr("event is not yet consumed...");
            }
        }
        
        public void mouseMoved(MouseEvent e) {
            super.mouseMoved(e);
        }
        
        public void mouseDragged(MouseEvent e) {
            //Dbg.pr("mouse released!");
            startMouseDragging(e);
            super.mouseDragged(e);
        }
        
        public void mouseReleased(MouseEvent e) {
            super.mouseReleased(e);
            endMouseDragging(e);
            //if (!e.isConsumed())
            //super.mouseReleased(e);
            //Dbg.pr("mouse released!");
        }
        
        protected boolean isMouseDragging = false;
        protected boolean draggingStartedAtSelectedCell = false;
        protected XNode[] selectedNodesWhileDragging;
        protected Point draggingStartPoint = null;
        
        protected void startMouseDragging(MouseEvent e0) {
            if (isMouseDragging) return;
            MouseEvent e = fromScreenSnap(e0);
            if (e0.isControlDown()) return;
            isMouseDragging = true;
            XGraphUI.this.isMouseDragging = true;
            draggingStartedAtSelectedCell = false;
            draggingStartPoint = e.getPoint();
            //collapseSelectedContainerNodes();
            selectedNodesWhileDragging = ((XGraphDisplay)graph).getSelectedNodes();
            ((XGraphDisplay)graph).setSelectionAlwaysWins(true);
            Object cell = graph.getFirstCellForLocation(e.getX(),e.getY());
            ((XGraphDisplay)graph).resetNextViewBehaviour();
            if (cell != null)
                if (graph.isCellSelected(cell)) {
                    draggingStartedAtSelectedCell = true;
                    Dbg.pr2("start dragging...");
                }
        }
        
        protected void endMouseDragging(MouseEvent e0) {
            if (!isMouseDragging) return;
            XGraphDisplay xgraph = (XGraphDisplay)graph;
            MouseEvent e = fromScreenSnap(e0);
            XNode[] selNodes = selectedNodesWhileDragging;
            if (selNodes.length > 0 && draggingStartedAtSelectedCell) {
                xgraph.setSelectionAlwaysWins(false);
                xgraph.setNextViewClass("edu.kestrel.graphs.XContainerView");
                // construct the array of container views representing the parents of the cell views
                ArrayList parentviews = new ArrayList();
                for(int i=0;i<selNodes.length;i++) {
                    CellView selview = graph.getView().getMapping(selNodes[i],false);
                    if (selview != null)
                        if (!parentviews.contains(selview))
                            parentviews.add(selview);
                    XContainerNode[] pnodes = selNodes[i].getAncestorNodes();
                    if (pnodes != null) {
                        CellView[] cv = xgraph.getView().getMapping(pnodes,false);
                        if (cv != null)
                            for(int j=0;j<cv.length;j++)
                                if (!parentviews.contains(cv[j]))
                                    parentviews.add(cv[j]);
                    }
                }
                CellView[] pviews = new CellView[parentviews.size()];
                parentviews.toArray(pviews);
                xgraph.setNextViewIgnoredViews(pviews);
                // re-parent nodes, if dropped over a container node
                Object cell = graph.getFirstCellForLocation(e.getX(),e.getY());
                xgraph.resetNextViewBehaviour();
                if (cell != null) {
                    if (cell instanceof XContainerNode) {
                        XContainerNode cntnode = (XContainerNode)cell;
                        Dbg.pr2("drop over container "+cntnode);
                        // check whether the container node itself is selected, if yes cancel everything...
                        boolean cntnodeIsAmongSelected = false;
                        for(int j=0;j<selNodes.length && !cntnodeIsAmongSelected;j++) {
                            if (selNodes[j].equals(cntnode))
                                cntnodeIsAmongSelected = true;
                            if (selNodes[j].isNodeDescendant(cntnode))
                                cntnodeIsAmongSelected = true;
                        }
                        if (!cntnodeIsAmongSelected) {
                            XContainerView cv = (XContainerView)graph.getView().getMapping(cntnode,false);
                            //Dbg.pr("drop over container node.");
                            XNodeView[] adoptedViews = cv.addChildNodes(selNodes,true);
                        }
                    }
                }
            }
            isMouseDragging = false;
            XGraphUI.this.isMouseDragging = false;
            Dbg.pr2("end dragging.");
        }
    }
    
    /**
     * Creates an instance of TransferHandler. Used for subclassers
     * to provide different TransferHandler.
     */
    protected TransferHandler createTransferHandler() {
        return new XGraphTransferHandler();
    }
    
    public CellHandle createHandle(GraphContext context) {
        if (context != null && !context.isEmpty() && graph.isEnabled())
            return new XRootHandle(context);
        return null;
    }
    
    
    
    /** overwrites the class in BasicGraphUI to install customized cut/copy actions.
     */
    public class XGraphTransferHandler extends BasicGraphUI.GraphTransferHandler {
        public XGraphTransferHandler() {
            super();
            Dbg.pr("XGraphTransferHandler created.");
        }
        
        public int getSourceActions(JComponent c) {
            Dbg.pr("getSourceActions called.");
            return NONE;
        }
        
    }
    
    private JFrame _f;
    
    public class XRootHandle extends RootHandle {
        
        private Rectangle contextBounds = null;
        private Rectangle imageBounds = null;
        
        private Image img;
        private java.util.List cellViews = null;
        private boolean overwriteOverlayDetermined = false;
        private boolean overwriteOverlay;
        
        public XRootHandle(GraphContext ctxt) {
            super(ctxt);
            reset();
        }
        
        /** determine whether we want to let this code be active or the super.overlay().
         */
        private boolean overwriteOverlay() {
            //if (overwriteOverlayDetermined) return overwriteOverlay;
            // check whether the cells consist solely of edges
            Object[] cells = context.getCells();
            boolean onlyEdges = true;
            for(int i=0;i<cells.length && onlyEdges;i++) {
                if (!(cells[i] instanceof Edge)) {
                    onlyEdges = false;
                }
            }
            overwriteOverlayDetermined = true;
            overwriteOverlay = (isMoving?!onlyEdges:false);
            return overwriteOverlay;
        }
        
        private void reset() {
            getContextBounds();
            getMoveImage();
        }
        
        public void overlay(Graphics g) {
            if (!overwriteOverlay()) {
                super.overlay(g);
                return;
            }
            //super.overlay(g);
            if (contextBounds == null) return;
            Graphics2D g2d = (Graphics2D)g;
            Rectangle b = new Rectangle(contextBounds);
            //b = context.getGraph().toScreen(b);
            int bw = (int) (Math.max(100,context.getGraph().getScale()*100));
            bw = (int) (Math.max(Math.abs(dx),Math.abs(dy))*context.getGraph().getScale());
            b.translate(dx,dy);
            b = context.getGraph().toScreen(b);
            ((XGraphDisplay)context.getGraph()).setOutlineBounds(b);
            Rectangle imgb = new Rectangle(imageBounds);
            ((XGraphDisplay)context.getGraph()).setMoveImage(img,imgb);
            ((XGraphDisplay)context.getGraph()).repaint(b.x-bw,b.y-bw,b.width+bw*2,b.height+bw*2);
        }
        
        private void getMoveImage() {
            try {
                Dbg.pr("generating move image...");
                Object[] cells = context.getCells();
                com.jgraph.JGraph graph = context.getGraph();
                int imgwidth = graph.getWidth();
                int imgheight = graph.getHeight();
                img = new java.awt.image.BufferedImage(imgwidth,imgheight,java.awt.image.BufferedImage.TYPE_INT_RGB);
                Graphics2D g2d = (Graphics2D) img.getGraphics();
                //g2d.scale(graph.getScale(),graph.getScale());
                Rectangle cliprect = new Rectangle(contextBounds);
                graph.toScreen(cliprect);
                g2d.setClip(cliprect.x, cliprect.y, cliprect.width, cliprect.height);
                g2d.setColor(graph.getBackground());
                g2d.fillRect(cliprect.x, cliprect.y, cliprect.width, cliprect.height);
                //for (int i=0;i<cells.length;i++) {
                //    CellView cv = context.getMapping(cells[i],true);
                //    if (cv != null) {
                //        graph.getUI().paintCell(g2d,cv, cv.getBounds(),false);
                //    }
                //}
                graph.getUI().paint(g2d,graph);
                imageBounds = new Rectangle(cliprect);
            } catch (Exception e) {/*ignore*/}
            Dbg.pr("generating move image done.");
            /*
            if (_f == null) {
                _f = new JFrame();
                _f.getContentPane().setLayout(new BorderLayout());
                _f.setSize(200,200);
            } else {
                _f.getContentPane().removeAll();
            }
            _f.getContentPane().add(new JButton(new ImageIcon(img)));
            _f.show();
             */
        }
        
        private Rectangle getContextBounds() {
            cellViews = new ArrayList();
            Object[] cells = context.getCells();
            Rectangle b = null;
            for(int i=0;i<cells.length;i++) {
                CellView cv = context.getMapping(cells[i],true);
                if (cv != null) {
                    cellViews.add(cv);
                    if (b == null)
                        b = new Rectangle(cv.getBounds());
                    else
                        b.add(cv.getBounds());
                }
            }
            if (overwriteOverlay()) {
                if (contextViews != null) {
                    for(int i=0;i<contextViews.length;i++) {
                        if (b == null)
                            b = new Rectangle(contextViews[i].getBounds());
                        else
                            b.add(contextViews[i].getBounds());
                    }
                }
            }
            contextBounds = b;
            return b;
        }
        
        private Point startPoint;
        private int dx,dy;
        
        public void mousePressed(MouseEvent e) {
            ((XGraphDisplay)context.getGraph()).setOutlineBounds(null);
            ((XGraphDisplay)context.getGraph()).setMoveImage(null,null);
            startPoint = context.getGraph().fromScreen(new Point(e.getPoint()));
            super.mousePressed(e);
        }
        
        public void mouseDragged(MouseEvent e) {
            if (startPoint != null) {
                //Point snapCurrent = graph.snap(new Point(e.getPoint()));
                //Point current = graph.toScreen(snapCurrent);
                //dx = current.x - start.x;
                //dy = current.y - start.y;
                Point p = context.getGraph().fromScreen(e.getPoint());
                dx = p.x - startPoint.x;
                dy = p.y - startPoint.y;
            }
            if (overwriteOverlay()) {
                overlay(graph.getGraphics());
            } else {
                super.mouseDragged(e);
            }
        }
        
        public void mouseReleased(MouseEvent event) {
            ((XGraphDisplay)context.getGraph()).setMoveImage(null,null);
            ((XGraphDisplay)context.getGraph()).setOutlineBounds(null);
            try {
                if (event != null && !event.isConsumed()) {
                    if (overwriteOverlay() && !event.getPoint().equals(start)) {
                        Dbg.pr("do the move...!");
                        XGraphDisplay graph = (XGraphDisplay)context.getGraph();
                        XGraphView gv = graph.getXGraphView();
                        CellView[] views = gv.getToplevelViews(context.getCells());
                        gv.startGroupTranslate();
                        gv.translateViewsInGroup(views,dx,dy);
                        gv.endGroupTranslate();
                        graph.repaint();
                        reset();
                    } else {
                        super.mouseReleased(event);
                    }
                }
            } catch (Exception ex) {
                /* ignore */
            }
        }
    }
    
}
