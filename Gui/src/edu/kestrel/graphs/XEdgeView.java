/*
 * XEdgeView.java
 *
 * Created on October 23, 2002, 2:21 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.editor.*;
import com.jgraph.graph.*;
import com.jgraph.*;
import javax.swing.undo.*;
import javax.swing.*;
import java.awt.*;
import java.awt.geom.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class XEdgeView extends EdgeView implements XGraphElementView {
    
    protected CellViewRenderer renderer;
    protected boolean straightenEdgeActivated = true;
    
    private boolean straighteningEdge = false;
    
    private java.util.List savedPoints = null;
    
    protected XEdge edge = null;
    
    protected JPopupMenu popupMenu;
    protected Point popupMenuEventPoint = null;
    protected JMenuItem addRemovePointMenuItem;
    
    protected boolean useMultiLineEditor = false;
    protected boolean showMultiLineLabel = false;
    protected boolean fillLabelBackground = true;
    
    protected XGraphCellEditor xcellEditor;
    
    public final static int NO_INDEX = -2;
    
    /** Creates a new instance of XEdgeView */
    public XEdgeView(XEdge edge, XGraphDisplay graph, CellMapper cm) {
        super(edge,graph,cm);
        this.edge = edge;
        this.graph = graph;
        initPopupMenu();
        this.xcellEditor = null; // will be initialized on first use
        //setFont(new Font("Courier",Font.PLAIN,12));
        //System.out.println("XedgeView created.");
        //straightenEdge();
        setRenderer(new XEdgeRenderer(this));
    }
    
    public GraphCellEditor getEditor() {
        if (useMultiLineEditor) {
            if (xcellEditor == null) {
                xcellEditor = new XGraphCellEditor((XGraphDisplay)graph,edge,this);
                Font f = GraphConstants.getFont(getAttributes());
                xcellEditor.setFont(f);
            }
            return xcellEditor;
        } else {
            return super.getEditor();
        }
    }
    
    
    public CellViewRenderer getRenderer() {
        return renderer;
    }
    
    protected void setRenderer(CellViewRenderer r) {
        this.renderer = r;
    }
    
    protected void translateTextBounds(int dx, int dy) {
        if (isShowMultiLineLabel())
            if (getRenderer() instanceof XEdgeRenderer) {
                //Dbg.pr("translating edge text bounds...");
                ((XEdgeRenderer)getRenderer()).translateTextBounds(dx,dy);
            }
    }
    
    /** sets the font used for the label text. */
    public void setFont(Font f) {
        viewFont = f;
        if (xcellEditor != null)
            xcellEditor.setFont(f);
    }
    
    /** sets the font used for the label text; this method can be used in the context
     * of a view edit, where the <code>map</code> argument is used as a view attribute map.
     */
    public void setFont(Font f, Map map) {
        setFont(f);
        GraphConstants.setFontName(map,f.getFamily());
        GraphConstants.setFontSize(map,f.getSize());
        GraphConstants.setFontStyle(map,f.getStyle());
    }
    
    /** sets whether or not to use a multi-line editor for editing the edge's label.
     * @param useit true means use a multi-line editor, false means use a single line editor
     */
    public void setUseMultiLineEditor(boolean useit) {
        useMultiLineEditor = useit;
    }
    
    /** sets whether or not the label should be shown as a multi-line text.
     * @param true means show the label in multiple lines, if it consists of multiple lines, otherwise paste
     * all lines together and show it on a single line. This option only affects edges with labels consisting
     * of multiple lines.
     */
    public void setShowMultiLineLabel(boolean showit) {
        showMultiLineLabel = showit;
    }
    
    /** returns whether or not the label should be displayed as multi-line object. If not, the label is
     * shown on a single line.
     */
    public boolean isShowMultiLineLabel() {
        return showMultiLineLabel;
    }
    
    /** sets the flag that determines whether or not the area behind the edge label will be filled with the
     * background color of the graph; if not the line might "strike through" the label. This flag is only active, if
     * multi-line labels are also activated.
     */
    public void setFillLabelBackground(boolean fillit) {
        fillLabelBackground = fillit;
    }
    
    /** returns whether the background of the edge's label is filled with the background color of the graph.
     */
    public boolean isFillLabelBackground() {
        return fillLabelBackground;
    }
    
    protected void initPopupMenu() {
        popupMenu = new XGraphElementPopupMenu(graph,this);
        addRemovePointMenuItem = new JMenuItem("remove point");
        addRemovePointMenuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (popupMenuEventPoint != null) {
                    graph.getSelectionModel().addSelectionCell(edge);
                    addOrRemovePoint(popupMenuEventPoint);
                }
            }}
        );
        popupMenu.add(addRemovePointMenuItem,0);
        if (Dbg.isDebug()) {
            // debug entries
            JMenuItem menuItem = new JMenuItem("select source node");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XNode srcNode = edge.getSourceNode();
                    graph.getSelectionModel().setSelectionCell(srcNode);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("select target node");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XNode srcNode = edge.getTargetNode();
                    graph.getSelectionModel().setSelectionCell(srcNode);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("straighten edge");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XEdgeView.this.straightenEdge();
                }
            });
            popupMenu.add(menuItem);
        }
    }
    
    protected boolean isTemporaryView = false;
    
    public void setTemporaryView(boolean b) {
        isTemporaryView = b;
    }
    
    public boolean isTemporaryView() {
        return isTemporaryView;
    }
    
    public XGraphElement getGraphElement() {
        return (XGraphElement) getCell();
    }
    
    /** the font to be used for this edge. */
    protected Font viewFont;
    
    public Font getFont() {
        return viewFont;
    }
    
    
    
    public void delete(boolean interactive) {
        if (interactive) {
            int anws = JOptionPane.showConfirmDialog(graph, "Do you really want to delete this edge?", "Delete?", JOptionPane.OK_CANCEL_OPTION);
            if (anws != JOptionPane.YES_OPTION) return;
        }
        edge.remove(graph.getModel());
    }
    
    public void edit() {
        graph.startEditingAtCell(getCell());
    }
    
    
    
    public void showPopupMenu(Component c, int x, int y) {
        if (popupMenu == null) return;
        popupMenuEventPoint = new Point(x,y);
        if (getPointIndexAt(popupMenuEventPoint) == NO_INDEX)
            addRemovePointMenuItem.setText("add point");
        else
            addRemovePointMenuItem.setText("remove point");
        popupMenu.show(c,x,y);
    }
    
    /** adds a new point to the edge at point p, which is assumed to be in screen coordinates.
     **/
    public void addPoint(Point p0) {
        int s = graph.getSnapSize();
        int x = p0.x, y = p0.y;
        int index = NO_INDEX;
        Rectangle rect = graph.fromScreen(new Rectangle(x-s, y-s, 2*s, 2*s));
        if (intersects(graph.getGraphics(), rect)) {
            Point point = graph.snap(new Point(p0));
            double min = Double.MAX_VALUE, dist = 0;
            for (int i = 0; i < getPointCount()-1; i++) {
                Point p = getPoint(i);
                Point p1 = getPoint(i+1);
                dist = new Line2D.Double(p, p1).ptLineDistSq(point);
                if (dist < min) {
                    min = dist;
                    index = i+1;
                }
            }
            if (index != NO_INDEX) {
                addPoint(index, point);
                ((XGraphDisplay)graph).setPointsOfEdge(edge, points);
                //reloadPoints(edge);
                //paint(graph.getGraphics());
            }
        }
    }
    
    public void removePoint(Point p0) {
        int index = getPointIndexAt(p0);
        if (index != NO_INDEX) {
            removePoint(index);
            ((XGraphDisplay)graph).setPointsOfEdge(edge, points);
        }
    }
    
    /** returns the index of the edge corner point that corresponds to the point on screen.
     * @return index of edge corner point or <code>NO_INDEX</code>, if pointOnScreen is not over an edge corner point.
     */
    public int getPointIndexAt(Point pointOnScreen) {
        int s = graph.getSnapSize();
        int x = pointOnScreen.x, y = pointOnScreen.y;
        int index = NO_INDEX;
        // Search control point
        for (int i = 0; i < getPointCount() && index == NO_INDEX; i++) {
            Point edgePoint = getPoint(i);
            Rectangle pointEnv = new Rectangle(edgePoint.x-s,edgePoint.y-s,2*s,2*s);
            if (pointEnv.contains(x, y))
                index = i;
        }
        return index;
    }
    
    protected void addOrRemovePoint(Point pointOnScreen) {
        if (getPointIndexAt(pointOnScreen) == NO_INDEX)
            addPoint(pointOnScreen);
        else
            removePoint(pointOnScreen);
    }
    
    /** adds an intermediate point to the edge, if the edge has at least two points.
     * @param index the index of the point to be added; index can range from 1 to (#points-1)
     * @param p the point to be added to the edge
     * @return true, if adding was successful, false otherwise
     */
    public boolean addIntermediatePoint(int index, Point p) {
        int pcnt = getPointCount();
        if (pcnt < 2) {
            Dbg.pr("could not add point; edge has less than 2 points.");
            return false;
        }
        if ((index >= 1) && (index <= (pcnt-1))) {
            try {
                addPoint(index,p);
                return true;
            } catch (Exception e) {
                return false;
            }
        }
        return false;
    }
    
    /** adds intermediate points to the edge starting from the given index.
     */
    public void addIntermediatePoints(int index, Point[] points) {
        if (points == null)
            return;
        int index0 = index;
        for(int i=0;i<points.length;i++) {
            if (addIntermediatePoint(index0,points[i]))
                index0++;
        }
    }
    
    /** adds intermediate points at index 1
     */
    public void addIntermediatePoints(Point[] points) {
        addIntermediatePoints(1,points);
    }
    
    public void refresh(boolean b) {
        //System.out.println("refreshing edge..."+b);
        super.refresh(b);
        straightenEdge();
    }
    
    public void update() {
        super.update();
        if (edge != null) {
            //Dbg.pr2("updating edge "+edge+", isDetached()="+edge.isDetached()+"...");
            if (!edge.isDetached()) {
                moveInnerPointsAfterUpdate();
                //straightenEdge();
                setSavedPoints();
            }
            //else System.out.println("skipping moving inner point, because edge is detached.");
        }
        if (edge != null)
            edge.updateViewData(this);
    }
    
    
    /** calls the super method and <code>setSavePoints()</code>.
     */
    public void translate(int dx, int dy) {
        super.translate(dx,dy);
        setSavedPoints();
    }
    
    /** saves the current points list into an internal variable which is used during the next update
     * to move inner points correctly.
     */
    public void setSavedPoints() {
        savedPoints = portViewsToPoints(points);
        Dbg.pr2("setSavedPoints("+edge+"): "+savedPoints);
    }
    
    /** moves the inner points of the edge, if the source PortView and the target PortView have been
     * translated with the same (dx,dy). This method assumes, that the new point list is stored in the <code>points</code> field of this view.
     * This method is necessary, because otherwise edges connecting child nodes
     * of a container would not be updated correctly.
     */
    protected void moveInnerPointsAfterUpdate() {
        if (points == null || savedPoints == null) return;
        int lenOld = savedPoints.size();
        int lenNew = points.size();
        if (lenOld != lenNew)
            // something else is going on, not just a simple move...
            return;
        if (lenOld < 2) return;
        Dbg.pr2("checking whether inner points must be moved...");
        if (innerPointsHaveChanged()) {
            if (Dbg.isDebug2()) {
                java.util.List oldp = portViewsToPoints(savedPoints);
                java.util.List newp = portViewsToPoints(points);
                //Dbg.pr2("  old: "+oldp);
                //Dbg.pr2("  new: "+newp);
                Dbg.showPoints(graph.getGraphics(),oldp,Color.gray);
                Dbg.showPoints(graph.getGraphics(),newp,Color.green);
            }
            return;
        }
        // first and last points must be PortViews before and after
        Point[] pointsOld = new Point[] {(Point)savedPoints.get(0),(Point)savedPoints.get(lenOld-1)};
        Object[] objNew = new Object[] {points.get(0),points.get(lenNew-1)};
        Point[] pointsNew = new Point[2];
        for(int i=0;i<2;i++) {
            if (objNew[i] instanceof PortView) {
                pointsNew[i] = portViewToPoint((PortView) objNew[i]);
            } else return;
        }
        Dbg.pr2("  checking move distance...");
        // check whether the start and end points have moved the same distance in x and y direction
        int dxStart = pointsNew[0].x - pointsOld[0].x;
        int dyStart = pointsNew[0].y - pointsOld[0].y;
        int dxEnd = pointsNew[1].x - pointsOld[1].x;
        int dyEnd = pointsNew[1].y - pointsOld[1].y;
        Dbg.pr2("  dxStart="+dxStart+", dxEnd="+dxEnd+", dyStart="+dyStart+", dyEnd="+dyEnd);
        if (dxStart == dxEnd && dyStart == dyEnd && ((dxStart != 0) || (dyStart != 0))) {
            Dbg.pr2("inner point(s) of edge "+edge+" will be moved...");
            // translate the edge points (only inner points will be translated)
            translate(dxStart, dyStart);
            translateTextBounds(dxStart,dyStart);
        }
        else if (dxStart != 0 || dyStart != 0) {
            if (Dbg.isDebug2()) {
                Graphics g = graph.getGraphics();
                Dbg.showPoint(g,graph.toScreen(pointsOld[0]),Color.gray);
                Dbg.showPoint(g,graph.toScreen(pointsOld[1]),Color.gray);
                Dbg.showPoint(g,graph.toScreen(pointsNew[0]),Color.green);
                Dbg.showPoint(g,graph.toScreen(pointsNew[1]),Color.green);
                BufferedReader bs = new BufferedReader(new InputStreamReader(System.in));
                //try {
                //    Dbg.pr2("press enter");
                //    System.in.read();
                //} catch (IOException ee) {}
            }
        }
        
    }
    
    /** checks whether the inner points of the saved and the current points have changed */
    private boolean innerPointsHaveChanged() {
        int lenOld = savedPoints.size();
        int lenNew = points.size();
        if (lenOld != lenNew) return true;
        if (lenOld<3) return false;
        boolean res = false;
        for(int i=1;i<lenOld-1;i++) {
            Point sp = (Point) savedPoints.get(i);
            Point cp = (Point) points.get(i);
            if (!sp.equals(cp)) {
                if (Dbg.isDebug2()) {
                    Dbg.pr2("  inner points have moved, no translation.");
                    Dbg.pr2("  point "+i+": dx="+(sp.x-cp.x)+", dy="+(sp.y-cp.y));
                    res = true;
                } else
                    return true;
            }
        }
        return res;
    }
    
    /** helper class used be straightenEdge */
    private class PointInfo {
        int[] coord;
        boolean[] canBeChanged;
        
        public PointInfo(int x, int y, boolean xCanBeChanged, boolean yCanBeChanged) {
            this.coord = new int[2];
            this.canBeChanged = new boolean[2];
            this.coord[0] = x;
            this.coord[1] = y;
            this.canBeChanged[0] = xCanBeChanged;
            this.canBeChanged[1] = yCanBeChanged;
        }
        
        public String toString() {
            String res = "";
            String sep = "[";
            for(int i=0;i<coord.length;i++) {
                String xstr = String.valueOf(coord[i]);
                String cstr = (canBeChanged[i]?"*":"");
                res += sep+xstr+cstr;
                sep = ",";
            }
            return res+"]";
        }
    }
    
    protected boolean isStraigthenOk() {
        if (straighteningEdge) return false;
        Map map = getAttributes();
        int linestyle = GraphConstants.getLineStyle(map);
        if ((linestyle == GraphConstants.QUADRATIC) || (linestyle == GraphConstants.BEZIER))
            return false;
        else
            return true;
    }
    
    /** maximal correction distance used in the straightening function. */
    protected int maxCorrection = 20;
    private Object firstPoint, lastPoint;
    
    /** tries to straighten the edge, i.e. adjust the coordinates of the inner points so that they
     * align with their neighboured points. Adjustment is only done, if the difference of the old
     * and the new coordinate would not be greater than <code>maxCorrection</code> (default: 20) */
    public void straightenEdge() {
        if (!straightenEdgeActivated) return;
        if (!isStraigthenOk()) return;
        if (edge.isDetached()) return;
        if (((XGraphDisplay)graph).isReattaching()) return;
        straighteningEdge = true;
        Dbg.pr2("straightening edge...");
        Map m = getAttributes();
        //List points = GraphConstants.getPoints(m);
        if (points == null) {
            Dbg.pr2("no points found?!");
            straighteningEdge = false;
            return;
        }
        ArrayList pointInfos = portViewsToPointInfos(points);
        //System.out.println("point infos: "+pointInfos);
        int l = pointInfos.size();
        if (l<=2) {
            //System.out.println("to few points to straighten the edge.");
            straighteningEdge = false;
            return;
        }
        boolean somethingHasChanged = false;
        for(int i=1;i<(l-1);i++) {
            PointInfo prev = (PointInfo) pointInfos.get(i-1);
            PointInfo p = (PointInfo) pointInfos.get(i);
            PointInfo next = (PointInfo) pointInfos.get(i+1);
            for(int j=0;j<2;j++) { // coord[0] is x coord; coord[1] is y coord
                if (p.canBeChanged[j]) {
                    if (prev.coord[j] == p.coord[j]) {
                        prev.canBeChanged[j] = false;
                        p.canBeChanged[j] = false;
                    }
                    else if (next.coord[j] == p.coord[j]) {
                        next.canBeChanged[j] = false;
                        p.canBeChanged[j] = false;
                    }
                    else if (Math.abs(prev.coord[j]-p.coord[j]) < maxCorrection) {
                        //System.out.println("Point #"+i+": adjusting coord "+j+" to previous point.");
                        p.coord[j] = prev.coord[j];
                        prev.canBeChanged[j] = false;
                        p.canBeChanged[j] = false;
                        somethingHasChanged = true;
                    }
                    else if (Math.abs(next.coord[j]-p.coord[j]) < maxCorrection) {
                        //System.out.println("Point #"+i+": adjusting coord "+j+" to next point.");
                        p.coord[j] = next.coord[j];
                        next.canBeChanged[j] = false;
                        p.canBeChanged[j] = false;
                        somethingHasChanged = true;
                    }
                    else {
                        //System.out.println("Point #"+i+": no adjustment possible.");
                    }
                }
            }
        }
        if (!somethingHasChanged) {
            straighteningEdge = false;
            return;
        }
        // construct the new points list
        //ArrayList newpoints = new ArrayList();
        //newpoints.add(firstPoint);
        for(int i=1;i<(l-1);i++) {
            PointInfo pi = (PointInfo) pointInfos.get(i);
            //newpoints.add(new Point(p.coord[0],p.coord[1]));
            Point p = new Point(pi.coord[0],pi.coord[1]);
            setPoint(i, p);
        }
        //CellView[] views = new CellView[]{this};
        XGraphDisplay graph = (XGraphDisplay) getGraph();
        setSavedPoints();
        graph.setPointsOfEdge(edge,points);
        straighteningEdge = false;
    }
    
    /** auxiliary method used by starightenEdge to transform a port view to a point */
    private Point portViewToPoint(PortView pview) {
        Rectangle b = pview.getBounds();
        return new Point(b.x+b.width/2,b.y+b.height/2);
    }
    
    /** side effect: sets private variables firstPoint and lastPoint */
    
    private ArrayList portViewsToPointInfos(java.util.List points) {
        if (points == null) return null;
        firstPoint = null;
        lastPoint = null;
        ArrayList res = new ArrayList();
        Iterator iter = points.iterator();
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (firstPoint == null) firstPoint = obj;
            lastPoint = obj;
            if (obj instanceof PortView) {
                Point p = portViewToPoint((PortView)obj);
                res.add(new PointInfo(p.x,p.y,false,false));
            }
            else if (obj instanceof Point) {
                Point p = (Point) obj;
                res.add(new PointInfo(p.x,p.y,true,true));
            }
            else
                Dbg.pr("an instance of class \""+obj.getClass().getName()+
                " found in the points list!??");
            
        }
        return res;
    }
    
    private ArrayList portViewsToPoints(java.util.List points) {
        if (points == null) return null;
        ArrayList res = new ArrayList();
        Iterator iter = points.iterator();
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof PortView) {
                Point p = portViewToPoint((PortView)obj);
                res.add(new Point(p.x,p.y));
            }
            else if (obj instanceof Point) {
                Point p = (Point) obj;
                res.add(new Point(p.x,p.y));
            }
            else
                Dbg.pr("an instance of class \""+obj.getClass().getName()+
                " found in the points list!??");
            
        }
        return res;
    }
    
    protected class XEdgeRenderer extends EdgeRenderer implements CellViewRenderer {
        protected XEdgeView view;
        
        public XEdgeRenderer(XEdgeView view) {
            super();
            this.view = view;
        }
        
        protected Rectangle textb = null;
        
        public Rectangle getBounds(CellView cv) {
            Rectangle b = super.getBounds(cv);
            if (textb != null) {
                //t0.grow(2,2);
                Rectangle textb0 = new Rectangle(textb);
                return b.union(textb0);
                //b.grow(15,15);
            }
            return b;
        }
        
        public void computeTextBounds(Graphics g, String label) {
            //Dbg.pr("computing text bounds of edge...");
            Rectangle b = super.getBounds();
            Point lp = getLabelPosition(view);
            int bw = 2;
            int sh = metrics.getHeight();
            Dimension tdim = ((XGraphDisplay)graph).getStringDimension(g,label,bw,null,false,0,0);
            tdim.height += sh;
            int x = lp.x - tdim.width/2;
            int y = lp.y - tdim.height/2;
            textb = new Rectangle(x,y,tdim.width,tdim.height);
        }
        
        public void translateTextBounds(int dx, int dy) {
            if (textb != null)
                textb.translate(dx,dy);
        }
        
        /** specialized version of <code>paintLabel</code> for painting multi-line labels, if the flag
         * <code>setMultiLineUserObject</code> has been set for the view.
         */
        protected void paintLabel(Graphics g, String label) {
            if (!view.isShowMultiLineLabel()) {
                super.paintLabel(g,label);
                return;
            }
            g.setColor(fontColor);
            int bw = 2;
            /*
            Rectangle b = super.getBounds();
            Point lp = getLabelPosition(view);
            int bw = 2;
            int sh = metrics.getHeight();
            Dimension tdim = ((XGraphDisplay)graph).getStringDimension(g,label,bw,null,false,0,0);
            tdim.height += sh;
            int x = lp.x - tdim.width/2;
            int y = lp.y - tdim.height/2;
            // textb stored the text bounds relative to the bounds origin
            textb = new Rectangle(x-b.x,y-b.y,tdim.width,tdim.height);
             */
            computeTextBounds(g,label);
            if (view.isFillLabelBackground()) {
                g.setColor(graph.getBackground());
                g.fillRect(textb.x,textb.y,textb.width,textb.height);
                //g.setColor(Color.magenta);
                //g.drawRect(x,y, tdim.width,tdim.height);
            }
            g.setColor(fontColor);
            ((XGraphDisplay)graph).getStringDimension(g,label,bw,null,true,textb.x,textb.y);
            //g.setColor(Color.cyan);
            //g.drawRect(textb.x,textb.y,textb.width,textb.height);
        }
        
        /**
         * Returns the label bounds of the specified view in the given graph.
         */
        public Rectangle getLabelBounds(EdgeView view) {
            if (view instanceof XEdgeView)
                if (((XEdgeView) view).isShowMultiLineLabel()) {
                    return textb;
                }
            return super.getLabelBounds(view);
        }
        
        
        
        public void paint(Graphics g) {
            super.paint(g);
            //Rectangle b = new Rectangle(getBounds());
            //g.setColor(Color.cyan);
            //b.grow(-1,-1);
            //g.drawRect(b.x, b.y,b.width,b.height);
        }
        
    }
    
}
