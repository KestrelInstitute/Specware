package edu.kestrel.graphs;

import com.jgraph.graph.*;
import com.jgraph.JGraph;
import javax.swing.*;
import java.util.*;
import java.awt.geom.*;
import java.awt.event.*;
import java.awt.font.*;
import java.awt.*;

/** This class is a generic framework for node views that can be used to display different kinds of node shapes.
 * See the sub classes for possible extensions.
 */

public abstract class XNodeView extends VertexView implements XGraphElementView {
    
    protected CellViewRenderer renderer;
    public ViewOptions viewOptions;
    
    protected JPopupMenu popupMenu;
    
    private Rectangle parentBounds = null;
    protected XNode node = null;
    protected XContainerView parentNodeView = null;
    
    protected Dimension textDimension;
    
    protected double textScale = 1.0;
    
    protected Rectangle lastBounds;
    
    protected XNodeView(XNode node, XGraphDisplay graph, CellMapper cm) {
        super(node,graph,cm);
        viewOptions = new ViewOptions();
        this.node = node;
        initPopupMenu();
        if (node != null) {
            GraphConstants.setEditable(getAttributes(),node.isEditable());
        }
        //Dbg.pr("view for node "+node+" created.");
    }
    
    protected void initPopupMenu() {
        boolean isEditable = true;
        if (node != null)
            isEditable = node.isEditable();
        popupMenu = new XGraphElementPopupMenu(graph,this,isEditable);
        
        JMenuItem menuItem = new JMenuItem("clone");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                cloneView(50,50,false);
            }
        });
        popupMenu.add(menuItem);
        
        if (Dbg.isDebug()) {
            // debug entries:
            menuItem = new JMenuItem("select all edges");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XEdge[] edges = node.getEdges(XNode.INCOMING_AND_OUTGOING);
                    graph.getSelectionModel().setSelectionCells(edges);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("insert as root object");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    node.insertAsRootObject((XGraphDisplay)graph);
                    graph.setSelectionCell(node);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("show ports");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    Graphics g = graph.getGraphics();
                    g.setColor(Color.magenta);
                    PortView[] pviews = graph.getView().getPorts();
                    Dbg.pr("found "+pviews.length+" ports.");
                    Map pmap = new Hashtable();
                    for(int i=0;i<pviews.length;i++) {
                        CellView cv = pviews[i];
                        Object p = cv.getCell();
                        if (p instanceof DefaultPort) {
                            Object parent = ((DefaultPort)p).getParent();
                            if (parent != null) {
                                int cnt = 0;
                                if (pmap.containsKey(parent)) {
                                    cnt = ((Integer)pmap.get(parent)).intValue() + 1;
                                    pmap.remove(parent);
                                }
                                pmap.put(parent,new Integer(cnt));
                            }
                        }
                    }
                    Iterator iter = pmap.keySet().iterator();
                    while (iter.hasNext()) {
                        Object node = iter.next();
                        Dbg.pr("node "+node+": "+pmap.get(node)+" ports");
                    }
                    //try {Thread.sleep(300);} catch (Exception e0) {}
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
    
    public boolean hasTemporaryViewAncestor() {
        if (isTemporaryView()) return true;
        XContainerView pview = getParentNodeView();
        if (pview == null) return false;
        return pview.hasTemporaryViewAncestor();
    }
    
    /** the font to be used for this node. */
    protected Font viewFont;
    
    public void setFont(Font f) {
        viewFont = f;
    }
    
    public Font getFont() {
        return viewFont;
    }
    
    
    
    public void toBack() {
        graph.getView().toBack(new CellView[]{this});
    }
    
    public void edit() {
        graph.startEditingAtCell(getCell());
    }
    
    public void showPopupMenu(Component c, int x, int y) {
        initPopupMenu();
        if (popupMenu == null) return;
        popupMenu.show(c,x,y);
        //Dbg.pr(graph.getSelectionCount()+" elements selected...");
    }
    
    public void delete(boolean interactive) {
        if (interactive) {
            int anws = JOptionPane.showConfirmDialog(graph, "Do you want to delete node \""+node+"\" and all edges connected to it?", "Delete?", JOptionPane.OK_CANCEL_OPTION);
            if (anws != JOptionPane.YES_OPTION) return;
        }
        node.remove(graph.getModel());
    }
    
    public XGraphElement getGraphElement() {
        return (XGraphElement) getCell();
    }
    
    /** returns the views of the edges connected to this node. */
    public CellView[] getConnectedEdgeViews() {
        XEdge[] edges = node.getEdges(XNode.INCOMING_AND_OUTGOING);
        ArrayList viewsAL = new ArrayList();
        for(int i=0;i<edges.length;i++) {
            CellView cv = graph.getView().getMapping(edges[i],false);
            if (cv != null) {
                viewsAL.add(cv);
            }
        }
        CellView[] views = new CellView[viewsAL.size()];
        viewsAL.toArray(views);
        return views;
    }
    
    /** returns the view object of the parent node, if the associated node has
     * one that is an instance of XContainerView; returns null otherwise.
     */
    public XContainerView getParentNodeView() {
        XContainerNode pnode = node.getParentNode();
        if (pnode == null) return null;
        CellView cv = graph.getView().getMapping(pnode,false);
        if (cv == null) return null;
        if (cv instanceof XContainerView)
            return (XContainerView) cv;
        return null;
    }
    
    /** returns the bounds of the parent view, if one exists, null otherwise */
    public Rectangle getParentBounds() {
        XContainerView pview = getParentNodeView();
        if (pview == null) return null;
        return pview.getBounds();
    }
    
    public CellViewRenderer getRenderer() {
        return renderer;
    }
    
    public void doubleClickAction() {
        graph.startEditingAtCell(node);
    }
    
    protected void setRenderer(CellViewRenderer r) {
        this.renderer = r;
    }
    
    /** clones the view and the associated node and translates the new view for (dx,dy). */
    public XNodeView cloneView(int dx, int dy, boolean createReadOnlyClone) {
        XNodeView clonedView = null;
        Map cellMap = ((XGraphDisplay)graph).cloneCells(new Object[]{node},createReadOnlyClone);
        if (cellMap != null)
            if (cellMap.containsKey(node)) {
                Object obj = cellMap.get(node);
                CellView cv = graph.getView().getMapping(obj,false);
                if (cv != null) {
                    GraphView.translateViews(new CellView[]{cv},dx,dy);
                    if (cv instanceof XContainerView) {
                        ((XContainerView)cv).setBoundsToChildrenBounds();
                    }
                    graph.setSelectionCell(obj);
                    if (cv instanceof XNodeView) {
                        clonedView = (XNodeView)cv;
                    }
                }
            }
        return clonedView;
    }
    
    /** overrides the method in <code>AbstractCellView</code> to disable the distinction between leaf node and
     * non-leaf nodes.
     */
    public boolean intersects(Graphics g, Rectangle rect) {
        Rectangle bounds = getBounds();
        if (bounds != null)
            return bounds.intersects(rect);
        return false;
    }
    
    public boolean isVisible() {
        Map map = getAttributes();
        return GraphConstants.isVisible(map);
    }
    
    public Rectangle getLastBounds() {
        return lastBounds;
    }
    
    public Rectangle getBounds() {
        lastBounds = super.getBounds();
        if (node != null)
            node.setSavedBounds(lastBounds);
        return lastBounds;
    }
    
    public void update() {
        super.update();
        if (node != null)
            node.updateViewData(this);
    }
    
    /** sets the text dimensions of the view. */
    public void setTextDimension(Dimension textDimension) {
        this.textDimension = textDimension;
    }
    
    /** adjusts the bounds of the view to the text dimensions.
     * @return true, if the bounds have been changed, false otherwise
     */
    public boolean adjustBoundsToTextDimension(double scale) {
        if (viewOptions.getTextDisplayOption() != viewOptions.BOUNDS_ARE_ADJUSTED_TO_TEXT)
            return false;
        //Dbg.pr("adjustBoundstoTextDimension: scale="+scale);
        if (!isTemporaryView())
            if (textDimension != null) {
                int bw = 1;
                Rectangle b = getBounds();
                Rectangle oldbounds = new Rectangle(b);
                b = new Rectangle(b.x+bw,b.y+bw,(int)(textDimension.width*scale),(int)(textDimension.height*scale));
                b.grow(bw,bw);
                if (b.width < viewOptions.minimumWidth)
                    b.width = viewOptions.minimumWidth;
                if (b.height < viewOptions.minimumHeight)
                    b.height = viewOptions.minimumHeight;
                if (!viewOptions.getBoundsAreAdjustedExactlyToText()) {
                    if (oldbounds.width > b.width)
                        b.width = oldbounds.width;
                    if (oldbounds.height > b.height)
                        b.height = oldbounds.height;
                }
                setBounds(b);
                return !oldbounds.equals(b);
            }
        return false;
    }
    
    
    /** sets the text scale that is currently used by the node renderer.
     */
    public void setTextScale(double scale) {
        textScale = scale;
    }
    
    /** returns the text scale currently used by the node renderer of this view.
     */
    public double getTextScale() {
        return textScale;
    }
    
    /** contains a list of options, which can be used to customize the view
     **/
    public class ViewOptions implements java.io.Serializable {
        
        /** options controlling the relation between the surrounding shape and the text label, set
         * using method setTextDisplayOption():
         * <ul>
         * <li> <code>TEXT_SCALES_TO_BOUNDS</code>: the text will be scaled down, so that it fits into the bounds of
         * the node.
         * <li> <code>BOUNDS_ARE_ADJUSTED_TO_TEXT</code>: the bounds of the nodes are adjusted to the size of the text;
         * this is usually done for "text-dominant" node, like multi-line text nodes.
         * <li> <code>TEXT_IS_CUT</code>: The text is displayed without being scaled, but only upto the length, to which
         * it fits into the bounds of the node. This is the default.
         * </ul>
         */
        final public int TEXT_SCALES_TO_BOUNDS = 0;
        final public int BOUNDS_ARE_ADJUSTED_TO_TEXT = 1;
        final public int TEXT_IS_CUT = 2;
        
        /**
         * this flag is used, if the text display option is set to <code>BOUNDS_ARE_ADJUSTED_TO_TEXT</code>. If this flag is
         * true, it means that the bounds of the box are exactly the bounds of the text. If it is false, the bounds of the box
         * are at least the bounds of the text, meaning that the box may be bigger than the text.
         */
        boolean BOUNDS_ARE_EXACTLY_ADJUSTED_TO_TEXT = true;
        
        boolean useGradientPaint = false;
        Color gradientPaintTopLeftColor;
        Color gradientPaintBottomRightColor = null;
        boolean usePaint = true;
        boolean useSolidPaint = true;
        Color solidPaintColor = new Color(195,196,219);
        boolean useShadow = true;
        int shadowOffset = 2;
        Color shadowColor = new Color(80,80,80);
        boolean showText = true;
        Color textColor = Color.black;
        boolean useBorder = false;
        Color borderColor = Color.black;
        int borderWidth = 1;
        float fontSize = 14;
        int fontStyle = Font.BOLD;
        String fontName = null;
        int minimumWidth = 30;
        int minimumHeight = 30;
        int horizontalTextPosition = JLabel.CENTER; // or LEFT or RIGHT
        int verticalTextPosition = JLabel.CENTER; // or TOP or BOTTOM
        boolean callDefaultPaintMethod = false;
        int textDisplayOption = TEXT_IS_CUT;
        int internalBorderWidth = 20;
        
        /** whether or not to use paint for the view, i.e. whether it's filled with paint; default: true.
         * either a border or a paint must be used; if b is false it calls setUseBorder(true).
         */
        public void setUsePaint(boolean b) {
            usePaint = b;
            if (!b)
                setUseBorder(true);
        }
        
        /** sets the view option whether a gradient paint from topleft to bottomright should be used;
         * default: false
         */
        public void setUseGradientPaint(boolean b) {
            useGradientPaint = b;
        }
        
        /** if gradient paint is used, sets the "start" color for the top left corner of the view. */
        public void setGradientPaintTopLeftColor(Color col) {
            gradientPaintTopLeftColor = col;
        }
        
        /** if gradient paint is used, sets the "end" color for the bottom right corner of the view.
         * If not set, gradientTopLeftColor.brighter().brighter() is used. */
        public void setGradientPaintBottomRightColor(Color col) {
            gradientPaintBottomRightColor = col;
        }
        
        /** whether or not a solid paint shall be used for the view. */
        public void setUseSolidPaint(boolean b) {
            useSolidPaint = b;
        }
        
        /** if solid paint is used, sets its color. */
        public void setSolidPaintColor(Color col) {
            solidPaintColor = col;
        }
        
        /** whether or not shadow shall be used; default: true */
        public void setUseShadow(boolean b) {
            useShadow = b;
        }
        
        /** the offset of the shadow relative to the "foreground", default: 5 */
        public void setShadowOffset(int n) {
            shadowOffset = n;
        }
        
        /** the color used for the shadow; usually some gray color; default: grey80 */
        public void setShadowColor(Color col) {
            shadowColor = col;
        }
        
        /** whether or not the text of the node should be shown; default: true */
        public void setShowText(boolean b) {
            showText = b;
        }
        
        /** sets the color to be used for the text inside the view; default: black */
        public void setTextColor(Color col) {
            textColor = col;
        }
        
        /** sets the font name, default: default system font. */
        public void setFontName(String n) {
            fontName = n;
        }
        
        /** sets the font size: default: default system font size */
        public void setFontSize(float s) {
            fontSize = s;
        }
        
        /** sets the font style; style is usually a constant in class Font, e.g. Font.BOLD;
         * default: default system font style. */
        public void setFontStyle(int style) {
            fontStyle = style;
        }
        
        /** whether or not to draw a border; default false.
         * either a border or a paint must be used; if b is false it calls setUsePaint(true).
         */
        public void setUseBorder(boolean b) {
            useBorder = b;
            if (!b)
                setUsePaint(true);
        }
        
        /** sets the color of the border; default black */
        public void setBorderColor(Color col) {
            borderColor = col;
        }
        
        /** sets the width of the border */
        public void setBorderWidth(int n) {
            borderWidth = n;
        }
        
        /** sets the minimum dimension of the view; default (30,30). */
        public void setMinimumDimension(int width, int height) {
            minimumWidth = width;
            minimumHeight = height;
        }
        
        /** sets the horizontal text position; can be one of JLabel.CENTER, JLabel.LEFT, or JLabel.RIGHT;
         * default: JLabel.CENTER
         */
        public void setHorizontalTextPosition(int pos) {
            horizontalTextPosition = pos;
        }
        
        /** sets the vertical text position; can be one of JLabel.CENTER, JLabel.TOP, or JLabel.BOTTOM;
         * default: JLabel.CENTER
         */
        public void setVerticalTextPosition(int pos) {
            verticalTextPosition = pos;
        }
        
        /** sets the flag that determined, whether the <code>paint</code> method of the super class --
         * <code>com.jgraph.graph.VertexRenderer</code> should be called at the end of the paint method or not;
         * default: false
         */
        public void setCallDefaultPaintMethod(boolean callit) {
            callDefaultPaintMethod = callit;
        }
        
        /** sets the textDisplayOption; see the documentation of the fields of this class for possible values.
         */
        public void setTextDisplayOption(int option) {
            textDisplayOption = option;
        }
        
        public int getTextDisplayOption() {
            return textDisplayOption;
        }
        
        /** set the flag controlling the behaviour, if the text display option is set to BOUNDS_ARE_ADJUSTED_TO_TEXT.
         */
        public void setBoundsAreAdjustedExactlyToText(boolean b) {
            BOUNDS_ARE_EXACTLY_ADJUSTED_TO_TEXT = b;
        }
        
        public boolean getBoundsAreAdjustedExactlyToText() {
            return BOUNDS_ARE_EXACTLY_ADJUSTED_TO_TEXT;
        }
        
        /** sets the internal border width that is used for container nodes when they are expanded; default 20.
         */
        public void setInternalBorderWidth(int bw) {
            internalBorderWidth = bw;
        }
        
    }
    
    /** inner class implementing the default renderer for leaf nodes. it uses the options defined
     * by the viewOptions in the corresponding view object. Sub classes defining customized view
     * may also subclass this inner class. (see XBoxView and XEllipseView for examples. */
    
    protected abstract class XNodeRenderer extends VertexRenderer implements CellViewRenderer {
        protected XNodeView view;
        
        public XNodeRenderer(XNodeView view) {
            super();
            this.view = view;
        }
        
        protected int getShadowOffset() {
            if (viewOptions.useShadow)
                return viewOptions.shadowOffset;
            else
                return 0;
        }
        protected Color getShadowColor() {
            return viewOptions.shadowColor;
        }
        protected Paint getPaint(Rectangle b) {
            boolean editable = GraphConstants.isEditable(view.getAttributes());
            if (viewOptions.useGradientPaint) {
                Color col1 = viewOptions.gradientPaintTopLeftColor;
                if (col1 == null) {
                    if (editable)
                        return viewOptions.solidPaintColor;
                    else
                        return viewOptions.solidPaintColor.darker();
                }
                if (!editable)
                    col1 = col1.darker();
                Color col2 = viewOptions.gradientPaintBottomRightColor;
                if (col2 == null) {
                    col2 = col1.brighter().brighter();
                } else {
                    if (!editable)
                        col2 = col2.darker();
                }
                int x0 = b.x, y0 = b.y;
                int w = b.width, h = b.height;
                GradientPaint gp = new GradientPaint(0,0,col1,w,h,col2);
                return gp;
            } else {
                Color col = viewOptions.solidPaintColor;
                if (!editable)
                    col = col.darker();
                return col;
            }
        }
        
        protected Color getBorderColor() {
            return viewOptions.borderColor;
        }
        
        protected Color getTextColor() {
            return viewOptions.textColor;
        }
        
        protected abstract Shape getShape(RectangularShape bounds);
        
        protected int getMinimumWidth() {
            return viewOptions.minimumWidth;
        }
        protected int getMinimumHeight() {
            return viewOptions.minimumHeight;
        }
        
        protected boolean localTransformInstalled = false;
        protected AffineTransform localTransform;
        protected AffineTransform savedTransform;
        
        /** saves the current scale and installs an additional scale.
         */
        protected void pushLocalScale(Graphics g, double scaleFactor) {
            if (localTransformInstalled) return;
            Graphics2D g2d = (Graphics2D) g;
            savedTransform = g2d.getTransform();
            localTransform = new AffineTransform(savedTransform);
            AffineTransform stf = new AffineTransform();
            stf.setToScale(scaleFactor, scaleFactor);
            localTransform.concatenate(stf);
            g2d.setTransform(localTransform);
            localTransformInstalled = true;
        }
        
        /** reinstalls the previous scale. */
        protected void popLocalScale(Graphics g) {
            if (savedTransform != null) {
                Graphics2D g2d = (Graphics2D) g;
                g2d.setTransform(savedTransform);
            }
            localTransformInstalled = false;
        }
        
        /** returns the label position of the node using the HORIZONTAL_TEXT_POSITION and VERTICAL_TEXT_POSITION
         * attributes of the view. The position is given relative to the node's bounds and returns the coordinates
         * of the top-left corner of the text bounds using the text dimensions given as argument.
         */
        protected Point getLabelPosition(Dimension tdim) {
            Rectangle b = view.getBounds();
            if (b == null) return null;
            int hpos = viewOptions.horizontalTextPosition;
            int vpos = viewOptions.verticalTextPosition;
            int x, y, shoff = 0;
            if (viewOptions.useShadow) {
                shoff = viewOptions.shadowOffset;
            }
            if (hpos == JLabel.LEFT) x = 0;//tdim.width/2;
            else if (hpos == JLabel.RIGHT) x = b.width-tdim.width-shoff;
            else x = (b.width/2)-tdim.width/2-shoff;
            if (vpos == JLabel.TOP) y = 0;//tdim.height/2;
            else if(vpos == JLabel.BOTTOM) y = b.height-tdim.height-shoff;
            else y = (b.height/2)-tdim.height/2-shoff;
            return new Point(x,y);
        }
        
        /** computes the scale factor that has to be applied to tdim in order to fill out the bounds without aspect change.
         */
        protected double getScaleForTextLabel(Rectangle bounds, Dimension tdim) {
            if (viewOptions.getTextDisplayOption() == viewOptions.TEXT_SCALES_TO_BOUNDS) {
                int w0 = bounds.width;
                int h0 = bounds.height;
                int w1 = tdim.width;
                int h1 = tdim.height;
                double wscale = (double)w0/(double)w1;
                double hscale = (double)h0/(double)h1;
                return Math.min(wscale,hscale);
            } else {
                return 1.0;
            }
        }
        
        /** paints the text label of the node. */
        public Rectangle paintTextLabel(Graphics g, String label) {
            //Dbg.pr("computing text bounds of edge...");
            XGraphDisplay xgraph = (XGraphDisplay)graph;
            Font fn = view.getFont();
            if (fn == null)
                fn = GraphConstants.getFont(getAttributes());
            if (fn != null) {
                g.setFont(fn);
            }
            int bw = 2;
            FontMetrics metrics = ((Graphics2D)g).getFontMetrics();
            int sh = metrics.getHeight();
            Dimension tdim = xgraph.getStringDimension(g,label,bw,null,false,0,0);
            tdim.height += sh;
            setTextDimension(tdim);
            Rectangle b = super.getBounds();
            Point lp = getLabelPosition(tdim);
            if (lp == null) return null;
            //Dbg.showPoint(g,lp,Color.cyan);
            double scale = getScaleForTextLabel(b, tdim);
            //Dbg.pr("scale="+scale);
            int x = lp.x;// - tdim.width/2;
            int y = lp.y;// - tdim.height/2;
            Rectangle res = new Rectangle(x,y,tdim.width,tdim.height);
            //g.setColor(Color.magenta);
            //g.drawRect(x,y, tdim.width,tdim.height);
            g.setColor(viewOptions.textColor);
            if (scale < 1.0) {
                pushLocalScale(g,scale);
                int dx = (int)((tdim.width - tdim.width*scale)/2);
                int dy = (int)((tdim.height - tdim.height*scale)/2);
                x = (int)Math.round((x+dx)/scale);
                y = (int)Math.round((y+dy)/scale);
                //g.setColor(Color.black);
                //g.drawRect(x,y, tdim.width,tdim.height);
                xgraph.getStringDimension(g,label,bw,null,true,x,y);
                popLocalScale(g);
                view.setTextScale(scale);
            } else {
                xgraph.getStringDimension(g,label,bw,null,true,x,y);
                view.setTextScale(1.0);
            }
            return res;
        }
        
        /** the generic paint routines for leaf nodes. */
        
        public void paint(Graphics g) {
            //pushLocalScale(g);
            ViewOptions vopts = viewOptions;
            if (hasTemporaryViewAncestor()) {
                vopts = new XNodeView.ViewOptions();
                vopts.setUseShadow(false);
                vopts.setUsePaint(false);
                vopts.setUseBorder(true);
            }
            Graphics2D g2d = (Graphics2D)g;
            Rectangle b = this.getBounds();
            int shadowDepth = getShadowOffset();
            int w0 = Math.max(b.width,getMinimumWidth());
            int h0 = Math.max(b.height,getMinimumHeight());
            int w = w0-shadowDepth-1;
            int h = h0-shadowDepth-1;
            if (vopts.useShadow && shadowDepth>0) {
                g2d.setColor(getShadowColor());
                Shape sh = getShape(new Rectangle(shadowDepth,shadowDepth,w,h));
                if (sh instanceof Rectangle) {
                    g2d.fill(getShape(new Rectangle(w0-shadowDepth-1,shadowDepth,shadowDepth,h)));
                    g2d.fill(getShape(new Rectangle(shadowDepth,h0-shadowDepth-1,w,shadowDepth)));
                } else {
                    g2d.fill(sh);
                }
            }
            if (vopts.usePaint) {
                g2d.setPaint(getPaint(new Rectangle(0,0,w,h)));
                g2d.fill(getShape(new Rectangle(0,0,w,h)));
            } else {
                g2d.setPaint(graph.getBackground());
            }
            if (vopts.useBorder) {
                g2d.setColor(vopts.borderColor);
                int bw = vopts.borderWidth;
                g2d.setStroke(new BasicStroke(bw));
                double wh = (bw/2);
                g2d.draw(getShape(new Rectangle2D.Double(wh,wh,w-wh,h-wh)));
            }
            setBounds(new Rectangle(b.x,b.y,w,h));
            
            // draw the node's label text
            String text = "";
            if (node.getUserObject() != null) {
                text = node.getUserObject().toString();
            }
            boolean showtext = viewOptions.showText;
            if (showtext) {
                Object ecell = graph.getEditingCell();
                if (ecell != null) {
                    if (ecell.equals(node)) {
                        showtext = false;
                    }
                }
            }
            if (showtext) {
                Rectangle tdim = paintTextLabel(g, text);
                setTextDimension(new Dimension(tdim.width,tdim.height));
                if (viewOptions.getTextDisplayOption() == viewOptions.BOUNDS_ARE_ADJUSTED_TO_TEXT) {
                    if (adjustBoundsToTextDimension(1.0)) {
                        //Dbg.pr("text dim changed bounds.");
                        graph.repaint();
                    }
                }
            }
            
            // markings if selected (copied from JGraph code)
            if (selected || hasFocus) {
                ((Graphics2D) g).setStroke(GraphConstants.SELECTION_STROKE);
                if (hasFocus)
                    g.setColor(graph.getGridColor());
                else if (selected)
                    g.setColor(graph.getHighlightColor());
                Dimension d = getSize();
                g.drawRect(0, 0, d.width-1, d.height-1);
            }
            if (viewOptions.callDefaultPaintMethod) {
                super.paint(g);
            }
            
        }
    }
    
}
