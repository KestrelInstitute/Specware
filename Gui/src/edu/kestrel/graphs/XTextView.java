/*
 * XTextView.java
 *
 * Created on October 24, 2002, 2:13 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.editor.*;
import com.jgraph.graph.*;
import java.awt.geom.*;
import java.util.*;
import javax.swing.*;
import java.text.*;
import java.awt.font.*;
import java.awt.event.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XTextView extends XNodeView {
    
    protected XGraphCellEditor xcellEditor;
    
    /** Creates a new instance of XTextView */
    
    public XTextView(XNode element, XGraphDisplay graph, CellMapper cm) {
        super(element,graph,cm);
        setRenderer(new XBoxRenderer(this));
        this.xcellEditor = new XGraphCellEditor(graph,element,this);
        //setFont(new Font("Courier",Font.PLAIN,14));
    }
    
    public GraphCellEditor getEditor() {
        if (node instanceof XTextNode) {
            if (((XTextNode)node).isCollapsed()) {
                return super.getEditor();
            }
        }
        return xcellEditor;
    }
    
    public void setFont(Font f) {
        super.setFont(f);
        if (xcellEditor != null)
            xcellEditor.setFont(f);
    }
    
    private JMenuItem getPopupMenuItem(String label) {
        MenuElement[] items = popupMenu.getSubElements();
        for(int i=0;i<items.length;i++) {
            if (items[i] instanceof JMenuItem) {
                JMenuItem mi = (JMenuItem)items[i];
                if (mi.getText().equals(label)) {
                    return mi;
                }
            }
        }
        return null;
    }
    
    public void doubleClickAction() {
        if (node != null) {
            if (node instanceof XTextNode) {
                if (((XTextNode)node).isCollapsed()) {
                    ((XTextNode)node).expand();
                    return;
                }
            }
        }
        super.doubleClickAction();
    }
    
    
    
    /** add items to the node's menu that are specific to a text node.
     */
    protected void initPopupMenu() {
        super.initPopupMenu();
        if (node instanceof XTextNode) {
            final XTextNode tnode = (XTextNode) node;
            JMenuItem menuItem = new JMenuItem(tnode.isCollapsed()?"expand":"collapse");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XTextNode tnode = (XTextNode) node;
                    if (tnode.isCollapsed()) {
                        tnode.expand();
                        update();
                    } else {
                        tnode.collapse();
                    }
                }
            });
            popupMenu.add(menuItem,0);
            menuItem = getPopupMenuItem(XGraphElementPopupMenu.EditMenuItemLabel);
            if (menuItem != null) {
                try {
                    EventListener[] listener = menuItem.getListeners(Class.forName("java.awt.event.ActionListener"));
                    for(int i=0;i<listener.length;i++) {
                        if (listener[i] instanceof ActionListener) {
                            menuItem.removeActionListener((ActionListener)listener[i]);
                        }
                    }
                } catch (Exception ee) {}
                menuItem.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        if (node instanceof XTextNode) {
                            XTextNode tnode = (XTextNode)node;
                            if (tnode.isCollapsed()) {
                                tnode.setDontSetExpandedFlag();
                                tnode.expand();
                                Dbg.pr("  user object="+tnode.getUserObject());
                                graph.repaint();
                                GraphCellEditor editor = getEditor();
                                if (editor instanceof XGraphCellEditor) {
                                    //Dbg.pr("*********** fitEditorPaneToTextSize...");
                                    XGraphCellEditor xed = (XGraphCellEditor)editor;
                                    xed.setCollapseAfterEdit(true);
                                    xed.fitEditorPaneToTextSize();
                                } else {
                                    tnode.resetDontSetExpandedFlag();
                                }
                            }
                        }
                        XTextView.this.edit();
                    }
                });
            }
            menuItem = new JMenuItem("edit in new frame");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XTextNode tnode = (XTextNode) node;
                    XTextEditorInternalFrame tf = new XTextEditorInternalFrame(tnode);
                    tf.setFont(getFont());
                    XGraphApplication appl = ((XGraphDisplay)graph).getApplication();
                    if (appl != null) {
                        appl.getDesktop().newInternalFrame(tf);
                    }
                }
            });
            popupMenu.add(menuItem,2);
        }
    }
    
    static public String newline = System.getProperty("line.separator");
    
    protected class XBoxRenderer extends XNodeRenderer {
        
        public XBoxRenderer(XTextView view) {
            super(view);
        }
        
        protected Shape getShape(RectangularShape b) {
            return new Rectangle2D.Double(b.getX(),b.getY(),b.getWidth(),b.getHeight());
        }
        
        public void paint0(Graphics g) {
            viewOptions.setCallDefaultPaintMethod(false);
            super.paint(g);
            String text = null;
            Object obj = node.getUserObject();
            int bw = 5;
            if (obj instanceof XGraphCellEditor.MultiLineUserObject) {
                text = ((XGraphCellEditor.MultiLineUserObject)obj).getText();
            } else {
                text = obj.toString();
            }
            if (viewFont != null)
                g.setFont(viewFont);
            g.setColor(Color.black);
            Dimension tdim = ((XGraphDisplay)graph).getStringDimension(g,text,bw,new Dimension(0,0),true,0,0);
            setTextDimension(tdim);
        }
        
        public void paint(Graphics g) {
            if (view instanceof XNodeView) {
                ((XNodeView)view).prepareResizing();
            }
            super.paint(g);
            if (node instanceof XTextNode) {
                XTextNode tnode = (XTextNode)node;
                if (tnode.hasBeenExpanded()) {
                    Dbg.pr("Text node has been expanded.");
                    ((XNodeView)view).adjustGraphAfterResizing();
                } else if (tnode.hasBeenCollapsed()) {
                    Dbg.pr("Text node has been collapsed.");
                    ((XNodeView)view).undoResizeChanges(false);
                }
            }
        }
        
    }
    
}
