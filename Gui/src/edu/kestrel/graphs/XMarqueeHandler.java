/*
 * XMarqueeHandler.java
 *
 * Created on October 23, 2002, 2:36 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 * The default global mouse handler for XGraphDisplays.
 * @author  ma
 */
public class XMarqueeHandler extends XBasicMarqueeHandler {
    
    protected JPopupMenu popupMenu;
    
    /** Creates a new instance of XMarqueeHandler */
    public XMarqueeHandler(XGraphDisplay graph) {
        super(graph);
        initPopupMenu();
    }
    
    protected void initPopupMenu() {
        popupMenu = new JPopupMenu();
        JMenuItem menuItem = new JMenuItem("edit");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Object val = JOptionPane.showInternalInputDialog(graph,"new value:","edit",JOptionPane.PLAIN_MESSAGE,null,null,graph.getValue());
                if (val != null)
                    graph.setValue(val);
            }
        });
        popupMenu.add(menuItem);
        popupMenu.addSeparator();
        menuItem =        new JMenuItem("scale to fit [ s f ]");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                //Dbg.pr("invoking graph.writeToFile()...");
                //graph.writeToFile();
                graph.scaleToFit(20,XGraphDisplay.ALWAYS_SCALE);
            }
        });
        popupMenu.add(menuItem);
        popupMenu.add(new ScaleMenuItem("set scale to 1 [ s 1 ]",1));
        JMenu zoomMenu = new JMenu("zoom out [ - ]");
        zoomMenu.add(new ScaleMenuItem("1/2",1/2.0));
        zoomMenu.add(new ScaleMenuItem("1/4",1/4.0));
        zoomMenu.add(new ScaleMenuItem("1/8",1/8.0));
        zoomMenu.add(new ScaleMenuItem("1/16",1/16.0));
        zoomMenu.add(new ScaleMenuItem("1/32",1/32.0));
        zoomMenu.add(new ScaleMenuItem("1/64",1/64.0));
        popupMenu.add(zoomMenu);
        zoomMenu = new JMenu("zoom in [ + ]");
        zoomMenu.add(new ScaleMenuItem("2",2));
        zoomMenu.add(new ScaleMenuItem("4",4));
        zoomMenu.add(new ScaleMenuItem("8",8));
        zoomMenu.add(new ScaleMenuItem("16",16));
        zoomMenu.add(new ScaleMenuItem("32",32));
        zoomMenu.add(new ScaleMenuItem("64",64));
        popupMenu.add(zoomMenu);
        popupMenu.addSeparator();
        menuItem = new JMenuItem("delete all");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                //Dbg.pr("invoking graph.writeToFile()...");
                //graph.writeToFile();
                graph.getXGraphView().deleteAll(graph,true);
            }
        });
        popupMenu.add(menuItem);
    }
    
    protected class ScaleMenuItem extends JMenuItem {
        public ScaleMenuItem(String label, final double scaleFactor) {
            super(label);
            addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    graph.setScale(scaleFactor);
                }
            });
        }
    }
    
    public boolean isForceMarqueeEvent(MouseEvent e) {
        if (e.getClickCount() == graph.getEditClickCount())
            return true;
        if (getMouseButton(e) == 3)
            return true;
        if (e.isControlDown())
            return true;
        //return true;
        return super.isForceMarqueeEvent(e);
    }
    
    public void mouseDragged(MouseEvent e0) {
        if (getMouseButton(e0) == 3) {
            e0.consume();
        }
        super.mouseDragged(e0);
    }
    
    public void mouseMoved(MouseEvent e0) {
        super.mouseMoved(e0);
    }
    
    public void mousePressed(MouseEvent e0) {
        //Dbg.pr("mouse pressed in XMarqueeHandler...");
        if (!e0.isConsumed()) {
            MouseEvent e = fromScreenSnap(e0);
            int x = e.getX(), y = e.getY();
            if (e0.getClickCount() == 2) {
                //System.out.println("not consumed double click");
                CellView cv = graph.getNextViewAt(null,x,y);
                if (cv != null) {
                    if (cv instanceof XNodeView) {
                        ((XNodeView) cv).doubleClickAction();
                    }
                }
            }
            else if (getMouseButton(e) == 3 || e.isControlDown()) {
                //System.out.println("right button press.");
                CellView cv = graph.getNextViewAt(null,x,y);
                if (cv != null) {
                    //System.out.println("right mouse press at view of class "+cv.getClass().getName());
                    //System.out.println(graph.getSelectionCount()+" elements selected.");
                    if (cv instanceof XGraphElementView) {
                        //System.out.println("showing popup menu...");
                        ((XGraphElementView)cv).showPopupMenu(e0.getComponent(),e0.getX(),e0.getY());
                        e0.consume();
                    }
                } else {
                    popupMenu.show(e0.getComponent(),e0.getX(),e0.getY());
                    e0.consume();
                    return;
                }
            }
            else {
                Object cell = graph.getFirstCellForLocation(x,y);
                if (cell instanceof XGraphElement) {
                    XGraphElement elem = (XGraphElement)cell;
                    Dbg.pr("mouse pressed at graph element "+elem);
                }
            }
        }
        super.mousePressed(e0);
    }
    
    public void mouseReleased(MouseEvent e0) {
        if (getMouseButton(e0) == 3) {
            e0.consume();
        }
        super.mouseReleased(e0);
    }
    
    protected void overlay(Graphics graphics) {
        super.overlay(graphics);
    }
    
}
