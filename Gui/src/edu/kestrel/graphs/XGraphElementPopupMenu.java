/*
 * XGraphElementPopupMenu.java
 *
 * Created on November 6, 2002, 4:28 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import com.jgraph.JGraph;
import javax.swing.*;
import java.util.Map;
import java.awt.event.*;

/**
 * This class implements a popup menu containing the items common to all nodes and edge in a graph
 * @author  ma
 */
public class XGraphElementPopupMenu extends JPopupMenu {
    
    static public final String EditMenuItemLabel = "edit";
    static public final String DeleteMenuItemLabel = "delete";
    
    protected XGraphElementView elementView;
    protected JGraph graph;
    protected boolean isEditable = true;
    /** Creates a new instance of XGraphElementPopupMenu */
    public XGraphElementPopupMenu(JGraph graph, XGraphElementView elementView, boolean isEditable) {
        super();
        this.graph = graph;
        this.elementView = elementView;
        this.isEditable = isEditable;
        addDefaultItems();
    }
    
    public XGraphElementPopupMenu(JGraph graph, XGraphElementView elementView) {
        this(graph,elementView,true);
    }
    
    protected void addDefaultItems() {
        JMenuItem menuItem;
        menuItem = new JMenuItem(DeleteMenuItemLabel);
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                //Dbg.pr(graph.getSelectionCount()+" elements selected.");
                if (graph.getSelectionCount() > 1) {
                    int answ = JOptionPane.showConfirmDialog(graph, "Do you really want to delete these elements?", "Delete?", JOptionPane.OK_CANCEL_OPTION);
                    if (answ != JOptionPane.YES_OPTION) return;
                    
                    Object[] sel = graph.getSelectionCells();
                    for(int i=0;i<sel.length;i++) {
                        CellView cv = graph.getView().getMapping(sel[i],false);
                        if (cv != null)
                            if (cv instanceof XGraphElementView)
                                ((XGraphElementView)cv).delete(false);
                    }
                } else {
                    elementView.delete(true);
                }
            }
        });
        add(menuItem);
        menuItem = new JMenuItem(EditMenuItemLabel);
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                elementView.edit();
            }
        });
        menuItem.setEnabled(isEditable);
        add(menuItem);
        
        if (Dbg.isDebug()) {
            // some debugging entries
            menuItem = new JMenuItem("show attributes of view object");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    Dbg.pr(graph.getSelectionCount()+" elements selected.");
                    XGraphDisplay.showAttributes(elementView);
                }
            });
            add(menuItem);
            menuItem = new JMenuItem("show attributes of model object");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    GraphCell c = (GraphCell) elementView.getCell();
                    XGraphDisplay.showAttributes(c);
                }
            });
            add(menuItem);
        }
    }
    
}
