/*
 * XGraphDisplayInternalFrame.java
 *
 * Created on November 25, 2002, 12:52 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.event.*;
import javax.swing.event.*;
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;
/**
 *
 * @author  ma
 */
public class XGraphDisplayInternalFrame extends JInternalFrame implements XGraphDisplayValueListener {
    
    protected XGraphDisplay graph;
    
    protected XGraphDisplay getXGraphDisplay() {
        return graph;
    }
    
    /** Creates a new instance of XGraphDisplayInternalFrame */
    public XGraphDisplayInternalFrame(XGraphDisplay graph) {
        super(graph.getTitleString(),true,true,true,true);
        this.graph = graph;
        getContentPane().setLayout(new BorderLayout());
        addInternalFrameListener(new InternalFrameAdapter() {
            public void internalFrameClosing(InternalFrameEvent e) {
                //Dbg.pr("internal frame closing...");
                Dimension dim = getSize();
                Point p = getLocation();
                Rectangle bounds = new Rectangle(p.x,p.y,dim.width,dim.height);
                getXGraphDisplay().closeAction(bounds);
            }
        });
        graph.addGraphDisplayValueListener(this);
        getContentPane().add(new JScrollPane(graph),BorderLayout.CENTER);
        getContentPane().add(graph.createToolBar(JToolBar.HORIZONTAL),BorderLayout.NORTH);
        Rectangle b = graph.getSavedBounds();
        setVisible(true);
        if (b == null) {
            setSize(400,350);
        } else {
            setBounds(b);
        }
    }
    
    
    public void graphValueChanged(XGraphDisplay graph, Object oldValue, Object newValue) {
        setTitle(newValue.toString());
    }
    
    public XGraphDisplay getGraph() {
        return graph;
    }
    
    public boolean displaysGraph(XGraphDisplay graph) {
        return this.graph.equals(graph);
    }
    
}
