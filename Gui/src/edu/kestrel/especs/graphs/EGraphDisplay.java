/*
 * EGraphDisplay.java
 *
 * Created on November 15, 2002, 12:50 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.graphs.*;
import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.spec.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.io.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class EGraphDisplay extends XGraphDisplay {
    
    /** Creates a new instance of EGraphDisplay */
    public EGraphDisplay(Object value) {
        super(value,new EGraphSpec());
    }
    
    public EGraphDisplay(Object value, XGraphSpec spec) {
        super(value,spec);
    }
    
    public EGraphDisplay() {
        this(null,new EGraphSpec());
    }
    
    /*
    public EGraphDisplay(XGraphSpec spec, GraphView view) {
        super(spec,view);
    }
     */
    
    static public void main(String[] args) {
        JFrame frame = new JFrame("ESpecs Graph Editor");
        frame.getContentPane().setLayout(new BorderLayout());
        Dbg.setDebugLevel(1);
        EGraphDisplay graph = new EGraphDisplay("");
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                System.exit(0);
            }
        });
        frame.getContentPane().add(new JScrollPane(graph));
        frame.getContentPane().add(graph.createToolBar(JToolBar.HORIZONTAL),"North");
        frame.setSize(500,500);
        frame.show();
        
    }
    
}
