/*
 * EspecView.java
 *
 * Created on November 15, 2002, 3:47 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;
/**
 *
 * @author  ma
 */
public class EspecView extends XContainerBoxView {
    
    /** Creates a new instance of EspecView */
    public EspecView(XContainerNode element, XGraphDisplay graph, CellMapper cm) {
        super(element,graph,cm);
    }
    
    protected void initPopupMenu() {
        super.initPopupMenu();
        JMenuItem menuItem = new JMenuItem("create import");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                createImport(0,getBounds().height+50);
            }
        });
        popupMenu.add(menuItem);
        if (Dbg.isDebug()) {
            menuItem = new JMenuItem("show imported especs");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if (node instanceof EspecNode) {
                        String msg = node+" imports ", sep = "";
                        boolean nothing = true;
                        EspecModelNode mnode = (EspecModelNode)node.getModelNode();
                        if (mnode.getImportedEspecs() != null) {
                            Iterator iter = mnode.getImportedEspecs().iterator();
                            while(iter.hasNext()) {
                                EspecModelNode imp = (EspecModelNode)iter.next();
                                msg += sep + imp.getShortName();
                                sep = ", ";
                                nothing = false;
                            }
                        }
                        if (nothing) msg += "nothing.";
                        JOptionPane.showMessageDialog(graph,msg);
                    }
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("create import edge");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if (node instanceof EspecNode) {
                        ((EspecNode)node).createImportEdgeInGraph((XGraphDisplay)graph);
                    }
                }
            });
            popupMenu.add(menuItem);
        }
    }
    
    /** clones the view and the associated node and translates the new view for (dx,dy). */
    public void createImport(int dx, int dy) {
        if (!(node instanceof EspecNode)) return;
        Object val = JOptionPane.showInternalInputDialog(graph,"enter name for new espec:","edit",JOptionPane.PLAIN_MESSAGE,null,null,node.getUserObject());
        EspecNode espec = ((EspecNode)node).createImport(val);
        String msg =  (espec == null?"There have been problems creating an import for this espec.":
            "Espec \""+espec+"\" importing espec \""+node+"\" has been created and put into the clipboard.");
            JOptionPane.showMessageDialog(graph,msg);
        /*
        Map cellMap = ((XGraphDisplay)graph).copyCells(new Object[]{node});
        if (cellMap != null)
            if (cellMap.containsKey(node)) {
                Object obj = cellMap.get(node);
                CellView cv = graph.getView().getMapping(obj,false);
                if (cv != null) {
                    XGraphView gview = (XGraphView)graph.getView();
                    gview.startGroupTranslate();
                    gview.translateViewsInGroup(new CellView[]{cv},dx,dy);
                    gview.endGroupTranslate();
                    if (cv instanceof XContainerView) {
                        ((XContainerView)cv).setBoundsToChildrenBounds();
                    }
                    graph.setSelectionCell(obj);
                    if (cv instanceof XContainerView) {
                        ((XContainerView)cv).collapse();
                    }
                }
                Dbg.pr("clone has class "+obj.getClass().getName());
                // create ImportEdge
                if (obj instanceof EspecNode) {
                    EspecNode clone = (EspecNode) obj;
                    //clone.setIsExpandable(false);
                    //clone.setIsEditable(false);
                    Port p1 = node.getDefaultPort();
                    Port p2 = clone.getDefaultPort();
                    ImportEdge impedge = new ImportEdge();
                    ((XGraphDisplay)graph).insertEdge(impedge);
                    ConnectionSet cs = new ConnectionSet(impedge,p1,p2);
                    graph.getModel().edit(cs,null,null,null);
                }
            }
         */
    }
    
}
