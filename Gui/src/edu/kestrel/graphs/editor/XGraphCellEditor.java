/*
 * XGraphCellEditor.java
 *
 * Created on November 14, 2002, 11:23 PM
 */

package edu.kestrel.graphs.editor;

import com.jgraph.graph.*;
import com.jgraph.*;
import edu.kestrel.graphs.*;
import javax.swing.event.*;
import javax.swing.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;

/**
 * This implements a multi-line editor
 * @author  ma
 */
public class XGraphCellEditor implements GraphCellEditor, java.io.Serializable {
    
    protected XGraphDisplay graph;
    protected XGraphElement elem;
    protected XGraphElementView elemview;
    
    protected XGraphCellEditor.MultiLineUserObject elemUserObject;
    
    protected JEditorPane editorPane;
    protected Dimension editorPaneDimension;
    protected Font editorFont;
    protected boolean listenersInstalled = false;
    
    protected double viewsTextScale = 1.0;
    
    private boolean blockAutoFit = false;
    private boolean collapseAfterEdit = false;
    
    /** Creates a new instance of XGraphCellEditor */
    public XGraphCellEditor(XGraphDisplay graph, XGraphElement elem, XGraphElementView elemview) {
        this.graph = graph;
        this.elem = elem;
        this.elemview = elemview;
        this.editorPane = new JEditorPane("text/plain","");
        if (elem != null)
            setUserObject();
        installEditorListeners();
    }
    
    private void setUserObject() {
        if (elem == null) return;
        Object obj;
        obj = elem.getUserObject();
        if (obj == null)
            obj = "";
        //Dbg.pr("user object is of type "+obj.getClass().getName());
        if (obj instanceof XGraphCellEditor.MultiLineUserObject) {
            elemUserObject = (XGraphCellEditor.MultiLineUserObject)obj;
            return;
        }
        elemUserObject = new XGraphCellEditor.MultiLineUserObject(obj.toString());
        elem.setUserObject(elemUserObject);
    }
    
    /** installs the listeners for the editor panel
     */
    protected void installEditorListeners() {
        if (listenersInstalled) return;
        if (editorPane != null) {
            editorPane.addKeyListener(new XGraphCellEditor.EditorPanelEventHandler(editorPane));
            editorPane.addComponentListener(new ComponentAdapter() {
                public void componentResized(ComponentEvent e) {
                    if (!blockAutoFit) {
                        fitEditorPaneToTextSize();
                        boolean blockAutoFit = true;
                    }
                }
            });
            listenersInstalled = true;
        }
    }
    
    public void setFont(Font f) {
        editorFont = f;
    }
    
    /** Adds a listener to the list that's notified when the editor
     * stops, or cancels editing.
     *
     * @param	l		the CellEditorListener
     *
     */
    public void addCellEditorListener(CellEditorListener l) {
    }
    
    /** Tells the editor to cancel editing and not accept any partially
     * edited value.
     *
     */
    public void cancelCellEditing() {
        Dbg.pr("cancelCellEditing");
        elemUserObject.setText(editorPane.getText());
        elem.setUserObject(elem.getUserObject());
        if (elem instanceof XNode) ((XNode)elem).getModelNode().sync();
        if (elem instanceof XEdge) ((XEdge)elem).getModelEdge().sync();
        if (elemview instanceof XTextView) {
            graph.update(graph.getGraphics());
            ((XTextView)elemview).adjustBoundsToTextDimension(viewsTextScale);
        }
        if (collapseAfterEdit) {
            if (elem instanceof XTextNode) {
                ((XTextNode)elem).collapse();
                collapseAfterEdit = false;
            }
        }
    }
    
    public void setCollapseAfterEdit(boolean b) {
        collapseAfterEdit = b;
    }
    
    /** Returns the value contained in the editor.
     * @return the value contained in the editor
     *
     */
    public Object getCellEditorValue() {
        return editorPane.getText();
    }
    
    /** Asks the editor if it can start editing using <code>anEvent</code>.
     * <code>anEvent</code> is in the invoking component coordinate system.
     * The editor can not assume the Component returned by
     * <code>getCellEditorComponent</code> is installed.  This method
     * is intended for the use of client to avoid the cost of setting up
     * and installing the editor component if editing is not possible.
     * If editing can be started this method returns true.
     *
     * @param	anEvent		the event the editor should use to consider
     * 				whether to begin editing or not
     * @return	true if editing can be started
     * @see #shouldSelectCell
     *
     */
    public boolean isCellEditable(EventObject anEvent) {
        return true;
    }
    
    /** Removes a listener from the list that's notified
     *
     * @param	l		the CellEditorListener
     *
     */
    public void removeCellEditorListener(CellEditorListener l) {
    }
    
    /** Returns true if the editing cell should be selected, false otherwise.
     * Typically, the return value is true, because is most cases the editing
     * cell should be selected.  However, it is useful to return false to
     * keep the selection from changing for some types of edits.
     * eg. A table that contains a column of check boxes, the user might
     * want to be able to change those checkboxes without altering the
     * selection.  (See Netscape Communicator for just such an example)
     * Of course, it is up to the client of the editor to use the return
     * value, but it doesn't need to if it doesn't want to.
     *
     * @param	anEvent		the event the editor should use to start
     * 				editing
     * @return	true if the editor would like the editing cell to be selected;
     *    otherwise returns false
     * @see #isCellEditable
     *
     */
    public boolean shouldSelectCell(EventObject anEvent) {
        return false;
    }
    
    /** Tells the editor to stop editing and accept any partially edited
     * value as the value of the editor.  The editor returns false if
     * editing was not stopped; this is useful for editors that validate
     * and can not accept invalid entries.
     *
     * @return	true if editing was stopped; false otherwise
     *
     */
    public boolean stopCellEditing() {
        Dbg.pr("stopCellEditing");
        cancelCellEditing();
        return true;
    }
    
    public Component getGraphCellEditorComponent(JGraph jGraph, Object obj, boolean param) {
        installEditorListeners();
        setUserObject();
        editorPane.setText(elemUserObject.getText());
        if (elemview != null)
            if (elemview instanceof XNodeView) {
                XNodeView nv = (XNodeView) elemview;
                viewsTextScale = nv.getTextScale();
                Rectangle b = elemview.getBounds();
                b.width /= viewsTextScale;
                b.height /= viewsTextScale;
                editorPane.setPreferredSize(new Dimension(b.width,b.height));
            }
        if (editorFont != null)
            editorPane.setFont(editorFont);
        editorPane.setBorder(new javax.swing.border.EtchedBorder());
        editorPaneDimension = editorPane.getSize();
        return editorPane;
    }
    
    /** class used for multi-line user objects.
     */
    public class MultiLineUserObject implements java.io.Serializable {
        
        protected String text = null;
        protected String newline = System.getProperty("line.separator");
        
        public MultiLineUserObject() {
            this("");
        }
        
        public MultiLineUserObject(MultiLineUserObject mlobj) {
            this(mlobj.getText());
        }
        
        public MultiLineUserObject createClone() {
            return new MultiLineUserObject(MultiLineUserObject.this);
        }
        
        public MultiLineUserObject(String text) {
            setText(text);
        }
        
        public void setText(String text) {
            this.text = text;
        }
        
        public String getText() {
            return text;
        }
        
        public String toString() {
            if (text == null) return "";
            /*
            int ind = 0;
            if ((ind = text.indexOf(newline)) < 0) {
                return text;
            }
            return text.substring(0,ind)+"...";
             */
            return text;
        }
    }
    
    public void fitEditorPaneToTextSize() {
        Graphics g = editorPane.getGraphics();
        if (g == null) return;
        String text = editorPane.getText();
        text.trim();
        int bw1 = 5, bw2 = 5;
        Dimension tdim = graph.getStringDimension(g, text, bw1, null /*editorPaneDimension*/, false, 0, 0);
        tdim.width = tdim.width+bw2;
        tdim.height = tdim.height+bw2;
        //Dbg.pr("tdim="+tdim);
        editorPane.setSize(tdim);
    }
    
    
    /** inner class used to implement the listener methods for the editor panel
     */
    protected class EditorPanelEventHandler implements KeyListener {
        
        protected JEditorPane editorPane;
        
        public EditorPanelEventHandler(JEditorPane editorPane) {
            this.editorPane = editorPane;
        }
        /** Invoked when a key has been pressed.
         * See the class description for {@link KeyEvent} for a definition of
         * a key pressed event.
         *
         */
        public void keyPressed(KeyEvent e) {
        }
        
        /** Invoked when a key has been released.
         * See the class description for {@link KeyEvent} for a definition of
         * a key released event.
         *
         */
        public void keyReleased(KeyEvent e) {
            blockAutoFit = false;
            fitEditorPaneToTextSize();
        }
        
        /** Invoked when a key has been typed.
         * See the class description for {@link KeyEvent} for a definition of
         * a key typed event.
         *
         */
        public void keyTyped(KeyEvent e) {
        }
        
    }
    
    
}
