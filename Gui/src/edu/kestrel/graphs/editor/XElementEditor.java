/*
 * XGraphElementEditor.java
 *
 * Created on January 28, 2003, 8:04 PM
 */

package edu.kestrel.graphs.editor;

/**
 * This is an interface for "external" i.e. not in-place editors for graph cells. This editor is invoked by the menu item
 * "edit in new frame" of the graph element (if present).
 * @author  ma
 */
public interface XElementEditor {
    
    public String getTitleText();
    
    public void setFont(java.awt.Font f);
    
    /** applies the changes made in the editor. */
    public void apply();
    
    /** actions that need to be performed in the context of a cancel operation.
     */
    public void cancel();
    
    /** returns the panel that is actually embedded into the frame; implementors might embed the actual editor instance
     * into a JScrollPane, for instance, using this method.
     */
    public javax.swing.JComponent getPanel();
    
    public java.awt.Dimension getPreferredSize();
    
    /** returns true, if the frame containing the editor shall constantly update its size according to
     * changed size of this editor.
     */
    public boolean autoUpdateFrameSize();
    
}
