/*
 * XTextEditor.java
 *
 * Created on January 23, 2003, 6:57 PM
 */

package edu.kestrel.graphs.editor;

import edu.kestrel.graphs.*;
import javax.swing.*;

/**
 *
 * @author  ma
 */
public class XTextEditor extends JEditorPane implements XElementEditor {
    
    protected XTextEditorEditable elem;
    
    /** Creates a new instance of XTextEditor */
    public XTextEditor() {
    }
    
    public XTextEditor(XTextEditorEditable elem) {
        this();
        setElem(elem);
    }
    
    public void setElem(XTextEditorEditable elem) {
        this.elem = elem;
        if (elem != null) {
            setText(elem.getText());
        }
    }
    
    public XTextEditorEditable getElem() {
        return elem;
    }
    
    public String getTitleText() {
        if (elem == null) return "";
        return elem.getTitleText();
    }
    
    /** propagate the contents of the text editor to the text node.
     */
    public void apply() {
        if (elem == null) return;
        elem.setText(getText());
    }
    
    /** returns the panel that is actually embedded into the frame; embeds the actual editor instance
     * into a JScrollPane.
     *
     */
    public javax.swing.JComponent getPanel() {
        return new JScrollPane(this);
    }
    
    /** actions that need to be performed in the context of a cancel operation.
     *
     */
    public void cancel() {
    }
    
    /** returns true, if the frame containing the editor shall constantly update its size according to
     * changed size of this editor.
     *
     */
    public boolean autoUpdateFrameSize() {
        return false;
    }
    
}
