/*
 * XTextEditorEditable.java
 *
 * Created on January 24, 2003, 3:25 PM
 */

package edu.kestrel.graphs.editor;

/**
 * Interface used for objects that can be edited using the XTextEditor
 * @author  ma
 */
public interface XTextEditorEditable {
    public String getText();
    public void setText(String t);
    public String getTitleText();
    public XElementEditor createEditorPane();
}
