package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.Component;
import java.util.*;
import java.awt.*;

public interface XGraphElementView extends CellView {
    
    public XGraphElement getGraphElement();
    
    public void showPopupMenu(Component c, int x, int y);
    
    public void delete(boolean interactive);
    
    public void edit();
    
    public void setTemporaryView(boolean b);
    
    public boolean isTemporaryView();
    
    public void setFont(Font f);
    
    public Font getFont();

    /** called, if the view has changed, i.e. if the view is either directly changed or affected as part
     * of the context of a view change. The view object is either part of the changedView list or the contextViews list.
     */
    public void viewChanged(java.util.List changedViews, java.util.List contextViews);
    
}
