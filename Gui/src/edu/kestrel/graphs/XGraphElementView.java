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

}
