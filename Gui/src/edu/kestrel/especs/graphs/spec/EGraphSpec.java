/*
 * EGraphSpec.java
 *
 * Created on November 15, 2002, 12:57 PM
 */

package edu.kestrel.especs.graphs.spec;

import edu.kestrel.especs.graphs.drawingmode.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.drawingmode.*;
import edu.kestrel.graphs.*;
/**
 *
 * @author  ma
 */
public class EGraphSpec extends XGraphSpec {
    
    /** Creates a new instance of EGraphSpec */
    public EGraphSpec() {
        DrawingMode basic = new DrawingModeBasic();
        addDrawingMode(basic);
        addDrawingMode(new DrawingModeAddEspecNode());
        addDrawingMode(new DrawingModeAddStadNode());
        //addDrawingMode(new DrawingModeAddEllipse());
        //addDrawingMode(new DrawingModeAddStraightEdge());
        addDrawingMode(new DrawingModeAddStepEdge());
        addDrawingMode(new DrawingModeAddSpecText());
        //addDrawingMode(new DrawingModeAddImportEdge());
        //addDrawingMode(new DrawingModeAddContainerBox());
        addDrawingMode(new DrawingModeAddEllipse());
        addDrawingMode(new DrawingModeZoom());
        if (Dbg.isDebug()) {
            addDrawingMode(new DrawingModeDebug());
        }
        setInitialDrawingMode(basic);
    }
    
}
