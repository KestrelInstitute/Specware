/*
 * Dbg.java
 *
 * Created on November 8, 2002, 12:38 PM
 */

package edu.kestrel.graphs;

import java.util.*;
import java.awt.*;

/**
 * Debugging utilities
 * @author  ma
 */
public class Dbg {
    
    static int DEBUG_LEVEL = 0;
    
    static public void pr(String s) {
        if (DEBUG_LEVEL > 0)
            System.out.println(s);
    }

    static public void pr2(String s) {
        if (DEBUG_LEVEL > 1)
            System.out.println(s);
    }
 
    static public void setDebugLevel(int lvl) {
        DEBUG_LEVEL = lvl;
        if (lvl > 1) {
            Runtime.getRuntime().traceMethodCalls(true);
        }
    }
    
    static public boolean isDebug() {
        return DEBUG_LEVEL > 0;
    }
    
    static public boolean isDebug2() {
        return DEBUG_LEVEL > 1;
    }
    
    static public void showPoint(Graphics g, Point p, Color color) {
        int s = 5;
        g.setColor(color);
        g.fillRect(p.x-s,p.y-s,2*s,2*s);
        g.setColor(Color.black);
        g.drawLine(p.x-s,p.y-s,p.x+s,p.y+s);
        g.drawLine(p.x+s, p.y-s,p.x-s,p.y+s);
    }
    
    static public java.util.List showPoints(Graphics g, java.util.List points, Color color) {
        Iterator iter = points.iterator();
        while(iter.hasNext()) {
            Object p = iter.next();
            if (p instanceof Point) {
                showPoint(g,(Point)p,color);
            }
        }
        return points;
    }
    
}
