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
    
    static int msgcnt = 0;
    
    static private void pr_(String s) {
        System.out.println("["+(msgcnt++)+"] "+s);
    }
    
    static public void pr(String s) {
        if (DEBUG_LEVEL == 1)
            pr_(s);
    }
    
    static public void pr2(String s) {
        if (DEBUG_LEVEL == 2)
            pr_(s);
    }
    
    static public void pr3(String s) {
        if (DEBUG_LEVEL == 3)
            pr_(s);
    }
    
    static public void setDebugLevel(int lvl) {
        DEBUG_LEVEL = lvl;
    }
    
    static public boolean isDebug() {
        return DEBUG_LEVEL == 1;
    }
    
    static public boolean isDebug2() {
        return DEBUG_LEVEL == 2;
    }

    static public boolean isDebug(int lvl) {
        return DEBUG_LEVEL == lvl;
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
