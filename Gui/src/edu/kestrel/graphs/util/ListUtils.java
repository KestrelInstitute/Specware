/*
 * ListUtils.java
 *
 * Created on January 30, 2003, 7:49 PM
 */

package edu.kestrel.graphs.util;

import java.util.*;

/**
 *
 * @author  ma
 */
public class ListUtils {
    
    /** interface use in doForall method.
     */
    static public interface ListAction {
        /** method providing the action on a list element; return true on success.
         */
        public boolean execute(Object obj);
    }
    
    /** adds the obj to the list; return the updated list which is the same object, if the list
     * existed before; otherwise a new ArrayList is created and the object added to it.
     */
    static public java.util.List addToList(java.util.List list, Object obj) {
        java.util.List res = list;
        if (list == null) {
            res = new ArrayList();
        }
        if (!res.contains(obj))
            res.add(obj);
        return res;
    }
    
    /** removes the object from the list.
     */
    static public void removeFromList(java.util.List list, Object obj) {
        if (list == null) return;
        list.remove(obj);
    }
    
    /** this method iterates over all elements of the list; it uses the ListAction interface do execute customized
     * actions. The method exits immediately, if a call to execute returns false; otherwise -- also if list == null --
     * it returns true.
     */
    static public boolean doForall(java.util.List list, ListAction action) {
        if (list == null) return true;
        Iterator iter = list.iterator();
        while(iter.hasNext()) {
            if (!action.execute(iter.next())) {
                return false;
            }
        }
        return true;
    }
    
    static public boolean containsSomething(java.util.List list) {
        if (list == null) return false;
        return list.size() > 0;
    }
    
}
