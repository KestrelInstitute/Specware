/*
 * Util.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/02/13 19:02:57  weilyn
 * Fixed 'specwareware' type
 *
 * Revision 1.1  2003/01/30 02:01:38  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.util.*;
import java.lang.ref.Reference;
import java.lang.ref.SoftReference;

import org.openide.ErrorManager;
import org.openide.TopManager;
import org.openide.windows.*;
import org.openide.src.SourceException;
import org.openide.util.NbBundle;

import org.netbeans.modules.java.model.IndexedPropertyBase;

import edu.kestrel.netbeans.model.MemberElement;
import edu.kestrel.netbeans.parser.*;
import edu.kestrel.netbeans.codegen.ElementBinding;

/** Utilities.
 *
 */
public class Util {
    
    /** ResourceBundle for java-loader package. */
    private static ResourceBundle bundle;
    
    /**
     * Instance of error manager used for annotating exceptions.
     */
    private static ErrorManager errorManager;
    
    public static void log(String msg) {
	msg = Thread.currentThread().toString() + msg;
	OutputWriter out = TopManager.getDefault().getIO("specware", false).getOut();
	out.println(msg);
	System.err.println(msg); //ErrorManager.getDefault().log(msg);
    }

    public static ErrorManager getErrorManager() {
        if (errorManager != null)
            return errorManager;
        ErrorManager main = ErrorManager.getDefault();
        if (main == null) {
            System.err.println("WARNING: can't lookup error manager"); // NOI18N
            return null;
        }
        return errorManager = main;
    }
    
    public static void trace(String msg) {
	log(msg);
        Exception e = new Exception("Testing");
	e.printStackTrace();
    }

    /** Computes the localized string for the key.
    * @param key The key of the string.
    * @return the localized string.
    */
    static String getString(String key) {
        if (bundle==null)
            bundle=NbBundle.getBundle(Util.class);
        return bundle.getString(key);
    }
    
    public static void throwException(String desc, String bundleKey) throws SourceException {
	throw (SourceException)getErrorManager().annotate(
	    new SourceException(desc),
	    getString(bundleKey)
	);
    }
    
    public static void annotateThrowable(Throwable t, Throwable nested) {
        getErrorManager().annotate(t, nested);
    }
    
    public static void annotateThrowable(Throwable t, String localizedMessage, 
        boolean user) {
        if (user) {
            getErrorManager().annotate(t, ErrorManager.USER, null,
                localizedMessage, null, null);
        } else {
            getErrorManager().annotate(t, ErrorManager.EXCEPTION, null,
                localizedMessage, null, null);
        }
    }

    public static String print(int[] ints) {
	if (ints == null)
	    return "null";
	StringBuffer buf = new StringBuffer("[");
	for (int i = 0; i < ints.length; i++) {
	    if (i > 0) {
		buf.append(", ");
	    }
	    buf.append(ints[i]);
	}
	buf.append("]");
	return buf.toString();
    }
	
    public static String print(Object[] objs) {
	return print(objs, false);
    }

    public static String print(Object[] objs, boolean paren) {
	if (objs == null)
	    return "null";
	StringBuffer buf = new StringBuffer((paren)? "(" : "[");
	for (int i = 0; i < objs.length; i++) {
	    if (i > 0) {
		buf.append(", ");
	    }
	    Object obj = objs[i];
	    buf.append((obj instanceof MemberElement) ? ((MemberElement)obj).getName() : obj.toString());
	}
	buf.append((paren)? ")" : "]");
	return buf.toString();
    }
	
    public static String print(Collection objs) {
	StringBuffer buf = new StringBuffer("[");
	boolean first = true;
	for (Iterator i = objs.iterator(); i.hasNext();) {
	    if (first) {
		first = false;
	    } else {
		buf.append(", ");
	    }
	    Object obj = i.next();
	    buf.append(print(obj));
	}
	buf.append("]");
	return buf.toString();
    }

    public static String print(Object obj) {
	if (obj == null)
	    return "null";
	if (obj instanceof MemberElement) {
	    return ((MemberElement)obj).getName();
	}
	if (obj instanceof ElementBinding) {
	    return print(((ElementBinding)obj).getElement());
	}
	if (obj instanceof IndexedPropertyBase.Change) {
            IndexedPropertyBase.Change chg = (IndexedPropertyBase.Change) obj;
	    StringBuffer sb = new StringBuffer();
	    Collection removed = chg.removed;
	    int[] reordered = chg.reordered;
	    Collection inserted = chg.inserted;
	    Collection replacements = chg.replacements;
	    int sizeDiff = chg.sizeDiff;
	    if (removed != null) {
		sb.append("removed(size=" + removed.size() + ", indices=" + print(chg.removeIndices) + ")"); // NOI18N
		sb.append(print(removed));
	    }
	    if (reordered != null) {
		sb.append(" reordered "); // NOI18N
	    }
	    if (inserted != null) {
		sb.append("inserted(size=" + inserted.size() + ", indices=" + print(chg.insertIndices) + ")"); // NOI18N
		sb.append(print(inserted));
	    }
	    if (replacements != null) {
		sb.append("replaced(size=" + replacements.size() + ", indices=" + print(chg.replaceIndices) + ")"); // NOI18N
		sb.append(print(replacements));
	    }
	    sb.append("sizedif=" + sizeDiff); // NOI18N
	    return sb.toString();
	}
	return obj.toString();
    }
        

}
