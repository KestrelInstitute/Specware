/*
 * Parsing.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:25  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.EventListener;
import java.util.EventObject;
import java.util.Iterator;
import java.util.List;

import edu.kestrel.netbeans.MetaSlangDataLoader;
import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.model.SourceElement;

/** The public interface for parsing of meta-slang sources. This class contains listener
* interface and the event class, also the methods for registration and unregistration
* of the listener.
*
*/
public class Parsing extends Object {

    /** Add the specific listener to the list of global parsing listeners.
    * @param l listener to add
    */
    public static void addParsingListener(Listener l) {
        synchronized (MetaSlangDataLoader.parsingListeners) {
            MetaSlangDataLoader.parsingListeners.add(l);
        }
    }

    /** Remove the specific listener from the list of global parsing listeners.
    * @param l listener to remove
    */
    public static void removeParsingListener(Listener l) {
        synchronized (MetaSlangDataLoader.parsingListeners) {
            MetaSlangDataLoader.parsingListeners.remove(l);
        }
    }

    /** Fire the event for specified MetaSlangDataObject.
    */
    public static void fireEvent(MetaSlangDataObject jdo, Object hook) {
        Event evt = new Event(jdo, hook);
        Iterator it = null;
        synchronized (MetaSlangDataLoader.parsingListeners) {
            List list = (List) MetaSlangDataLoader.parsingListeners.clone();
            it = list.iterator();
        }
        while (it.hasNext()) {
            ((Listener) it.next()).objectParsed(evt);
        }
    }

    /** The listener interface for everybody who want to control all
    * parsed MetaSlangDataObjects.
    */
    public static interface Listener extends EventListener {
        /** Method which is called everytime when some object is parsed.
        * @param evt The event with the details.
        */
        public void objectParsed(Event evt);
    }

    /** The event class used in Listener.
    */
    public static class Event extends EventObject {
        static final long serialVersionUID =8512232095851109211L;
        /** Construct the new Event.
        * @param jdo MetaSlangDataObject which is the source of the event.
        * @param hook the object which prevents the garbage collector remove the parsing
        *   information till this event lives.
        */
        Event(MetaSlangDataObject jdo, Object hook) {
            super(jdo);
        }

        /** @return the data object which is the source of the event.
        */
        public MetaSlangDataObject getMetaSlangDataObject() {
            return (MetaSlangDataObject) getSource();
        }

        /** @return the source element which was parsed.
        */
        public SourceElement getSourceElement() {
            return getMetaSlangDataObject().getSource();
        }
    }
}
