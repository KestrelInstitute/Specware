package edu.kestrel.netbeans.nodes;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.util.Comparator;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Arrays;
import java.util.HashMap;

import org.openide.nodes.Children;
import org.openide.nodes.Node;
import org.openide.cookies.FilterCookie;
import org.openide.util.WeakListener;

import edu.kestrel.netbeans.model.*;


/** Normal implementation of children list for a morphism element node.
* Semantics are similar to those of {@link SourceChildren}.
*/
public class MorphismChildren extends Children.Keys implements FilterCookie {

    /** Converts property names to filter. */
    protected static HashMap              propToFilter;

    /** For sorting groups of elements. */
    private static Comparator           comparator = new Comparator () {
                public int compare (Object o1, Object o2) {
                    if (o1 instanceof MemberElement)
                        if (o2 instanceof MemberElement)
                            return ((MemberElement) o1).getName ().compareToIgnoreCase (
                                       ((MemberElement) o2).getName ()
                                   );
                        else
                            return -1;
                    else
                        if (o2 instanceof MemberElement)
                            return 1;
                        else
                            return 0;
                }
            };

    static {
        propToFilter = new HashMap ();
        propToFilter.put (ElementProperties.PROP_SOURCE_UNIT_ID, new Integer (MorphismElementFilter.SOURCE));        
        propToFilter.put (ElementProperties.PROP_TARGET_UNIT_ID, new Integer (MorphismElementFilter.TARGET));
    }

    /** The morphism element whose subelements are represented. */
    protected MorphismElement              element;
    /** Filter for elements, or <code>null</code> to disable. */
    protected MorphismElementFilter        filter;
    /** Factory for creating new child nodes. */
    protected ElementNodeFactory        factory;
    /** Weak listener to the element and filter changes */
    private PropertyChangeListener      wPropL;
    /** Listener to the element and filter changes. This reference must
    * be kept to prevent the listener from finalizing when we are alive */
    private ElementListener             propL;
    /** Central memory of mankind is used when some elements are changed */
    protected Collection[]              cpl;
    /** Flag saying whether we have our nodes initialized */
    private boolean                     nodesInited = false;


    // init ................................................................................

    /** Create morphism children with the default factory.
    * The children are initially unfiltered.
    * @param element attached class element (non-<code>null</code>)
    */
    public MorphismChildren(final MorphismElement element) {
        this(DefaultFactory.READ_WRITE, element);
    }

    /** Create class children.
    * The children are initially unfiltered.
    * @param factory the factory to use to create new children
    * @param element attached class element (non-<code>null</code>)
    */
    public MorphismChildren(final ElementNodeFactory factory, final MorphismElement element) {
        super();
        this.element = element;
        this.factory = factory;
        this.filter = null;
    }


    /********** Implementation of filter cookie **********/

    /* @return The class of currently asociated filter or null
    * if no filter is asociated with these children.
    */
    public Class getFilterClass () {
        return MorphismElementFilter.class;
    }

    /* @return The filter currently asociated with these children
    */
    public Object getFilter () {
        return filter;
    }

    /* Sets new filter for these children.
    * @param filter New filter. Null == disable filtering.
    */
    public void setFilter (final Object filter) {
        if (!(filter instanceof MorphismElementFilter)) throw new IllegalArgumentException();
        this.filter = (MorphismElementFilter)filter;
        // change element nodes according to the new filter
        if (nodesInited) refreshAllKeys ();
    }


    // Children implementation ..............................................................

    /* Overrides initNodes to run the preparation task of the
    * source element, call refreshKeys and start to
    * listen to the changes in the element too. */
    protected void addNotify () {
        refreshAllKeys ();
        // listen to the changes in the class element
        if (wPropL == null) {
            propL = new ElementListener();
            wPropL = WeakListener.propertyChange (propL, element);
        }
        element.addPropertyChangeListener (wPropL);
        nodesInited = true;
    }

    protected void removeNotify () {
        setKeys (java.util.Collections.EMPTY_SET);
        nodesInited = false;
    }
    
    private Node hookNodeName(Node n) {
        MemberElement el = (MemberElement)n.getCookie(MemberElement.class);
        if (el != null)
            el.addPropertyChangeListener(wPropL);
        return n;
    }

    /* Creates node for given key.
    * The node is created using node factory.
    */
    protected Node[] createNodes (final Object key) {
        System.out.println("MorphismChildren.createNodes with key="+key);
        if (key != null) {
            return new Node[] { hookNodeName(factory.createUnitIDObjectNode(key)) };
        }
        // ?? unknown type
        return new Node[0];
    }


    /************** utility methods ************/

    /** Updates all the keys (elements) according to the current filter &
    * ordering.
    */
    protected void refreshAllKeys () {
        cpl = new Collection [getOrder ().length];
        refreshKeys (MorphismElementFilter.ALL);
    }

    protected void refreshKeys (int filter, Object oldValue, Object newValue) {
	refreshKeys(filter);
    }

    /** Updates all the keys with given filter.
    */
    protected void refreshKeys (int filter) {
        int[] order = getOrder ();
        LinkedList keys = new LinkedList();
        // build ordered and filtered keys for the subelements
        for (int i = 0; i < order.length; i++) {
            if (((order[i] & filter) != 0) || (cpl [i] == null))
                keys.addAll (cpl [i] = getKeysOfType (order[i]));
            else
                keys.addAll (cpl [i]);
        }
        // set new keys
        setKeys(keys);
    }

    /** Filters and returns the keys of specified type.
    */
    protected Collection getKeysOfType (final int elementType) {
        LinkedList keys = new LinkedList();
        if ((elementType & MorphismElementFilter.SOURCE) != 0) {
            keys.add(element.getSourceUnitID());
        }
        if ((elementType & MorphismElementFilter.TARGET) != 0) {
            keys.add(element.getTargetUnitID());
        }
        if ((filter == null) || filter.isSorted ())
            Collections.sort(keys, comparator);
        return keys;
    }

    /** Returns order form filter.
    */
    protected int[] getOrder () {
        return (filter == null || (filter.getOrder() == null))
               ? MorphismElementFilter.DEFAULT_ORDER : filter.getOrder();
    }

    /** The listener for listening to the property changes in the filter.
    */
    private final class ElementListener implements PropertyChangeListener {
        /** This method is called when the change of properties occurs in the element.
        * PENDING - (should be implemented better, change only the
        * keys which belong to the changed property).
        */
        public void propertyChange (PropertyChangeEvent evt) {
            Object src = evt.getSource();
            String propName = evt.getPropertyName();
            int filter = 0;
	    Object oldValue = evt.getOldValue();
	    Object newValue = evt.getNewValue();
            
            if (src != element) {
/*                if (src instanceof MemberElement &&
                    (propName == null || ElementProperties.PROP_NAME == propName)) {
                    if (src instanceof URIElement && oldValue instanceof URIElement) {
                        if (((URIElement)oldValue).getPath().equals(element.getSourceURI().getPath())) {
                            filter = MorphismElementFilter.SOURCE;
                        } else if (((URIElement)oldValue).getPath().equals(element.getDestinationURI().getPath())) {
                            filter = MorphismElementFilter.TARGET;
                        }
                    }
                } else
                    return;*/
            } else {
               Integer i = (Integer) propToFilter.get (propName);
               if (i == null)
                   return;
               filter = i.intValue();
            }
            refreshKeys (filter, oldValue, newValue);
        }
    } // end of ElementListener inner class
}
