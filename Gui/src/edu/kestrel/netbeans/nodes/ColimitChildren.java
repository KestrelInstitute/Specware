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


/** Normal implementation of children list for a colimit element node.
* Semantics are similar to those of {@link SourceChildren}.
*/
public class ColimitChildren extends Children.Keys implements FilterCookie {

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
/*        propToFilter.put (ElementProperties.PROP_IMPORTS, new Integer (SpecElementFilter.IMPORT));        
        propToFilter.put (ElementProperties.PROP_SORTS, new Integer (SpecElementFilter.SORT));
        propToFilter.put (ElementProperties.PROP_OPS, new Integer (SpecElementFilter.OP));
        propToFilter.put (ElementProperties.PROP_DEFS, new Integer (SpecElementFilter.DEF));
        propToFilter.put (ElementProperties.PROP_CLAIMS, new Integer (SpecElementFilter.CLAIM));*/
    }

    /** The colimit element whose subelements are represented. */
    protected ColimitElement              element;
    /** Filter for elements, or <code>null</code> to disable. */
    protected ColimitElementFilter        filter;
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

    /** Create colimit children with the default factory.
    * The children are initially unfiltered.
    * @param element attached class element (non-<code>null</code>)
    */
    public ColimitChildren(final ColimitElement element) {
        this(DefaultFactory.READ_WRITE, element);
    }

    /** Create class children.
    * The children are initially unfiltered.
    * @param factory the factory to use to create new children
    * @param element attached class element (non-<code>null</code>)
    */
    public ColimitChildren(final ElementNodeFactory factory, final ColimitElement element) {
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
        return ColimitElementFilter.class;
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
        if (!(filter instanceof ColimitElementFilter)) throw new IllegalArgumentException();
        this.filter = (ColimitElementFilter)filter;
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
/*        if (key instanceof ImportElement) {
            return new Node[] { hookNodeName(factory.createImportNode((ImportElement)key)) };
        }
        if (key instanceof SortElement) {
            return new Node[] { hookNodeName(factory.createSortNode((SortElement)key)) };
        }
        if (key instanceof OpElement) {
            return new Node[] { hookNodeName(factory.createOpNode((OpElement)key)) };
        }
        if (key instanceof DefElement) {
            return new Node[] { hookNodeName(factory.createDefNode((DefElement)key)) };
        }
        if (key instanceof ClaimElement) {
            return new Node[] { hookNodeName(factory.createClaimNode((ClaimElement)key)) };
        }*/
        // ?? unknown type
        return new Node[0];
    }


    /************** utility methods ************/

    /** Updates all the keys (elements) according to the current filter &
    * ordering.
    */
    protected void refreshAllKeys () {
        cpl = new Collection [getOrder ().length];
        refreshKeys (ColimitElementFilter.ALL);
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
/*        if ((elementType & SpecElementFilter.IMPORT) != 0) {
            keys.addAll(Arrays.asList(element.getImports()));
        }
        if ((elementType & SpecElementFilter.SORT) != 0) {
            keys.addAll(Arrays.asList(element.getSorts()));
        }
        if ((elementType & SpecElementFilter.OP) != 0) {
            keys.addAll(Arrays.asList(element.getOps()));
        }
        if ((elementType & SpecElementFilter.DEF) != 0) {
            keys.addAll(Arrays.asList(element.getDefs()));
        }
        if ((elementType & SpecElementFilter.CLAIM) != 0) {
            keys.addAll(Arrays.asList(element.getClaims()));
        }*/
        if ((filter == null) || filter.isSorted ())
            Collections.sort(keys, comparator);
        return keys;
    }

    /** Returns order form filter.
    */
    protected int[] getOrder () {
        return (filter == null || (filter.getOrder() == null))
               ? ColimitElementFilter.DEFAULT_ORDER : filter.getOrder();
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
                if (src instanceof MemberElement &&
                    (propName == null || ElementProperties.PROP_NAME == propName)) {
/*                    if (src instanceof ImportElement) 
                        filter = SpecElementFilter.IMPORT;
                    else if (src instanceof SortElement) 
                        filter = SpecElementFilter.SORT;
                    else if (src instanceof OpElement) 
                        filter = SpecElementFilter.OP;
                    else if (src instanceof DefElement) 
                        filter = SpecElementFilter.DEF;
                    else if (src instanceof ClaimElement) 
                        filter = SpecElementFilter.CLAIM;*/
                } else
                    return;
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
