/*
 * SourceChildren.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.6  2003/07/05 07:46:39  lambert
 * *** empty log message ***
 *
 * Revision 1.5  2003/04/23 01:15:44  weilyn
 * ClaimCustomizer.java
 *
 * Revision 1.4  2003/04/01 02:29:40  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.3  2003/03/29 03:13:59  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.2  2003/03/14 04:14:21  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:11  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Arrays;
import java.util.List;

import org.openide.nodes.Children;
import org.openide.nodes.Node;
import org.openide.cookies.FilterCookie;
import org.openide.util.WeakListener;
import org.openide.util.Task;

import edu.kestrel.netbeans.model.*;

/** Normal implementation of children for source element nodes.
* <P>
* Ordering and filtering of the children can be customized
* using {@link SourceElementFilter}.
* {@link FilterCookie} is implemented to provide a means
* for user customization of the filter.
* <p>The child list listens to changes in the source element, as well as the filter, and
* automatically updates itself as appropriate.
* <p>A child factory can be used to cause the children list to create
* non-{@link DefaultFactory default} child nodes, if desired, both at the time of the creation
* of the children list, and when new children are added.
* <p>The children list may be unattached to any source element temporarily,
* in which case it will have no children (except possibly an error indicator).
*
*/
public class SourceChildren extends Children.Keys implements FilterCookie {

    /** The key describing state of source element */
    static final Object                   NOT_KEY = new Object();
    /** The key describing state of source element */
    static final Object                   ERROR_KEY = new Object();

    /** The element whose subelements are represented. */
    protected SourceElement               element;
    /** Filter for elements. Can be <code>null</code>, in which case
    * modifier filtering is disabled, and ordering may be reset to the default order. */
    protected SourceElementFilter         filter;
    /** Factory for obtaining class nodes. */
    protected ElementNodeFactory          factory;
    /** Weak listener to the element and filter changes */
    private PropertyChangeListener        wPropL;
    /** Listener to the element and filter changes. This reference must
    * be kept to prevent the listener from finalizing when we are alive */
    private ElementListener               propL;
    /** Flag saying whether we have our nodes initialized */
    private boolean                       nodesInited = false;


    // init ................................................................................

    /** Create a children list with the default factory and no attached source element.
    */
    public SourceChildren () {
        this (DefaultFactory.READ_WRITE, null);
    }

    /** Create a children list with the default factory.
    * @param element source element to attach to, or <code>null</code>
    */
    public SourceChildren (final SourceElement element) {
        this(DefaultFactory.READ_WRITE, element);
    }

    /** Create a children list with no attached source element.
    * @param factory a factory for creating children
    */
    public SourceChildren (final ElementNodeFactory factory) {
        this(factory, null);
    }

    /** Create a children list.
    * @param factory a factory for creating children
    * @param element source element to attach to, or <code>null</code>
    */
    public SourceChildren (final ElementNodeFactory factory,
                           final SourceElement element) {
        super();
        this.element = element;
        this.factory = factory;
        this.filter = new SourceElementFilter ();
    }


    // FilterCookie implementation .............................................................

    /* @return The class of currently asociated filter or null
    * if no filter is asociated with these children.
    */
    public Class getFilterClass () {
        return SourceElementFilter.class;
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
        if (!(filter instanceof SourceElementFilter))
            throw new IllegalArgumentException();

        this.filter = (SourceElementFilter)filter;
        // change element nodes according to the new filter
        if (nodesInited)
            refreshKeys ();
    }


    // Children implementation ..............................................................

    /* Overrides initNodes to run the preparation task of the
    * source element, call refreshKeys and start to
    * listen to the changes in the element too. */
    protected void addNotify () {
        if (element != null) {
            // listen to the source element property changes
            if (wPropL == null) {
                propL = new ElementListener();
                wPropL = WeakListener.propertyChange(propL, element);
            }
            element.addPropertyChangeListener (wPropL);
            element.prepare();
        }
        refreshKeys ();
        nodesInited = true;
    }

    protected void removeNotify () {
        setKeys (java.util.Collections.EMPTY_SET);
        nodesInited = false;
    }

    /* Create nodes for given key.
    * The node is created using node factory.
    */
  protected Node[] createNodes (final Object key) {
    // find out the type of the key and create appropriate node
    if (key instanceof SpecElement) {
      return new Node[] { factory.createSpecNode((SpecElement)key) };
    }
    if (key instanceof ProofElement) {
        return new Node[] { factory.createProofNode((ProofElement)key) };
    }
    if (key instanceof MorphismElement) {
        return new Node[] { factory.createMorphismNode((MorphismElement)key) };
    }
    if (key instanceof DiagramElement) {
        return new Node[] { factory.createDiagramNode((DiagramElement)key) };
    }
    if (key instanceof ColimitElement) {
        return new Node[] { factory.createColimitNode((ColimitElement)key) };
    }
    /*if (key instanceof UnitIdElement) {
        return new Node[] { factory.createUnitIdNode((UnitIdElement)key) };
    }*/
    if (NOT_KEY.equals(key))
      return new Node[] { factory.createWaitNode() };
    // never should get here
    return new Node[] { factory.createErrorNode() };
  }

    /**
     * If `initialize' is true, invokes the parser and waits for it to finish.
     * If false, it just returns whatever nodes are available right now.
     * @return array of nodes after the Children are fully initialized
     */
    public Node[] getNodes(boolean initialize) {
        if (!initialize) {
            return super.getNodes();
        }
        Task t = element.prepare();
        Node[] result;
        
        t.waitFinished();
        refreshKeys();
        result = getNodes();
        t.isFinished();
        return result;
    }

    /* Find a child node.
    * First makes sure any pending parse is done.
    */
    public Node findChild (String name) {
        Node supe = super.findChild (name);
        if (supe != null) {
            return supe;
        } else {
            if (element != null) {
                // this may seem strange, but keeping the Task live till the end of
                // the method may help keeping the structure data in memory
                // (they're referenced from the task most probably)
                org.openide.util.Task t = element.prepare ();
                t.waitFinished ();
                refreshKeys ();
                Node n = super.findChild (name);
                t.isFinished();
                return n;
            } else {
                return null;
            }
        }
    }


    // main public methods ..................................................................

    /** Get the currently attached source element.
    * @return the element, or <code>null</code> if unattached
    */
    public SourceElement getElement () {
        return element;
    }

    /** Set a new source element to get information about children from.
    * @param element the new element, or <code>null</code> to detach
    */
    public void setElement (final SourceElement element) {
        if (this.element != null) {
            this.element.removePropertyChangeListener(wPropL);
        }
        this.element = element;
        if (this.element != null) {
            if (wPropL == null) {
                propL = new ElementListener();
                wPropL = WeakListener.propertyChange(propL, this.element);
            }
            this.element.addPropertyChangeListener(wPropL);
        }
        // change element nodes according to the new element
        if (nodesInited) {
            if (this.element != null) this.element.prepare();
            refreshKeys ();
        }
    }

    // other methods ..........................................................................

    /** Refreshes the keys according to the current state of the element and
    * filter etc.
    * (This method is also called when the change of properties occurs either
    * in the filter or in the element)
    * PENDING - (for Hanz - should be implemented better, change only the
    * keys which belong to the changed property).
    * @param evt the event describing changed property (or null to signalize
    * that all keys should be refreshed)
    */
    private void refreshKeys () {
        int status = (element == null) ? SourceElement.STATUS_ERROR : element.getStatus();
        switch (status) {
        case SourceElement.STATUS_NOT:
            setKeys(new Object[] { NOT_KEY });
            // start parsing
            element.prepare ();
            break;
        case SourceElement.STATUS_ERROR:
            setKeys(new Object[] { ERROR_KEY });
            break;
        case SourceElement.STATUS_PARTIAL:
        case SourceElement.STATUS_OK:
            refreshAllKeys();
            break;
        }
    }

    /** Updates all the keys (elements) according to the current
    * filter and ordering */
    private void refreshAllKeys () {
        int[] order = (filter == null || (filter.getOrder() == null))
                      ? SourceElementFilter.DEFAULT_ORDER : filter.getOrder();

        final LinkedList keys = new LinkedList();
        // build ordered and filtered keys for the subelements
        for (int i = 0; i < order.length; i++)
            addKeysOfType(keys, order[i]);

        // set new keys
        SourceChildren.this.setKeys(keys);
    }

    /** Filters and adds the keys of specified type to the given
    * key collection.
    */
    private void addKeysOfType (Collection keys, final int elementType) {
	if ((elementType & SourceElementFilter.SPEC) != 0) {
	    keys.addAll(Arrays.asList(element.getSpecs()));
	}
        if ((elementType & SourceElementFilter.PROOF) != 0) {
            keys.addAll(Arrays.asList(element.getProofs()));
        }
        if ((elementType & SourceElementFilter.MORPHISM) != 0) {
            keys.addAll(Arrays.asList(element.getMorphisms()));
        }
        if ((elementType & SourceElementFilter.DIAGRAM) != 0) {
            keys.addAll(Arrays.asList(element.getDiagrams()));
        }
        if ((elementType & SourceElementFilter.COLIMIT) != 0) {
            keys.addAll(Arrays.asList(element.getColimits()));
        }
        /*if ((elementType & SourceElementFilter.UnitId) != 0) {
            keys.addAll(Arrays.asList(element.getUnitIds()));
        }*/
    }


    // innerclasses ...........................................................................

    /** The listener for listening to the property changes in the filter.
    */
    private final class ElementListener implements PropertyChangeListener {
        public void propertyChange (PropertyChangeEvent evt) {
            String propName = evt.getPropertyName();
            boolean refresh = (propName.equals(ElementProperties.PROP_SPECS) ||
                               propName.equals(ElementProperties.PROP_PROOFS) ||
                               propName.equals(ElementProperties.PROP_MORPHISMS) ||
                               propName.equals(ElementProperties.PROP_DIAGRAMS) ||
                               propName.equals(ElementProperties.PROP_COLIMITS)/* ||
                               propName.equals(ElementProperties.PROP_UnitIdS)*/);
			       
            if (!refresh && ElementProperties.PROP_STATUS.equals(evt.getPropertyName())) {
                Integer val = (Integer) evt.getNewValue();
                refresh = ((val == null) || (val.intValue() != SourceElement.STATUS_NOT));
            }
	    if (refresh) 
                javax.swing.SwingUtilities.invokeLater(new Runnable() {
                    public void run() {
                        refreshKeys();
                    }
                });
        }

    } // end of ElementListener inner class
}
