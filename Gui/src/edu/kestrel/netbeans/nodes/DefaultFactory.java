/*
 * DefaultFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.4  2003/02/17 04:33:05  weilyn
 * Fixed an out-of-bounds array exception bug and cleaned up context menu actions.
 *
 * Revision 1.3  2003/02/16 02:15:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:42:08  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:06  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.*;
import java.util.ArrayList;
import java.util.TreeSet;
import java.util.Collection;
import java.util.Vector;

import org.openide.actions.*;
import org.openide.nodes.*;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;
import org.openide.util.actions.SystemAction;
import org.openide.util.datatransfer.NewType;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;

/** The default implementation of the hierarchy nodes factory.
 * Uses the standard node implementations in this package.
 */
public class DefaultFactory extends Object implements ElementNodeFactory, IconStrings { 
  public static final Node[] EMPTY = new Node[0];
  
  /** Default instance of the factory with read-write properties. */
  public static final DefaultFactory READ_WRITE = new DefaultFactory(true);
  
  /** Default instance of the factory with read-only properties. */
  public static final DefaultFactory READ_ONLY = new DefaultFactory(false);
  
  public static final Integer[] CATEGORIES;
  
  private static final int FILTER_CATEGORIES = 0x1000;
  
  static {
    CATEGORIES = new Integer[5];
    for (int i = 0; i < 5; i++) {
      CATEGORIES[i] = new Integer(i);
    }
  }
  
  static Integer filterToCategory(int filter) {
    switch (filter) {
    case 1: return CATEGORIES[0];
    case 2: return CATEGORIES[1];
    case 4: return CATEGORIES[2];
    case 8: return CATEGORIES[3];
    case 16: return CATEGORIES[4];
    }
    return null;
  }
  
  /** Should be the element nodes read-only or writeable
   * (properties, clipboard operations,...)
   */
  private boolean writeable;
  
  /** Create a new factory.
   * @param writeable <code>true</code> if the produced nodes
   * should have writable properties
   * @see ElementNode#writeable
   */
  public DefaultFactory(boolean writeable) {
    this.writeable = writeable;
  }
  
  /* Test whether this factory produces writeable nodes.
   * @return <code>true</code> if so
   */
  public boolean isWriteable() {
    return writeable;
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createSpecNode (SpecElement element) {
    return new SpecElementNode(element, createSpecChildren(element), writeable);
  }

  /** Create children for a spec node.
   * Could be subclassed to customize, e.g., the ordering of children.
   * The default implementation used {@link SpecChildren}.
   * @param element a spec element
   * @return children for the spec element
   */
  protected Children createSpecChildren(SpecElement element) {
    return createSpecChildren( element, writeable ? READ_WRITE : READ_ONLY );
  }

  /** Create children for a spec node, with specified factory.
   * The default implementation used {@link SpecChildren}.
   * @param element a spec element
   * @param factory the factory which will be used to create children
   * @return children for the spec element
   */
  final protected Children createSpecChildren(SpecElement element, ElementNodeFactory factory ) {
    if (ElementNode.sourceOptions.getCategoriesUsage()) {
      SpecChildren children = new SpecCategorizingChildren(factory, element, writeable);
      SpecElementFilter filter = new SpecElementFilter();
      filter.setOrder(new int[] {FILTER_CATEGORIES});
      children.setFilter(filter);
      return children;
    }
    else {
      return new SpecChildren(factory, element);
    }
  }
    

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createSortNode (final SortElement element) {
    return new SortElementNode(element, writeable);
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createOpNode (final OpElement element) {
    return new OpElementNode(element, writeable);
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createDefNode (final DefElement element) {
    return new DefElementNode(element, writeable);
  }

  /** Make a node representing a claim.
   * @param element the claim
   * @return a claim node instance
   *
   */
  public Node createClaimNode(ClaimElement element) {
    return new ClaimElementNode(element, writeable);
  }

  /** Make a node representing an import.
   * @param element the import
   * @return an import node instance
   *
   */
  public Node createImportNode(ImportElement element) {
    return new ImportElementNode(element, writeable);
  }

  /* Creates and returns the instance of the node
   * representing the status 'WAIT' of the DataNode.
   * It is used when it spent more time to create elements hierarchy.
   * @return the wait node.
   */
  public Node createWaitNode () {
    AbstractNode n = new AbstractNode(Children.LEAF);
    n.setName(ElementNode.bundle.getString("Wait"));
    n.setIconBase(WAIT);
    return n;
  }

  /* Creates and returns the instance of the node
   * representing the status 'ERROR' of the DataNode
   * @return the error node.
   */
  public Node createErrorNode () {
    AbstractNode n = new AbstractNode(Children.LEAF);
    n.setName(ElementNode.bundle.getString("Error")); // NO18N
    n.setIconBase(ERROR);
    return n;
  }

  
  /** Array of the actions of the category nodes. */
  private static final SystemAction[] CATEGORY_ACTIONS = new SystemAction[] {
    /*
      SystemAction.get(CopyAction.class),
    */
    SystemAction.get(PasteAction.class),
    null,
    SystemAction.get(NewAction.class),
    //null,
    //SystemAction.get(ToolsAction.class),
    //SystemAction.get(PropertiesAction.class)
  };

  /** Filters under each category node */
  static final int[][] FILTERS = new int[][] {
    { SpecElementFilter.IMPORT },
    { SpecElementFilter.SORT },
    { SpecElementFilter.OP },
    { SpecElementFilter.DEF },
    { SpecElementFilter.CLAIM }
  };

  /** The names of the category nodes */
  static final String[] NAMES = new String[] {
    ElementNode.bundle.getString("Imports"), //NO18N
    ElementNode.bundle.getString("Sorts"), // NO18N
    ElementNode.bundle.getString("Ops"), // NO18N
    ElementNode.bundle.getString("Defs"), // NO18N
    ElementNode.bundle.getString("Claims"), // NO18N
  };

  /** The short descriptions of the category nodes */
  static final String[] SHORTDESCRS = new String[] {
    ElementNode.bundle.getString("Imports_HINT"), //NO18N
    ElementNode.bundle.getString("Sorts_HINT"), // NO18N
    ElementNode.bundle.getString("Ops_HINT"), // NO18N
    ElementNode.bundle.getString("Defs_HINT"), // NO18N
    ElementNode.bundle.getString("Claims_HINT"), // NO18N
  };

  /** Help IDs for the individual categories */
  static final String[] HELP_IDS = new String[] {
    "org.openide.src.nodes.ElementCategory.Imports", // NO18N
    "org.openide.src.nodes.ElementCategory.Sorts", // NO18N
    "org.openide.src.nodes.ElementCategory.Ops", // NO18N
    "org.openide.src.nodes.ElementCategory.Defs", // NO18N
    "org.openide.src.nodes.ElementCategory.Claims" // NO18N
  };

  /** Array of the icons used for category nodes */
  static final String[] SPEC_CATEGORY_ICONS = new String[] {
    IMPORTS_CATEGORY,
    SORTS_CATEGORY,
    OPS_CATEGORY,
    DEFS_CATEGORY,
    CLAIMS_CATEGORY
  };

  /*
   * Simple descendant of SpecChildren that distributes nodes from the spec to various
   * categories. 
   */
  static class SpecCategorizingChildren extends SpecChildren {
    boolean writeable;
    TreeSet activeCategories;
        
    SpecCategorizingChildren(ElementNodeFactory factory, SpecElement data, boolean wr) {
      super(factory, data);
      writeable = wr;
      initializeCategories();
    }

    private void initializeCategories() {
      activeCategories = new TreeSet();
      if (element.getImports().length > 0) {
        activeCategories.add(CATEGORIES[0]);
      }
      if (element.getSorts().length > 0) {
	activeCategories.add(CATEGORIES[1]);
      }
      if (element.getOps().length > 0) {
	activeCategories.add(CATEGORIES[2]);
      }
      if (element.getDefs().length > 0) {
	activeCategories.add(CATEGORIES[3]);
      }
      if (element.getClaims().length > 0) {
	activeCategories.add(CATEGORIES[4]);
      }      
    }
        
    protected Node[] createNodes(Object key) {
      if (key instanceof Integer) {
	return new Node[]{new SpecElementCategoryNode(((Integer)key).intValue(), factory, element, writeable)};
      } 
      return super.createNodes(key);
    }
        
    protected void addCategory(int filter) {
      activeCategories.add(filterToCategory(filter));
    }

    protected void removeCategory(int filter) {
      activeCategories.remove(filterToCategory(filter));
    }

    protected void refreshKeys (int filter, Object oldValue, Object newValue) {
      boolean emptyOld = ((Element[])oldValue).length == 0;
      boolean emptyNew = ((Element[])newValue).length == 0;
      if (emptyOld && !emptyNew) {
	addCategory(filter);
      } else if (!emptyOld && emptyNew) {
	removeCategory(filter);
      }
      super.refreshKeys(filter);
    }

    protected Collection getKeysOfType(int type) {
      if (type == FILTER_CATEGORIES) {
	return activeCategories;
      }
      return super.getKeysOfType(type);
    }
  }
    

  /**
   * Category node - represents one section under spec element node - imports, sorts, 
   * ops, defs, claims.
   */
  static class SpecElementCategoryNode extends AbstractNode {

    /** The spec element for this node */
    SpecElement element;

    /** The type of the category node - for new types. */
    int newTypeIndex;
        
    /** The Help context ID for this node. */
    String  helpID;

    /** Create new element category node for the specific category.
     * @param index The index of type 
     * @param factory The factory which is passed down to the spec children object
     * @param element the spec element which this node is created for
     */
    SpecElementCategoryNode(int index, ElementNodeFactory factory, SpecElement element, boolean writeable) {
      this(index, new SpecChildren(factory, element));
      this.element = element;
      newTypeIndex = writeable ? index : -1;
      switch (index) {
      case 0: setName("Imports"); break; //NOI18N
      case 1: setName("Sorts"); break; // NOI18N
      case 2: setName("Ops"); break; // NOI18N
      case 3: setName("Defs"); break; // NOI18N
      case 4: setName("Claims"); break; // NOI18N
      }
    }

    /** Create new element node.
     * @param index The index of type (0=imports, 1=sorts, 2=ops, 3=defs, 4=claims)
     * @param children the spec children of this node
     */
    private SpecElementCategoryNode(int index, SpecChildren children) {
      super(children);
      setDisplayName(NAMES[index]);
      setShortDescription (SHORTDESCRS[index]);
      helpID = HELP_IDS[index];
      SpecElementFilter filter = new SpecElementFilter();
      filter.setOrder(FILTERS[index]);
      children.setFilter(filter);
      systemActions = CATEGORY_ACTIONS;
      setIconBase(SPEC_CATEGORY_ICONS[index]);
    }

    public org.openide.util.HelpCtx getHelpCtx () {
      return new org.openide.util.HelpCtx (helpID);
    }
	
    /** Disables copy for the whole category. Sub-elements need to be selected individually.
     */
    public boolean canCopy() {
      return false;
    }

    /* Get the new types that can be created in this node.
     * @return array of new type operations that are allowed
     */
    public NewType[] getNewTypes() {
      if (!SourceEditSupport.isWriteable(element)) {
	return new NewType[0];
      }
      switch (newTypeIndex) {
      case 0:
	return new NewType[] {
	  new SourceEditSupport.SpecElementNewType(element, (byte) 0)
	    };
      case 1:
	return new NewType[] {
	  new SourceEditSupport.SpecElementNewType(element, (byte) 1),
	    };
      case 2:
	return new NewType[] {
	  new SourceEditSupport.SpecElementNewType(element, (byte) 2),
	    };
      case 3:
	return new NewType[] {
	  new SourceEditSupport.SpecElementNewType(element, (byte) 3),
	    };
      case 4:
	return new NewType[] {
	  new SourceEditSupport.SpecElementNewType(element, (byte) 4),
	    };            
      default:
	return super.getNewTypes();
      }
    }

    public void createPasteTypes(java.awt.datatransfer.Transferable t, java.util.List s) {
      Node n = getParentNode();
      if (n == null || !(n instanceof SpecElementNode)) {
	return;
      }
      ((SpecElementNode)n).createPasteTypes(t, s);
    }
  }

}
