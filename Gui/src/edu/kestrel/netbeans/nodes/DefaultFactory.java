/*
 * DefaultFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.12  2003/07/05 07:46:38  lambert
 * *** empty log message ***
 *
 * Revision 1.11  2003/06/23 18:00:16  weilyn
 * internal release version
 *
 * Revision 1.10  2003/04/26 02:36:06  weilyn
 * Commented out MorphismCategorizingChildren.refreshKeys because it gave exceptions on UnitID classes
 *
 * Revision 1.9  2003/04/23 01:15:42  weilyn
 * ClaimCustomizer.java
 *
 * Revision 1.8  2003/04/01 02:29:39  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:13:58  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:14:21  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:06:34  weilyn
 * Added support for imports.
 *
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

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createProofNode (ProofElement element) {
    return new ProofElementNode(element, createProofChildren(element), writeable);
  }

  /** Create children for a proof node.
   * Could be subclassed to customize, e.g., the ordering of children.
   * The default implementation used {@link ProofChildren}.
   * @param element a proof element
   * @return children for the proof element
   */
  protected Children createProofChildren(ProofElement element) {
    return createProofChildren( element, writeable ? READ_WRITE : READ_ONLY );
  }

  /** Create children for a proof node, with specified factory.
   * The default implementation used {@link SpecChildren}.
   * @param element a proof element
   * @param factory the factory which will be used to create children
   * @return children for the proof element
   */
  final protected Children createProofChildren(ProofElement element, ElementNodeFactory factory ) {
    if (ElementNode.sourceOptions.getCategoriesUsage()) {
      ProofChildren children = new ProofCategorizingChildren(factory, element, writeable);
      ProofElementFilter filter = new ProofElementFilter();
      filter.setOrder(new int[] {FILTER_CATEGORIES});
      children.setFilter(filter);
      return children;
    }
    else {
      return new ProofChildren(factory, element);
    }
  }
  
  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createMorphismNode (MorphismElement element) {
    return new MorphismElementNode(element, createMorphismChildren(element), writeable);
  }

  /** Create children for a morphism node.
   * Could be subclassed to customize, e.g., the ordering of children.
   * The default implementation used {@link MorphismChildren}.
   * @param element a morphism element
   * @return children for the morphism element
   */
  protected Children createMorphismChildren(MorphismElement element) {
    return createMorphismChildren( element, writeable ? READ_WRITE : READ_ONLY );
  }

  /** Create children for a morphism node, with specified factory.
   * The default implementation used {@link SpecChildren}.
   * @param element a morphism element
   * @param factory the factory which will be used to create children
   * @return children for the morphism element
   */
  final protected Children createMorphismChildren(MorphismElement element, ElementNodeFactory factory ) {
    if (ElementNode.sourceOptions.getCategoriesUsage()) {
      MorphismChildren children = new MorphismCategorizingChildren(factory, element, writeable);
      MorphismElementFilter filter = new MorphismElementFilter();
      filter.setOrder(new int[] {FILTER_CATEGORIES});
      children.setFilter(filter);
      return children;
    }
    else {
      return new MorphismChildren(factory, element);
    }
  }
  
    public Node createUnitIDObjectNode(Object object) {
	return new UnitIDObjectNode(object);
    }
    
    /** Make a node representing a diagElem
   * @param element the diagElem
   * @return a diagElem node instance
   *
   */
  public Node createDiagElemNode(DiagElemElement element) {
    return new DiagElemElementNode(element, writeable);
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createDiagramNode (DiagramElement element) {
    return new DiagramElementNode(element, createDiagramChildren(element), writeable);
  }

  /** Create children for a diagram node.
   * Could be subclassed to customize, e.g., the ordering of children.
   * The default implementation used {@link DiagramChildren}.
   * @param element a diagram element
   * @return children for the diagram element
   */
  protected Children createDiagramChildren(DiagramElement element) {
    return createDiagramChildren( element, writeable ? READ_WRITE : READ_ONLY );
  }

  /** Create children for a diagram node, with specified factory.
   * The default implementation used {@link SpecChildren}.
   * @param element a diagram element
   * @param factory the factory which will be used to create children
   * @return children for the diagram element
   */
  final protected Children createDiagramChildren(DiagramElement element, ElementNodeFactory factory ) {
    if (ElementNode.sourceOptions.getCategoriesUsage()) {
      DiagramChildren children = new DiagramCategorizingChildren(factory, element, writeable);
      DiagramElementFilter filter = new DiagramElementFilter();
      filter.setOrder(new int[] {FILTER_CATEGORIES});
      children.setFilter(filter);
      return children;
    }
    else {
      return new DiagramChildren(factory, element);
    }
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  public Node createColimitNode (ColimitElement element) {
    return new ColimitElementNode(element, createColimitChildren(element), writeable);
  }

  /** Create children for a colimit node.
   * Could be subclassed to customize, e.g., the ordering of children.
   * The default implementation used {@link ColimitChildren}.
   * @param element a colimit element
   * @return children for the colimit element
   */
  protected Children createColimitChildren(ColimitElement element) {
    return createColimitChildren( element, writeable ? READ_WRITE : READ_ONLY );
  }

  /** Create children for a colimit node, with specified factory.
   * The default implementation used {@link SpecChildren}.
   * @param element a colimit element
   * @param factory the factory which will be used to create children
   * @return children for the colimit element
   */
  final protected Children createColimitChildren(ColimitElement element, ElementNodeFactory factory ) {
/*    if (ElementNode.sourceOptions.getCategoriesUsage()) {
      ColimitChildren children = new ColimitCategorizingChildren(factory, element, writeable);
      ColimitElementFilter filter = new ColimitElementFilter();
      filter.setOrder(new int[] {FILTER_CATEGORIES});
      children.setFilter(filter);
      return children;
    }
    else {*/
      return new ColimitChildren(factory, element);
    //}
  }

  /* Returns the node asociated with specified element.
   * @return ElementNode
   */
  /*public Node createUnitIdNode (final UnitIdElement element) {
    return new UnitIdElementNode(element, writeable);
  }*/
  
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

  /** Filters under each spec category node */
  static final int[][] SPEC_FILTERS = new int[][] {
    { SpecElementFilter.IMPORT },
    { SpecElementFilter.SORT },
    { SpecElementFilter.OP },
    { SpecElementFilter.DEF },
    { SpecElementFilter.CLAIM }
  };

  /** The names of the spec category nodes */
  static final String[] SPEC_NAMES = new String[] {
    ElementNode.bundle.getString("Imports"), //NO18N
    ElementNode.bundle.getString("Sorts"), // NO18N
    ElementNode.bundle.getString("Ops"), // NO18N
    ElementNode.bundle.getString("Defs"), // NO18N
    ElementNode.bundle.getString("Claims"), // NO18N
  };

  /** The short descriptions of the spec category nodes */
  static final String[] SPEC_SHORTDESCRS = new String[] {
    ElementNode.bundle.getString("Imports_HINT"), //NO18N
    ElementNode.bundle.getString("Sorts_HINT"), // NO18N
    ElementNode.bundle.getString("Ops_HINT"), // NO18N
    ElementNode.bundle.getString("Defs_HINT"), // NO18N
    ElementNode.bundle.getString("Claims_HINT"), // NO18N
  };

  /** Help IDs for the individual categories */
  static final String[] SPEC_HELP_IDS = new String[] {
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

  /** Filters under each proof category node */
  static final int[][] PROOF_FILTERS = new int[][] {
  };

  /** The names of the proof category nodes */
  static final String[] PROOF_NAMES = new String[] {
  };

  /** The short descriptions of the proof category nodes */
  static final String[] PROOF_SHORTDESCRS = new String[] {
  };

  /** Help IDs for the individual categories */
  static final String[] PROOF_HELP_IDS = new String[] {
  };
  
  /** Array of the icons used for category nodes */
  static final String[] PROOF_CATEGORY_ICONS = new String[] {
  };

  /** Filters under each morphism category node */
  static final int[][] MORPHISM_FILTERS = new int[][] {
    { MorphismElementFilter.SOURCE },
    { MorphismElementFilter.TARGET },
  };

  /** The names of the morphism category nodes */
  static final String[] MORPHISM_NAMES = new String[] {
    ElementNode.bundle.getString("Source"), //NO18N
    ElementNode.bundle.getString("Target"), // NO18N
  };

  /** The short descriptions of the morphism category nodes */
  static final String[] MORPHISM_SHORTDESCRS = new String[] {
    ElementNode.bundle.getString("Source_HINT"), //NO18N
    ElementNode.bundle.getString("Target_HINT"), // NO18N
  };

  /** Help IDs for the individual categories */
  static final String[] MORPHISM_HELP_IDS = new String[] {
    "org.openide.src.nodes.ElementCategory.Source", // NO18N
    "org.openide.src.nodes.ElementCategory.Target", // NO18N
  };
  
  /** Array of the icons used for category nodes */
  static final String[] MORPHISM_CATEGORY_ICONS = new String[] {
    SOURCE_CATEGORY,
    TARGET_CATEGORY,
  };
  
  /** Filters under each diagram category node */
  static final int[][] DIAGRAM_FILTERS = new int[][] {
      { DiagramElementFilter.DIAG_ELEM },
  };

  /** The names of the diagram category nodes */
  static final String[] DIAGRAM_NAMES = new String[] {
      ElementNode.bundle.getString("DiagElems"), //NO18N
  };

  /** The short descriptions of the diagram category nodes */
  static final String[] DIAGRAM_SHORTDESCRS = new String[] {
      ElementNode.bundle.getString("DiagElems_HINT"), //NO18N
  };

  /** Help IDs for the individual categories */
  static final String[] DIAGRAM_HELP_IDS = new String[] {
      "org.openide.src.nodes.ElementCategory.DiagElems", // NO18N
  };
  
  /** Array of the icons used for category nodes */
  static final String[] DIAGRAM_CATEGORY_ICONS = new String[] {
      DIAG_ELEMS_CATEGORY,
  };
  
  /** Filters under each colimit category node */
  static final int[][] COLIMIT_FILTERS = new int[][] {
    { ColimitElementFilter.DIAGRAM },
  };

  /** The names of the colimit category nodes */
  static final String[] COLIMIT_NAMES = new String[] {
    ElementNode.bundle.getString("Diagrams"), //NO18N
  };

  /** The short descriptions of the colimit category nodes */
  static final String[] COLIMIT_SHORTDESCRS = new String[] {
    ElementNode.bundle.getString("Diagrams_HINT"), //NO18N
  };

  /** Help IDs for the individual categories */
  static final String[] COLIMIT_HELP_IDS = new String[] {
    "org.openide.src.nodes.ElementCategory.Diagrams", // NO18N
  };
  
  /** Array of the icons used for category nodes */
  static final String[] COLIMIT_CATEGORY_ICONS = new String[] {
      DIAGRAMS_CATEGORY,
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
        Util.log("DefaultFactory.Spec.createNodes");
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
      setDisplayName(SPEC_NAMES[index]);
      setShortDescription (SPEC_SHORTDESCRS[index]);
      helpID = SPEC_HELP_IDS[index];
      SpecElementFilter filter = new SpecElementFilter();
      filter.setOrder(SPEC_FILTERS[index]);
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

  /*
   * Simple descendant of ProofChildren that distributes nodes from the proof to various
   * categories. 
   */
  static class ProofCategorizingChildren extends ProofChildren {
    boolean writeable;
    TreeSet activeCategories;
        
    ProofCategorizingChildren(ElementNodeFactory factory, ProofElement data, boolean wr) {
      super(factory, data);
      writeable = wr;
      initializeCategories();
    }

    private void initializeCategories() {
      activeCategories = new TreeSet();
/*      if (element.getImports().length > 0) {
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
      } */     
    }
        
    protected Node[] createNodes(Object key) {
      if (key instanceof Integer) {
	return new Node[]{new ProofElementCategoryNode(((Integer)key).intValue(), factory, element, writeable)};
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
   * Category node - represents one section under proof element node.
   */
  static class ProofElementCategoryNode extends AbstractNode {

    /** The proof element for this node */
    ProofElement element;

    /** The type of the category node - for new types. */
    int newTypeIndex;
        
    /** The Help context ID for this node. */
    String  helpID;

    /** Create new element category node for the specific category.
     * @param index The index of type 
     * @param factory The factory which is passed down to the proof children object
     * @param element the proof element which this node is created for
     */
    ProofElementCategoryNode(int index, ElementNodeFactory factory, ProofElement element, boolean writeable) {
      this(index, new ProofChildren(factory, element));
      this.element = element;
      newTypeIndex = writeable ? index : -1;
      switch (index) {
/*      case 0: setName("Imports"); break; //NOI18N
      case 1: setName("Sorts"); break; // NOI18N
      case 2: setName("Ops"); break; // NOI18N
      case 3: setName("Defs"); break; // NOI18N
      case 4: setName("Claims"); break; // NOI18N*/
      }
    }

    /** Create new element node.
     * @param index The index of type (0=imports, 1=sorts, 2=ops, 3=defs, 4=claims)
     * @param children the proof children of this node
     */
    private ProofElementCategoryNode(int index, ProofChildren children) {
      super(children);
      setDisplayName(PROOF_NAMES[index]);
      setShortDescription (PROOF_SHORTDESCRS[index]);
      helpID = PROOF_HELP_IDS[index];
      ProofElementFilter filter = new ProofElementFilter();
      filter.setOrder(PROOF_FILTERS[index]);
      children.setFilter(filter);
      systemActions = CATEGORY_ACTIONS;
      setIconBase(PROOF_CATEGORY_ICONS[index]);
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
/*      case 0:
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
	    };            */
      default:
	return super.getNewTypes();
      }
    }

    public void createPasteTypes(java.awt.datatransfer.Transferable t, java.util.List s) {
      Node n = getParentNode();
      if (n == null || !(n instanceof ProofElementNode)) {
	return;
      }
      ((ProofElementNode)n).createPasteTypes(t, s);
    }
  }

  /*
   * Simple descendant of MorphismChildren that distributes nodes from the morphism to various
   * categories. 
   */
  static class MorphismCategorizingChildren extends MorphismChildren {
    boolean writeable;
    TreeSet activeCategories;
        
    MorphismCategorizingChildren(ElementNodeFactory factory, MorphismElement data, boolean wr) {
      super(factory, data);
      writeable = wr;
      initializeCategories();
    }

    private void initializeCategories() {
      activeCategories = new TreeSet();
      if (element.getSourceUnitID() != null) {
        activeCategories.add(CATEGORIES[0]);
      }
      if (element.getTargetUnitID() != null) {
	activeCategories.add(CATEGORIES[1]);
      }
/*      if (element.getOps().length > 0) {
	activeCategories.add(CATEGORIES[2]);
      }
      if (element.getDefs().length > 0) {
	activeCategories.add(CATEGORIES[3]);
      }
      if (element.getClaims().length > 0) {
	activeCategories.add(CATEGORIES[4]);
      } */     
    }
        
    protected Node[] createNodes(Object key) {
      if (key instanceof Integer) {
	return new Node[]{new MorphismElementCategoryNode(((Integer)key).intValue(), factory, element, writeable)};
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
/*      boolean emptyOld = ((UnitID[])oldValue).length == 0;
      boolean emptyNew = ((UnitID[])newValue).length == 0;
      if (emptyOld && !emptyNew) {
	addCategory(filter);
      } else if (!emptyOld && emptyNew) {
	removeCategory(filter);
      }*/
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
   * Category node - represents one section under morphism element node.
   */
  static class MorphismElementCategoryNode extends AbstractNode {

    /** The morphism element for this node */
    MorphismElement element;

    /** The type of the category node - for new types. */
    int newTypeIndex;
        
    /** The Help context ID for this node. */
    String  helpID;

    /** Create new element category node for the specific category.
     * @param index The index of type 
     * @param factory The factory which is passed down to the morphism children object
     * @param element the morphism element which this node is created for
     */
    MorphismElementCategoryNode(int index, ElementNodeFactory factory, MorphismElement element, boolean writeable) {
      this(index, new MorphismChildren(factory, element));
      this.element = element;
      newTypeIndex = writeable ? index : -1;
      switch (index) {
      case 0: setName("Source"); break; //NOI18N
      case 1: setName("Target"); break; // NOI18N
/*      case 2: setName("Ops"); break; // NOI18N
      case 3: setName("Defs"); break; // NOI18N
      case 4: setName("Claims"); break; // NOI18N*/
      }
    }

    /** Create new element node.
     * @param index The index of type (0=imports, 1=sorts, 2=ops, 3=defs, 4=claims)
     * @param children the morphism children of this node
     */
    private MorphismElementCategoryNode(int index, MorphismChildren children) {
      super(children);
      setDisplayName(MORPHISM_NAMES[index]);
      setShortDescription (MORPHISM_SHORTDESCRS[index]);
      helpID = MORPHISM_HELP_IDS[index];
      MorphismElementFilter filter = new MorphismElementFilter();
      filter.setOrder(MORPHISM_FILTERS[index]);
      children.setFilter(filter);
      systemActions = CATEGORY_ACTIONS;
      setIconBase(MORPHISM_CATEGORY_ICONS[index]);
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
/*      case 0:
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
	    };            */
      default:
	return super.getNewTypes();
      }
    }

    public void createPasteTypes(java.awt.datatransfer.Transferable t, java.util.List s) {
      Node n = getParentNode();
      if (n == null || !(n instanceof MorphismElementNode)) {
	return;
      }
      ((MorphismElementNode)n).createPasteTypes(t, s);
    }
  }

  /*
   * Simple descendant of DiagramChildren that distributes nodes from the diagram to various
   * categories. 
   */
  static class DiagramCategorizingChildren extends DiagramChildren {
    boolean writeable;
    TreeSet activeCategories;
        
    DiagramCategorizingChildren(ElementNodeFactory factory, DiagramElement data, boolean wr) {
      super(factory, data);
      writeable = wr;
      initializeCategories();
    }

    private void initializeCategories() {
      activeCategories = new TreeSet();
      if (element.getDiagElems().length > 0) {
        activeCategories.add(CATEGORIES[0]);
      }
/*      if (element.getSorts().length > 0) {
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
      } */     
    }
        
    protected Node[] createNodes(Object key) {
      if (key instanceof Integer) {
	return new Node[]{new DiagramElementCategoryNode(((Integer)key).intValue(), factory, element, writeable)};
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
   * Category node - represents one section under diagram element node.
   */
  static class DiagramElementCategoryNode extends AbstractNode {

    /** The diagram element for this node */
    DiagramElement element;

    /** The type of the category node - for new types. */
    int newTypeIndex;
        
    /** The Help context ID for this node. */
    String  helpID;

    /** Create new element category node for the specific category.
     * @param index The index of type 
     * @param factory The factory which is passed down to the diagram children object
     * @param element the diagram element which this node is created for
     */
    DiagramElementCategoryNode(int index, ElementNodeFactory factory, DiagramElement element, boolean writeable) {
      this(index, new DiagramChildren(factory, element));
      this.element = element;
      newTypeIndex = writeable ? index : -1;
      switch (index) {
      case 0: setName("Diagram Elements"); break; //NOI18N
/*      case 1: setName("Sorts"); break; // NOI18N
      case 2: setName("Ops"); break; // NOI18N
      case 3: setName("Defs"); break; // NOI18N
      case 4: setName("Claims"); break; // NOI18N*/
      }
    }

    /** Create new element node.
     * @param index The index of type (0=imports, 1=sorts, 2=ops, 3=defs, 4=claims)
     * @param children the diagram children of this node
     */
    private DiagramElementCategoryNode(int index, DiagramChildren children) {
      super(children);
      setDisplayName(DIAGRAM_NAMES[index]);
      setShortDescription (DIAGRAM_SHORTDESCRS[index]);
      helpID = DIAGRAM_HELP_IDS[index];
      DiagramElementFilter filter = new DiagramElementFilter();
      filter.setOrder(DIAGRAM_FILTERS[index]);
      children.setFilter(filter);
      systemActions = CATEGORY_ACTIONS;
      setIconBase(DIAGRAM_CATEGORY_ICONS[index]);
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
	  new SourceEditSupport.DiagramElementNewType(element, (byte) 0)
	    };
/*      case 1:
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
	    };            */
      default:
	return super.getNewTypes();
      }
    }

    public void createPasteTypes(java.awt.datatransfer.Transferable t, java.util.List s) {
      Node n = getParentNode();
      if (n == null || !(n instanceof DiagramElementNode)) {
	return;
      }
      ((DiagramElementNode)n).createPasteTypes(t, s);
    }
  }

  /*
   * Simple descendant of ColimitChildren that distributes nodes from the colimit to various
   * categories. 
   */
/*  static class ColimitCategorizingChildren extends ColimitChildren {
    boolean writeable;
    TreeSet activeCategories;
        
    ColimitCategorizingChildren(ElementNodeFactory factory, ColimitElement data, boolean wr) {
      super(factory, data);
      writeable = wr;
      initializeCategories();
    }

    private void initializeCategories() {
      activeCategories = new TreeSet();
      if (element.getDiagrams().length > 0) {
        activeCategories.add(CATEGORIES[0]);
      }
    }
        
    protected Node[] createNodes(Object key) {
      if (key instanceof Integer) {
	return new Node[]{new ColimitElementCategoryNode(((Integer)key).intValue(), factory, element, writeable)};
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
  */
  /**
   * Category node - represents one section under colimit element node.
   */
  static class ColimitElementCategoryNode extends AbstractNode {

    /** The colimit element for this node */
    ColimitElement element;

    /** The type of the category node - for new types. */
    int newTypeIndex;
        
    /** The Help context ID for this node. */
    String  helpID;

    /** Create new element category node for the specific category.
     * @param index The index of type 
     * @param factory The factory which is passed down to the colimit children object
     * @param element the colimit element which this node is created for
     */
    ColimitElementCategoryNode(int index, ElementNodeFactory factory, ColimitElement element, boolean writeable) {
      this(index, new ColimitChildren(factory, element));
      this.element = element;
      newTypeIndex = writeable ? index : -1;
      switch (index) {
      case 0: setName("Diagrams"); break; //NOI18N
      }
    }

    /** Create new element node.
     * @param index The index of type (0=diagrams)
     * @param children the colimit children of this node
     */
    private ColimitElementCategoryNode(int index, ColimitChildren children) {
      super(children);
      setDisplayName(COLIMIT_NAMES[index]);
      setShortDescription (COLIMIT_SHORTDESCRS[index]);
      helpID = COLIMIT_HELP_IDS[index];
      ColimitElementFilter filter = new ColimitElementFilter();
      filter.setOrder(COLIMIT_FILTERS[index]);
      children.setFilter(filter);
      systemActions = CATEGORY_ACTIONS;
      setIconBase(COLIMIT_CATEGORY_ICONS[index]);
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
	  new SourceEditSupport.ColimitElementNewType(element, (byte) 0)
	    };
      default:
	return super.getNewTypes();
      }
    }

    public void createPasteTypes(java.awt.datatransfer.Transferable t, java.util.List s) {
      Node n = getParentNode();
      if (n == null || !(n instanceof ColimitElementNode)) {
	return;
      }
      ((ColimitElementNode)n).createPasteTypes(t, s);
    }
  }  
}
