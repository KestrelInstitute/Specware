/*
 * MetaSlangElementNodeFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.12  2003/04/26 02:30:53  weilyn
 * Added GoToUnitDefinitionAction support
 *
 * Revision 1.11  2003/04/23 00:43:19  weilyn
 * Added UnitID object support and diagram element node support
 *
 * Revision 1.10  2003/04/01 02:29:33  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.9  2003/03/29 03:13:52  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.8  2003/03/14 04:11:56  weilyn
 * Added support for proof terms
 *
 * Revision 1.7  2003/02/20 23:07:14  weilyn
 * Added prove stuff.
 *
 * Revision 1.6  2003/02/19 18:48:03  weilyn
 * Commented out ProcessUnit as a spec action for now because Specware doesn't process on the spec level, just file level.
 *
 * Revision 1.5  2003/02/18 17:58:48  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:28:16  weilyn
 * Cleaned up active context menu actions.
 *
 * Revision 1.3  2003/02/16 02:11:15  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:00:52  weilyn
 * Added createClaimNode method
 *
 * Revision 1.1  2003/01/30 02:01:34  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.beans.*;
import java.util.Collection;
import java.util.LinkedList;

import org.openide.actions.*;
import org.openide.cookies.OpenCookie;
import org.openide.cookies.ElementCookie;
import org.openide.cookies.FilterCookie;
import org.openide.nodes.*;
import org.openide.loaders.DataObject;
import org.openide.src.SourceException;
//import org.openide.src.nodes.*;
import org.openide.util.NbBundle;
import org.openide.util.actions.SystemAction;
import org.openide.*;

import edu.kestrel.netbeans.actions.*;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.nodes.*;
import edu.kestrel.netbeans.parser.MetaSlangParser;
import edu.kestrel.netbeans.codegen.ElementFormat;

/** The implementation of hierarchy nodes factory for the meta-slang loader.
 *
 */
class MetaSlangElementNodeFactory extends DefaultFactory {
    /** Default instance of this factory. */
    public static final DefaultFactory DEFAULT = new MetaSlangElementNodeFactory();

    private static final SystemAction[] DEFAULT_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	null,
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };

    private static final SystemAction[] CLAIM_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
        SystemAction.get(ProveClaimAction.class),
        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	null,
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };
    
    /** Array of the actions of the meta-slang classes. */
    private static final SystemAction[] SPEC_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
        SystemAction.get(CompileSpecAction.class),
 //       SystemAction.get(ProcessUnitAction.class),
        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	SystemAction.get(PasteAction.class),
	null,
	SystemAction.get(NewAction.class),
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(OverrideAction.class),
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };

    /** Array of the actions of the meta-slang classes. */
    private static final SystemAction[] PROOF_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
 //       SystemAction.get(ProcessUnitAction.class),
//        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	SystemAction.get(PasteAction.class),
	null,
	SystemAction.get(NewAction.class),
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(OverrideAction.class),
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };

    /** Array of the actions of the meta-slang classes. */
    private static final SystemAction[] MORPHISM_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
 //       SystemAction.get(ProcessUnitAction.class),
//        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	SystemAction.get(PasteAction.class),
	null,
	SystemAction.get(NewAction.class),
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(OverrideAction.class),
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };
    
    /** Array of the actions of the meta-slang classes. */
    private static final SystemAction[] DIAGRAM_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
 //       SystemAction.get(ProcessUnitAction.class),
//        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	SystemAction.get(PasteAction.class),
	null,
	SystemAction.get(NewAction.class),
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(OverrideAction.class),
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };

    /** Array of the actions of the meta-slang classes. */
    private static final SystemAction[] COLIMIT_ACTIONS = new SystemAction[] {
	SystemAction.get(EditAction.class),
	//SystemAction.get(OpenAction.class),
	null,
 //       SystemAction.get(ProcessUnitAction.class),
//        null,
	SystemAction.get(CutAction.class),
	SystemAction.get(CopyAction.class),
	SystemAction.get(PasteAction.class),
	null,
	SystemAction.get(NewAction.class),
	SystemAction.get(DeleteAction.class),
	SystemAction.get(RenameAction.class),
	//null,
	//SystemAction.get(OverrideAction.class),
	//SystemAction.get(ToolsAction.class),
	//SystemAction.get(PropertiesAction.class)
    };

    private static final SystemAction[] UNIT_ID_ACTIONS = new SystemAction[] {
	SystemAction.get(GoToUnitDefinitionAction.class),
    };
    
    private static final SystemAction[] CONTAINER_ACTIONS
	= new SystemAction[] {SystemAction.get(CutAction.class),
			      SystemAction.get(CopyAction.class),
			      SystemAction.get(PasteAction.class),
			      null,
			      SystemAction.get(NewAction.class),
			      SystemAction.get(DeleteAction.class),
			      SystemAction.get(RenameAction.class),
			      //null,
			      //SystemAction.get(ToolsAction.class),
			      //SystemAction.get(PropertiesAction.class)
                             };

    /** This node can return current element factory as cookie */
    private final Node FACTORY_GETTER_NODE = new FactoryGetterNode();


    /** Create nodes for tree */
    private boolean tree = false;

    /** Creates new factory. */
    public MetaSlangElementNodeFactory() {
        super(true);
    }

    /** If true generate nodes for tree.
     */
    public void setGenerateForTree (boolean tree) {
        this.tree = tree;
    }

    /** Returns true if generate nodes for tree.
     * @returns true if generate nodes for tree.
     */
    public boolean getGenerateForTree () {
        return tree;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createSpecNode(final SpecElement element) {
        if ( element == null ) {
            return FACTORY_GETTER_NODE;
        }
        SpecElementNode n;
        if (tree) {
            SpecChildren children = (SpecChildren) createSpecChildren(element);
            SpecElementFilter filter = new SpecElementFilter();
            n = new SpecElementNode(element, children ,true) {
		    {
			getCookieSet().add((FilterCookie) getChildren ());
		    }
		};

            n.setElementFormat(new ElementFormat(NbBundle.getBundle (MetaSlangElementNodeFactory.class).getString("CTL_Spec_name_format")));

            filter.setOrder (new int[] {
                SpecElementFilter.IMPORT,
		SpecElementFilter.SORT,
		SpecElementFilter.OP,
                SpecElementFilter.DEF,
                SpecElementFilter.CLAIM,
            });
            children.setFilter (filter);
        }
        else {
            n = (SpecElementNode) super.createSpecNode(element);
        }
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(SPEC_ACTIONS);
        return n;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createSortNode(SortElement element) {
        SortElementNode n = new SortElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createOpNode(OpElement element) {
        OpElementNode n = new OpElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createDefNode(DefElement element) {
        DefElementNode n = new DefElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createClaimNode(ClaimElement element) {
        ClaimElementNode n = new ClaimElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(CLAIM_ACTIONS);
        return n;
    }
    
    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createImportNode(ImportElement element) {
        ImportElementNode n = new ImportElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }

    protected Children createSpecChildren( SpecElement element ) {
        return createSpecChildren(element, MetaSlangDataObject.getExplorerFactory() );
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createProofNode(final ProofElement element) {
        if ( element == null ) {
            return FACTORY_GETTER_NODE;
        }
        ProofElementNode n;
        if (tree) {
            ProofChildren children = (ProofChildren) createProofChildren(element);
            ProofElementFilter filter = new ProofElementFilter();
            n = new ProofElementNode(element, children ,true) {
		    {
			getCookieSet().add((FilterCookie) getChildren ());
		    }
		};

            n.setElementFormat(new ElementFormat(NbBundle.getBundle (MetaSlangElementNodeFactory.class).getString("CTL_Proof_name_format")));

            filter.setOrder (new int[] {
/*                SpecElementFilter.IMPORT,
		SpecElementFilter.SORT,
		SpecElementFilter.OP,
                SpecElementFilter.DEF,
                SpecElementFilter.CLAIM,*/
            });
            children.setFilter (filter);
        }
        else {
            n = (ProofElementNode) super.createProofNode(element);
        }
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(PROOF_ACTIONS);
        return n;
    }
    
    protected Children createProofChildren( ProofElement element ) {
        return createProofChildren(element, MetaSlangDataObject.getExplorerFactory() );
    }
    
    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createMorphismNode(final MorphismElement element) {
        if ( element == null ) {
            return FACTORY_GETTER_NODE;
        }
        MorphismElementNode n;
        if (tree) {
            MorphismChildren children = (MorphismChildren) createMorphismChildren(element);
            MorphismElementFilter filter = new MorphismElementFilter();
            n = new MorphismElementNode(element, children ,true) {
		    {
			getCookieSet().add((FilterCookie) getChildren ());
		    }
		};

            n.setElementFormat(new ElementFormat(NbBundle.getBundle (MetaSlangElementNodeFactory.class).getString("CTL_Morphism_name_format")));

            filter.setOrder (new int[] {
/*                SpecElementFilter.IMPORT,
		SpecElementFilter.SORT,
		SpecElementFilter.OP,
                SpecElementFilter.DEF,
                SpecElementFilter.CLAIM,*/
            });
            children.setFilter (filter);
        }
        else {
            n = (MorphismElementNode) super.createMorphismNode(element);
        }
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(MORPHISM_ACTIONS);
        return n;
    }
    
    protected Children createMorphismChildren(MorphismElement element ) {
        return createMorphismChildren(element, MetaSlangDataObject.getExplorerFactory() );
    }
    
    public Node createUnitIDObjectNode(Object object) {
        UnitIDObjectNode n = new UnitIDObjectNode(object);
        n.setDefaultAction(SystemAction.get(GoToUnitDefinitionAction.class));
        n.setActions(UNIT_ID_ACTIONS);
        return n;
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createDiagElemNode(DiagElemElement element) {
        DiagElemElementNode n = new DiagElemElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }
    
    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createDiagramNode(final DiagramElement element) {
        if ( element == null ) {
            return FACTORY_GETTER_NODE;
        }
        DiagramElementNode n;
        if (tree) {
            DiagramChildren children = (DiagramChildren) createDiagramChildren(element);
            DiagramElementFilter filter = new DiagramElementFilter();
            n = new DiagramElementNode(element, children ,true) {
		    {
			getCookieSet().add((FilterCookie) getChildren ());
		    }
		};

            n.setElementFormat(new ElementFormat(NbBundle.getBundle (MetaSlangElementNodeFactory.class).getString("CTL_Diagram_name_format")));

            filter.setOrder (new int[] {
                DiagramElementFilter.DIAG_ELEM,
/*		SpecElementFilter.SORT,
		SpecElementFilter.OP,
                SpecElementFilter.DEF,
                SpecElementFilter.CLAIM,*/
            });
            children.setFilter (filter);
        }
        else {
            n = (DiagramElementNode) super.createDiagramNode(element);
        }
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DIAGRAM_ACTIONS);
        return n;
    }
    
    protected Children createDiagramChildren( DiagramElement element ) {
        return createDiagramChildren(element, MetaSlangDataObject.getExplorerFactory() );
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    public Node createColimitNode(final ColimitElement element) {
        if ( element == null ) {
            return FACTORY_GETTER_NODE;
        }
        ColimitElementNode n;
        if (tree) {
            ColimitChildren children = (ColimitChildren) createColimitChildren(element);
            ColimitElementFilter filter = new ColimitElementFilter();
            n = new ColimitElementNode(element, children ,true) {
		    {
			getCookieSet().add((FilterCookie) getChildren ());
		    }
		};

            n.setElementFormat(new ElementFormat(NbBundle.getBundle (MetaSlangElementNodeFactory.class).getString("CTL_Colimit_name_format")));

            filter.setOrder (new int[] {
                ColimitElementFilter.DIAGRAM,
            });
            children.setFilter (filter);
        }
        else {
            n = (ColimitElementNode) super.createColimitNode(element);
        }
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(COLIMIT_ACTIONS);
        return n;
    }
    
    protected Children createColimitChildren( ColimitElement element ) {
        return createColimitChildren(element, MetaSlangDataObject.getExplorerFactory() );
    }

    /** Returns the node asociated with specified element.
     * @return ElementNode
     */
    /*public Node createURINode(URIElement element) {
        URIElementNode n = new URIElementNode(element, true);
        n.setDefaultAction(SystemAction.get(EditAction.class));
        n.setActions(DEFAULT_ACTIONS);
        return n;
    }*/

    /**
     * This method will try to extract more information than the ordinary Error message.
     */
    public Node createErrorNode() {
        final Node n = super.createErrorNode();

        n.addNodeListener(new NodeListener() {
		public void propertyChange(PropertyChangeEvent e) {
		    Node parent = n.getParentNode();
		    DataObject d = null;
               
		    if (parent == null)
			return;
		    n.removeNodeListener(this);
		    do {
			d = (DataObject)parent.getCookie(DataObject.class);
			parent = parent.getParentNode();
		    } while (parent != null && d == null);
		    if (d == null)
			return;
		    setErrorDescription(n, (MetaSlangParser)d.getCookie(MetaSlangParser.class));
		}
            
		public void childrenAdded(NodeMemberEvent e) {}
		public void childrenRemoved(NodeMemberEvent e) {}
		public void childrenReordered(NodeReorderEvent e) {}
		public void nodeDestroyed(NodeEvent e) {}
	    });
        return n;
    }

    private void setErrorDescription(Node n, MetaSlangParser p) {
        if (p == null)
            return;
        SourceException e = p.getErrorCause();
        String msg = findErrorMessage(e);
        if (msg == null)
            return;
        
        if (e instanceof SourceException.IO) {
            n.setDisplayName(Util.getString("MSG_PARSE_ERROR_IO"));
        }
        n.setShortDescription(msg);
    }

    private String findErrorMessage(Throwable t) {
        if (t == null) {
            return null;
        }
        
        ErrorManager.Annotation[] ann = ErrorManager.getDefault().findAnnotations(t);
        if (ann == null)
            return t.getLocalizedMessage();
        for (int i = 0; i < ann.length; i++) {
            String normal = ann[i].getMessage();
            String localized = ann[i].getLocalizedMessage();
            if (localized != null)
                return localized;
            Throwable t2 = ann[i].getStackTrace();
            if (t2 == null)
                continue;
            localized = t2.getLocalizedMessage();
            if (localized != null) {
                if (!localized.equals(normal))
                    return localized;
            }
        }
        return null;
    }
    
    /** This is an unusuall use of Node and FilterCookie */

    private class FactoryGetterNode extends AbstractNode implements FilterCookie {

        FactoryGetterNode( ) {
            super ( Children.LEAF );
        }

        public synchronized Node.Cookie getCookie( Class clazz ) {
            if ( clazz == FilterFactory.class )
                return this;
            else
                return super.getCookie( clazz );
        }

        public Class getFilterClass() {
            return null;
        }

        public void setFilter( Object filter ) {}

        public Object getFilter( ) {
            if ( tree )
                return MetaSlangDataObject.getBrowserFactory();
            else
                return MetaSlangDataObject.getExplorerFactory();
        }

    }

}

