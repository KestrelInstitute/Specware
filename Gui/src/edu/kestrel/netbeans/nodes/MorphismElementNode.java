package edu.kestrel.netbeans.nodes;

import java.awt.Component;
import java.beans.*;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.DataFlavor;

import org.openide.TopManager;
import org.openide.ErrorManager;
import org.openide.src.SourceException;
import org.openide.nodes.*;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;
import org.openide.util.datatransfer.*;
import org.openide.NotifyDescriptor;
import org.openide.explorer.propertysheet.PropertyEnv;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.ElementFormat;

/** Node representing a morphism.
 * @see MorphismElement
 */
public class MorphismElementNode extends MemberElementNode {

    /** Return value of getIconAffectingProperties op. */
    private static final String[] ICON_AFFECTING_PROPERTIES = new String[] {
    };

    /** Menu labels */
/*    private static final String MENU_CREATE_IMPORT;
    private static final String MENU_CREATE_SORT;
    private static final String MENU_CREATE_OP;
    private static final String MENU_CREATE_DEF;
    private static final String MENU_CREATE_CLAIM;*/

    static {
        ResourceBundle bundle = NbBundle.getBundle(MorphismElementNode.class);
/*        MENU_CREATE_IMPORT = bundle.getString("MENU_CREATE_IMPORT");
        MENU_CREATE_SORT = bundle.getString("MENU_CREATE_SORT");
        MENU_CREATE_OP = bundle.getString("MENU_CREATE_OP");
        MENU_CREATE_DEF = bundle.getString("MENU_CREATE_DEF");
        MENU_CREATE_CLAIM = bundle.getString("MENU_CREATE_CLAIM");*/
    }

    /** Create a new morphism node.
     * @param element morphism element to represent
     * @param children node children
     * @param writeable <code>true</code> to be writable
     */
    public MorphismElementNode(MorphismElement element, Children children, boolean writeable) {
        super(element, children, writeable);
	String name = element.getName();
        setElementFormat0(sourceOptions.getMorphismElementFormat());
    }

    /*
      public org.openide.util.HelpCtx getHelpCtx () {
      return new org.openide.util.HelpCtx ("org.openide.src.nodes.MorphismNode"); // NOI18N
      }
    */

    /* Resolve the current icon base.
     * @return icon base string.
     */
    protected String resolveIconBase() {
        return MORPHISM;
    }

    /* This op is used for resolving the names of the properties,
     * which could affect the icon 
     * @return the appropriate array.
     */
    protected String[] getIconAffectingProperties() {
        return ICON_AFFECTING_PROPERTIES;
    }

    /* This op resolve the appropriate hint format for the type
     * of the element. It defines the short description.
     */
    protected ElementFormat getHintElementFormat() {
        return sourceOptions.getMorphismElementLongFormat();
    }

    /* Creates property set for this node */
    protected Sheet createSheet () {
        Sheet sheet = Sheet.createDefault();
        Sheet.Set ps = sheet.get(Sheet.PROPERTIES);
        boolean canWrite = isWriteable();
        ps.put(createNameProperty(canWrite));
        return sheet;
    }

    /** Remove this morphism from its source file.
     *
     * @exception IOException if the containing element refuses to delete it
     */
    public void destroy() throws IOException {
        SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		public void run() throws SourceException {
		    MorphismElement el = (MorphismElement) element;
		    el.getSource().removeMorphism(el);
		}
	    });
        super.destroy();
    }

    public Component getCustomizer() {
	return null;   // new MorphismCustomizer((MorphismElement)element)
    }

    public boolean hasCustomizer() {
	return false;  // isWriteable()
    }

    /* Accumulate the paste types that this node can handle
     * for a given transferable.
     * <P>
     * The default implementation simply tests whether the transferable supports
     * {@link NodeTransfer#nodePasteFlavor}, and if so, it obtains the paste types
     * from the {@link NodeTransfer.Paste transfer data} and inserts them into the set.
     *
     * @param t a transferable containing clipboard data
     * @param s a set of {@link PasteType}s that will have added to it all types
     *    valid for this node
     */
    protected void createPasteTypes (final Transferable t, java.util.List s) {
        if (isWriteable()) {
            // special case - multiple source element nodes...
            if (t.isDataFlavorSupported(ExTransferable.multiFlavor)) {
                createMultiPasteTypes(t, s, NodeTransfer.COPY);
                createMultiPasteTypes(t, s, NodeTransfer.MOVE);
                return;
            }
            for (int i = 0; i <= 1; i++) {
                final boolean delete = (i == 1);
                final Element addingElement = (Element) NodeTransfer.cookie(t,
									    delete ? NodeTransfer.MOVE : NodeTransfer.COPY, Element.class);

                if (addingElement != null) {
                    s.add(new PasteType() {
			    public Transferable paste() throws IOException {
				pasteElement(addingElement, delete);
				return delete ? ExTransferable.EMPTY : null;
			    }
			});
                }
            }
        }
        super.createPasteTypes(t, s);
    }
    
    private void createMultiPasteTypes(Transferable t, List s, int action) {
        MultiTransferObject mto;
        
        try {
            mto = (MultiTransferObject) t.getTransferData (ExTransferable.multiFlavor);
        } catch (java.awt.datatransfer.UnsupportedFlavorException ex) {
            return;
        } catch (IOException ex) {
            return;
        }
        
        int count = mto.getCount();
        Collection candidates = new LinkedList();

        for (int i = 0; i < count; i++) {
            Node n = NodeTransfer.node(mto.getTransferableAt(i), action);
            if (n == null) 
                break;
            Element el = (Element)n.getCookie(Element.class);
            // filter out non-Elements and elements that cannot be pasted
            // to a spec.
            if (el == null ||
                !(el instanceof MemberElement))
                break;
            // check whether one of the candidates is a parent of the node.
            // alternatively, the node may be parent of one of the nodes 
            // in candidates.
            addNodeCandidate(candidates, el);
        }
        if (candidates.isEmpty())
            return;
        s.add(new SourceEditSupport.MorphismMultiPasteType(this, candidates, (action & NodeTransfer.MOVE) > 0));
    }
    
    // What should this do for morphisms???
    private void addNodeCandidate(Collection candidates, Element el) {
        MorphismElement enc2 = findEnclosingMorphism(el);
        SourceElement enc2Src = enc2.getSource();
        String fn2 = enc2.getName();        
        for (Iterator it = candidates.iterator(); it.hasNext(); ) {
            Element can = (Element)it.next();
            MorphismElement enc1 = findEnclosingMorphism(can);
            if (enc1.getSource() != enc2Src) {
                continue;
            }
            // next, if the enclosing morphisms are the same...
            if (enc1 == enc2) {
                if (can == enc1) {
                    // enc2 must be member of enc1, don't add it at all!
                    return;
                } else if (el == enc2) {
                    // can != enc1 -> can is member of enc1.
                    // el == enc2 --> el is declaring morphism of `can'
                    // replace `can' with `el'.
                    it.remove();
                    // there can be more such member elements.
                    continue;
                } else {
                    // OK, there is a member of the same morphism
                    break;
                }
            }
            String fn1 = enc1.getName();
            if (fn2.startsWith(fn1)) {
                if (enc1 == can) {
                    // enc2 is inner spec of enc1 --> do *NOT* add this element.
                    return;
                } else
                    continue;   
            } else if (fn1.startsWith(fn2)) {
                if (enc2 == el) {
                    it.remove();
                    continue;
                } else
                    break;
            }
        }
        candidates.add(el);
    }
    
    private MorphismElement findEnclosingMorphism(Element el) {
        if (el instanceof MorphismElement)
            return (MorphismElement)el;
        else if (el instanceof MemberElement) 
	    return findEnclosingMorphism(((MemberElement)el).getParent());
        else
            return null;
    }
    
    PropertyChangeListener createElementListener() {
	return new MorphismElementListener();
    }

    /** Paste element into this morphism.
     * @param addingElement Element to add.
     * @param delete Whether element should be deleted from the original morphism
     * @exception IOException if any proble occured
     */
    void pasteElement(final Element addingElement, final boolean delete) throws IOException {
        final boolean[] cancelled = {false};
	
        SourceEditSupport.invokeAtomicAsUser(element, new SourceEditSupport.ExceptionalRunnable() {
		public void run() throws SourceException {
		    MorphismElement morphism = (MorphismElement) element;
/*		    if (addingElement instanceof ImportElement) {
			morphism.addImport((ImportElement)addingElement);
                    } else if (addingElement instanceof SortElement) {
			spec.addSort((SortElement)addingElement);
		    } else if (addingElement instanceof OpElement) {
			OpElement me = (OpElement) addingElement;
			me  = (OpElement) me.clone();
			spec.addOp(me);
                    } else if (addingElement instanceof DefElement) {
			spec.addDef((DefElement)addingElement);
		    } else if (addingElement instanceof ClaimElement) {
			ClaimElement me = (ClaimElement) addingElement;
			me  = (ClaimElement) me.clone();
			spec.addClaim(me);
		    }*/
		}
	    });
        if (delete && (!cancelled[0])) {
            final MorphismElement origMorphism;
            SourceElement src = null;

            if (addingElement instanceof MemberElement) {
                origMorphism = findEnclosingMorphism(addingElement);
            } else {
                origMorphism = null;
            }
	    
	    if (src == null && origMorphism != null) {
		src = origMorphism.getSource();
	    }

            final SourceElement morphismSource = src;
	    SourceEditSupport.ExceptionalRunnable r = new SourceEditSupport.ExceptionalRunnable() {
		    public void run() throws SourceException {
			if (addingElement instanceof MemberElement) {
			    if (origMorphism != null) {
/*                                if (addingElement instanceof ImportElement) {
				    origMorphism.removeImport((ImportElement)addingElement);
				} else if (addingElement instanceof SortElement) {
				    origSpec.removeSort((SortElement)addingElement);
				} else if (addingElement instanceof OpElement) {
				    origSpec.removeOp((OpElement)addingElement);
                                } else if (addingElement instanceof DefElement) {
				    origSpec.removeDef((DefElement)addingElement);
				} else if (addingElement instanceof ClaimElement) {
				    origSpec.removeClaim((ClaimElement)addingElement);
				}*/
	                    } else if ((addingElement instanceof MorphismElement) &&
				       morphismSource != null) {
				morphismSource.removeMorphism((MorphismElement)addingElement);
			    }
			}
		    }
		};
	    
	    if (src == null) {
		try {
		    r.run();
		} catch (SourceException e) {
		    throw new IOException(e.getMessage());
		}
	    } else {
        	SourceEditSupport.invokeAtomicAsUser(addingElement, r);
    	    }
	}
    }
    
    public NewType[] getNewTypes() {
        if (isWriteable()) {
            return SourceEditSupport.createNewTypes((MorphismElement)element);
        } else {
            return super.getNewTypes();
        }
    }
    
    public Transferable clipboardCopy() {
        Transferable t = NodeTransfer.transferable(this, NodeTransfer.CLIPBOARD_COPY);
        ExTransferable xt = ExTransferable.create(t);
        xt.put(NodeTransfer.createPaste(new SourceEditSupport.PackagePaste(
									   (MorphismElement)this.element, false
									   )));
        return xt;
    }

    public Transferable clipboardCut() {
        Transferable t = NodeTransfer.transferable(this, NodeTransfer.CLIPBOARD_CUT);
        ExTransferable xt = ExTransferable.create(t);
        xt.put(NodeTransfer.createPaste(new SourceEditSupport.PackagePaste(
									   (MorphismElement)this.element, true
									   )));
        return xt;
    }
    
    private class MorphismElementListener extends ElementListener {
	public void propertyChange(PropertyChangeEvent evt) {
	    super.propertyChange(evt);
	}
    }
}
