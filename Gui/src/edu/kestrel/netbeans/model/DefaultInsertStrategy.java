/*
 * DefaultInsertStrategy.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.7  2003/06/23 18:00:15  weilyn
 * internal release version
 *
 * Revision 1.6  2003/04/23 01:14:38  weilyn
 * BindingFactory.java
 *
 * Revision 1.5  2003/04/01 02:29:36  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.4  2003/03/29 03:13:55  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.3  2003/03/14 04:14:00  weilyn
 * Added support for proof terms
 *
 * Revision 1.2  2003/02/18 18:13:46  weilyn
 * Added insert strategy for claims, defs and imports.
 *
 * Revision 1.1  2003/01/30 02:01:53  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.util.*;

import edu.kestrel.netbeans.Util;

/**
 * Dump insertion strategy, that inserts after all elemnets with the given type.
 * Element types are ordered -- a future extension would be to allow specify the order
 * of element types.
 *
 */
class DefaultInsertStrategy implements Positioner {
    
    private static final boolean DEBUG = true;
    
    public Element[] findInsertPositions(Element container, Element[] els, Acceptor posAcceptor) {
        Element[] siblings = findElements(container, els[0]);;
        Element[] refs = new Element[els.length];
        Element ref;
        if (siblings == null || siblings.length == 0) {
            ref = Positioner.FIRST;
        } else {
            ref = siblings[siblings.length - 1];
        }
        ref = findSuitablePos(container, ref, posAcceptor);
        refs[0] = ref;
        for (int i = 1; i < refs.length; i++) {
            refs[i] = els[i - 1];
        }
        return refs;
    }
    
    private Element findSuitablePos(Element container, Element ref, Acceptor acc) {
        if (acc.canInsertAfter(ref))
            return ref;
        ElementOrder o = (ElementOrder)container.getCookie(ElementOrder.class);
        Element[] children = o.getElements();
        int prefPos = 0;
        int i;
        
        for (i = 0; i < children.length; i++) {
            if (ref == children[i]) {
                prefPos = i;
                break;
            }
        }
        int after = prefPos + 1;
        int before = prefPos - 1;

        while (before >= -1 || after < children.length) {
            if (after < children.length) {
                if (acc.canInsertAfter(children[after]))
                    return children[after];
                after++;
            }
            if (before >= 0) {
                if (acc.canInsertAfter(children[before])) {
                    return children[before];
                }
                before--;
            } else if (before == -1) {
                if (acc.canInsertAfter(FIRST)) 
                    return FIRST;
                before--;
            }
        }
        return null;
    }

    private Element[] findElements(Element container, Element selector) {
	if (container instanceof SourceElement) {
	    SourceElement source = (SourceElement) container;

            Vector allElements = new Vector();
            
            // insert new containers at the end rather than after a sibling
            Element[] currArray;
            currArray = source.getSpecs();
            for (int i = 0; i < currArray.length; i++) {
                allElements.add(currArray[i]);
            }
            currArray = source.getProofs();
            for (int i = 0; i < currArray.length; i++) {
                allElements.add(currArray[i]);
            }
            currArray = source.getDiagrams();
            for (int i = 0; i < currArray.length; i++) {
                allElements.add(currArray[i]);
            }
            currArray = source.getMorphisms();
            for (int i = 0; i < currArray.length; i++) {
                allElements.add(currArray[i]);
            }
            currArray = source.getColimits();
            for (int i = 0; i < currArray.length; i++) {
                allElements.add(currArray[i]);
            }
            
            Element[] allElemsArray = new Element[allElements.size()];
            allElements.copyInto(allElemsArray);
            if (DEBUG) {
                Util.log("DefaultInsertStrategy.findElements: num elements found is "+allElements.size());
            }
            return allElemsArray;
            
/*	    if (selector instanceof SpecElement) {
		return getFirstNonEmpty(source, 0);
	    } else if (selector instanceof ProofElement) {
                return getFirstNonEmpty(source, 1);
            } else if (selector instanceof MorphismElement) {
                return getFirstNonEmpty(source, 2);
            } else if (selector instanceof DiagramElement) {
                return getFirstNonEmpty(source, 3);
            } else if (selector instanceof ColimitElement) {
                return getFirstNonEmpty(source, 4);
            } */
	} else if (container instanceof SpecElement) {
	    SpecElement spec = (SpecElement) container;
	    if (selector instanceof ImportElement) {
		return getFirstNonEmpty(spec, 0);
	    } else if (selector instanceof SortElement) {
		return getFirstNonEmpty(spec, 1);
	    } else if (selector instanceof OpElement) {
		return getFirstNonEmpty(spec, 2);
	    } else if (selector instanceof DefElement) {
		return getFirstNonEmpty(spec, 3);
	    } else if (selector instanceof ClaimElement) {
		return getFirstNonEmpty(spec, 4);
	    }
	} else if (container instanceof ProofElement) {
            ProofElement proof = (ProofElement) container;
            //TODO
        } else if (container instanceof MorphismElement) {
            MorphismElement morphism = (MorphismElement) container;
            //TODO
        } else if (container instanceof DiagramElement) {
            DiagramElement diagram = (DiagramElement) container;
            //TODO
        } else if (container instanceof ColimitElement) {
            ColimitElement colimit = (ColimitElement) container;
            //TODO
        }
	return null;
    }
        
/*    private Element[] getFirstNonEmpty(SourceElement container, int startPos) {
	//Util.log("*** DefaultInsertStrategy.getFirstNonEmpty(): startPos="+startPos);
        Element[] items;
        
        //TODO: decide on the real order
        if (startPos > 4) {
            items = container.getColimits();
            if (items != null && items.length > 0) {
                return items;
            }
        }
	if (startPos > 3) {
            items = container.getDiagrams();
            if (items != null && items.length > 0) {
                return items;
            }
        }
 	if (startPos > 2) {
            items = container.getMorphisms();
            if (items != null && items.length > 0) {
                return items;
            }
        }
 	if (startPos > 1) {
            items = container.getProofs();
            if (items != null && items.length > 0) {
                return items;
            }
        }
        items = container.getSpecs();
	if (items != null && items.length > 0) {
	    //edu.kestrel.netbeans.Util.log("*** DefaultInsertStrategy.getFirstNonEmpty(): return "+Util.print((MemberElement[])items));
	    return items;
	}
        return null;
    }*/

    private Element[] getFirstNonEmpty(SpecElement container, int startPos) {
        Element[] items;
        
        if (startPos > 4) {
            items = container.getClaims();
            if (items != null && items.length > 0)
                return items;
        }
        if (startPos > 3) {
            items = container.getDefs();
            if (items != null && items.length > 0)
                return items;
        }
        if (startPos > 2) {
            items = container.getOps();
            if (items != null && items.length > 0)
                return items;
        }
        if (startPos > 1) {
            items = container.getSorts();
            if (items != null && items.length > 0)
                return items;
        }
        items = container.getImports();
        if (items != null && items.length > 0)
            return items;
        return null;
    }

}
