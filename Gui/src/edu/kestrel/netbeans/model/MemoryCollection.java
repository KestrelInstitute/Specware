/*
 * MemoryCollection.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.8  2003/04/23 01:14:39  weilyn
 * BindingFactory.java
 *
 * Revision 1.7  2003/04/01 02:29:37  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.6  2003/03/29 03:13:56  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:14:01  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:13:01  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:14:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:59  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.io.Serializable;
import java.util.*;

/** Support class that manages set of objects and fires events
* about its changes.
*
*/
abstract class MemoryCollection extends Object implements Serializable {
    /** array of objects */
    LinkedList array;
    
    /** Object to fire info about changes to */
    MemberElement.Memory memory;
    
    /** If set, new elements will be inserted before or after this one, depending on {@link #insertAfter }
     */
    private Element insertionMark;
    
    /** Determines, if new elements are inserted before (false) or after (true) the insertionMark. If insertionMark
	is null elements are inserted at the end (true) or at the beginning (false) of the collection.
    */      
    private boolean insertAfter;
    
    /** name of property to fire */
    private String propertyName;

    /** array template to return */
    private Object[] template;

    static final long serialVersionUID =-9215370960397120952L;

    /**
    * @param memory memory element to fire changes to
    * @param propertyName name of property to fire when array changes
    * @param emptyArray emptyArray instance that provides the type of arrays
    *   that should be returned by toArray method
    */
    public MemoryCollection(
        MemberElement.Memory memory, String propertyName, Object[] emptyArray
    ) {
        this.memory = memory;
        this.propertyName = propertyName;
        this.template = emptyArray;
    }
    
    Collection makeClones(Object[] els) {
        Collection contents = array == null ? Collections.EMPTY_LIST : array;
        
        Set hashContents = new HashSet(contents.size() * 4 / 3 + 1);
        for (Iterator it = contents.iterator(); it.hasNext(); ) {
	    Object e = it.next();
            hashContents.add(e);
        }
        Collection result = new ArrayList(els.length);
        for (int i = 0; i < els.length; i++) {
            Object el = els[i];
            if (!hashContents.contains(el)) {
                result.add(clone(el));
            } else {
                result.add(el);
	    }
        }
        return result;
    }
    
    Collection cloneElements(Object[] els) {
        Collection n = new ArrayList(els.length);
        for (int i = 0; i < els.length; i++) {
            n.add(clone(els[i]));
        }
        return n;
    }
    
    protected abstract Object clone(Object el);

    /** Changes the content of this object.
    * @param arr array of objects to change
    * @param action the action to do
    */
    public void change (Object[] arr, int action) {
        Collection data;
        
        switch (action) {
            case Element.Impl.ADD:
                data = cloneElements(arr);
                break;
            case Element.Impl.REMOVE:
                data = Arrays.asList(arr);
                break;
            case Element.Impl.SET:
                data = makeClones(arr);
                break;
            default:
                return;
        }
        change (data, action);
    }
    /** Changes the content of this object.
    * @param c collection of objects to change
    * @param action the action to do
    */
    protected void change (Collection c, int action) {
        boolean anChange;
        switch (action) {
        case Element.Impl.ADD:
            anChange = c.size () > 0;
            if (array != null) {
                if (insertionMark != null) {
                    int index = array.indexOf(insertionMark);
	                if (index == -1) {
    	                insertionMark = null;
	                    index = array.size();
	                } else if (insertAfter) {
	                    index++;
	                }
	                array.addAll(index, c);
        	    } else {
                    array.addAll (c);
	            }
                break;
            }
            // fall thru to initialize the array
        case Element.Impl.SET:
            // PENDING: better change detection; currently any SET operation will fire change.
            anChange = c.size () > 0 || (array != null && array.size () > 0);
            array = new LinkedList (c);
            insertionMark = null;
            break;
        case Element.Impl.REMOVE:
        {
            Element newMark = null;
            if (insertionMark != null && c.contains(insertionMark)) {
                Set removing = new HashSet(c.size() * 4 / 3);
                removing.addAll(c);
                int markIndex = array.indexOf(insertionMark);
                if (markIndex == -1) {
                    insertionMark = null;
	            } else {
                    ListIterator it = array.listIterator(markIndex);
	                while (it.hasNext()) {
	                    Object x = it.next();
	                    if (!removing.contains(x)) {
	                        newMark = (Element)x;
                            insertAfter = false;
                            break;
	                    }
	                }
	                if (newMark == null) {
	                    it = array.listIterator(markIndex);
 	                    while (it.hasPrevious()) {
	                        Object x = it.previous();
	                        if (!removing.contains(x)) {
	                            newMark = (Element)x;
                                insertAfter = true;
                                break;
	                        }
	                    }
	                }
	            }
                insertionMark = newMark;
            }
            anChange = array != null && array.removeAll (c);
            break;
        }
        default:
            // illegal argument in internal implementation
            throw new InternalError ();
        }

        if (anChange) {
            // do not construct array values if not necessary
            memory.firePropertyChange (propertyName, null, null);
        }
    }

    /** Access to the array.
    * @return array of objects contained here
    */
    public Object[] toArray () {
        if (array == null) {
            return template;
        } else {
            return array.toArray (template);
        }
    }
  
    void markCurrent(Element el, boolean after) {
        insertionMark = el;
        insertAfter = after;
    }

    /** Collection for members. Assignes to each class its
    * members.
    */
    static abstract class Member extends MemoryCollection {
        static final long serialVersionUID =7875426480834524238L;
        /**
        * @param memory memory element to fire changes to
        * @param propertyName name of property to fire when array changes
        * @param emptyArray emptyArray instance that provides the type of arrays
        *   that should be returned by toArray method
        */
        public Member (
            MemberElement.Memory memory, String propertyName, Object[] emptyArray
        ) {
            super (memory, propertyName, emptyArray);
        }

        /** Find method that looks in member elements
        * @param id the indetifier (or null)
        * @param types array of types to test (or null)
        * @return the element or null
        */
        public MemberElement find (String id) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                MemberElement me = (MemberElement)it.next ();
                if (id == null || id.equals(me.getName ())) {
                    // found element
                    return me;
                }
            }
            // nothing found
            return null;
        }

    }
   
    static final class Import extends Member {
        private static final ImportElement[] EMPTY = new ImportElement[0];

        static final long serialVersionUID =5715072242254795093L;
        /**
        * @param memory memory element to fire changes to
        * @param propertyName name of property to fire when array changes
        * @param emptyArray emptyArray instance that provides the type of arrays
        *   that should be returned by toArray method
        */
        public Import (SpecElement.Memory memory) {
            super (memory,
		   ElementProperties.PROP_IMPORTS,
		   EMPTY);
        }

        protected Object clone(Object el) {
            return new ImportElement(new ImportElement.Memory((ImportElement)el), 
					((SpecElement.Memory)memory).getSpecElement());
        }
    }
    
    static final class DiagElem extends Member {
        private static final DiagElemElement[] EMPTY = new DiagElemElement[0];

        static final long serialVersionUID =5715072242254795093L;
        /**
        * @param memory memory element to fire changes to
        * @param propertyName name of property to fire when array changes
        * @param emptyArray emptyArray instance that provides the type of arrays
        *   that should be returned by toArray method
        */
        public DiagElem (DiagramElement.Memory memory) {
            super (memory,
		   ElementProperties.PROP_DIAG_ELEMS,
		   EMPTY);
        }

        protected Object clone(Object el) {
            return new DiagElemElement(new DiagElemElement.Memory((DiagElemElement)el), 
					((DiagramElement.Memory)memory).getDiagramElement());
        }
    }

    static final class Sort extends Member {
        private static final SortElement[] EMPTY = new SortElement[0];

        static final long serialVersionUID =5715072242254795093L;
        /**
        * @param memory memory element to fire changes to
        * @param propertyName name of property to fire when array changes
        * @param emptyArray emptyArray instance that provides the type of arrays
        *   that should be returned by toArray method
        */
        public Sort (SpecElement.Memory memory) {
            super (memory,
		   ElementProperties.PROP_SORTS,
		   EMPTY);
        }

        protected Object clone(Object el) {
            return new SortElement(new SortElement.Memory((SortElement)el), 
					((SpecElement.Memory)memory).getSpecElement());
        }
    }

    /** Collection of ops.
    */
    static class Op extends Member {
        private static final OpElement[] EMPTY = new OpElement[0];

        static final long serialVersionUID =5747776340409139399L;
        /** @param ce class element memory impl to work in
        */
        public Op (SpecElement.Memory ce) {
            super (ce,
		   ElementProperties.PROP_OPS,
		   EMPTY);
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
            return new OpElement (new OpElement.Memory ((OpElement)obj),
				  ((SpecElement.Memory)memory).getSpecElement ());
        }

        public OpElement find (String id, String sort) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                OpElement op = (OpElement)it.next ();
                if (id.equals(op.getName()) && sort.equals(op.getSort())) {
		    return op;
		}
	    }
            // nothing found
            return null;
        }


    }

    static final class Def extends Member {
        private static final DefElement[] EMPTY = new DefElement[0];

        static final long serialVersionUID =5715072242254795093L;
        /**
        * @param memory memory element to fire changes to
        * @param propertyName name of property to fire when array changes
        * @param emptyArray emptyArray instance that provides the type of arrays
        *   that should be returned by toArray method
        */
        public Def (SpecElement.Memory memory) {
            super (memory,
		   ElementProperties.PROP_DEFS,
		   EMPTY);
        }

        protected Object clone(Object el) {
            return new DefElement(new DefElement.Memory((DefElement)el), 
					((SpecElement.Memory)memory).getSpecElement());
        }
    }

    /** Collection of claims.
    */
    static class Claim extends Member {
        private static final ClaimElement[] EMPTY = new ClaimElement[0];

        static final long serialVersionUID =5715072242254795093L;
        
        /** @param ce class element memory impl to work in
        */
        public Claim (SpecElement.Memory ce) {
            super (ce,
		   ElementProperties.PROP_CLAIMS,
		   EMPTY);
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
            return new ClaimElement (new ClaimElement.Memory ((ClaimElement)obj),
				  ((SpecElement.Memory)memory).getSpecElement ());
        }

        public ClaimElement find (String id, String claimKind) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                ClaimElement claim = (ClaimElement)it.next ();
                if (id.equals(claim.getName()) && claimKind.equals(claim.getClaimKind())) {
		    return claim;
		}
	    }
            // nothing found
            return null;
        }


    }


    /** Collection of specs.
    */
    static class Spec extends Member {
        private static final SpecElement[] EMPTY = new SpecElement[0];

        static final long serialVersionUID =3206093459760846163L;

        /** @param ce spec element memory impl to work in
        */
        public Spec (SpecElement.Memory memory) {
            super (memory, ElementProperties.PROP_SPECS, EMPTY);
        }
        
        public MemberElement find(String name) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                SpecElement element = (SpecElement)it.next ();
                String ename = element.getName();
                if (name.equals(ename)) {
                    return element;
                }
            }
            // nothing found
            return null;
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
	    SpecElement spec = (SpecElement) obj;
            SpecElement.Memory mem = new SpecElement.Memory (spec);
            SpecElement newSpec = new SpecElement(mem, spec.getSource());
            mem.copyFrom(spec);
            return newSpec;
        }
    }

    /** Collection of proofs.
    */
    static class Proof extends Member {
        private static final ProofElement[] EMPTY = new ProofElement[0];

        static final long serialVersionUID =3206093459760846163L;

        /** @param ce proof element memory impl to work in
        */
        public Proof (ProofElement.Memory memory) {
            super (memory, ElementProperties.PROP_PROOFS, EMPTY);
        }
        
        public MemberElement find(String name) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                ProofElement element = (ProofElement)it.next ();
                String ename = element.getName();
                if (name.equals(ename)) {
                    return element;
                }
            }
            // nothing found
            return null;
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
	    ProofElement proof = (ProofElement) obj;
            ProofElement.Memory mem = new ProofElement.Memory (proof);
            ProofElement newProof = new ProofElement(mem, proof.getSource());
            mem.copyFrom(proof);
            return newProof;
        }
    }    
    
    /** Collection of morphisms.
    */
    static class Morphism extends Member {
        private static final MorphismElement[] EMPTY = new MorphismElement[0];

        static final long serialVersionUID =3206093459760846163L;

        /** @param ce morphism element memory impl to work in
        */
        public Morphism (MorphismElement.Memory memory) {
            super (memory, ElementProperties.PROP_PROOFS, EMPTY);
        }
        
        public MemberElement find(String name) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                MorphismElement element = (MorphismElement)it.next ();
                String ename = element.getName();
                if (name.equals(ename)) {
                    return element;
                }
            }
            // nothing found
            return null;
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
	    MorphismElement morphism = (MorphismElement) obj;
            MorphismElement.Memory mem = new MorphismElement.Memory (morphism);
            MorphismElement newMorphism = new MorphismElement(mem, morphism.getSource());
            mem.copyFrom(morphism);
            return newMorphism;
        }
    }        

    /** Collection of diagrams.
    */
    static class Diagram extends Member {
        private static final DiagramElement[] EMPTY = new DiagramElement[0];

        static final long serialVersionUID =3206093459760846163L;

        /** @param ce diagram element memory impl to work in
        */
        public Diagram (DiagramElement.Memory memory) {
            super (memory, ElementProperties.PROP_DIAGRAMS, EMPTY);
        }
        
        public Diagram (ColimitElement.Memory memory) {
            super (memory, ElementProperties.PROP_DIAGRAMS, EMPTY);
        }

        public MemberElement find(String name) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                DiagramElement element = (DiagramElement)it.next ();
                String ename = element.getName();
                if (name.equals(ename)) {
                    return element;
                }
            }
            // nothing found
            return null;
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
	    DiagramElement diagram = (DiagramElement) obj;
            DiagramElement.Memory mem = new DiagramElement.Memory (diagram);
            
            //WLP: will this work?
            DiagramElement newDiagram;
            if (diagram.getSource() != null) {
                newDiagram = new DiagramElement(mem, diagram.getSource());
                mem.copyFrom(diagram);
            } else {
                newDiagram = new DiagramElement(mem, ((ColimitElement.Memory)memory).getColimitElement());
            }
            return newDiagram;
        }
        
    }    

    /** Collection of colimits.
    */
    static class Colimit extends Member {
        private static final ColimitElement[] EMPTY = new ColimitElement[0];

        static final long serialVersionUID =3206093459760846163L;

        /** @param ce colimit element memory impl to work in
        */
        public Colimit (ColimitElement.Memory memory) {
            super (memory, ElementProperties.PROP_DIAGRAMS, EMPTY);
        }
        
        public MemberElement find(String name) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                ColimitElement element = (ColimitElement)it.next ();
                String ename = element.getName();
                if (name.equals(ename)) {
                    return element;
                }
            }
            // nothing found
            return null;
        }

        /** Clones the object.
        * @param obj object to clone
        * @return cloned object
        */
        protected Object clone (Object obj) {
	    ColimitElement colimit = (ColimitElement) obj;
            ColimitElement.Memory mem = new ColimitElement.Memory (colimit);
            ColimitElement newColimit = new ColimitElement(mem, colimit.getSource());
            mem.copyFrom(colimit);
            return newColimit;
        }
    }
    
   /* static final class UnitId extends Member {
        private static final UIDElement[] EMPTY = new UIDElement[0];

        static final long serialVersionUID =5715072242254795093L;
     
        public UnitId (UIDElement.Memory memory) {
            super (memory,
		   ElementProperties.PROP_UIDS,
		   EMPTY);
        }

        protected Object clone(Object el) {
	    UIDElement unitId = (UIDElement) el;
            UIDElement.Memory mem = new UIDElement.Memory (unitId);
            
            //WLP: will this work?
            UIDElement newUID = null;
            if (memory instanceof MorphismElement.Memory) {
                newUID = new UIDElement(mem, ((MorphismElement.Memory)memory).getMorphismElement());
            }
            return newUID;
        }
        
        public UIDElement find (String id, String path) {
            if (array == null)
                return null;

            Iterator it = array.iterator ();
            while (it.hasNext ()) {
                UIDElement unitId = (UIDElement)it.next ();
                if (id.equals(unitId.getName()) && path.equals(unitId.getPath())) {
		    return unitId;
		}
	    }
            // nothing found
            return null;
        }
        
    }    
    */
}
