/*
 * Binding.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.11  2003/07/05 07:46:36  lambert
 * *** empty log message ***
 *
 * Revision 1.10  2003/06/23 18:00:15  weilyn
 * internal release version
 *
 * Revision 1.9  2003/04/23 01:11:50  weilyn
 * Added morphism source/target support
 *
 * Revision 1.8  2003/04/01 02:29:36  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:13:55  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:14:00  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:12:50  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:30:12  weilyn
 * Added support for expressions.
 *
 * Revision 1.3  2003/02/16 02:14:02  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:53  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.util.*;

import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;

/**
 * The Binding (sub-)classes give individual model elements the I/O capabilities (e.g.
 * a Document or a Stream). Each element is, in fact, a composite of the element itself
 * and the I/O binding of that element. All model change operations are transformed into
 * simpler calls on the binding objects.
 */
public interface Binding {
    
    /** Binds any MemberElement to the underlying text.
     */
    public interface Member extends Binding {
        /**
         * Requests a change of member's name.
         */
        public void changeName(String name) throws SourceException;
    }

    /*
    public interface Body {
        public String getBodyContent() throws SourceException;
        public void changeBody(String bodyString) throws SourceException;
        public void copyBody(String bodyString);
    }
    */

    /** Binds a sort to the source.
     */
    public interface Sort extends Member {
        /**
         * Changes the formal parameters of the sort.
         */
        public void changeParameters(String[] newParams) throws SourceException;
    }
    
    /** Binds a op to the source.
     */
    public interface Op extends Member {
        /**
         * Changes the arguments of the op.
         */
        public void changeSort(String sort) throws SourceException;
    }
    
    /** Binds a def to the source.
     */
    public interface Def extends Member {
        /**
         * Changes the arguments of the def.
         */
        public void changeParameters(String[] newParams) throws SourceException;
        public void changeExpression(String expression) throws SourceException;
    }

    /** Binds a claim to the source.
     */
    public interface Claim extends Member {
        /**
         * Changes the arguments of the claim.
         */
        public void changeClaimKind(String claimKind) throws SourceException;
        public void changeExpression(String expression) throws SourceException;
    }

    /** Binds an import to the source.
     */
    public interface Import extends Member {
        
        public void changeUnitImported(MemberElement unit) throws SourceException;
        
    }
    
    /** Binds a unitId to the source.
     */
//    public interface UnitId extends Member {
        /**
         * Changes the arguments of the unitId.
         */
//        public void changePath(String path) throws SourceException;
//    }
    
    /** Binds a diagElem to the source.
     */
    public interface DiagElem extends Member {
    }
        
    
    
    /** Container interface that manages contained bindings. Currently only reorder operation
     * is supported.
     */
    public interface Container {
        /**
         * Initializes a new binding for the element so the element is stored after the
         * `previous' binding, if that matters to the binding implementation.
         * @param toInitialize the binding that is being initialized & bound to the storage.
         * @param previous marker spot, the binding that should precede the new one. 
         */
        public void insert(Binding toInitialize, Binding previous) throws SourceException;
        
        /** Replaces the slot contents with another element (different type permitted ?)
         */
        public void replace(Binding oldBinding, Binding newBinding) throws SourceException;
        
        /** The map contains mapping from target places to their new contents.
         */
        public void reorder(Map fromToMap) throws SourceException;
        
        /** Determines, if the executing code is allowed to insert after the specified
         * binding.
         */
        public boolean canInsertAfter(Binding b);

        /**
         * Changes container's contents as one operation, given the information in 
         * the event object.
         */
        public void changeMembers(MultiPropertyChangeEvent evt) throws SourceException;
    }
    
    public interface Source extends Binding, Container {
      //public Binding.Container    getSpecSection();
      //public Binding.Container    getOpSection();
    }

    public interface Spec extends Member, Container {
    }
    
    public interface Proof extends Member, Container {
        public void changeProofString(String proofString) throws SourceException;
    }
    
    public interface Morphism extends Member, Container {
        /**
         * Changes the sourceUnitID of the morphism
         */
        public void changeSourceUnitID(UnitID newSourceUnitID) throws SourceException;    
        
        /**
         * Changes the targetUnitID of the morphism
         */
        public void changeTargetUnitID(UnitID newTargetUnitID) throws SourceException;    
    }

    public interface Diagram extends Member, Container {
    }

    public interface Colimit extends Member, Container {
    }
    
}

