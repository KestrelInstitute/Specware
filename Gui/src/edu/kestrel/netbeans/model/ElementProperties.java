/*
 * ElementProperties.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.10  2003/06/23 18:00:15  weilyn
 * internal release version
 *
 * Revision 1.9  2003/04/23 01:14:39  weilyn
 * BindingFactory.java
 *
 * Revision 1.8  2003/04/01 02:29:37  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:13:56  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:14:01  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:12:59  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:30:23  weilyn
 * Added support for expressions.
 *
 * Revision 1.3  2003/02/16 02:14:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:56  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

/** Names of properties of elements.
 *
 */
public interface ElementProperties {
    public static final String PROP_MEMBERS = "members"; // NOI18N
    
    public static final String PROP_SPECS = "specs"; // NOI18N
    
    public static final String PROP_IMPORTS = "imports"; //NOI18N

    public static final String PROP_SORTS = "sorts"; // NOI18N
    
    public static final String PROP_OPS = "ops"; // NOI18N
    
    public static final String PROP_DEFS = "defs"; // NOI18N
    
    public static final String PROP_CLAIMS = "claims"; // NOI18N
    
    public static final String PROP_DIAG_ELEMS = "diagram_elements";
    
    public static final String PROP_NAME = "name"; // NOI18N
    
    public static final String PROP_PARAMETERS = "parameters"; // NOI18N
    
    public static final String PROP_SORT = "sort"; // NOI18N
    
    public static final String PROP_STATUS = "status"; // NOI18N
    
    public static final String PROP_VALID = "valid"; // NOI18N
    
    public static final String PROP_CLAIM_KIND = "claim_kind"; // NOI18N    

    public static final String PROP_EXPRESSION = "expression"; // NOI18N        

    public static final String PROP_PROOFS = "proofs"; // NOI18N        
    
    public static final String PROP_PROOFSTRING = "proof_string"; // NOI18N        

    public static final String PROP_MORPHISMS = "morphisms"; // NOI18N         
    
    public static final String PROP_DIAGRAMS = "diagrams"; // NOI18N      

    public static final String PROP_COLIMITS = "colimits"; // NOI18N      

//    public static final String PROP_UIDS = "uids"; // NOI18N
    
    public static final String PROP_PATH = "path"; // NOI18N
    
    public static final String PROP_SOURCE_UNIT_ID = "source_unit_id"; // NOI18N
    
    public static final String PROP_TARGET_UNIT_ID = "target_unit_id"; // NOI18N
    
    public static final String PROP_UNIT_IMPORTED = "unit_imported"; //NOI18N
}
