/*
 * SourceOptions.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.10  2003/07/05 07:46:39  lambert
 * *** empty log message ***
 *
 * Revision 1.9  2003/04/23 01:15:44  weilyn
 * ClaimCustomizer.java
 *
 * Revision 1.8  2003/04/01 02:29:41  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:13:59  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:14:22  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:06:45  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:32:11  weilyn
 * Added support for expressions.
 *
 * Revision 1.3  2003/02/16 02:15:05  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:42:09  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:13  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.util.ResourceBundle;

import org.openide.src.SourceException;
import org.openide.options.SystemOption;
import org.openide.util.HelpCtx;
import org.openide.util.NbBundle;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.ElementFormat;

/*
* TODO:
* <UL>
*  <LI> weak listeners for listening on format changes - all element nodes should react on it.
* </UL>
*/
/** Display options for the hierarchy of source elements.
* These options determine the display name format
* of each kind of element.
* <p>Also included are read-only properties for the "long formats",
* which are in practice used for {@link ElementNode#getHintElementFormat}.
* <p>Changes to settings will fire property change events.
*
*/
public final class SourceOptions extends SystemOption {
    private static final int lastCompatibleVersionTag = 1;
    private static final int currentVersionTag = 1;
    
    /** Resource bundle. */
    private static ResourceBundle bundle;

    /** Kinds of the format. */
    private static final byte T_SPEC = 0;
    private static final byte T_IMPORT = 1;
    private static final byte T_SORT = 2;
    private static final byte T_OP = 3;
    private static final byte T_DEF = 4;
    private static final byte T_CLAIM = 5;
    private static final byte T_PROOF = 6;
    private static final byte T_MORPHISM = 7;
    private static final byte T_DIAGRAM = 8;
    private static final byte T_COLIMIT = 9;
    //private static final byte T_UID = 10;
    private static final byte T_DIAG_ELEM = 11;

    /** Names of all properties. */
    static final String[] PROP_NAMES = {
        "specElementFormat", // NOI18N
        "importElementFormat", //NOI18N
        "sortElementFormat", // NOI18N
        "opElementFormat",   //NOI18N
        "defElementFormat",   //NOI18N
        "claimElementFormat", // NOI18N
        "proofElementFormat", // N0I18N
        "morphismElementFormat", // N0I18N
        "diagramElementFormat", // N0I18N
        "colimitElementFormat", // N0I18N
        "uidElementFormat", //NOI18N
        "diagElemElementFormat", // NOI18N
    };
    
    static Element[] TEST_ELEMENTS;

    /** default values for the formats - short form. */
    private static final ElementFormat[] DEFAULT_FORMATS_SHORT = new ElementFormat[PROP_NAMES.length];

    /** default values for the formats - long form. */
    private static final ElementFormat[] DEFAULT_FORMATS_LONG = new ElementFormat[PROP_NAMES.length];

    /**
     * Current format for individual element types, or null if the format is
     * not yet specified by the user.
     */
    private ElementFormat[] formats = new ElementFormat[PROP_NAMES.length];
    
    /**
     * Version tag to use;
     */
    private int version;
    
    private static synchronized void loadBundle() {
        if (bundle != null)
            return;
        bundle = NbBundle.getBundle(SourceOptions.class);
    }
    
    private static void loadDefaultFormats() {
        if (DEFAULT_FORMATS_SHORT[0] != null)
            return;
        synchronized (SourceOptions.class) {
            if (DEFAULT_FORMATS_SHORT[0] != null)
                return;
            loadBundle();
            for (int i = 0; i < PROP_NAMES.length; i++) {
                DEFAULT_FORMATS_SHORT[i] = new ElementFormat(bundle.getString("SHORT_"+PROP_NAMES[i]));
                DEFAULT_FORMATS_LONG[i] = new ElementFormat(bundle.getString("LONG_"+PROP_NAMES[i]));
            }
        }
    }
    
    /**
     * Resets all element formats to their default values.
     */
    private void clearElementFormats() {
        formats = new ElementFormat[PROP_NAMES.length];
    }

    /** Property name of the import display format. */
    public static final String PROP_IMPORT_FORMAT = PROP_NAMES[T_IMPORT];

    /** Property name of the sort display format. */
    public static final String PROP_SORT_FORMAT = PROP_NAMES[T_SORT];

    /** Property name of the op display format. */
    public static final String PROP_OP_FORMAT = PROP_NAMES[T_OP];

    /** Property name of the op display format. */
    public static final String PROP_DEF_FORMAT = PROP_NAMES[T_DEF];

    /** Property name of the op display format. */
    public static final String PROP_CLAIM_FORMAT = PROP_NAMES[T_CLAIM];

    /** Property name of the spec display format. */
    public static final String PROP_SPEC_FORMAT = PROP_NAMES[T_SPEC];

    /** Property name of the proof display format. */
    public static final String PROP_PROOF_FORMAT = PROP_NAMES[T_PROOF];
    
    /** Property name of the morphism display format. */
    public static final String PROP_MORPHISM_FORMAT = PROP_NAMES[T_MORPHISM];

    /** Property name of the diagElem display format. */
    public static final String PROP_DIAG_ELEM_FORMAT = PROP_NAMES[T_DIAG_ELEM];
    
    /** Property name of the diagram display format. */
    public static final String PROP_DIAGRAM_FORMAT = PROP_NAMES[T_DIAGRAM];
    
    /** Property name of the colimit display format. */
    public static final String PROP_COLIMIT_FORMAT = PROP_NAMES[T_COLIMIT];

    /** Property name of the unitId display format. */
   // public static final String PROP_uid_FORMAT = PROP_NAMES[T_UID];

    /** Property name of the 'categories usage' property. */
    public static final String PROP_CATEGORIES_USAGE = "categoriesUsage"; // NOI18N

    /** CategoriesUsage property current value */
    private static boolean categories = true;

    static final long serialVersionUID =-2120623049071035434L;

    /** @return display name
    */
    public String displayName () {
        loadBundle();
        return bundle.getString("MSG_sourceOptions");
    }

    public HelpCtx getHelpCtx () {
        return new HelpCtx (SourceOptions.class);
    }

    // ============= public methods ===================

    /** Set the spec format.
    * @param format the new format
    */
    public void setSpecElementFormat(ElementFormat format) {
        setElementFormat(T_SPEC, format);
    }

    /** Get the spec format.
    * @return the current format
    */
    public ElementFormat getSpecElementFormat() {
        return getElementFormat(T_SPEC);
    }

    private ElementFormat getElementFormat(int type) {
        synchronized (this) {
            if (formats[type] != null)
                return formats[type];
            // if writing the option to the disk, return a default == null value.
            if (isWriteExternal())
                return null;
        }
        loadDefaultFormats();
        return DEFAULT_FORMATS_SHORT[type];
    }

    /** Set the import format.
    * @param format the new format
    */
    public void setImportElementFormat(ElementFormat format) {
        setElementFormat(T_IMPORT, format);
    }
    
    /** Get the import format.
    * @return the current format
    */
    public ElementFormat getImportElementFormat() {
        return getElementFormat(T_IMPORT);
    }


    /** Set the sort format.
    * @param format the new format
    */
    public void setSortElementFormat(ElementFormat format) {
        setElementFormat(T_SORT, format);
    }
    
    /** Get the sort format.
    * @return the current format
    */
    public ElementFormat getSortElementFormat() {
        return getElementFormat(T_SORT);
    }

    /** Set the op format.
    * @param format the new format
    */
    public void setOpElementFormat(ElementFormat format) {
        setElementFormat(T_OP, format);
    }

    /** Get the op format.
    * @return the current format
    */
    public ElementFormat getOpElementFormat() {
        return getElementFormat(T_OP);
    }

    /** Set the def format.
    * @param format the new format
    */
    public void setDefElementFormat(ElementFormat format) {
        setElementFormat(T_DEF, format);
    }

    /** Get the def format.
    * @return the current format
    */
    public ElementFormat getDefElementFormat() {
        return getElementFormat(T_DEF);
    }

    /** Set the claim format.
    * @param format the new format
    */
    public void setClaimElementFormat(ElementFormat format) {
        setElementFormat(T_CLAIM, format);
    }

    /** Get the claim format.
    * @return the current format
    */
    public ElementFormat getClaimElementFormat() {
        return getElementFormat(T_CLAIM);
    }

    /** Set the proof format.
    * @param format the new format
    */
    public void setProofElementFormat(ElementFormat format) {
        setElementFormat(T_PROOF, format);
    }

    /** Get the proof format.
    * @return the current format
    */
    public ElementFormat getProofElementFormat() {
        return getElementFormat(T_PROOF);
    }
    
    /** Set the morphism format.
    * @param format the new format
    */
    public void setMorphismElementFormat(ElementFormat format) {
        setElementFormat(T_MORPHISM, format);
    }

    /** Get the morphism format.
    * @return the current format
    */
    public ElementFormat getMorphismElementFormat() {
        return getElementFormat(T_MORPHISM);
    }

    /** Set the diagElem format.
    * @param format the new format
    */
    public void setDiagElemElementFormat(ElementFormat format) {
        setElementFormat(T_DIAG_ELEM, format);
    }
    
    /** Get the diagElem format.
    * @return the current format
    */
    public ElementFormat getDiagElemElementFormat() {
        return getElementFormat(T_DIAG_ELEM);
    }

    /** Set the diagram format.
    * @param format the new format
    */
    public void setDiagramElementFormat(ElementFormat format) {
        setElementFormat(T_DIAGRAM, format);
    }

    /** Get the diagram format.
    * @return the current format
    */
    public ElementFormat getDiagramElementFormat() {
        return getElementFormat(T_DIAGRAM);
    }

    /** Set the colimit format.
    * @param format the new format
    */
    public void setColimitElementFormat(ElementFormat format) {
        setElementFormat(T_COLIMIT, format);
    }

    /** Get the colimit format.
    * @return the current format
    */
    public ElementFormat getColimitElementFormat() {
        return getElementFormat(T_COLIMIT);
    }

    /** Set the unitId format.
    * @param format the new format
    */
   /* public void setUIDElementFormat(ElementFormat format) {
        setElementFormat(T_UID, format);
    }*/
    
    /** Get the unitId format.
    * @return the current format
    */
    /*public ElementFormat getUIDElementFormat() {
        return getElementFormat(T_UID);
    }*/

    // ============= getters for long form of formats =================

    /** Get the spec format for longer hints.
    * @return the current format
    */
    public ElementFormat getSpecElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_SPEC];
    }

    /** Get the import format for longer hints.
    * @return the current format
    */
    public ElementFormat getImportElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_IMPORT];
    }

    /** Get the sort format for longer hints.
    * @return the current format
    */
    public ElementFormat getSortElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_SORT];
    }

    /** Get the op format for longer hints.
    * @return the current format
    */
    public ElementFormat getOpElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_OP];
    }

    /** Get the def format for longer hints.
    * @return the current format
    */
    public ElementFormat getDefElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_DEF];
    }

    /** Get the claim format for longer hints.
    * @return the current format
    */
    public ElementFormat getClaimElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_CLAIM];
    }

    /** Get the proof format for longer hints.
    * @return the current format
    */
    public ElementFormat getProofElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_PROOF];
    }

    /** Get the morphism format for longer hints.
    * @return the current format
    */
    public ElementFormat getMorphismElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_MORPHISM];
    }

    /** Get the diagElem format for longer hints.
    * @return the current format
    */
    public ElementFormat getDiagElemElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_DIAG_ELEM];
    }

    /** Get the diagram format for longer hints.
    * @return the current format
    */
    public ElementFormat getDiagramElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_DIAGRAM];
    }

    /** Get the colimit format for longer hints.
    * @return the current format
    */
    public ElementFormat getColimitElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_COLIMIT];
    }

    /** Get the unitId format for longer hints.
    * @return the current format
    */
    /*public ElementFormat getUIDElementLongFormat() {
        loadDefaultFormats();
        return DEFAULT_FORMATS_LONG[T_UID];
    }*/

    // ============= categories of elements usage ===================

    /** Set the property whether categories under spec elements should be used or not.
    * @param cat if <CODE>true</CODE> the elements under spec elements are divided into
    *     categories: sorts, ops. Otherwise (<CODE>false</CODE>) all elements
    *     are placed directly under spec element.
    */
    public void setCategoriesUsage(boolean cat) {
        categories = cat;
    }

    /** Test whether categiries under spec elements are used or not.
    * @return <CODE>true</CODE> if the elements under spec elements are divided into
    *     categories: sorts, ops. Otherwise <CODE>false</CODE> (all elements
    *     are placed directly under spec element).
    */
    public boolean getCategoriesUsage() {
        return categories;
    }

    // ============= private methods ===================
    
    private synchronized static Element getTestElement(int index) {
        if (TEST_ELEMENTS == null) {
            Element[] els = new Element[PROP_NAMES.length];
            
            try {
                String id = "foo"; // NOI18N

                SpecElement mm = new SpecElement();
                mm.setName(id);
                els[T_SPEC] = mm;
                TEST_ELEMENTS = els;

                ImportElement i = new ImportElement();
                i.setName(id); // NOI18N
                els[T_IMPORT] = i;

                SortElement f = new SortElement();
                f.setName(id); // NOI18N
                els[T_SORT] = f;

                OpElement m = new OpElement();
                m.setName(id);
                m.setSort(id);
                els[T_OP] = m;

                DefElement w = new DefElement();
                w.setName(id); // NOI18N
                els[T_DEF] = w;

                ClaimElement c = new ClaimElement();
                c.setName(id);
                c.setClaimKind(id);
                c.setExpression(id);
                els[T_CLAIM] = c;

            } catch (SourceException ex) {
                // cannot happen.
            }
        }
        return TEST_ELEMENTS[index];
    }
        
    /** Sets the format for the given index.
    * @param index One of the constants T_XXX
    * @param format the new format for the specific type.
    */
    private void setElementFormat(byte index, ElementFormat format) {
        ElementFormat old = formats[index];
        if (format != null) {
            // check whether the format is valid for the element type:
            Element el = getTestElement(index);
            try {
                format.format(el);
            } catch (IllegalArgumentException iae) {
                throw (IllegalArgumentException)
                    org.openide.ErrorManager.getDefault().annotate(
                        iae, org.openide.ErrorManager.USER, null,
                        bundle.getString("MSG_IllegalElementFormat"), // NOI18N
                        null, null);
            }
        }
        formats[index] = format;
        firePropertyChange (PROP_NAMES[index], old, formats[index]);
    }
    
    public void writeExternal(java.io.ObjectOutput out) throws java.io.IOException {
        super.writeExternal(out);
        out.writeInt(version);
    }
    
    public void readExternal (java.io.ObjectInput in)
    throws java.io.IOException, ClassNotFoundException {
        super.readExternal(in);
        if (in.available() > 0) {
	    version = in.readInt();
        }
        if (version < lastCompatibleVersionTag) {
            clearElementFormats();
            version = currentVersionTag;
        }
    }
}
