/*
 * DocumentModelBuilder.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.10  2003/06/23 18:00:18  weilyn
 * internal release version
 *
 * Revision 1.9  2003/04/23 01:16:24  weilyn
 * DiagElemInfo.java
 *
 * Revision 1.8  2003/04/01 02:29:41  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:14:00  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:15:31  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:10:09  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:35:21  weilyn
 * Added support for expressions.
 *
 * Revision 1.3  2003/02/16 02:16:02  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:45:52  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:16  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

//import java.util.List;
//import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import javax.swing.text.*;

import org.openide.text.CloneableEditorSupport;
import org.openide.text.PositionBounds;
import org.openide.text.PositionRef;
import org.openide.text.NbDocument;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.SourceText;


public class DocumentModelBuilder extends SourceInfo implements ElementFactory {
    CloneableEditorSupport  editSupp;
    char[]  inputText;
    boolean computeHash;
    int[]   lineOffsets;
    private static final boolean DEBUG = false;
    
    public DocumentModelBuilder(CloneableEditorSupport supp) {
        this.editSupp = supp;
    }
    
    protected void setContent(char[] content, boolean computeHash) {
        this.inputText = content;
        this.computeHash = computeHash;
    }
    
    /** Creates an element for a spec.
	@param name Name of the spec.
    */
    public Item createSpec(String name) {
	SpecInfo info = new SpecInfo(name);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createSpec(): "+info);
	}
	return info;
    }
    
    /** Creates an element for an sort.
	@param str The sort string.
    */
    public Item	createSort(String name, String[] params) {
	SortInfo info = new SortInfo(name, params);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createSort(): "+info);
	}
	return info;
    }
    
    /** Creates an element for an op.
	@param parameter Name of the parameter to be assigned value.
	@param value Value to be assigned to the parameter.
    */
    public Item	createOp(String name, String sort) {
	OpInfo info = new OpInfo(name, sort);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createOp(): "+info);
	}
	return info;
    }
    
    /** Creates an element for a def.
	@param str The def string.
    */
    public Item	createDef(String name, String[] params, String expression) {
	DefInfo info = new DefInfo(name, params, expression);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createDef(): "+info);
	}
	return info;
    }
  
    /** Creates an element for a claim.
	@param parameter Name of the parameter to be assigned value.
	@param value Value to be assigned to the parameter.
    */
    public Item	createClaim(String name, String claimKind, String expression) {
	ClaimInfo info = new ClaimInfo(name, claimKind, expression);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createClaim(): "+info);
	}
	return info;
    }
    
    /** Creates an element for an import.
	@param str The import string.
    */
    public Item	createImport(String name, ElementFactory.Item item) {
	ImportInfo info = new ImportInfo(name);
        if (item != null) {
            //TODO: do something
        }
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createImport(): "+info);
	}
	return info;
    }
 
    /** Creates an element for a proof.
	@param name Name of the proof.
    */
    public Item createProof(String name, String proofString) {
	ProofInfo info = new ProofInfo(name, proofString);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createProof(): "+info);
	}
	return info;
    }
    
    /** Creates an element for a morphism.
	@param name Name of the morphism.
    */
    public Item createMorphism(String name, String sourceUnitID, String targetUnitID) {
	MorphismInfo info = new MorphismInfo(name, sourceUnitID, targetUnitID);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createMorphism(): "+info);
	}
	return info;
    }

    /** Creates an element for a diagElem.
	@param str The diagElem string.
    */
    public Item	createDiagElem(String name) {
	DiagElemInfo info = new DiagElemInfo(name);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createDiagElem(): "+info);
	}
	return info;
    }
    
    /** Creates an element for a diagram.
	@param name Name of the diagram.
    */
    public Item createDiagram(String name) {
	DiagramInfo info = new DiagramInfo(name);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createDiagram(): "+info);
	}
	return info;
    }

    /** Creates an element for a colimit.
	@param name Name of the colimit.
    */
    public Item createColimit(String name) {
	ColimitInfo info = new ColimitInfo(name);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createColimit(): "+info);
	}
	return info;
    }
    
    /** Creates an element for a unitId.
	@param str The unitId string.
    */
    /*public Item	createUID(String name, String path) {
	UIDInfo info = new UIDInfo(name, path);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createUID(): "+info);
	}
	return info;
    }*/
    
    /** Sets bounds for the whole element. Begin is offset of first character of the element,
	end is the offset of the last one.
    */
    public void setBounds(Item item, int begin, int end) {
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.setBounds: item="+item+", bounds=("+begin+", "+end+")");
	}
        BaseElementInfo info = (BaseElementInfo)item;
        info.wholeBounds = createStableBounds(begin, end);
    }
    
    /** Sets bounds for the whole element.
    */
    public void setBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn) {
	int begin = getOffset(beginLine, beginColumn);
	int end = getOffset(endLine, endColumn);
	setBounds(item, begin, end);
    }
    
    public int getOffset(int line, int column) {
	return getLineOffset(line - 1) + column - 1;
    }

    public int getLineOffset(int line) {
	StyledDocument doc = editSupp.getDocument();
	if (doc == null) {
	    try {
		doc = editSupp.openDocument();
	    } catch (Exception e) {
	    }
	}
	if (doc != null) {
	    int lineOffset = NbDocument.findLineOffset(doc, line);
	    return lineOffset;
	}
	/*
	else {
	    if (lineOffsets == null) {
		String inputStr = new String(inputText);
		List lineOffsetList = new ArrayList();
		int numOflines = 1;
		for (int i = 0, j = 0; i < inputText.length; i++) {
		    if (inputText[i] == '\r') {
			continue;
		    }
		    if (inputText[i] == '\n') {
			lineOffsetList.add(new Integer(j + 1));
			numOflines++;
		    }
		    j++;
		}
		lineOffsets = new int[numOflines];
		lineOffsets[0] = 0;
		for (int i = 0, j = 1;  j < numOflines; i++, j++) {
		    lineOffsets[j] = ((Integer) lineOffsetList.get(i)).intValue();
		}
	    }
	    return lineOffsets[line];
	}
	*/
	return 0;
    }

    public void setHeaderBounds(Item item, int begin, int end) {
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.setHeaderBounds: item="+item+", bounds=("+begin+", "+end+")");
	}
        BaseElementInfo info = (BaseElementInfo)item;
        info.headerBounds = createStableBounds(begin, end);
    }
    
    public void setHeaderBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn) {
	int begin = getOffset(beginLine, beginColumn);
	int end = getOffset(endLine, endColumn);
	setHeaderBounds(item, begin, end);
    }
    
    /** Sets bounds for the body of the element.
     */
    public void setBodyBounds(Item item, int begin, int end) {
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.setBodyBounds: item="+item+", bounds=("+begin+", "+end+")");
	}
        BaseElementInfo info = (BaseElementInfo)item;
        info.bodyBounds = createAbsorbingBounds(begin, end);
	/*
        if (computeHash && ((info instanceof OpInfo)
			    || (info instanceof SortInfo))) {
            info.bodyContent = String.copyValueOf(this.inputText, begin, end - begin);
        }
	*/
    }
    
    public void setBodyBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn) {
	int begin = getOffset(beginLine, beginColumn);
	int end = getOffset(endLine, endColumn);
	setBodyBounds(item, begin, end);
    }
    
    public void setDocumentation(Item item, int begin, int end, String text) {
        BaseElementInfo info = (BaseElementInfo)item;
        info.docText = text;
        if (text != null && begin >= 0 && end > begin)
            info.docBounds = createStableBounds(begin, end);
        else
            info.docBounds = null;
    }
    
    public void setDocumentation(Item item, int beginLine, int beginColumn, int endLine, int endColumn, String text) {
	int begin = getOffset(beginLine, beginColumn);
	int end = getOffset(endLine, endColumn);
	setDocumentation(item, begin, end, text);
    }
    
    protected PositionBounds createStableBounds(int from, int to) {
        PositionRef posBegin = editSupp.createPositionRef(from, Position.Bias.Backward);
        PositionRef posEnd = editSupp.createPositionRef(to, Position.Bias.Forward);
        return new PositionBounds(posBegin, posEnd);
    }
    
    protected PositionBounds createAbsorbingBounds(int from, int to) {
        PositionRef posBegin = editSupp.createPositionRef(from, Position.Bias.Forward);
        PositionRef posEnd = editSupp.createPositionRef(to, Position.Bias.Backward);
        return new PositionBounds(posBegin, posEnd);
    }

    public void setParent(Collection children, Item parent) {
	for (Iterator i = children.iterator(); i.hasNext();) {
	    setParent((Item)i.next(), parent);
	}
    }

    /** Binds two Items together in a parent-child relationship.
	@param child Child item to be inserted into the parent
	@param parent Parent item
    */
    public void setParent(Item child, Item parent) {
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.setParent: child="+Util.print(child)+" parent="+Util.print(parent));
	}
	if (child == null) {
	    return;
	}

	BaseElementInfo childInfo = (BaseElementInfo) child;
	childInfo.parent = parent;
        if (DEBUG) {
            Util.log("DocumentModelBuilder.setParent Parent = "+parent);
        }
	if (parent == null) {
	    // must be a top-level class:
	    if (child instanceof SpecInfo) {
	       addMember(SourceInfo.SPEC, childInfo);
	    } else if (child instanceof ProofInfo) {
               addMember(SourceInfo.PROOF, childInfo); 
            } else if (child instanceof MorphismInfo) {
               addMember(SourceInfo.MORPHISM, childInfo); 
            } else if (child instanceof DiagramInfo) {
               addMember(SourceInfo.DIAGRAM, childInfo); 
            } else if (child instanceof ColimitInfo) {
               addMember(SourceInfo.COLIMIT, childInfo); 
            } /*else if (child instanceof UIDInfo) {
               addMember(SourceInfo.UnitId, childInfo);
            }*/
	} else if (parent instanceof SpecInfo) {
	    SpecInfo parentInfo = (SpecInfo)parent;
	    if (child instanceof SortInfo) {
		parentInfo.addMember(SpecInfo.SORT, childInfo);
	    } else if (child instanceof OpInfo) {
		parentInfo.addMember(SpecInfo.OP, childInfo);
	    } else if (child instanceof DefInfo) {
		parentInfo.addMember(SpecInfo.DEF, childInfo);
	    } else if (child instanceof ClaimInfo) {
		parentInfo.addMember(SpecInfo.CLAIM, childInfo);
	    } else if (child instanceof ImportInfo) {
                parentInfo.addMember(SpecInfo.IMPORT, childInfo);
            }
	} else if (parent instanceof ProofInfo) {
            ProofInfo parentInfo = (ProofInfo)parent;
        } else if (parent instanceof MorphismInfo) {
            MorphismInfo parentInfo = (MorphismInfo)parent;
        } else if (parent instanceof DiagramInfo) {
            DiagramInfo parentInfo = (DiagramInfo)parent;
            if (child instanceof DiagElemInfo) {
                parentInfo.addMember(DiagramInfo.DIAG_ELEM, childInfo);
            }
        } else if (parent instanceof ColimitInfo) {
            ColimitInfo parentInfo = (ColimitInfo)parent;
            if (child instanceof DiagramInfo) {
                parentInfo.addMember(ColimitInfo.DIAGRAM, childInfo);
            }
        } //TODO: import info
    }
    
    public void markError(Item item) {
        // huh ? attach some error-information-decorator to an element ??
    }
    
}
