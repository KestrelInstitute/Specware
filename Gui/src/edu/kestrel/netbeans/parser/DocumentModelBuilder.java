/*
 * DocumentModelBuilder.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
    
    /** Creates an element for an op.
	@param parameter Name of the parameter to be assigned value.
	@param value Value to be assigned to the parameter.
    */
    public Item	createClaim(String name, String claimKind) {
	ClaimInfo info = new ClaimInfo(name, claimKind);
	if (DEBUG) {
	    Util.log("*** DocumentModelBuilder.createClaim(): "+info);
	}
	return info;
    }
    
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
        
	//Util.log("DocumentModelBuilder.setParent Parent = "+parent);
	if (parent == null) {
	    // must be a top-level class:
	    //addSpec((SpecInfo)child);
	    if (child instanceof SpecInfo) {
	      //Util.log("DocumentModelBuilder.setParent child is an instance of specInfo = "+child);
	      addMember(SourceInfo.SPEC, childInfo);
	    } 
	} else if (parent instanceof SpecInfo) {
	    SpecInfo parentInfo = (SpecInfo)parent;
	    if (child instanceof SortInfo) {
		parentInfo.addMember(SpecInfo.SORT, childInfo);
	    } else if (child instanceof OpInfo) {
		parentInfo.addMember(SpecInfo.OP, childInfo);
	    } else if (child instanceof ClaimInfo) {
		parentInfo.addMember(SpecInfo.CLAIM, childInfo);
	    }
	} 
    }
    
    public void markError(Item item) {
        // huh ? attach some error-information-decorator to an element ??
    }
    
}
