/*
 * ElementBinding.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.beans.*;
import java.lang.reflect.Method;
import java.io.Writer;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.*;

import javax.swing.text.*;

import org.openide.text.*;
import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.model.Element;

/**
 *
 */
public abstract class ElementBinding implements TextBinding, ElementProperties {
    private Element                    el;

    /** Bounds of the element as whole.
     */
    protected PositionBounds      wholeBounds;
    
    /** Bounds of the element's header (exact meaning depends on the element type)
     */
    protected PositionBounds      headerBounds;

    /** Bounds of the body of the element.
     */
    protected PositionBounds      bodyBounds;
    
    /** SourceText text.
     */
    protected SourceText          source;
    
    protected ContainerImpl       containerRef;

    /**
     * Cached Methods used for setting property values.
     */
    static Map setterCache;
    
    private static final boolean DEBUG = false;

    /**
     * System-dependent line separator, or null if the system sep is not 
     * defined or is single LF char.
     */
    private static final String lineSeparator;
    
    /**
     * Length of the line separator string.
     */
    private static final int lineSeparatorLength;
    
    /**
     * Linefeed string, used internally to separate lines.
     */
    private static final String LINEFEED = "\n"; // NOI18N
    
    static {
        String sep = System.getProperty("line.separator"); // NOI18N
        if (sep == null || LINEFEED.equals(sep)) {
            lineSeparator = null;
            lineSeparatorLength = -1;
        } else {
            lineSeparator = sep;
            lineSeparatorLength = sep.length();
        }
    }
    
    /** Creates new ElementBinding */
    public ElementBinding(Element el, SourceText s) {
        this.el = el;
        this.source = s;
        s.registerBinding(el, this);
    }
    
    public TextBinding.Container getContainer(String type) {
        return containerRef;
    }
    
    public void linkAfter(TextBinding b) {
    }

    public Element getElement() {
        return this.el;
    }

    /**
     * Returns range occupied by this element.
     */
    public PositionBounds getElementRange(boolean defRange) {
        if (!defRange || headerBounds == null) {
            return wholeBounds;
        } else {
            return new PositionBounds(headerBounds.getBegin(),
                wholeBounds.getEnd());
        }
    }
    
    /**
     * Clones the target element.
     */
    protected abstract Element cloneElement();
    
    /** Actually creates the element in the SourceText text. This is called by the container
     * binding's insertAfter implementation to actually insert the element. The default
     * implementation will print the element through the ElementPrinter and compute
     * positions of the element's parts.
     */
    public void create(PositionBounds bounds) throws SourceException {
        wholeBounds = bounds;
        if (DEBUG) {
            System.err.println("Pre-create dump:\n----------------------------------------------------"); // NOI18N
            System.err.println("element: " + el); // NOI18N
            System.err.println("creating at " + bounds); // NOI18N
            source.dumpDocument();
        }
        regenerateWhole(this.el, true);
    }
    
    /**
     * Prepares the binding for insertion of its sibling. This implementation does nothing,
     * but bindings that are bound together in a textual order may perform some tasks
     * in this methods.
     */
    public PositionRef prepareInsert(ElementBinding tbi, boolean after)
    throws SourceException {
        return after ? wholeBounds.getEnd() : wholeBounds.getBegin();
    }
    
    /** Initializes the new binding with a position right after this element's own pos,
     * optionally creating an empty line for the element, if needed.
     * The implementation assumes that somebody else has already locked the document for
     * writing, so that all offset operations are thread-safe.
     */
    public void insertAfter(ElementBinding b) throws SourceException {
        b.createAt(wholeBounds.getEnd());
    }
    
    /**
     * Generates the associated element representation and associates the binding
     * with a particular container. The representation is inserted between other
     * bindings, "previous" and "next". Container bounds are passed to aid in case
     * of insertion at the container's boundary. emptyBefore and emptyAfter advises
     * whether the container wants the representation to separate itself from the
     * previous, or the next element.
     */
    public void create(ContainerImpl container, 
        ElementBinding previous, ElementBinding next,
        PositionBounds containerBounds, boolean emptyBefore, boolean emptyAfter)
        throws SourceException {
            
        PositionRef beginPos, top;
        if (previous == null) {
            beginPos = containerBounds.getBegin();
        } else {
            beginPos = previous.prepareInsert(this, true);
        }
        
        if (next == null) {
            top = containerBounds.getEnd();
        } else {
            top = next.prepareInsert(this, false);
        }
        PositionBounds gap = new PositionBounds(
            beginPos, top);
        PositionRef pos = source.findFreePosition(gap);
        if (pos == null)
            throw new SourceException("No room for element"); // NOI18N
        createAt(pos, emptyBefore, emptyAfter);
        containerRef = container;
    }
    
    protected void createAt(PositionRef r, boolean emptyLineBefore, boolean emptyLineAfter)
    throws SourceException {
	createAt(r, true, true, emptyLineBefore, emptyLineAfter);
    }

    protected void createAt(PositionRef r, boolean newLine, boolean newLineAfter, boolean emptyLineBefore, boolean emptyLineAfter)
    throws SourceException {
	PositionBounds newBounds = 
	    (newLine)
	    ? CodeGenerator.createNewLineBounds(r, CodeGenerator.BOUNDS_ALL, emptyLineBefore, emptyLineAfter, newLineAfter)
	    : new PositionBounds(r, r);
        create(newBounds);
    }
    
    private void createAt(PositionRef r) throws SourceException {
        PositionBounds newBounds = CodeGenerator.createNewLineBounds(r,
            CodeGenerator.BOUNDS_ALL);
        create(newBounds);
    }
    
    public void applyPropertyChange(Object bean, String property, Object value)
        throws SourceException {
        java.lang.reflect.Method setter;
        
        if (setterCache == null) {
            setterCache = new HashMap(29);
            setter = null;
        } else {
            setter = (java.lang.reflect.Method)setterCache.get(property);
        }
        if (setter == null) {
            try {
                BeanInfo binfo = Introspector.getBeanInfo(bean.getClass());
                PropertyDescriptor[] desc = binfo.getPropertyDescriptors();
                for (int i = 0; i < desc.length; i++) {
                    if (desc[i].getName().equals(property)) {
                        setter = desc[i].getWriteMethod();
                    }
                }
            } catch (IntrospectionException ex) {
            }
            if (setter == null) {
                throw new SourceException("Cannot find setter for " + property); // NOI18N
            }
            setterCache.put(property, setter);
        }
        try {
            setter.invoke(bean, new Object[] { value });
            return;
        } catch (IllegalAccessException ex) {
        } catch (java.lang.reflect.InvocationTargetException ex) {
        }
    }
    
    public void changeElementProperty(final PropertyChangeEvent evt) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        source.runAtomic(el, new ExceptionRunnable() {
            public void run() throws Exception {
                doChangeProperty(evt.getPropertyName(), 
                    evt.getOldValue(), evt.getNewValue());
            }
        });
    }
    
    static final int CLASS_IGNORE = 0;
    static final int CLASS_HEADER = 1;
    static final int CLASS_BODY = 2;
    
    protected void doChangeProperty(String property, Object old, Object now)
    throws Exception {
        int propClass = classifyProperty(property);
        if (propClass == CLASS_IGNORE)
            return;
        Element clonedBean = cloneElement();
        applyPropertyChange(clonedBean, property, now);
        switch (propClass) {
            case CLASS_HEADER:
                regenerateHeader(clonedBean);
                break;
            case CLASS_BODY:
                regenerateBody(clonedBean);
                break;
        }
    }
    
    protected int classifyProperty(String propName) {
        return CLASS_IGNORE;
    }

    public ElementBinding findBindingAt(int off) {
        if (wholeBounds.getBegin().getOffset() <= off && 
            wholeBounds.getEnd().getOffset() > off)
            return this;
        else
            return null;
    }
    
    /**
     * Removes the element from the SourceText.
     * @return UndoableEdit operation that will result in re-inserting of the element in
     * the storage
     */
    protected void remove(boolean collapseBefore, boolean collapseAfter) throws SourceException, IllegalStateException {
        // PENDING: record previous bounds for the case of a rollback.
        try {
            CodeGenerator.clearBounds(wholeBounds, collapseBefore);
        } catch (Exception ex) {
            SourceText.rethrowException(el,ex);
        }
    }
    
    protected void moveTo(ElementBinding before, ElementBinding after) throws SourceException {
        // PENDING: Undo the bounds change!
        PositionBounds oldWholeBounds = wholeBounds;
        containerRef.insertChild(this, before, after);
        try {
            CodeGenerator.clearBounds(oldWholeBounds, false);
        } catch (BadLocationException ex) {
            SourceText.rethrowException(getElement(),ex);
        }
    }
    
    /* ================ CODE GENERATION SUPPORT ======================== */
    
    /**
     * The method retrieves a document for the element. If the document is not already
     * opened, the method opens the document and returns the instance. The method may
     * throw SourceException.IO, that contains the reason of failure reported by 
     * FileSystem/EditSupport layer.
     */
    protected StyledDocument findDocument() throws SourceException {
        return source.getDocument();
    }

    /**
     * Replaces text for element's header with new contents taken from the parameter.
     * The implementation changes the document inside atomic lock.
     */
    protected void regenerateHeader(Element el) throws SourceException {
        Document doc = findDocument();

        source.runAtomic(this.el, new PartialGenerator(doc, el, headerBounds, ElementPrinter.HEADER_BEGIN, 
            ElementPrinter.HEADER_END));
    }
    
    protected void regenerateWhole(Element el, boolean updatePositions) throws SourceException {
        Document doc = findDocument();
        source.runAtomic(this.el, new PartialGenerator(doc, el, updatePositions));
    }
    
    protected void regenerateBody(Element el) throws SourceException {
        Document doc = findDocument();
        source.runAtomic(this.el, new PartialGenerator(doc, el, bodyBounds,
            ElementPrinter.BODY_BEGIN, ElementPrinter.BODY_END));
    }
    
    public boolean canInsertAfter() {
        return true;
    }
    
    protected class RemovingRunnable implements ExceptionRunnable {
        public void run() throws Exception {
            CodeGenerator.clearBounds(wholeBounds, true);
        }
    }
    
    public void updateBounds(int kind, PositionBounds bounds) {
        switch (kind) {
            case BOUNDS_ALL:
		if (DEBUG) {
		    edu.kestrel.netbeans.Util.trace("*** ElementBinding.updateBounds: new wholeBounds="+bounds);
		}
                wholeBounds = bounds;
                break;
            case BOUNDS_BODY:
                bodyBounds = bounds;
                break;
            case BOUNDS_HEADER:
                headerBounds = bounds;
        }
    }
    
    /** 
     * Helper class used for generating headers in {@link #regenerateHeader method}
     */
    protected class PartialGenerator implements ExceptionRunnable {
        PositionBounds posBounds;
        int begin;
        int end;
        Document doc;
        Element el;
        boolean update;
        
        PartialGenerator(Document doc, Element el, boolean updateBounds) {
	    if (DEBUG) {
		System.err.println("*** ElementBinding$PartialGenerator(): element="+((MemberElement)el).getName()+" updateBounds="+updateBounds);
	    }
            update = updateBounds;
            this.el = el;
            this.doc = doc;
            begin = ElementPrinter.ELEMENT_BEGIN;
            end = ElementPrinter.ELEMENT_END;
            posBounds = wholeBounds;
        }
        
        PartialGenerator(Document doc, Element el, PositionBounds pos, int begin, int end) {
	    if (DEBUG) {
		System.err.println("*** ElementBinding$PartialGenerator(): element="+((MemberElement)el).getName()+" pos="+pos+" begin="+begin+" end="+end);
	    }
            this.posBounds = pos;
            this.begin = begin;
            this.end = end;
            this.doc = doc;
            this.el = el;
        }
        
        public void run() throws Exception {
            PositionRef headerBegin = posBounds.getBegin();
            StyledDocument doc = findDocument();
            StringWriter wr = new StringWriter();
            Writer indentWriter = CodeGenerator.findIndentWriter(doc, headerBegin.getOffset(), wr);
            ElementPrinterImpl printer = update ?
                new WholeElementPrinter(indentWriter, wr) :
                new ElementPrinterImpl(indentWriter, el, begin, end);
            try {
                el.print(printer);
            }
            catch (ElementPrinterInterruptException e) {
            }
            try {
                indentWriter.close();
            } catch (java.io.IOException ex) {
                throw new InternalError(ex.getMessage());
            }
            if (DEBUG) {
		System.err.println("*** ElementBinding$PartialGenerator.run(): CodeGenerator.fillTextBounds - posBounds="+posBounds+" text="+wr.toString());
	    }
            CodeGenerator.fillTextBounds(posBounds, wr.toString());
            if (update) {
                ((WholeElementPrinter)printer).finish();
            }
        }
    }
    
    PositionRef getEndPosition() {
        StyledDocument doc = source.getEditorSupport().getDocument();
        return source.createPos(doc.getLength(), Position.Bias.Backward);
    }
    
    PositionBounds findContainerBounds(TextBinding.Container cont) {
        throw new UnsupportedOperationException(this.toString());
    }

    class WholeElementPrinter extends ElementPrinterImpl {
        StringWriter stringWriter;
        CloneableEditorSupport editor;

        int[] positions;

        WholeElementPrinter(Writer writer, StringWriter stringWriter
                            /*
                            Element element, ElementPositions poss,
                            CloneableEditorSupport editor */) {
            super(writer);
            this.stringWriter = stringWriter;
            /*
            this.element = element;
            this.poss = poss;
            this.editor = editor;
             */
            this.editor = source.getEditorSupport();
            this.positions = new int[12];
            java.util.Arrays.fill(positions, -1);
        }

        public void markNotify(Element el, int what) {
            if (lastText!=null && lastText.endsWith(" ")) {
                String writerText=stringWriter.getBuffer().toString();
                int len=lastText.length();
                
                if (len>0 && !writerText.endsWith(" ")) {
                    char ch=0;  // initialized only to keep compiler happy
                    int i;
                    
                    for (i=len-1;i>=0;i--) {
                        ch=lastText.charAt(i);
                        if (ch!=' ')
                            break;
                    }
                    if (ch!='\n') {
                        i++;
                        stringWriter.write(lastText,i,len-i);
                    }
                }
            }
            positions[what] = stringWriter.getBuffer().length();
        }

        void finish() {
            int offset = wholeBounds.getBegin().getOffset();
        
            if (positions[ELEMENT_BEGIN] != -1 && positions[ELEMENT_END] != -1) {
                wholeBounds = createStableBounds(positions[ELEMENT_BEGIN] + offset,
                                             positions[ELEMENT_END] + offset);
		if (DEBUG) {
		    System.err.println("ElementBinding$WholeElementPrinter.finish(): new wholeBounds="+wholeBounds);
		}
            }
            if (positions[HEADER_BEGIN] != -1 && positions[HEADER_END] != -1) {
                headerBounds = createStableBounds(positions[HEADER_BEGIN] + offset,
                                                positions[HEADER_END] + offset);
		if (DEBUG) {
		    System.err.println("ElementBinding$WholeElementPrinter.finish(): new headerBounds="+headerBounds);
		}
            } 
            if (positions[BODY_BEGIN] != -1 && positions[BODY_END] != -1) {
                bodyBounds = createBounds(positions[BODY_BEGIN] + offset,
                                              positions[BODY_END] + offset);
		if (DEBUG) {
		    System.err.println("ElementBinding$WholeElementPrinter.finish(): new bodyBounds="+bodyBounds);
		}
            }
        }
	
	private PositionBounds createStableBounds(int begin, int end) {
            if ((begin == -1) || (end == -1))
                return null;

            PositionRef posBegin = editor.createPositionRef(begin, Position.Bias.Backward);
            PositionRef posEnd = editor.createPositionRef(end, Position.Bias.Forward);
            return new PositionBounds(posBegin, posEnd);
	}

        private PositionBounds createBounds(int begin, int end) {
            if ((begin == -1) || (end == -1))
                return null;

            PositionRef posBegin = editor.createPositionRef(begin, Position.Bias.Backward);
            PositionRef posEnd = editor.createPositionRef(end, Position.Bias.Forward);
            return new PositionBounds(posBegin, posEnd);
        }

    }
    
    public String toString() {
        return "Binding for " + getElement(); // NOI18N
    }

    static String convertNewlines(String input) {
        if (lineSeparator == null)
            return input;

        int firstIndex;
        firstIndex = input.indexOf(lineSeparator);
        if (firstIndex == -1)
            return input;
        // replace from the beginning to the firstIndex
        StringBuffer result = new StringBuffer();
        char[] contents = input.toCharArray();
        if (firstIndex > 0)
            result.append(contents, 0, firstIndex);
        result.append(LINEFEED);

        firstIndex += lineSeparatorLength;
        int lastPos = firstIndex;
        while (firstIndex < contents.length) {
            firstIndex = input.indexOf(lineSeparator, firstIndex);
            if (firstIndex == -1) {
                // put there the rest of the string.
                result.append(contents, lastPos, contents.length - lastPos);
                return result.toString();
            }
            // put the portion not containing the separator.
            result.append(contents, lastPos, firstIndex - lastPos);
            result.append(LINEFEED);
            firstIndex += lineSeparatorLength;
            lastPos = firstIndex;
        }
        // execution comes here only if the line.sep is the last thing
        // in the string.
        result.append(contents, lastPos, firstIndex - lastPos);
        return result.toString();
    }

    // ================= methods ==============================

    static class ElementPrinterImpl implements ElementPrinter {
        PrintWriter writer;
        String lastText=null;

        Element printedElement;
        int beginMark;
        int endMark;
        int status;

        ElementPrinterImpl(Writer writer) {
            this(writer, null, 0, 0);
            status = 1;
        }

        ElementPrinterImpl(Writer writer, Element printedElement, int beginMark, int endMark) {
            this.writer = new PrintWriter(writer);
            this.printedElement = printedElement;
            this.beginMark = beginMark;
            this.endMark = endMark;
            status = 0;
        }

        public boolean isBegin(Element element, int what) {
            return (printedElement == null) ||
                   ((element == printedElement) && (what == beginMark));
        }

        public boolean isEnd(Element element, int what) {
            return (printedElement == element) && (what == endMark);
        }

        public void markNotify(Element element, int what) {
        }

        public String getString() {
            return writer.toString();
        }

        /** Prints the given text.
        * @param text The text to write
        */
        public void print(String text) throws ElementPrinterInterruptException {
            switch (status) {
            case 0:
                lastText=null;
                return;
            case 1:
                text = convertNewlines(text);
                lastText=text;
                writer.print(text);
                break;
            case 2:
                throw new ElementPrinterInterruptException();
            }
        }
        
        /** Prints the line. New-line character '\n' should be added.
        * @param text The line to write
        */
        public void println(String text) throws ElementPrinterInterruptException {
            print(text);
            print("\n"); // NOI18N
        }

        /** Add the mark to the list, if the printer is currently caching
        * (status == 1) or this mark is the begin.
        * @param element The element to mark
        * @param what The kind of event
        */
        private void mark(Element element, int what) throws ElementPrinterInterruptException {
            switch (status) {
            case 0:
                if (isBegin(element, what)) {
                    markNotify(element, what);
                    status = 1;
                }
                break;
            case 1:
                writer.flush();
                markNotify(element, what);
                if (isEnd(element, what)) {
                    status = 2;
                    writer.close();
                    throw new ElementPrinterInterruptException();
                }
                break;
            case 2:
                throw new ElementPrinterInterruptException();
            }
        }

        public void markSpec(SpecElement element, int what) throws ElementPrinterInterruptException {
            mark(element, what);
        }

        public void markSort(SortElement element, int what) throws ElementPrinterInterruptException {
            mark(element, what);
        }

        public void markOp(OpElement element, int what) throws ElementPrinterInterruptException {
            mark(element, what);
        }
    }
}
