/*
 * MetaSlangParserGlue.java 
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans;

import java.beans.*;
import java.io.*;
import java.util.*;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.lang.reflect.Modifier;

import javax.swing.event.ChangeListener;
import javax.swing.event.ChangeEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Segment;
import javax.swing.text.StyledDocument;

import org.openide.filesystems.FileObject;
import org.openide.util.Task;
import org.openide.cookies.*;
import org.openide.loaders.MultiDataObject;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.nodes.CookieSet;
import org.openide.text.*;
import org.openide.util.WeakSet;
import org.openide.util.RequestProcessor;

import edu.kestrel.netbeans.parser.LangEnvImpl;
import edu.kestrel.netbeans.parser.Parsing;
import edu.kestrel.netbeans.parser.MetaSlangParser;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

import edu.kestrel.netbeans.cookies.SourceCookie;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.editor.MetaSlangEditorSupport;
import edu.kestrel.netbeans.parser.ParsingSupport;
import edu.kestrel.netbeans.codegen.SourceText;


/**
 * A glue between a MetaSlangDataObject and MetaSlangParser
 * 
 */
class MetaSlangParserGlue implements MetaSlangParser.Env, DocumentBinding.Env, 
    LangModel.Env, SourceCookie.Editor
{

    private MultiDataObject.Entry   sourceEntry;
    private MetaSlangDataObject     metaSlangDataObj;
    private DocumentBinding         docBinding;
    private LangEnvImpl             envSupport;
    private ParsingSupport          parser;
    private Map                     cookieMap;
    private SiblingListener         l;
    private boolean                 documentLoaded;
    private CloneableEditorSupport  cloneableEditSupp;
    private int                     suspended;
    private PropertyChangeListener  weakPropListener;
    private boolean 		    disableCookieEvents;
    private boolean                 editorBound;
    
    /**
     * Constructs an implementation of a parsing environment and binds it to the
     * data object.
     */
    public MetaSlangParserGlue(MultiDataObject.Entry en) {
        this.sourceEntry = en;
        this.metaSlangDataObj = (MetaSlangDataObject)en.getDataObject();
        this.docBinding = new SourceText(this);
        this.envSupport = new LangEnvImpl(docBinding);
        this.cookieMap = new WeakHashMap(57);
        
        DefaultLangModel model = new DefaultLangModel(this);
        envSupport.setModel(model);
        
        ParsingSupport supp = new ParsingSupport(this, docBinding, model, model);
        supp.setParserEngine(((MetaSlangDataLoader)metaSlangDataObj.getLoader()).getParserEngine());
        parser = supp;
        l = new SiblingListener();
        parser.addChangeListener(l);
        parser.getSource().addPropertyChangeListener(l);
        metaSlangDataObj.addPropertyChangeListener(l);
        // 
        if (parser.getStatus() != SourceElement.STATUS_NOT)
            l.rescanSource(parser.getSource());
    }
    
    /**
     * The implementation provides custom OpenCookies that open the MetaSlangEditorSupport
     * associated with the MetaSlangDataObject at the where the Element starts.
     */
    public Node.Cookie findCookie(Element el, Class clazz) {
        Node.Cookie lookup = null;

        if (el == parser.getSource())
            // handle it specially for SourceElement - it has much more common with DataObject than
            // the rest of Elements.
            return findCookie((SourceElement)el, clazz);
        if (clazz == EditCookie.class) {
            lookup = lookupCookie(el, clazz);
            if (lookup != null)
                return lookup;
            lookup = createEditCookie(el);
        } else {
	    if (!clazz.isAssignableFrom(ElementCookie.class)) {
		return metaSlangDataObj.getCookie(clazz);
	    }
	}
        if (lookup != null)
            registerElementCookie(el, lookup);
        return lookup;
    }
    
    public void annotateThrowable(Throwable t, String locMessage, boolean user) {
        Util.annotateThrowable(t, locMessage, user);
    }
    
    public void annotateThrowable(Throwable wrapper, Throwable nested) {
        Util.annotateThrowable(wrapper, nested);
    }
    
    public Node.Cookie findCookie(SourceElement src, Class clazz) {
        return metaSlangDataObj.getCookie(clazz);
    }
    
    /**
     * Notifies the mediator that a CloneablEditorSupport has been created.
     */
    public void cloneableSupportCreated(CloneableEditorSupport supp) {
	bindEditorSupport(supp);
    }
    
    public MetaSlangParser getParser() {
        return parser;
    }
    
    /** 
     * The implementation first tries to get a document - if it is already opened.
     * If it is, then it returns a CharArrayReader constructed on the document's
     * contents. Document is read using {@link StyledDocument#render} to avoid
     * data corruption.<P>
     * If the document is not (yet) opened, a {@link MetaSlangEditorSupport#GuardedReader} is
     * constructed so the output will not contain any guarded block information.
     * <P>
     * The implementation does not handle IOException from lower layers in any
     * way and passes them to the caller.
     */
    public Reader getSourceText() throws IOException {
        CloneableEditorSupport editor = findEditorSupport();
	edu.kestrel.netbeans.Util.log("*** getSourceText(): editor="+editor);
        final StyledDocument doc = editor.getDocument();
        
        if (doc != null) {
            // can read from the document!
            final Segment s = new javax.swing.text.Segment();
            doc.render(new Runnable() {
		    public void run() {
			try {
			    doc.getText(0, doc.getLength(), s);
			} catch (BadLocationException ex) {
			    // should never happen
			}
		    }
		});
            return new CharArrayReader(s.array, s.offset, s.count);
        } else {
            return new InputStreamReader(getSourceFile().getInputStream());
        }
    }
    
    public FileObject getSourceFile() {
	return sourceEntry.getFile();
    }

    /**
     * Creates an EditCookie for the specified element. The cookies created are
     * kept in caching WeakHashMap keyed by the element instances for reuse.
     */
    protected EditCookie createEditCookie(Element el) {
        ElementImpl impl = (ElementImpl)el.getCookie(ElementImpl.class);
        EditCookie ck = new EditCookieImpl((TextBinding)impl.getBinding());
        return ck;
    }
    
    private Node.Cookie lookupCookie(Element el, Class clazz) {
        synchronized (cookieMap) {
            Object o = cookieMap.get(el);
            if (o == null)
                return null;
            
            if (o instanceof CookieSet) 
                return ((CookieSet)o).getCookie(clazz);
            
            if (o.getClass().isAssignableFrom(clazz))
                return (Node.Cookie)o;
            return null;
        }
    }
    
    private void registerElementCookie(Element el, Node.Cookie cookie) {
        synchronized (cookieMap) {
            Object o = cookieMap.get(el);
            if (o == null) {
                cookieMap.put(el, cookie);
                return;
            } else if (o instanceof CookieSet) {
                ((CookieSet)o).add(cookie);
            } else {
                Node.Cookie old = (Node.Cookie)o;
                CookieSet set = new CookieSet();
                set.add(old);
                set.add(cookie);
                cookieMap.put(el, set);
            }
        }
    }
    
    private TextBinding getBinding(Element el) {
        ElementImpl impl = (ElementImpl)el.getCookie(ElementImpl.class);
        if (impl == null) {
            Element.Impl iimpl = (Element.Impl)el.getCookie(Element.Impl.class);
            throw new IllegalArgumentException("Incompatible implementation: " + // NOI18N
					       iimpl);
        }
        return (TextBinding)impl.getBinding();
    }


    // ============== Implementation of DocumentBinding.Env ==================
    
    public CloneableEditorSupport findEditorSupport() {
        if (this.cloneableEditSupp == null) {
            bindEditorSupport(metaSlangDataObj.findCloneableEditorSupport());
        }
        return cloneableEditSupp;
    }
    
    private synchronized void bindEditorSupport(CloneableEditorSupport supp) {
        if (!editorBound) {
            supp.addChangeListener(l);
            documentLoaded = supp.isDocumentLoaded();
            editorBound = true;
            cloneableEditSupp = supp;
            if (documentLoaded)
                l.documentStateChanged(new ChangeEvent(supp));
        }
    }

    public PositionRef findFreePosition(PositionBounds bounds) {
        return getMetaSlangEditor().findFreePosition(bounds);
    }
    
    private MetaSlangEditorSupport getMetaSlangEditor() {
        return (MetaSlangEditorSupport)metaSlangDataObj.getCookie(MetaSlangEditorSupport.class);
    }

    // ============== Implementation of LangModel.Env -- DELEGATING ==================
    /**
     * Returns the document binding as the binding factory.
     */
    public BindingFactory getBindingFactory() {
        return envSupport.getBindingFactory();
    }

    public WrapperFactory getWrapperFactory() {
        return envSupport.getWrapperFactory();
    }

    public void complete(Element scope, int informationKind) {
        envSupport.complete(scope, informationKind);
    }
    
    /**
     * Implementation of SourceCookie.
     */
    public SourceElement getSource() {
        return parser.getSource();
    }
    
    /**
     * Implementation of EditCookie available on individual elements.
     */
    private class EditCookieImpl implements EditCookie, Runnable {
        TextBinding binding;
        
        EditCookieImpl(TextBinding binding) {
            this.binding = binding;
        }
        
        public void edit() {
            // Fix #20551: if the thread is not the event one, replan
            // the edit action into the AWT thread.
            org.openide.util.Mutex.EVENT.postReadRequest(this);
        }
        
        public void run() {
            PositionBounds elBounds = binding.getElementRange(true);
            getMetaSlangEditor().openAt(elBounds.getBegin(), -1);
        }
    }
    
    /**
     * Backfires PROP_COOKIE property change event in the source hierarchy.
     */
    protected void refireCookieChange(PropertyChangeEvent evt) {
        // fire the event on SourceElement.
        parser.fireElementPropertyChange(getSource(), evt);

        SourceElement.Impl impl = parser.getSourceImpl();
        // do not fire on lesser elements - there aren't any.
        if (impl == null)
            return;
        SpecElement[] specs = impl.getSpecs();
        Collection allElements = new ArrayList(40);

        allElements.addAll(Arrays.asList(specs));
        for (int i = 0; i < specs.length; i++) {
            SpecElement spec = specs[i];
            allElements.addAll(Arrays.asList(spec.getSorts()));
            allElements.addAll(Arrays.asList(spec.getOps()));
        }
        // FIRE!
	try {
	    disableCookieEvents = true;
    	    for (Iterator it = allElements.iterator(); it.hasNext(); ) {
    		parser.fireElementPropertyChange((Element)it.next(), evt);
    	    }
	} finally {
	    disableCookieEvents = false;
	}
    }
    
    public StyledDocument getDocument() {
        return findEditorSupport().getDocument();
    }
    
    public Line.Set getLineSet() {
        return findEditorSupport().getLineSet();
    }
    
    public javax.swing.JEditorPane[] getOpenedPanes() {
        return findEditorSupport().getOpenedPanes();
    }
    
    public boolean isModified() {
        return findEditorSupport().isModified();
    }
    
    public void open() {
        findEditorSupport().open();
    }
    
    public StyledDocument openDocument() throws IOException {
        return findEditorSupport().openDocument();
    }
    
    public Task prepareDocument() {
        return findEditorSupport().prepareDocument();
    }
    
    public void saveDocument() throws IOException {
        findEditorSupport().saveDocument();
    }
    
    public boolean close() {
        return findEditorSupport().close();        
    }
    
    public void suspendDocumentChanges() {
        suspended++;
    }
    
    public void resumeDocumentChanges() {
        --suspended;
    }
    
    protected boolean isDocumentSuspended() {
        return suspended > 0;
    }
    
    private void dissolve() {
        suspendDocumentChanges();
        metaSlangDataObj.removePropertyChangeListener(l);
        // callback to MetaSlangDataObject (disable rest of the system).
        metaSlangDataObj.suspendSupports();

        synchronized (this) {
            if (cloneableEditSupp != null) {
                cloneableEditSupp.removeChangeListener(l);
                editorBound = false;
                StyledDocument d = cloneableEditSupp.getDocument();
                if (d != null)
                    d.removeDocumentListener(l);
            }
        }
        parser.invalidate();
    }
    
    private class SiblingListener implements PropertyChangeListener, ChangeListener,
        DocumentListener {
        
        private StyledDocument doc;
        private Set     knownSpecs;
        
        SiblingListener() {
            knownSpecs = new WeakSet();
        }
        
        public void propertyChange(PropertyChangeEvent p) {
            String evName = p.getPropertyName();
            Object source = p.getSource();
            
            if (source == metaSlangDataObj)
                dataObjectPropertyChange(evName, p);
            else if (source instanceof SpecElement) {
                specPropertyChange(evName, (SpecElement)source, p);
            } else if (source instanceof SourceElement) {
                sourcePropertyChange(evName, p);
            }
        }
        
        private void specPropertyChange(String name, SpecElement spec,
					       PropertyChangeEvent e) {
            if (ElementProperties.PROP_VALID.equals(name)) {
                spec.removePropertyChangeListener(this);
            } else if (ElementProperties.PROP_NAME.equals(name)) {
		rescanSource(spec.getSource());
            }
        }
        
        private void sourcePropertyChange(String name, PropertyChangeEvent e) {
            if (ElementProperties.PROP_SPECS.equals(name)) {
                rescanSource((SourceElement)e.getSource());
            } else if (ElementProperties.PROP_STATUS.equals(name)) {
                Integer i = (Integer)e.getOldValue();
                if (i == null || i.intValue() != SourceElement.STATUS_NOT)
                    return;
                if (e.getNewValue() != null &&
                    ((Integer)e.getNewValue()).intValue() != SourceElement.STATUS_OK)
                    return;
                rescanSource((SourceElement)e.getSource());
            }
        }
        
        private void rescanSource(SourceElement el) {
            SpecElement[] specs = el.getSpecs();
            String currentName = metaSlangDataObj.getName();
            
            // sweep through all top-level specs.
            for (int i = 0; i < specs.length; i++) {
                SpecElement spec = specs[i];
                String specName = spec.getName();
                if (knownSpecs.add(spec)) {
                    spec.addPropertyChangeListener(this);
                }
            }
        }

        private void dataObjectPropertyChange(String evName, PropertyChangeEvent p) {
            if (DataObject.PROP_COOKIE.equals(evName)) {
		if (disableCookieEvents)
		    return;
                refireCookieChange(p);
            } else if (DataObject.PROP_MODIFIED.equals(evName) && !metaSlangDataObj.isModified()) {
                // after save of the object, or reload.
                if (metaSlangDataObj.isValid()) {
		    //??? Accept errors when the parser can handle multiple errors?
                    //parser.parse(parser.PRIORITY_NORMAL, false, true);
		    parser.parse(parser.PRIORITY_NORMAL, false, false);
		}
            } else if (DataObject.PROP_VALID.equals(evName) 
		       && ((Boolean)p.getNewValue()).booleanValue() == false) {
                dissolve();
            } else if (DataObject.PROP_NAME.equals(evName)) {
                SourceElement.Impl impl = parser.getSourceImpl();
                SourceElement el = parser.getSource();
                
                if (impl != null) {
                    rescanSource(el);
                }
            }
        }
        
        public void stateChanged(ChangeEvent e) {
            if (e.getSource() == parser) {
                parserStateChanged(e);
            } else {
                documentStateChanged(e);
            }
        }
        
        private void parserStateChanged(ChangeEvent e) {
            final Object hook = ((MetaSlangParser)e.getSource()).getSourceImpl();
            
            RequestProcessor.getDefault().post(new Runnable() {
		    public void run() {
			Parsing.fireEvent(metaSlangDataObj, hook);
		    }
		});
        }
                
            
        private void documentStateChanged(ChangeEvent p) {
            CloneableEditorSupport supp = (CloneableEditorSupport)p.getSource();
            StyledDocument d = supp.getDocument();
            
            if (d != null) {
                if (doc == null) {
                    //parser.parse(parser.PRIORITY_NORMAL, false, true);
		    ((MetaSlangEditorSupport)supp).parseSource(parser.PRIORITY_NORMAL, false);
                    synchronized (this) {
                        doc = d;
                        d.addDocumentListener(this);
                        documentLoaded = true;
                    }
                }
            } else {
                removeDocListener();
                if (metaSlangDataObj.isValid()) {
		    //??? Accept errors when the parser can handle multiple errors?
                    //parser.parse(parser.PRIORITY_NORMAL, false, true);
		    parser.parse(parser.PRIORITY_NORMAL, false, false);
		}
            }
        }
        
        private synchronized void removeDocListener() {
            if (doc != null)
                doc.removeDocumentListener(this);
            doc = null;
            documentLoaded = false;
        }
        
        public void removeUpdate(javax.swing.event.DocumentEvent p1) {
            documentChanged();
        }
        
        public void changedUpdate(javax.swing.event.DocumentEvent p1) {
            // text is not modified, so we can ignore this event
        }
        
        public void insertUpdate(javax.swing.event.DocumentEvent p1) {
            documentChanged();
        }
        
        private void documentChanged() {
            if (!isDocumentSuspended()) {
                parser.sourceChanged(-1, -1);
                getMetaSlangEditor().restartTimer(false);
            }
        }   
    }
    
    private Map     swingElementMap;
    
    // SourceCookie.Editor - specifics
    public edu.kestrel.netbeans.model.Element findElement(int offset) {
        javax.swing.text.Element swingEl = sourceToText(getSource());
        
        while (swingEl != null) {
            if (swingEl.isLeaf()) {
                return ((TextElement)swingEl).getSourceElement();
            }
            int elIndex = swingEl.getElementIndex(offset);
            if (elIndex == -1)
                return ((TextElement)swingEl).getSourceElement();
            swingEl = swingEl.getElement(elIndex);
        }
        return null;
    }
    
    public edu.kestrel.netbeans.model.Element textToSource(javax.swing.text.Element element) throws NoSuchElementException {
        if (!(element instanceof TextElement)) {
            throw new NoSuchElementException();
        }
        TextElement el = (TextElement)element;
        return el.getSourceElement();
    }

    /**
     * Returns null, if the underlying document has not yet been loaded
     */
    public javax.swing.text.Element sourceToText(Element element) {
        javax.swing.text.Document d;
        try {
            d = findEditorSupport().openDocument();
        } catch (IOException ex) {
            IllegalStateException x = new IllegalStateException("Could not load document");
            org.openide.ErrorManager.getDefault().annotate(x, ex);
            throw x;
        }
        if (swingElementMap == null) {
            synchronized (this) {
                if (swingElementMap == null)
                    swingElementMap = new WeakHashMap(75);
            }
        }
	Reference r = (Reference)swingElementMap.get(element);
        javax.swing.text.Element e = r == null ? null : (javax.swing.text.Element)r.get();
        if (e == null) {
            e = new TextElement(getBinding(element));
            synchronized (this) {
                swingElementMap.put(element, new WeakReference(e));
            }
        }
        return e;
    }
    
    private static final Element[] NO_CHILDREN = new Element[0];
    
    private class TextElement implements TextBinding.ExElement {
        private TextBinding    myBinding;
        private Element        myElement;
        
        public TextElement(TextBinding binding) {
            myBinding = binding;
            myElement = binding.getElement();
        }
        
        private PositionBounds getBounds() {
            return myBinding.getElementRange(false);
        }
        
        public PositionRef getDeclarationStart() {
            return myBinding.getElementRange(true).getBegin();
        }
        
        private Element[] getChildrenElements() {
            ElementOrder ck = (ElementOrder)myElement.getCookie(ElementOrder.class);
            if (ck == null)
                return NO_CHILDREN;
            return ck.getElements();
        }
        
        public int getElementIndex(int offset) {
            Element[] children = getChildrenElements();
            javax.swing.text.Element childElement;
            
            for (int i = 0; i < children.length; i++) {
                childElement = sourceToText(children[i]);
                if (childElement.getStartOffset() <= offset &&
                    childElement.getEndOffset() > offset) {
                    return i;
                }
            }
            return -1;
        }
        
        public javax.swing.text.AttributeSet getAttributes() {
            return null;
        }
        
        public Element getSourceElement() {
            return myElement;
        }
        
        public javax.swing.text.Document getDocument() {
            return MetaSlangParserGlue.this.getDocument();
        }
        
        public javax.swing.text.Element getElement(int index) {
            Element[] els =  getChildrenElements();
            if (index > els.length)
                throw new IllegalArgumentException();
            return sourceToText(els[index]);
        }
        
        public int getElementCount() {
            return getChildrenElements().length;
        }
        
        public int getEndOffset() {
            return getBounds().getEnd().getOffset() - 1;
        }
        
        public String getName() {
            return myElement.getClass().getName();
        }
        
        public javax.swing.text.Element getParentElement() {
            Element parent = null;

            if (myElement instanceof MemberElement) {
                if (myElement instanceof SpecElement) {
                    parent = ((SpecElement)myElement).getSource();
                }
            } else
                return null;
            return sourceToText(parent);
        }
        
        public int getStartOffset() {
            return getBounds().getBegin().getOffset();
        }
        
        public boolean isLeaf() {
            return getChildrenElements().length == 0;
        }
    }
}
