/*
 * MetaSlangDataLoader.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.7  2003/07/09 01:35:14  weilyn
 * specware.jar
 *
 * Revision 1.6  2003/06/21 00:57:10  weilyn
 * specware.jar
 *
 * Revision 1.5  2003/05/07 21:18:59  weilyn
 * UpdateSWPathAction
 *
 * Revision 1.4  2003/02/17 04:28:13  weilyn
 * Cleaned up active context menu actions.
 *
 * Revision 1.3  2003/02/14 21:36:24  weilyn
 * Added Start Lisp action.
 *
 * Revision 1.2  2003/02/14 16:56:42  weilyn
 * Added support for process unit action.
 *
 * Revision 1.1  2003/01/30 02:01:33  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.util.*;
import java.text.DateFormat;
import java.io.*;

import org.openide.actions.*;
import org.openide.filesystems.*;
import org.openide.loaders.*;
import org.openide.util.NbBundle;
import org.openide.util.MapFormat;
import org.openide.util.actions.SystemAction;

import edu.kestrel.netbeans.actions.*;
import edu.kestrel.netbeans.settings.MetaSlangSettings;

/** Recognizes single files in the Repository as being of a certain type.
 *
 * @author becker
 */
public class MetaSlangDataLoader extends UniFileLoader {
    public static final String META_SLANG_EXTENSION = "sw"; // NOI18N

    public static final String METASLANG_MIME = "text/x-meta-slang";
    
    public static final String PROP_PARSER_ENGINE = "parserEngine"; // NOI18N
    
    /** Class name of the default parsing engine. The engine is required to implemented
	edu.kestrel.netbeans.ParserEngine interface.
    */
    public static final String DEFAULT_PARSER_ENGINE = "edu.kestrel.netbeans.parser.MetaSlangParserEngine"; // NOI18N
    
    /** The list of parsing listener - the instance is in this class, because JavaDataLoader
     * class is prevented to be garbage collected.
     */
    public static ArrayList parsingListeners = new ArrayList();
    
    private transient ParserEngine	parserEngine;

   
    public MetaSlangDataLoader() {
        this("edu.kestrel.netbeans.MetaSlangDataObject");
    }
    
    // Can be useful for subclasses:
    protected MetaSlangDataLoader(String recognizedObjectClass) {
        super(recognizedObjectClass);
    }
    
    protected String defaultDisplayName() {
        return NbBundle.getMessage(MetaSlangDataLoader.class, "LBL_loaderName");
    }
    
    protected void initialize() {
        
        super.initialize();
        getExtensions().addMimeType(METASLANG_MIME); 
        
        ExtensionList extensions = new ExtensionList();
        extensions.addExtension(META_SLANG_EXTENSION);
        //extensions.addExtension("spec");
        setExtensions(extensions);
    }
    
    protected SystemAction[] defaultActions() {
        return new SystemAction[] {
            SystemAction.get(EditAction.class),
	    //SystemAction.get(OpenAction.class),
	    // SystemAction.get (CustomizeBeanAction.class),
	    //SystemAction.get(FileSystemAction.class),
	    null,
            SystemAction.get(ProcessUnitAction.class),
	    SystemAction.get(GenerateCodeAction.class),
            null,
            SystemAction.get(UpdateSWPathAction.class),
            null,
            //SystemAction.get(CompileAction.class),
            SystemAction.get(StartLispAction.class),
            SystemAction.get(KillLispAction.class),
            null,
	    /*
	    SystemAction.get(BuildAction.class),
	    null,
	    SystemAction.get(ExecuteAction.class),
	    */
	    SystemAction.get(CutAction.class),
	    SystemAction.get(CopyAction.class),
	    SystemAction.get(PasteAction.class),
	    null,
	    SystemAction.get(NewAction.class),
	    SystemAction.get(DeleteAction.class),
	    SystemAction.get(RenameAction.class),
	    //null,
	    //SystemAction.get(SaveAsTemplateAction.class),
	    //null,
	    //SystemAction.get(ToolsAction.class),
	    //SystemAction.get(PropertiesAction.class),
	    };
    }
    
    protected MultiDataObject createMultiObject(FileObject primaryFile)
	throws DataObjectExistsException, IOException {
        return new MetaSlangDataObject(primaryFile, this);
    }
    
    /** Create the primary file entry.
    * Subclasses may override {@link MetaSlangDataLoader.MetaSlangFileEntry} and return a new instance
    * of the overridden entry type.
    *
    * @param primaryFile primary file recognized by this loader
    * @return primary entry for that file
    */
    protected MultiDataObject.Entry createPrimaryEntry (MultiDataObject obj, FileObject primaryFile) {
        primaryFile.setImportant(true);
        return new MetaSlangFileEntry(obj, primaryFile);
    }

    /** Create the map of replaceable strings which is used
    * in the <code>MetaSlangFileEntry</code>. This method may be extended in subclasses
    * to provide the appropriate map for other loaders.
    * This implementation gets the map from the MetaSlang system option;
    * subclasses may add other key/value pairs which may be created without knowledge of the
    * file itself.
    *
    * @return the map of string which are replaced during instantiation
    *        from template
    */
    protected Map createStringsMap() {
        Map map = MetaSlangSettings.getDefault().getReplaceableStringsProps();
        map.put("DATE", DateFormat.getDateInstance(DateFormat.LONG).format(new Date())); // NOI18N
        map.put("TIME", DateFormat.getTimeInstance(DateFormat.SHORT).format(new Date())); // NOI18N
        return map;
    }
    
    /** Instructs MetaSlangDataLoader to use new parser engine instead of the old one.
	Old requests are still processed using the engine that was in effect during their creation.
	New requests will be processed and registered with the newly specified engine.
    */
    public void setParserEngine(ParserEngine eng) {
	if (eng == this.parserEngine) {
	    return;
	}
	ParserEngine old;
	synchronized (this) {
	    old = parserEngine;
	    parserEngine = eng;
	}
	old.unregisterAll();
	firePropertyChange(PROP_PARSER_ENGINE, old, eng);
    }
    
    /** Returns instance of parser engine to use.
	The method returns the object set by {@link #setParserEngine}. If no engine was set, it constructs
	instance of class designated by DEFAULT_PARSER_ENGINE and returns it.
	The method might return null -- in that case, parsing is impossible.
    */
    public ParserEngine getParserEngine() {
	synchronized (this) {
	    if (parserEngine != null) {
		return parserEngine;
	    }
	    boolean ok = false;
	    Exception ex = null;
	    
	    try {
		parserEngine = (ParserEngine)Class.forName(DEFAULT_PARSER_ENGINE).newInstance();
		ok = true;
	    } catch (IllegalAccessException e) {
		ex = e;
	    } catch (InstantiationException e) {
		ex = e;
	    } catch (ClassNotFoundException e) {
		ex = e;
	    }
	    if (!ok && ex != null && Boolean.getBoolean("netbeans.debug.exceptions")) { // NOI18N
		ex.printStackTrace();
	    }
	    return parserEngine;
	}
    }

    /** This entry defines the format for replacing text during
    * instantiation the data object.
    * Used to substitute keys in the source file.
    */
    public class MetaSlangFileEntry extends FileEntry.Format {
        static final long serialVersionUID =8244159045498569616L;
        
        /**
         * If true, the Entry refuses to open InputStream to prevent races
         * between readers and attempts to delete the file.
         */
        boolean disableInputStream;
        
        /**
         * Holds a collection of readers that read the file.
         */
        private Collection  activeReaders;

        /** Creates new entry. */
        public MetaSlangFileEntry(MultiDataObject obj, FileObject file) {
            super(obj, file);
        }

        /** Provide suitable format for substitution of lines.
        * Should not typically be overridden.
        * @param target the target folder of the installation
        * @param n the name the file will have
        * @param e the extension the file will have
        * @return format to use for formating lines
        */
        protected java.text.Format createFormat (FileObject target, String n, String e) {
            Map map = createStringsMap();

            modifyMap(map, target, n, e);

            MapFormat format = new MapFormat(map);
            format.setLeftBrace("__"); // NOI18N
            format.setRightBrace("__"); // NOI18N
            format.setExactMatch(false);
            return format;
        }

        /** Modify the replacement map.
        * May be extended in subclasses to provide additional key/value
        * pairs sensitive to the details of instantiation.
        * @param map the map to add to
        * @param target the destination folder for instantiation
        * @param n the new file name
        * @param e the new file extension
        */
        protected void modifyMap(Map map, FileObject target, String n, String e) {
            map.put("NAME", n); // NOI18N
        }
        
        public synchronized void addReader(InputStream r) {
            if (activeReaders == null) {
                activeReaders = new LinkedList();
            }
            activeReaders.add(r);
        }
        
        public synchronized void removeReader(InputStream r) {
            if (activeReaders == null)
                return;
            activeReaders.remove(r);
        }
        
        public void delete() throws IOException {
            synchronized (this) {
                if (activeReaders != null && activeReaders.size() > 0) {
                    for (Iterator it = activeReaders.iterator(); it.hasNext(); ) {
                        InputStream r = (InputStream)it.next();
                        r.close();
                    }
                }
                activeReaders = null;
                disableInputStream = true;
            }
            super.delete();
        }
        
        public InputStream getInputStream() throws FileNotFoundException {
            FileObject fob = getFile();
            synchronized (this) {
                if (disableInputStream) {
                    // refuse to create the stream.
                    throw new FileNotFoundException("File is being deleted."); // NOI18N
                }
                InputStream s = new NotifyInputStream(fob.getInputStream());
                addReader(s);
                return s;
            }
        }
        
        private class NotifyInputStream extends FilterInputStream {
            public NotifyInputStream(InputStream is) {
                super(is);
            }
            
            public void close() throws IOException {
                super.close();
                removeReader(this);
            }
        }
    }
        
    // Additional user-configurable properties:
    /*
      public String getMyProp () {
      return (String) getProperty ("myProp");
      }
      public void setMyProp (String nue) {
      putProperty ("myProp", nue, true);
      }
      public void writeExternal (ObjectOutput out) throws IOException {
      super.writeExternal (out);
      out.writeUTF (getMyProp ());
      }
      public void readExternal (ObjectInput in) throws IOException, ClassNotFoundException {
      super.readExternal (in);
      setMyProp (in.readUTF ());
      }
    */
    
}
