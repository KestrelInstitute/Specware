/*
 * MetaSlangSettings.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.settings;

import java.io.*;
import java.util.ResourceBundle;
import java.util.Properties;
import java.util.List;
import java.util.Iterator;
import java.util.Collection;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.openide.cookies.InstanceCookie;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.Repository;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataObjectNotFoundException;
import org.openide.options.ContextSystemOption;
import org.openide.util.HelpCtx;
import org.openide.util.Lookup;
import org.openide.util.NbBundle;
import org.openide.util.io.ReaderInputStream;
import org.openide.ServiceType;
import org.openide.ServiceType.Handle;
import org.openide.TopManager;
import org.openide.execution.NbClassPath;
import org.openide.debugger.DebuggerType;
import org.openide.nodes.Node;
import org.openide.util.SharedClassObject;
import org.openide.util.WeakListener;
import org.netbeans.modules.java.ClassPathConfigurator;

import edu.kestrel.netbeans.MetaSlangDataLoader;

/** Settings for meta-slang data loader and meta-slang source parser
 *
 */
public class MetaSlangSettings extends ContextSystemOption {
    private static final int currentVersion = 1;
    
    /** serial uid */
    static final long serialVersionUID = -8522143676848697297L;
    
    public static final String PROP_PARSER_BOOTPATH = "parserBootPath"; // NOI18N
    public static final String PROP_PARSER_CLASSPATH = "parserClassPath"; // NOI18N
    public static final String PROP_PARSER_SOURCEPATH = "parserSourcePath"; // NOI18N
    
    public static final String PROP_REPLACEABLE_STRINGS_TABLE = "replaceableStringsTable"; // NOI18N

    public static final String PROP_AUTO_PARSING_DELAY = "autoParsingDelay"; // NOI18N
    public static final String PROP_PARSING_ERRORS = "parsingErrors"; // NOI18N
    static final String PROP_SOURCE_14ENABLED = "source14Enabled"; // NOI18N
    
    public static final String PROP_PRESCAN_SOURCES = "prescanSources"; // NOI18N
    
    public static final int DEFAULT_AUTO_PARSING_DELAY = 2000;
    public static final int DEFAULT_PARSING_ERRORS = 10;
    
    static ResourceBundle bundle;
    
    /** class path settings or null */
    private NbClassPath parserClassPath;
    
    /** boot class path or null */
    private NbClassPath parserBootPath;
    
    /**
     * Keeps parser's filesystems in memory unless un-configured
     */
    private transient Collection keepClassPath, keepBootPath;
    
    /**
     * Bootclasspath obtained from the runtime environment.
     */
    private transient NbClassPath   runtimeBootClassPath;
    
    /**
     * Current version of the settings object. If < currentVersion,
     * a settings upgrade is made.
     */
    private int version;
    
    /**
     * Whether the "-source" argument should be passed to the parser.
     */
    private boolean source14Enabled = true;
    
    private static MetaSlangSettings metaSlangSettings;
    
    /** If true then external execution is used */
    public String displayName() {
        return getString("CTL_MetaSlang_option");
    }
    
    public MetaSlangSettings() {
    }
    
    public boolean isGlobal() {
        return false;
    }
    
    /** Sets the replaceable strings table - used during instantiating
    * from template.
    */
    public void setReplaceableStringsTable(String table) {
        String t = getReplaceableStringsTable();
        if (t.equals(table))
            return;
        putProperty(PROP_REPLACEABLE_STRINGS_TABLE, table, true);
    }

    /** Gets the replacable strings table - used during instantiating
    * from template.
    */
    public String getReplaceableStringsTable() {
        String table = (String)getProperty(PROP_REPLACEABLE_STRINGS_TABLE);
        if (table == null) {
            return "USER="+System.getProperty("user.name")+"\n"; // NOI18N
        } else {
            return table;
        }
    }

    /** Gets the replaceable table as the Properties class.
    * @return the properties
    */
    public Properties getReplaceableStringsProps() {
        Properties props = new Properties();
        String propString = getReplaceableStringsTable();
        int i,len = propString.length();
        StringBuffer unicodeString = new StringBuffer(len);
        
        for (i=0;i<len;i++) {
            char aChar = propString.charAt(i);
            
            if (aChar > 0x00ff) {
                String hex = Integer.toHexString(aChar);
                
                unicodeString.append("\\u"); // NOI18N
                if (aChar < 0x1000)
                    unicodeString.append("0"); // NOI18N
                unicodeString.append(hex);
            } else {
                unicodeString.append(aChar);
            }
        }
        try {
            props.load(new ByteArrayInputStream(unicodeString.toString().getBytes()));
        }
        catch (IOException e) {
        }
        return props;
    }

    /** Gets the delay time for the start of the parsing.
     * @return The time in milis
     */
    public int getAutoParsingDelay() {
        Integer delay = (Integer)getProperty(PROP_AUTO_PARSING_DELAY);
        if (delay == null)
            return DEFAULT_AUTO_PARSING_DELAY;
        return delay.intValue();
    }
    
    /** Sets the number of errors returned by the parsing and displayed as
     * annotations in source text
     * @param number of errors, 0 means disable
     */
    public void setParsingErrors(int errors) {
        if (errors < 0)
            throw new IllegalArgumentException();
        putProperty(PROP_PARSING_ERRORS, new Integer(errors),true); // fire property change
    }
    
    /** Gets the number of errors returned by the parsing and displayed as
     * annotations in source text
     * @return number of errors
     */
    public int getParsingErrors() {
        Integer errors = (Integer)getProperty(PROP_PARSING_ERRORS);
        if (errors == null)
            return DEFAULT_PARSING_ERRORS;
        return errors.intValue();
    }
    
    /** Sets the delay time for the start of the parsing.
     * @param delay The time in milis
     */
    public void setAutoParsingDelay(int delay) {
        if (delay < 0)
            throw new IllegalArgumentException();
        putProperty(PROP_AUTO_PARSING_DELAY, new Integer(delay));
    }
    
    /**
     * Returns true, if the sources in a directory should be "pre-scanned" when the
     * folder is opened. For details, see {@link #setPrescanSources}
     * @return true, if sources are parsed after their nodes are shown.
     */
    public boolean getPrescanSources() {
        Boolean b = (Boolean)getProperty(PROP_PRESCAN_SOURCES);
        if (b == null)
            return false;  // true
        else
            return b.booleanValue();
    }
    
    /** Enables or disables "pre-scan" of source files. The prescan operation is
     * scheduled after the node comes out visible somewhere in order to determine file's
     * type, contents and state. The most common trigger operation is opening of a folder
     * in the Explorer. After the prescan completes, UI of MetaSlang source file nodes is
     * updated with icons that reflect the exact state of the file - clean, compiled, with errors,
     * executable, ...<BR>
     * Note that the operation may be seen as costly because it requires parsing all the source
     * files attached to the nodes and on some systems it may have adverse impact on IDE's
     * performance. Default = on.
     * @param enable true if pre-scan should be enabled, false if not.
     */
    public void setPrescanSources(boolean enable) {
        Boolean b = (Boolean)getProperty(PROP_PRESCAN_SOURCES);
        if ((b == null && enable) ||
        (b != null && b.booleanValue() == enable))
            return;
        putProperty(PROP_PRESCAN_SOURCES,
        enable ? Boolean.TRUE : Boolean.FALSE, true);
    }
    
    /** @return localized string */
    static String getString(String s) {
        if (bundle == null) {
            bundle = NbBundle.getBundle(MetaSlangSettings.class);
        }
        return bundle.getString(s);
    }
    
    /** Getter for parser class path.
     */
    public NbClassPath getParserClassPath() {
        NbClassPath cp = parserClassPath;
        return cp != null || isWriteExternal() ? cp : new NbClassPath(""); // NOI18N
    }
    
    public Collection getParserClassPathFS() {
        return keepClassPath = ClassPathConfigurator.getInstance().getFileSystems(
        getParserClassPath());
    }
    
    /**
     * Creates and returns bootclasspath from the runtime environment.
     */
    private synchronized NbClassPath getRuntimeBootPath() {
        if (runtimeBootClassPath != null)
            return runtimeBootClassPath;
        return runtimeBootClassPath = new NbClassPath("");
    }
    
    /** Setter for parser class path.
     */
    public void setParserClassPath(NbClassPath path) {
        NbClassPath old = parserClassPath;
        parserClassPath = path;
        firePropertyChange(PROP_PARSER_CLASSPATH, old, path); // NOI18N
    }
    
    /** Getter for parser boot class path.
     */
    public NbClassPath getParserBootPath() {
        return (parserBootPath == null && !isWriteExternal()
        ? getRuntimeBootPath() : parserBootPath);
    }
    
    /**
     * Returns a colleciton of FileSystems that should be used by the parser
     * as runtime classes. If nothing is defined by the user, it will default
     * to IDE's own runtime classes.
     */
    public Collection getParserBootPathFS() {
        NbClassPath pbcp = getParserBootPath();
        if (pbcp == null ||
        "".equals(pbcp.getClassPath()))
            pbcp = NbClassPath.createBootClassPath();
        return keepBootPath = ClassPathConfigurator.getInstance().getFileSystems(
        pbcp);
    }
    
    /** Setter for parser boot class path.
     */
    public void setParserBootPath(NbClassPath path) {
        if (path == getParserBootPath() ||
        (path != null && path.equals(getParserBootPath())))
            // no change.
            return;
        NbClassPath old = parserBootPath;
        parserBootPath = path;
        firePropertyChange(PROP_PARSER_BOOTPATH, old, path); // NOI18N
    }
    
    public static final MetaSlangSettings getDefault() {
        if (metaSlangSettings==null){
            //  Util.log("MetaSlangSetting.getDefault metaSlangSettings is null");
            metaSlangSettings=(MetaSlangSettings) MetaSlangSettings.findObject(MetaSlangSettings.class, true);
        }
        //Util.log("MetaSlangSetting.getDefault metaSlangSettings is " +metaSlangSettings);
        return metaSlangSettings;
    }
    
}
