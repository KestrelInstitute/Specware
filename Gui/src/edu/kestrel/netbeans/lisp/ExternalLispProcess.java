/*
 * ExternalLispProcess.java
 *
 * Created on February 13, 2003, 6:25 PM
 */

package edu.kestrel.netbeans.lisp;

import edu.kestrel.netbeans.Util;

import java.io.File;
import java.io.IOException;
import java.lang.Process;

import org.openide.execution.ProcessExecutor;
import org.openide.execution.NbProcessDescriptor;
import org.openide.util.Utilities;

/**
 *
 * @author  weilyn
 */
public class ExternalLispProcess extends ProcessExecutor {
    
    // HACKY: change this to your root Specware directory for now...
    private static final String SPECWARE_ROOT = "C:\\Progra~1\\Specware4\\";
   
    private String lispImagePath;
    private NbProcessDescriptor DEFAULT;
    
    /** Creates a new instance of ExternalLispProcess */
    public ExternalLispProcess() {

        lispImagePath = SPECWARE_ROOT;
        
        String lispImageFile = (lispImagePath+ (Utilities.isWindows() ? "\\Applications\\Specware\\bin\\windows\\" : "Applications/Specware/bin/linux/") +"Specware4.dxl"); 
        String initFile = (lispImagePath + (Utilities.isWindows() ? "\\Gui\\src\\Lisp\\" : "Gui/src/Lisp/") + "specware-init.lisp");
        String lispExecutable = (Utilities.isWindows() ? "\"c:\\Progra~1\\acl62\\alisp.exe\"" : "/usr/local/acl/acl62/alisp");
        DEFAULT = new NbProcessDescriptor(lispExecutable, (("-I "+lispImageFile+" -L "+initFile)));
        setExternalExecutor(DEFAULT);
    }
    
    public Process createProcess() throws IOException {
        NbProcessDescriptor ee = getExternalExecutor();
        
        return ee.exec();
    }
    
    public static void main(String[] args) {
        ExternalLispProcess lisp = new ExternalLispProcess();
        try {
            Process p = lisp.createProcess();
        } catch (Exception e) {
            Util.trace("Exception starting Lisp");
        }
    }
    
}
