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
       
    /** Creates a new instance of ExternalLispProcess */
    public ExternalLispProcess() {

        String lispImagePath = System.getProperty("Env-SPECWARE4");
    
        if (lispImagePath == null)
            LispProcessManager.writeToSpecwareStatus("ERROR: The SPECWARE4 environment variable is not set.");
        
        String lispImageFile = (lispImagePath+ (Utilities.isWindows() ? "\\Applications\\Specware\\bin\\windows\\" : "/Applications/Specware/bin/linux/") +"Specware4.dxl"); 
        String initFile = (lispImagePath + (Utilities.isWindows() ? "\\Gui\\src\\Lisp\\" : "/Gui/src/Lisp/") + "specware-init.lisp");
        String lispExecutable = (Utilities.isWindows() ? "\"c:\\Progra~1\\acl62\\alisp.exe\"" : "/usr/local/acl/acl62/alisp");
        NbProcessDescriptor DEFAULT = new NbProcessDescriptor(lispExecutable, (("-I "+lispImageFile+" -L "+initFile)));
        setExternalExecutor(DEFAULT);
    }
    
    public Process createProcess() throws IOException {
        NbProcessDescriptor ee = getExternalExecutor();
        
        return ee.exec();
    }
    
}
