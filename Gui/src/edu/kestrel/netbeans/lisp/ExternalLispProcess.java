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
       
    public ExternalLispProcess() {
    }
    
    /** Creates a new instance of ExternalLispProcess */
    public ExternalLispProcess(int lispPort) {

        String lispImagePath = System.getProperty("Env-SPECWARE4");
    
        if (lispImagePath == null) {
            lispImagePath = "/usr/home/kestrel/weilyn/specware/Specware4";
            Util.log("ERROR: The SPECWARE4 environment variable is not set; setting it to /usr/home/kestrel/weilyn/specware/Specware4");
        }
        
        String lispImageFile = (lispImagePath+ (Utilities.isWindows() ? "\\Applications\\Specware\\bin\\windows\\" : "/Applications/Specware/bin/linux/") +"Specware4.dxl"); 
        String initFile = (lispImagePath + (Utilities.isWindows() ? "\\Gui\\src\\Lisp\\" : "/Gui/src/Lisp/") + "specware-socket-init.lisp");
        String lispExecutable =  Utilities.isWindows() ? "\"c:\\Progra~1\\acl62\\alisp.exe\"" : (lispImagePath + "/Applications/Specware/bin/linux/SpecBeans-text");
        String exeArgs = Utilities.isWindows() ? ("-I "+lispImageFile+" -L "+initFile+" -- socket "+lispPort) : "" + lispPort;
        NbProcessDescriptor DEFAULT = new NbProcessDescriptor(lispExecutable, exeArgs);
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
            Util.log("e is "+e.getMessage());
        }
    }
    
}
