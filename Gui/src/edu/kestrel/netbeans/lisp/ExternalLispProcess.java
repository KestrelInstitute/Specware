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
    private String lispImagePath;
    private NbProcessDescriptor DEFAULT;
    
    /** Creates a new instance of ExternalLispProcess */
    public ExternalLispProcess() {

        lispImagePath = (Utilities.isWindows() ? "c:\\Specware4\\" : "~/specware/Specware4/") ;
        
        String lispImageFile = (lispImagePath+ (Utilities.isWindows() ? "\\Applications\\Specware\\bin\\windows\\" : "Applications/Specware/bin/linux/") +"Specware.dxl"); 
        String initFile = (lispImagePath + (Utilities.isWindows() ? "\\Gui\\src\\edu\\kestrel\\netbeans\\lisp\\" : "Gui/src/edu/kestrel/netbeans/lisp/") + "init-java-connection.lisp");
        String lispExecutable = (Utilities.isWindows() ? "\"c:\\Progra~1\\acl62\\alisp.exe\"" : "/usr/local/acl/acl62/alisp");
        DEFAULT = new NbProcessDescriptor(lispExecutable, (("-I "+lispImageFile+" -L "+initFile)));
        setExternalExecutor(DEFAULT);
    }
    
    public Process createProcess() throws IOException {
        NbProcessDescriptor ee = getExternalExecutor();
        System.out.println("Args are "+ee.getArguments()+", and Info is "+ee.getInfo());
 
        File testFile = new File("usr/local/acl/acl62/alisp");
        System.out.println("alisp file is a file: "+testFile.isFile());
        
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
