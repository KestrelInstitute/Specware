/*
 * LispProcessManager.java
 *
 * Created on February 13, 2003, 6:49 PM
 */

package edu.kestrel.netbeans.lisp;

import com.franz.jlinker.TranStruct;
import com.franz.jlinker.JavaLinkDist;
import com.franz.jlinker.LispConnector;

import edu.kestrel.netbeans.Util;

import java.util.HashSet;
import java.util.Set;

import org.openide.TopManager;
import org.openide.windows.InputOutput;
import org.openide.windows.OutputWriter;


/**
 *
 * @author  weilyn
 */
public class LispProcessManager {
    private static Set machines = new HashSet() ;
    private static String lispFile     = "";
    private static String lispHost     = "";
    private static int    lispPort     = 4321;
    private static int    pollInterval = 1000;
    private static int    pollCount    = 300;
    private static int    javaTimeout   = -1;
    private static String javaFile      = "";
    private static String javaHost      = "";
    private static int    javaPort      = 0;
    
    static private ExternalLispProcess lispServer = null;
    static private Process lispProcess = null;
    
    /** Creates a new instance of LispProcessManager */
    public LispProcessManager() {
    }

    public static boolean connectToLisp() {
        if (JavaLinkDist.query(true)) {
//            writeToOutput("LispProcessManager.connectToLisp --> Already Connected");
            return true;
        } else if (JavaLinkDist.connect(lispHost, lispPort, javaHost, javaPort, pollInterval, javaTimeout)) {
//            writeToOutput("LispProcessManager.connectToLisp --> New Connection Established");
            return true;
        } else {
//            writeToOutput("LispProcessManager.connectToLisp --> Failed to Connect to LISP " + JavaLinkDist.query());
//            writeToOutput("LispServer = "+ lispServer + "\n Lisp Process "+lispProcess + "\n");
            if (lispServer == null){
                lispServer = new ExternalLispProcess();
                try {
                    lispProcess = lispServer.createProcess();
//                    writeToOutput("****  lispServer.createProcess returned "+lispServer);
                    Thread.sleep(5000);
                } catch (Exception e) {
                    writeToOutput("LispProcessManager.connectToLisp.Exception "+e+" starting Lisp");
                }
//                writeToOutput("LispProcessManager.connectToLisp --> Calling Connect to Lisp again");
                if (lispProcess != null) {
                    return connectToLisp();
                }
            }
            return false;
        }
    }
    
    public static void destroyLispProcess() {
        if (lispProcess != null) {
//            writeToOutput("\n Destroying Lisp Process "+lispProcess);
            lispProcess.destroy();
            lispProcess = null;
            lispServer = null;
        }
    }
    
    public static void processUnit(String pathName, String fileName) {
//	Util.log("*** LispProcessManager.processUnit(): pathName="+pathName+", fileName="+fileName);
        if (connectToLisp()) {
            TranStruct [] ARGS = new TranStruct[2];
            TranStruct [] RES;
            ARGS[0] = JavaLinkDist.newDistOb(pathName);
            ARGS[1] = JavaLinkDist.newDistOb(fileName);
            com.franz.jlinker.LispConnector.go(false, null);
            //Set focus to Specware Status tab
            writeToSpecwareStatus("");
            try {
                RES = JavaLinkDist.invokeInLispEx(3, JavaLinkDist.newDistOb("USER::PROCESS-UNIT"), ARGS);
//               Util.log("Done.");
                if (com.franz.jlinker.JavaLinkDist.stringP(RES[0])) {
                    Util.log("Error while generating code for scheduler: \n"+ RES[0]);
                } else {
//                    Util.log("Call succeeded");
                }
            } catch (JavaLinkDist.JLinkerException ex) {
                Util.log("Exception in generateCode "+ ex);
            }
        } else {
//            writeToOutput("LispProcessManager.generateCode ==> No Connection to Lisp");
        }
    }
    
    // THis is called from specware
    public static void setProcessUnitResults(String results) {
        writeToSpecwareStatus(results);
        
    }
    
    public static void writeToOutput(String s) {
        InputOutput outputStream = TopManager.getDefault().getIO("LispProcessManager", false);
        OutputWriter writer = outputStream.getOut();
        writer.println(s);
    }
    
    public static void writeToSpecwareStatus(String s) {
        InputOutput outputStream = TopManager.getDefault().getIO("Specware Status", false);
        outputStream.select();
        OutputWriter writer = outputStream.getOut();
        writer.println(s);
    }
}
