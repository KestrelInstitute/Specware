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
            System.out.println("ModeMachineManager.connectToLisp --> Already Connected");
            writeToOutput("ModeMachineManager.connectToLisp --> Already Connected");
            return true;
        } else if (JavaLinkDist.connect(lispHost, lispPort, javaHost, javaPort, pollInterval, javaTimeout)) {
            System.out.println("ModeMachineManager.connectToLisp --> New Connection Established");
            writeToOutput("ModeMachineManager.connectToLisp --> New Connection Established");
            return true;
        } else {
            System.out.println("ModeMachineManager.connectToLisp --> Failed to Connect to LISP " + JavaLinkDist.query());
            writeToOutput("ModeMachineManager.connectToLisp --> Failed to Connect to LISP " + JavaLinkDist.query());
            writeToOutput("LispServer = "+ lispServer + "\n Lisp Process "+lispProcess + "\n");
            //destroyLispProcess();
            //lispServer = null;
            if (lispServer == null){
                lispServer = new ExternalLispProcess();
                try {
                    lispProcess = lispServer.createProcess();
                    writeToOutput("****  lispServer.createProcess returned "+lispServer);
                    Thread.sleep(5000);
                } catch (Exception e) {
                    writeToOutput("ModeMachineManager.connectToLisp.Exception "+e+" starting Lisp");
                }
                writeToOutput("ModeMachineManager.connectToLisp --> Calling Connect to Lisp again");
                if (lispProcess != null) {
                    return connectToLisp();
                }
            }
            //destroyLispProcess(); 
            //lispServer = null;
            return false;
        }
    }
    
    public static void processUnit(String fileName) {
	Util.log("*** LispProcessManager.processUnit(): fileName="+fileName);
        if (connectToLisp()) {
            TranStruct [] ARGS = new TranStruct[3];
            TranStruct [] RES;
            ARGS[0] = JavaLinkDist.newDistOb(fileName);
            com.franz.jlinker.LispConnector.go(false, null);
            Util.log("Processing unit ..."+ fileName);
            try {
                RES = JavaLinkDist.invokeInLispEx(3, JavaLinkDist.newDistOb("USER::SW"), ARGS);
                Util.log("Done.");
                if (com.franz.jlinker.JavaLinkDist.stringP(RES[0])) {
                    Util.log("Error while generating code for scheduler: \n"+ RES[0]);
                } else {
                    Util.log("Call succeeded");
                }
            } catch (JavaLinkDist.JLinkerException ex) {
                Util.log("Exception in generateCode "+ ex);
            }
        } else {
            writeToOutput("ModeMachineManager.generateCode ==> No Connection to Lisp");
        }
    }
    
    protected static InputOutput outputStream = TopManager.getDefault().getIO("MachineManager", false);
    protected static OutputWriter writer = outputStream.getOut();
    public static void writeToOutput(String s) {
        //System.out.println(s);
        writer.println(s);
    }    
}
