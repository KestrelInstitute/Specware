/*
 * LispProcessManager.java
 *
 * Created on February 13, 2003, 6:49 PM
 */

package edu.kestrel.netbeans.lisp;

import com.franz.jlinker.TranStruct;
import com.franz.jlinker.JavaLinkDist;
import com.franz.jlinker.LispConnector;

//hacky stuff:
import org.openide.nodes.Node;
import org.openide.loaders.DataObject;
import org.openide.filesystems.FileObject;
import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.actions.ProcessUnitAction;
import edu.kestrel.netbeans.parser.ParseSourceRequest;

import edu.kestrel.netbeans.Util;

import java.util.HashSet;
import java.util.Set;

import org.openide.TopManager;
import org.openide.filesystems.FileSystem;
import org.openide.filesystems.Repository;
import org.openide.text.CloneableEditor;
import org.openide.text.CloneableEditorSupport;
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
                    Util.log("Error while generating code for: \n"+ RES[0]);
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
    
    // This is called from specware
    public static void setProcessUnitResults(String results) {
        writeToSpecwareStatus(results);
        FileObject fileObj = Repository.getDefault().find("Demo_Examples", null, null);
        if (fileObj != null)
            fileObj.refresh();
    }
    
    public static void setProcessUnitResults(String pathName, String fileName, int lineNum, int colNum, String errorMsg) {
        FileObject fileObj = Repository.getDefault().find(pathName, fileName, "sw");
        if (fileObj != null) {
            // SLIGHT HACK: ParseSourceRequest is the same class used for the netbeans parsing stuff...
            // should probably create different class for the Specware processing stuff
            ParseSourceRequest.pushProcessUnitError(fileObj, lineNum, colNum, errorMsg, "");
        }
    }
    
    public static void generateLispCode(String pathName, String fileName) {
        if (connectToLisp()) {
            TranStruct [] ARGS = new TranStruct[2];
            TranStruct [] RES;
            ARGS[0] = JavaLinkDist.newDistOb(pathName);
            ARGS[1] = JavaLinkDist.newDistOb(fileName);
            com.franz.jlinker.LispConnector.go(false, null);
            //Set focus to Specware Status tab
            writeToSpecwareStatus("");
            try {
                RES = JavaLinkDist.invokeInLispEx(3, JavaLinkDist.newDistOb("USER::GENERATE-LISP"), ARGS);
//               Util.log("Done.");
                if (com.franz.jlinker.JavaLinkDist.stringP(RES[0])) {
                    Util.log("Error while generating code for: \n"+ RES[0]);
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
    
    public static void setGenerateLispResults(String pathName, String fileName, String results) {
        writeToSpecwareStatus(results);

        // TOTAL HACK: 14 is the length of "Demo_Examples/", which is the path to fileName in Weilyn's setup from the
        //  mounted local directory C:\Program Files\Specware4\Gui\src
        String nonQualifiedFileName = fileName.substring(14);
        
        // Do a refresh of Demo_Examples folder to show the possibly newly created "lisp" folder
        FileObject fileObj = Repository.getDefault().find("Demo_Examples", null, null);
        if (fileObj != null) fileObj.refresh();
        // Do a refresh of lisp folder to show the newly generated file
        fileObj = Repository.getDefault().find("Demo_Examples.lisp", null, null);
        if (fileObj != null) fileObj.refresh();
        
        // TODO: Open the new lisp file in the editor as a text file
        fileObj = Repository.getDefault().find("Demo_Examples.lisp", nonQualifiedFileName, "lisp");
        if (fileObj != null) {
//            CloneableEditorSupport editSupp = new CloneableEditorSupport(new CloneableEditorSupport.Env(fileObj));
//            CloneableEditor editor = new CloneableEditor(editSupp);
            
        }
    }
        
    public static void generateJavaCode(String pathName, String fileName) {
        if (connectToLisp()) {
            TranStruct [] ARGS = new TranStruct[2];
            TranStruct [] RES;
            ARGS[0] = JavaLinkDist.newDistOb(pathName);
            ARGS[1] = JavaLinkDist.newDistOb(fileName);
            com.franz.jlinker.LispConnector.go(false, null);
            //Set focus to Specware Status tab
            writeToSpecwareStatus("");
            try {
                RES = JavaLinkDist.invokeInLispEx(3, JavaLinkDist.newDistOb("USER::GENERATE-JAVA"), ARGS);
//               Util.log("Done.");
                if (com.franz.jlinker.JavaLinkDist.stringP(RES[0])) {
                    Util.log("Error while generating code for: \n"+ RES[0]);
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
    
    public static void setGenerateJavaResults(String pathName, String fileName, String results) {
        writeToSpecwareStatus(results);
        // TOTAL HACK: 14 is the length of "Demo_Examples/", which is the path to fileName in Weilyn's setup from the
        //  mounted local directory C:\Program Files\Specware4\Gui\src
        String nonQualifiedFileName = fileName.substring(14);

        // Do a refresh of Demo_Examples folder to show the possibly newly created "java" folder
        FileObject fileObj = Repository.getDefault().find("Demo_Examples", null, null);
        if (fileObj != null) fileObj.refresh();
        // Do a refresh of java folder to show the newly generated file
        fileObj = Repository.getDefault().find("Demo_Examples.java", null, null);
        if (fileObj != null) fileObj.refresh();
  
        // TODO: Open the new java file in the editor
        fileObj = Repository.getDefault().find("Demo_Examples.java", nonQualifiedFileName, "java");
        if (fileObj != null) {
//            CloneableEditorSupport editSupp = new CloneableEditorSupport(new CloneableEditorSupport.Env(fileObj));
//            CloneableEditor editor = new CloneableEditor(editSupp);
            
        }
    }
    
    public static void writeToOutput(String s) {
        InputOutput outputStream = TopManager.getDefault().getIO("Debug: LispProcessManager", false);
        OutputWriter writer = outputStream.getOut();
        writer.println(s);
    }
    
    public static void writeToSpecwareStatus(String s) {
        InputOutput outputStream = TopManager.getDefault().getIO("Specware Output", false);
        outputStream.select();
        OutputWriter writer = outputStream.getOut();
        writer.println(s);
    }
}
