package edu.kestrel.netbeans.lisp;

/* Use sockets instead
import com.franz.jlinker.TranStruct;
import com.franz.jlinker.JavaLinkDist;
import com.franz.jlinker.LispConnector;
*/

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;
import java.lang.ClassNotFoundException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.Set;

//hacky stuff:
import org.openide.nodes.Node;
import org.openide.loaders.DataObject;
import org.openide.filesystems.FileObject;
import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.actions.ProcessUnitAction;
import edu.kestrel.netbeans.parser.ParseSourceRequest;

import edu.kestrel.netbeans.Util;

import org.openide.TopManager;
import org.openide.filesystems.FileSystem;
import org.openide.filesystems.Repository;
import org.openide.text.CloneableEditor;
import org.openide.text.CloneableEditorSupport;
import org.openide.util.Utilities;
import org.openide.windows.InputOutput;
import org.openide.windows.OutputWriter;


/**
 *
 * @author  weilyn
 */
public class LispSocketManager {
    private static final boolean DEBUG = true;
    private static final String END_OF_PARAMETER_MARKER = "ENDPARAMETER";
    
    private static Set machines = new HashSet() ;
    private static String lispFile     = "";
    private static String lispHost     = "localhost";
    private static int    lispPort     = 4324;
    private static int    pollInterval = 1000;
    private static int    pollCount    = 300;
    private static int    javaTimeout   = -1;
    private static String javaFile      = "";
    private static String javaHost      = "";
    private static int    javaPort      = 0;
    
    static private ExternalLispProcess lispServer = null;
    static private Process lispProcess = null;
    
    static private ServerSocket serverSocket = null;
    static private Socket lispSocket = null;
    static private BufferedReader fromLispStream = null;
    static private OutputStream toLispStream = null;
    static private Thread readThread = null;
    static private Thread serverSocketThread = null;
    
    static private Class lispSocketManagerClass;
    static private Class stringClass;
   
    /** Creates a new instance of LispSocketManager */
    public LispSocketManager() {
    }
    
    private static class FromLispReader implements Runnable {
        FromLispReader() {
        }
        
        public void run() {
            try {
                while (!readThread.isInterrupted()) {
                    Util.log("LispSocketManager.FromLispReader.run is about to call lispCallBack()");
                    lispCallBack();
                }
            } catch (Exception e) {
                Util.log("LispSocketManager.FromLispReader.run caught " + e.getClass().getName() + ": " + e.getMessage());
            }
        }
    }
    
    private static class SocketConnector implements Runnable {
        SocketConnector() {
        }
        
        public void run() {
            /*try {
                
                if (DEBUG) {
                    Util.log("SocketConnector's serverSocket is "+serverSocket);
                }
            } catch (IOException ioe) {
                Util.log("LispSocketManager.SocketConnector.run caught exception: "+ioe.getMessage());
            }*/
        }
    }
    
    public static boolean connectToLisp() {
        if (lispServer == null || lispProcess == null || lispSocket == null) {
            try {
                //serverSocketThread = new Thread(new SocketConnector());
                //serverSocketThread.start();
                if (serverSocket == null) {
                    serverSocket = new ServerSocket(lispPort);
                }
                
                if (DEBUG) {
                    Util.log("LispSocketManager.connectToLisp about to call serverSocket.accept; port is "+serverSocket.getLocalPort());
                }
                
/*                lispSocket = serverSocket.accept();
                
                if (DEBUG) {
                    Util.log("LispSocketManager.connectToLisp done with serverSocket.accept");
                }
*/                
                lispPort = serverSocket.getLocalPort();
                if (DEBUG) {
                    Util.log("LispSocketManager.connectToLisp got lispPort = "+lispPort);
                }
                
                /*System.setProperty("SpecBeansSocketPort", Integer.toString(lispPort));
                if (DEBUG) {
                    Util.log("All properties: "+System.getProperties());
                }*/

                lispServer = new ExternalLispProcess();

                lispProcess = lispServer.createProcess();
                Thread.sleep(5000);

                if (DEBUG) {
                    Util.log("lispServer = "+lispServer+"; lispProcess = "+lispProcess);
                }
                
                lispSocket = serverSocket.accept();//new Socket(lispHost, lispPort);
                if (DEBUG) {
                    Util.log("LispSocketManager.connectToLisp: lispSocket.isConnected() = "+lispSocket.isConnected());
                }
                toLispStream = lispSocket.getOutputStream();
                fromLispStream = new BufferedReader(new InputStreamReader(lispSocket.getInputStream()));
                if (DEBUG) {
                    Util.log("LispSocketManager.connectToLisp has fromLispStream = "+fromLispStream);
                }

                lispSocketManagerClass = Class.forName("edu.kestrel.netbeans.lisp.LispSocketManager");
                stringClass = Class.forName("java.lang.String");
                
                readThread = new Thread(new FromLispReader());
                readThread.start();
                
                return true;
                
            } catch (UnknownHostException uhe) {
                 Util.log("LispSocketManager caught UnknownHostException: "+uhe.getMessage());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.connectToLisp got IOException: "+ioe.getMessage());
            } catch (ClassNotFoundException cnfe) {
                Util.log("LispSocketManager caught ClassNotFoundException: "+cnfe.getMessage());
            } catch (InterruptedException ie) {
                Util.log("LispSocketManager caught InterruptedException: "+ie.getMessage());
            }
            return false;
        } else {
            if (lispSocket.isConnected() && !lispSocket.isInputShutdown() && !lispSocket.isOutputShutdown()) {
               return true;
            } else {
                destroyLispProcess();
                return connectToLisp();
            }
        }
    }

    public static void lispCallBack() {
        try {
            String methodName = fromLispStream.readLine();
            if (DEBUG) {
                Util.log("LispSocketManager.lispCallBack read methodName = "+methodName);
            }
            // Assumes next line is an integer: add catch for NumberFormatException
            int numParams = (Integer.decode(fromLispStream.readLine())).intValue();
            if (DEBUG) {
                Util.log("LispSocketManager.lispCallBack read numParams = "+numParams);
            }
            String[] params = new String[numParams];
            Class[] paramClasses = new Class[numParams];

            for(int i = 0; i < numParams; i++) {
                String oneLine = fromLispStream.readLine();
                String oneParam = "";
                while (!oneLine.equals(END_OF_PARAMETER_MARKER)) {
                    oneParam = oneParam + oneLine + "\n";
                    oneLine = fromLispStream.readLine();
                }
                params[i] = oneParam;
                if (DEBUG) {
                    Util.log("LispSocketManager.lispCallBAck read param[" + i + "] = "+params[i]);
                }
                paramClasses[i] = stringClass;
            }
            Method m = lispSocketManagerClass.getMethod(methodName,paramClasses);
            if (DEBUG) {
                Util.log("LispSocketManager.lispCallBack created Method m = " + m);
            }
            m.invoke(null, params);
        } catch (IOException ioe) {
            Util.log("LispSocketManager.lispCallBack caught IOException: " + ioe.getMessage());
        } catch (NoSuchMethodException nsme) {
            Util.log("LispSocketManager.lispCallBack caught NoSuchMethodException: " + nsme.getMessage());
        } catch (IllegalAccessException iae) {
            Util.log("LispSocketManager.lispCallBack caught IllegalAccessException: " + iae.getMessage());
        } catch (InvocationTargetException ite) {
            Util.log("LispSocketManager.lispCallBack caught InvocationTargetException: " + ite.getMessage());
        }
    }

    public static void destroyLispProcess() {
        // first exit from lisp
        if (lispSocket != null && lispSocket.isConnected()) {
            String message = "(exit)";
            
            if (DEBUG) {
                Util.log ("LispSocketManager.destroyLispProcess sending message: "+message);
            }

            try {
                toLispStream.write(message.getBytes());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.destroyLispProcess caught exception: "+ioe.getMessage());
            }
        }      
        if (lispProcess != null) {
            lispProcess.destroy();
            lispProcess = null;
            lispServer = null;
            try {
                //toLispStream.close();
                //fromLispStream.close();
                lispSocket.shutdownInput();
                lispSocket.shutdownOutput();
                lispSocket.close();
                readThread.interrupt();
            } catch (IOException ioe) {
                Util.log("LispSocketManager.destroyLispProcess caught exception: "+ioe.getMessage());
            }
        }
    }
    

    public static void processUnit(String pathName, String fileName) {
        if (connectToLisp()) {
            String message = "";
            message = message + "(USER::PROCESS-UNIT ";
            message = message + "\"" + pathName;
            message = message + (Utilities.isWindows() ? "\\\" " : "/\" ");
            message = message + "\"" + fileName + "\"";
            message = message + ")";
            
            if (DEBUG) {
                Util.log ("LispSocketManager.processUnit sending message: "+message);
            }

            try {
                toLispStream.write(message.getBytes());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.processUnit caught exception: "+ioe.getMessage());
            }
        }
    }
    
    // This is called from specware
    public static void setProcessUnitResults(String results) {
        writeToSpecwareStatus(results);
    }

    // Entry point from lisp interface that takes only strings
    public static void setProcessUnitResults(String pathName, String fileName,
					     String lineNum, String colNum, String errorMsg) {
	// decode can throw NumberFormatException
        if (DEBUG) {
            Util.log("called setProcessUnitResults with all Strings");
        }
	setProcessUnitResults(pathName, fileName, (Integer.decode(lineNum)).intValue(), 
                              (Integer.decode(colNum)).intValue(), errorMsg);
    }

    public static void setProcessUnitResults(String pathName, String fileName,
					     int lineNum, int colNum, String errorMsg) {
        FileObject fileObj = Repository.getDefault().find(pathName, fileName, "sw");
        if (DEBUG) {
            Util.log("called setProcessUnitResults with pathName = "+pathName+" and fileName = "+fileName+" and got fileObj = "+fileObj);
        }

        if (fileObj != null) {
            // SLIGHT HACK: ParseSourceRequest is the same class used for the netbeans parsing stuff...
            // should probably create different class for the Specware processing stuff
            ParseSourceRequest.pushProcessUnitError(fileObj, lineNum, colNum, errorMsg);
        }
    }
    
    public static void compileSpec(String pathName, String fileName, String specName) {
        if (connectToLisp()) {
            String message = "";
            message = message + "(CL-USER::GENERATE-INCREMENTAL-LISP ";
            message = message + "\"" + pathName;
            message = message + (Utilities.isWindows() ? "\\\" " : "/\" ");
            message = message + "\"" + fileName;
            if (!specName.equals("")) 
                message = message + "#" + specName;
            message = message + "\"";
            message = message + ")";
            
            if (DEBUG) {
                Util.log ("LispSocketManager.compileSpec sending message: "+message);
            }

            try {
                toLispStream.write(message.getBytes());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.compileSpec caught exception: "+ioe.getMessage());
            }
        }
    }
    
    
    public static void generateLispCode(String pathName, String fileName) {
        if (connectToLisp()) {
            String message = "";
            message = message + "(USER::GENERATE-LISP ";
            message = message + "\"" + pathName + "\" ";
            message = message + "\"" + fileName + "\"";
            message = message + ")";
            
            if (DEBUG) {
                Util.log ("LispSocketManager.generateLisp sending message: "+message);
            }

            try {
                toLispStream.write(message.getBytes());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.generateLisp caught exception: "+ioe.getMessage());
            }
        }    
    }
    
    public static void setGenerateLispResults(String pathName, String fileName, String results) {
        writeToSpecwareStatus(results);
    }
        
    public static void generateJavaCode(String pathName, String fileName) {
        if (connectToLisp()) {
            String message = "";
            message = message + "(USER::GENERATE-JAVA ";
            message = message + "\"" + pathName;
            message = message + (Utilities.isWindows() ? "\\\" " : "/\" ");
            message = message + "\"" + fileName + "\"";
            message = message + ")";
            
            if (DEBUG) {
                Util.log ("LispSocketManager.generateJavaCode sending message: "+message);
            }

            try {
                toLispStream.write(message.getBytes());
            } catch (IOException ioe) {
                Util.log("LispSocketManager.generateJavaCode caught exception: "+ioe.getMessage());
            }
        }
    }
    
    public static void setGenerateJavaResults(String pathName, String fileName, String results) {
        writeToSpecwareStatus(results);
    }

    public static void writeToSpecwareStatus(String s) {
        InputOutput outputStream = TopManager.getDefault().getIO("Specware Output", false);
        outputStream.select();
        OutputWriter writer = outputStream.getOut();
        writer.println(s);
    }
}
