/*
 * MetaSlangParserCodeGen.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:20  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.*;
import java.io.*;

/**
* Generator of code used for matching the keywords or more generally some
* group of words.
*
*/

public class MetaSlangParserCodeGen {

    private static final String USAGE
    = "Usage: java org.netbeans.editor.ext.MetaSlangParserCodeGen [options]" // NOI18N
      + " keyword-file [match-function-name]\n\n" // NOI18N
      + "Options:\n" // NOI18N
      + "  -i Ignore case in matching\n" // NOI18N
      + "  -s Input is in 'input' String or StringBuffer instead of char buffer\n\n" // NOI18N
      + "Generator of method that matches" // NOI18N
      + " the keywords provided in the file.\n" // NOI18N
      + "Keywords in the file must be separated by spaces or new-lines" // NOI18N
      + " and they don't need to be sorted.\n"; // NOI18N

    private static final String UNKNOWN_OPTION = " is unknown option.\n"; // NOI18N

    public static final String IGNORE_CASE = "-i"; // NOI18N

    public static final String USE_STRING = "-s"; // NOI18N

    private static final String DEFAULT_METHOD_NAME = "matchKeyword"; // NOI18N

    private static final String[] OPTION_LIST = { IGNORE_CASE, USE_STRING };

    private static final String PARSER_FILE_NAME = "MetaSlangParserFromAntlr.java";
    private static final String TOKENS_TYPE_FILE_NAME = "MetaSlangParserFromAntlrTokenTypes.txt";
    private static final String TOKEN_CONTEXT_FILE_NAME = "MetaSlangTokenContext.java";
    private static final String SYNTAX_FILE_NAME = "MetaSlangSyntax.java";

    /** The list of keywords */
    private String[] keywords;

    /** The list of operators */
    private String[] operators;

    /** Maximum length of keyword */
    private int maxKeywordLen;

    /** Options */
    private HashMap options = new HashMap();

    private HashMap keywordConstants = new HashMap();

    private HashMap operatorConstants = new HashMap();

    private StringBuffer stringBuffer;

    private void generateTokenContext(File file) {
	StringBuffer operatorNumericConstants = new StringBuffer();
	StringBuffer operatorTokenConstants = new StringBuffer();
	StringBuffer keywordNumericConstants = new StringBuffer();
	StringBuffer keywordTokenConstants = new StringBuffer();
	StringBuffer keywordTokens = new StringBuffer();
        // write operator numeric ID table
	String prevConstant = "INT_LITERAL";
	String curConstant, operator, keyword;
	int lastIndex = operators.length - 1;
        for (int i = 0; i < operators.length; i++) {
	    operator = operators[i];
	    curConstant = (String) operatorConstants.get(operator);
            operatorNumericConstants.append(indent(1) + "public static final int " + curConstant // NOI18N
					    + "_ID = " + prevConstant + "_ID + 1;"); // NOI18N
	    for (int j = curConstant.length() + prevConstant.length(); j < 20; j++) {
		operatorNumericConstants.append(" ");
	    }
            operatorNumericConstants.append(" // " + operator); // NOI18N
	    operatorTokenConstants.append(indent(1) + "public static final BaseImageTokenID " + curConstant // NOI18N
					  + " = new BaseImageTokenID(\"" + curConstant.toLowerCase() + "\", "+ curConstant + "_ID, OPERATORS, \""+operator+"\");");
	    if (i < lastIndex) {
		operatorNumericConstants.append("\n");
		operatorTokenConstants.append("\n");
	    }
	    prevConstant = curConstant;
	}
	int len, lineLen = 0;
	lastIndex = keywords.length - 1;
        for (int i = 0; i < keywords.length; i++) {
	    keyword = keywords[i];
	    curConstant = (String) keywordConstants.get(keyword);
            keywordNumericConstants.append(indent(1) + "public static final int " + curConstant // NOI18N
					   + "_ID = " + prevConstant + "_ID + 1;"); // NOI18N
	    keywordTokenConstants.append(indent(1) + "public static final BaseImageTokenID " + curConstant // NOI18N
					 + " = new BaseImageTokenID(\"" + keyword + "\", "+ curConstant + "_ID, KEYWORDS);");
	    prevConstant = curConstant;
	    len = curConstant.length();
	    if (lineLen + len > 60 && i < lastIndex) {
		keywordTokens.append("\n");
		lineLen = 0;
	    }
	    if (lineLen == 0) {
		keywordTokens.append(indent(3));
	    }
	    keywordTokens.append(curConstant);
	    lineLen = lineLen + len;
	    if (i < lastIndex) {
		keywordNumericConstants.append("\n");
		keywordTokenConstants.append("\n");
		keywordTokens.append(", ");
		lineLen = lineLen + 2;
	    }
	}
	String isKeywardReturnStatement = indent(2) + "return (numID >= " +
	    keywordConstants.get(keywords[0]) + "_ID && numID <= " +
	    keywordConstants.get(keywords[lastIndex]) + "_ID);";
	replaceGeneratedCode(file,
			     new String[] {operatorNumericConstants.toString(),
					       keywordNumericConstants.toString(),
					       operatorTokenConstants.toString(),
					       keywordTokenConstants.toString(),
					       keywordTokens.toString(),
					       isKeywardReturnStatement});
    }

    private void generateMatchKeywordMethod(String methodName, File file) {
	stringBuffer = new StringBuffer();
        initScan(methodName);
        scan();
        finishScan();
	replaceGeneratedCode(file, new String[]{stringBuffer.toString()});
    }

    private void replaceGeneratedCode(File file, String[] generatedCodes) {
	try {
	    char[] originalCode = readFile(file);
	    StringBuffer buffer = new StringBuffer();
	    buffer.append(originalCode);
	    int pos = 0;
	    int pos2 = 0;
	    for (int i = 0; i < generatedCodes.length; i++) {
		String generatedCode = generatedCodes[i];
		//System.out.println("*** MetaSlangParserCodeGen.replaceGeneratedCode(): generatedCode="+generatedCode);
		pos = buffer.indexOf("//GEN-BEGIN", pos);
		if (pos < 0) {
		    System.err.println("Failed to find //GEN-BEGIN marker");
		    return;
		} else {
		    pos = buffer.indexOf("\n", pos);
		    pos2 = buffer.indexOf("//GEN-END", pos);
		    if (pos < 0) {
			System.err.println("Failed to find //GEN-END marker");
			return;
		    } else {
			pos2 = buffer.lastIndexOf("\n", pos2);
			buffer.replace(pos+1, pos2, generatedCode);
		    }
		}
	    }
	    writeFile(file, buffer.toString());
	} catch (IOException e) {
	    System.err.println("*** Failed to replace generated code: "+e);
	} 
    }

    private void fixParser(File file) {
	try {
	    String code = new String(readFile(file));
	    int pos = 0;
	    int len = code.length();
	    pos = code.indexOf('{');
	    if (pos >= 0) {
		pos = code.indexOf("\n", pos);
		if (pos >= 0) {
		    String newCode = (code.substring(0, pos + 1) +
			    "\n    ParseObjectRequest request;" + 
			    "\n    ElementFactory builder;" + 
			    "\n    Set processedUnitNames = new HashSet();\n" + 
			    "\n    public void reportError(RecognitionException ex) {" + 
			    "\n        request.setSyntaxErrors(request.getSyntaxErrors() + 1);" + 
			    "\n        ErrConsumer errConsumer = request.getErrConsumer();" +
			    "\n        if (errConsumer != null) {" + 
			    "\n            errConsumer.pushError(null, ex.getLine(), ex.getColumn(), ex.getMessage(), \"\");" +
			    "\n        }" + 
			    "\n    }\n" +
			    "\n    public MetaSlangParserFromAntlr(TokenStream lexer, ParseObjectRequest request) {" + 
			    "\n        this(lexer);" + 
			    "\n        this.request = request;" + 
			    "\n        this.builder = request.getFactory();" + 
			    "\n    }\n" + 
			    code.substring(pos + 1, len));
		    writeFile(file, newCode);			
		}
	    }
	} catch (IOException e) {
	    System.err.println("*** Failed to fix generated parser: "+e);
	} 
    }

    private char[] readFile(File file) throws IOException {
	char[] arr = new char[(int)file.length()];
	Reader reader = new FileReader(file);
	int n = 0;
	while (n < file.length()) {
	    int count = reader.read(arr, n, (int)file.length() - n);
	    if (count < 0)
		break;
	    n += count;
	}
	reader.close();
	return arr;
    }

    private void writeFile(File file, String content) throws IOException {
	BufferedWriter writer = new BufferedWriter(new FileWriter(file));
	writer.write(content);
	writer.close();
    }

    /** Provide indentation (default 4 spaces) */
    private String indent(int cnt) {
        StringBuffer sb = new StringBuffer();

        while(cnt-- > 0) {
            sb.append("    "); // NOI18N
        }
        return sb.toString();
    }

    protected void initScan(String methodName) {

        if (methodName == null) {
            methodName = DEFAULT_METHOD_NAME;
        }

        // write method header
        stringBuffer.append(indent(1) + "public static TokenID "); // NOI18N
        stringBuffer.append(methodName);
        if (options.get(USE_STRING) != null) {
            stringBuffer.append("(String buffer, int offset, int len) {\n"); // NOI18N
        } else {
            stringBuffer.append("(char[] buffer, int offset, int len) {\n"); // NOI18N
        }
        stringBuffer.append(indent(2) + "if (len > " + maxKeywordLen + ")\n"); // NOI18N
        stringBuffer.append(indent(3) + "return null;\n"); // NOI18N
    }

    public void scan() {
        scan(0, keywords.length, 0, 2, 0);
    }

    protected void finishScan() {
        stringBuffer.append(indent(1) + "}"); // NOI18N
    }

    public void addOption(String option) {
        options.put(option, option);
    }

    protected String getKeywordConstantPrefix() {
        return ""; // "KEYWORD_"; // NOI18N
    }

    protected String getKeywordConstant(String keyword) {
        return "MetaSlangTokenContext."+(String)keywordConstants.get(keyword);
    }

    protected boolean upperCaseKeyConstants() {
        return true;
    }

    /** Parse the keywords from a string */
    private void parseTokens(List tokenDescrs) {
        List keywordList = new ArrayList();
        List operatorList = new ArrayList();
	String tokenDescr= null, token = null, tokenName = null;
	int len, pos, pos2;
	for (Iterator i = tokenDescrs.iterator(); i.hasNext();) {
	    tokenDescr = (String) i.next();
	    //System.out.println("*** MetaSlangParserCodeGen.parseTokens(): input: "+tokenDescr);
	    if (tokenDescr.charAt(0) == '"') {
		pos = tokenDescr.indexOf('"', 1);
		token = tokenDescr.substring(1, pos);
		tokenName = token.replace('-', '_').replace('?', 'P').toUpperCase();
		maxKeywordLen = Math.max(maxKeywordLen, token.length());
		keywordList.add(token);
		keywordConstants.put(token, tokenName);
		//System.out.println("*** MetaSlangParserCodeGen.parseTokens(): keyword: "+token+", "+tokenName);
	    } else {
		len = tokenDescr.length();
		if (len > 8 && tokenDescr.substring(0, 8).equals("LITERAL_")) {
		    pos = tokenDescr.indexOf('=');
		    token = tokenDescr.substring(8, pos);
		    tokenName = token.toUpperCase();
		    maxKeywordLen = Math.max(maxKeywordLen, token.length());
		    keywordList.add(token);
		    keywordConstants.put(token, tokenName);
		    //System.out.println("*** MetaSlangParserCodeGen.parseTokens(): keyword: "+token+", "+tokenName);
		} else {
		    pos = tokenDescr.indexOf("(\"\'");
		    if (pos > 0) {
			tokenName = tokenDescr.substring(0, pos);
			pos2 = tokenDescr.indexOf("'\")", pos + 3);
			token = tokenDescr.substring(pos + 3, pos2);
			operatorList.add(token);
			operatorConstants.put(token, tokenName);
			//System.out.println("*** MetaSlangParserCodeGen.parseTokens(): operator: "+token+", "+tokenName);
		    }
		}
	    }
	}
        keywords = new String[keywordList.size()];
        keywordList.toArray(keywords);
        Arrays.sort(keywords);
        operators = new String[operatorList.size()];
        operatorList.toArray(operators);
        Arrays.sort(operators);
    }

    protected String getCurrentChar() {
        boolean useString = (options.get(USE_STRING) != null);
        boolean ignoreCase = (options.get(IGNORE_CASE) != null);

        if(useString) {
            return ignoreCase ? "Character.toLowerCase(buffer.charAt(offset++))" // NOI18N
                   : "buffer.charAt(offset++)"; // NOI18N
        } else {
            return ignoreCase ? "Character.toLowerCase(buffer[offset++])" // NOI18N
                   : "buffer[offset++]"; // NOI18N
        }
    }

    private void appendCheckedReturn(String keyword, int offset, int indent) {
        stringBuffer.append(indent(indent) + "return (len == " // NOI18N
                     + keyword.length());

        int keywordLenM1 = keyword.length() - 1;
        for(int k = offset; k <= keywordLenM1; k++) {
            stringBuffer.append("\n" + indent(indent + 1) + "&& "); // NOI18N
            stringBuffer.append(getCurrentChar() + " == '" + keyword.charAt(k) + "'"); // NOI18N
        }

        stringBuffer.append(")\n" + indent(indent + 2) + "? " + getKeywordConstant(keyword) + " : null;\n"); // NOI18N
    }

    /** Scan the keywords and generate the output. This method is initially
    * called with the full range of keywords and offset equal to zero.
    * It recursively calls itself to scan the subgroups.
    * @param indFrom index in keywords[] where the subgroup of keywords starts
    * @pararm indTo index in keywords[] where the subgroup of keywords ends
    * @param offset current horizontal offset. It's incremented as the subgroups
    *   are recognized. All the characters prior to offset index are the same
    *   in all keywords in the group.
    */
    private void scan(int indFrom, int indTo, int offset, int indent, int minKeywordLen) {
        //    System.out.println(">>>DEBUG<<< indFrom=" + indFrom + ", indTo=" + indTo + ", offset=" + offset + ", indent=" + indent + ", minKeywordLen="+ minKeywordLen); // NOI18N
        int maxLen = 0;
        for (int i = indFrom; i < indTo; i++) {
            maxLen = Math.max(maxLen, keywords[i].length());
        }

        int same;
        int minLen;
        do {
            minLen = Integer.MAX_VALUE;
            // Compute minimum and maximum keyword length in the current group
            for (int i = indFrom; i < indTo; i++) {
                minLen = Math.min(minLen, keywords[i].length());
            }

            //      System.out.println(">>>DEBUG<<< while(): minLen=" + minLen + ", minKeywordLen=" + minKeywordLen); // NOI18N
            if (minLen > minKeywordLen) {
                stringBuffer.append(indent(indent) + "if (len <= " + (minLen - 1) + ")\n"); // NOI18N
                stringBuffer.append(indent(indent + 1) + "return null;\n"); // NOI18N
            }

            // Compute how many chars from current offset on are the same
            // in all keywords in the current group
            same = 0;
            boolean stop = false;
            for (int i = offset; i < minLen; i++) {
                char c = keywords[indFrom].charAt(i);
                for (int j = indFrom + 1; j < indTo; j++) {
                    if (keywords[j].charAt(i) != c) {
                        stop = true;
                        break;
                    }
                }
                if (stop) {
                    break;
                }
                same++;
            }

            //      System.out.println(">>>DEBUG<<< minLen=" + minLen + ", maxLen=" + maxLen + ", same=" + same); // NOI18N

            // Add check for all the same chars
            if (same > 0) {
                stringBuffer.append(indent(indent) + "if ("); // NOI18N
                for (int i = 0; i < same; i++) {
                    if (i > 0) {
                        stringBuffer.append(indent(indent + 1) + "|| "); // NOI18N
                    }
                    stringBuffer.append(getCurrentChar() + " != '" + keywords[indFrom].charAt(offset + i) + "'"); // NOI18N
                    if (i < same - 1) {
                        stringBuffer.append("\n"); // NOI18N
                    }
                }
                stringBuffer.append(")\n"+ indent(indent + 2) + "return null;\n"); // NOI18N
            }

            // Increase the offset to the first 'non-same' char
            offset += same;

            // If there's a keyword with the length equal to the current offset
            // it will be first in the (sorted) group and it will be matched now
            if (offset == keywords[indFrom].length()) {
                stringBuffer.append(indent(indent) + "if (len == " + offset + ")\n"); // NOI18N
                stringBuffer.append(indent(indent + 1) + "return " // NOI18N
                             + getKeywordConstant(keywords[indFrom]) + ";\n"); // NOI18N
                indFrom++; // increase starting index as first keyword already matched
                if (offset >= minLen) {
                    minLen = offset + 1;
                }
            }

            minKeywordLen = minLen; // minLen already tested, so assign new minimum

        } while (same > 0 && indFrom < indTo);

        // If there are other chars at the end of any keyword,
        // add the switch statement
        if (offset < maxLen) {
            stringBuffer.append(indent(indent) + "switch (" + getCurrentChar() + ") {\n"); // NOI18N

            // Compute subgroups
            int i = indFrom;
            while(i < indTo) {
                // Add the case statement
                char actChar = keywords[i].charAt(offset);
                stringBuffer.append(indent(indent + 1) + "case '" + actChar + "':\n"); // NOI18N

                // Check whether the subgroup will have more than one keyword
                int subGroupEndInd = i + 1;
                while(subGroupEndInd < indTo
                        && keywords[subGroupEndInd].length() > offset
                        && keywords[subGroupEndInd].charAt(offset) == actChar
                     ) {
                    subGroupEndInd++;
                }

                if(subGroupEndInd > i + 1) { // more than one keyword in subgroup
                    scan(i, subGroupEndInd, offset + 1, indent + 2, minLen);
                } else { // just one keyword in the subgroup
                    appendCheckedReturn(keywords[i], offset + 1, indent + 2);
                }

                // advance current index to the end of current subgroup
                i = subGroupEndInd;
            }

            stringBuffer.append(indent(indent + 1) + "default:\n"); // NOI18N
            stringBuffer.append(indent(indent + 2) + "return null;\n"); // NOI18N
            stringBuffer.append(indent(indent) + "}\n"); // NOI18N
        } else { // no add-on chars, keyword not found in this case
            stringBuffer.append(indent(indent) + "return null;\n"); // NOI18N
        }

    }

    /** Main method */
    public static void main(String args[]) {
        MetaSlangParserCodeGen generator = new MetaSlangParserCodeGen();

        // parse options
        int argIndex;
        for (argIndex = 0; argIndex < args.length; argIndex++) {
            int j;
            if (args[argIndex].charAt(0) != '-') {
                break; // no more options
            }
            for (j = 0; j < OPTION_LIST.length; j++) {
                if (args[argIndex].equals(OPTION_LIST[j])) {
                    generator.addOption(OPTION_LIST[j]);
                    break;
                }
            }
            if (j == OPTION_LIST.length) {
                System.err.println("'" + args[argIndex] + "'" + UNKNOWN_OPTION); // NOI18N
                System.err.println(USAGE);
                return;
            }
        }

        // check count of mandatory args
        if (args.length - argIndex < 1) {
            System.err.println(USAGE);
            return;
        }

        // read token file
        List tokenDescrs = new LinkedList();
	String parserDir = args[argIndex];
	File parserFile = new File(parserDir, PARSER_FILE_NAME);
	File tokenTypesFile = new File(parserDir, TOKENS_TYPE_FILE_NAME);
        try {
            if (!parserFile.exists()) {
                System.err.println("Non-existent file " + parserFile); // NOI18N
                return;
            }

            if (!tokenTypesFile.exists()) {
                System.err.println("Non-existent file " + tokenTypesFile); // NOI18N
                return;
            }
            BufferedReader reader = new BufferedReader(new FileReader(tokenTypesFile));

            boolean first = true;
	    String line = reader.readLine();
            while (line != null) {
		if (first) {
		    // skip the first line
		    first = false;
		} else {
		    if (line.length() > 0) {
			tokenDescrs.add(line);
		    }
		}
		line = reader.readLine();
            }
        } catch(EOFException e) {
        } catch(IOException e) {
            // IO exception
            System.err.println("Cannot read from keyword file '" + args[argIndex] + "'"); // NOI18N
            return;
        }

	
	String editorDir = args[++argIndex];
	File tokenContextFile = new File(editorDir, TOKEN_CONTEXT_FILE_NAME);
	File syntaxFile = new File(editorDir, SYNTAX_FILE_NAME);

        // Check for optional method name
        String methodName = null;
        if (args.length - argIndex >= 2) {
            methodName = args[argIndex + 1];
        }

        // generate
	generator.fixParser(parserFile);
        generator.parseTokens(tokenDescrs);
	generator.generateTokenContext(tokenContextFile);
	generator.generateMatchKeywordMethod(methodName, syntaxFile);
    }


}
