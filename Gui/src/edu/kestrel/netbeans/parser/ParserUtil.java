/*
 * ParserUtil.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/02/07 20:06:21  gilham
 * Added opDefinition and scUnitId to MetaSlangGrammar.
 *
 * Revision 1.1  2003/01/30 02:02:25  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import antlr.Token;

import edu.kestrel.netbeans.Util;

public class ParserUtil {

    public static boolean DEBUG = false;

    public static void setBounds(ElementFactory builder, ElementFactory.Item item, Token begin, Token end) {
	builder.setBounds(item,
			  begin.getLine(), begin.getColumn(),
			  end.getLine(), end.getColumn() + end.getText().length());
    }

    public static void setBodyBounds(ElementFactory builder, ElementFactory.Item item, Token begin, Token end) {
	if (DEBUG) Util.log("ParserUtil.setBodyBounds: builder="+builder+" item="+item+" begin="+begin+" end="+end);
	builder.setBodyBounds(item,
			      begin.getLine(), begin.getColumn(),
			      end.getLine(), end.getColumn() + end.getText().length());
    }

    public static void setAllBounds(ElementFactory builder, ElementFactory.Item item, Token begin, Token headerEnd, Token end) {
	int beginLine = begin.getLine();
	int beginColumn = begin.getColumn();
	int headerEndLine = headerEnd.getLine();
	int headerEndColumn = headerEnd.getColumn() + headerEnd.getText().length();
	int endLine = end.getLine();
	int endColumn = end.getColumn();
	builder.setHeaderBounds(item, beginLine, beginColumn, headerEndLine, headerEndColumn);
	builder.setBodyBounds(item, headerEndLine, headerEndColumn + 1, endLine, endColumn - 1);
	builder.setBounds(item, beginLine, beginColumn, endLine, endColumn + end.getText().length());
    }

}
