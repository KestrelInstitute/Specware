import java.io.*;

class ExpressionsTest {
    static int nextCh;
    static StringReader s;
    static void next() throws IOException {
	nextCh = s.read();
    }	
    static Expr readExpr() throws IOException {
	if (nextCh == -1) throw new Error("Empty expression");
	if (nextCh == '-' || ('0' <= nextCh && nextCh <= '9'))
	    return readConstExpr();
	if (nextCh == '(') return readBinExpr();
	throw new Error("Constant or binary expression expected");
    }
    static Expr readBinExpr() throws IOException {
	if (nextCh != '(') throw new Error("Open parenthesis expected");
	next();
	Expr e1 = readExpr();
	char operator = (char) nextCh;
	next();
	Expr e2 = readExpr();
	Expr result;
	switch (operator) {
	case '+' : result = Expr.plus(e1,e2); break;
	case '*' : result = Expr.times(e1,e2); break;
	case '^' : result = Expr.power(e1,e2); break;
	default : throw new Error("Plus, times, or power operator expected");
	}
	if (nextCh != ')') throw new Error("Close parenthesis expected");
	return result;
    }
    static Expr readConstExpr() throws IOException {
	return Expr.constant(readConst());
    }
    static int readConst() throws IOException {
	boolean negative = false;
	if (nextCh == '-') {
	    negative = true;
	    next();
	}
	int num = 0;
	while ('0' <= nextCh && nextCh <= '9') {
	    num = num * 10 + (nextCh - '0');
	    next();
	}
	if (negative) num = -num;
	return num;
    }
    public static void main(String[] args) throws IOException {
	if (args.length != 1) throw new Error("Expected 1 argument");
	s = new StringReader(args[0]);
	next();
	Expr e = readExpr();
	System.out.println("Depth is " + e.depth());
	System.out.println("Value is " + e.eval());
    }
}
