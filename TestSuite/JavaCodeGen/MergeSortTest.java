class MergeSortTest {
    static String listString(ListI l) {
	StringBuffer s = new StringBuffer("[");
	boolean firstElement = true;
	while (! l.isempty()) {
	    if (!firstElement) s.append(",");
	    firstElement = false;
	    s.append(l.head());
	    l = l.tail();
	}
	s.append("]");
	return (new String(s));
    }
    public static void main(String[] args) {
	int nargs = args.length;
	ListI l = ListI.nilI();
	for (int i = nargs-1; i >= 0; i--)
	    try {
		l = ListI.consI(Integer.parseInt(args[i]),l);
	    } catch (NumberFormatException e) {
		throw new Error("Expected integer arguments");
	    }
	ListI sorted = l.msort();
	System.out.println("Result of merge sort is " + listString(sorted));
    }
}
