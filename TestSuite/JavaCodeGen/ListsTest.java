class ListsTest {
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
	boolean empty = l.isempty();
	int len = l.length();
	int max = l.max();
	ListI cat = l.concat(l);
	ListI h1 = l.half1();
	ListI h2 = l.half2();
	int hd = l.head();
	ListI tl = l.tail();
	ListI cat2 = l.concat2(l);
	System.out.println("List is " + (empty ? "" : "not ") + "empty");
	System.out.println("Length of list is " + len);
	if (empty) System.out.println("List has no max");
	else System.out.println("Max of list is " + max);
	System.out.println("Concatenation with itself is " + listString(cat));
	System.out.println("First half is " + listString(h1));
	System.out.println("Second half is " + listString(h2));
	if (empty) System.out.println("List has no head or tail");
	else {
	    System.out.println("Head is " + hd);
	    System.out.println("Tail is " + listString(tl));
	}
	System.out.println("Concatenation, again, is " +
			   listString(cat2));
    }
}
