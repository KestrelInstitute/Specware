class FactorialTest {
    public static void main(String[] args) {
	if (args.length != 1) throw new Error("Expected 1 argument");
	int arg;
	try {
	    arg = Integer.parseInt(args[0]);
	} catch (NumberFormatException e) {
	    throw new Error("Expected integer argument");
	}
	if (arg < 0) throw new Error("Expected non-negative argument");
	boolean wrappedAround = (arg >= 13);
	int res = Primitive.fact(arg);
	System.out.print("Factorial is " + res);
	if (wrappedAround) System.out.println(" (wrapped around)");
	else System.out.println();
    }
}
