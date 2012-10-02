class GCDTest {
    public static void main(String[] args) {
	if (args.length != 2) throw new Error("Expected 2 arguments");
	int arg1, arg2;
	try {
	    arg1 = Integer.parseInt(args[0]);
	    arg2 = Integer.parseInt(args[1]);
	} catch (NumberFormatException e) {
	    throw new Error("Expected integer arguments");
	}
	if (arg1 <= 0 || arg2 <= 0)
	    throw new Error("Expected positive arguments");
	int res = Primitive.gcd(arg1,arg2);
	System.out.println("Greatest common divisor is " + res);
    }
}
