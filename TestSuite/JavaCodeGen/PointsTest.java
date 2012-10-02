class PointsTest {
    static String pointString(Point p) {
	return ("[" + p.x + "," + p.y + "]");
    }
    public static void main(String[] args) {
	if (args.length != 4) throw new Error("Expected 4 arguments");
	int x1, y1, x2, y2;
	try {
	    x1 = Integer.parseInt(args[0]);
	    y1 = Integer.parseInt(args[1]);
	    x2 = Integer.parseInt(args[2]);
	    y2 = Integer.parseInt(args[3]);
	} catch (NumberFormatException e) {
	    throw new Error("Expected integer arguments");
	}
	Point p1 = new Point(x1,y1);
	Point p2 = new Point(x2,y2);
	boolean orig1 = p1.equals(Point.origin);
	boolean orig2 = p2.equals(Point.origin);
	Point sum = p1.add(p2);
	int dist = p1.square_distance(p2);
	if (orig1) System.out.println("First point is origin");
	else System.out.println("First point is not origin");
	if (orig2) System.out.println("Second point is origin");
	else System.out.println("Second point is not origin");
	System.out.println("Sum of points is " + pointString(sum));
	System.out.println("Square distance is " + dist);
    }
}
