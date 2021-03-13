
package bobj;

class FloatModule {
    static Module floatt = ModuleFactory.createFloat();

    static Sort boolSort = floatt.sorts.elementAt(0);

    static Sort floatSort = floatt.sorts.elementAt(2);

    static Operation add = floatt.operations.elementAt(10);

    static Operation sub = floatt.operations.elementAt(11);

    static Operation mult = floatt.operations.elementAt(12);

    static Operation div = floatt.operations.elementAt(13);

    static Operation le = floatt.operations.elementAt(14);

    static Operation leq = floatt.operations.elementAt(15);

    static Operation gt = floatt.operations.elementAt(16);

    static Operation gte = floatt.operations.elementAt(17);

    static Operation exp = floatt.operations.elementAt(18);

    static Operation log = floatt.operations.elementAt(19);

    static Operation sqrt = floatt.operations.elementAt(20);

    static Operation abs = floatt.operations.elementAt(21);

    static Operation sin = floatt.operations.elementAt(22);

    static Operation cos = floatt.operations.elementAt(23);

    static Operation atan = floatt.operations.elementAt(24);

    static Operation pi = floatt.operations.elementAt(25);

    public static void main(String args[]) {
        System.out.println("pt = " + pi);
        System.out.println("log = " + log);
        System.out.println("gt = " + gt);
        System.out.println("div = " + div);
    }

}
