
package bobj;

public class BoolModule {
    public static Module bool = ModuleFactory.createBool();

    public static Sort boolSort = bool.sorts.elementAt(0);

    public static Sort univSort = bool.sorts.elementAt(1);

    public static Operation trueOp = bool.operations.elementAt(0);

    public static Operation falseOp = bool.operations.elementAt(1);

    public static Operation metaEq = bool.operations.elementAt(2);

    public static Operation metaNeq = bool.operations.elementAt(3);

    public static Operation metaIf = bool.operations.elementAt(4);

    public static Operation and = bool.operations.elementAt(5);

    public static Operation or = bool.operations.elementAt(6);

    public static Operation not = bool.operations.elementAt(9);

}
