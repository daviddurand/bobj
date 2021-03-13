
package bobj;

public class IdenticalModule {

    static public Module identical = ModuleFactory.createIdentical();

    static public Operation eqOp = identical.operations.elementAt(5);

    static public Operation neqOp = identical.operations.elementAt(6);

    public static void main(String[] args) {
        System.out.println(eqOp);
    }

}
