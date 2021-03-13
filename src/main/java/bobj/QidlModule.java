
package bobj;

class QidlModule {
    static Module qidl = ModuleFactory.createQidl();

    static Sort idSort = qidl.sorts.elementAt(2);

    static Operation lessOp = qidl.operations.elementAt(10);

    public static void main(String args[]) {
        System.out.println(lessOp);
    }

}
