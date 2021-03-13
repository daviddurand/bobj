
package bobj;

class IntModule {
    static Module imt = ModuleFactory.createInt();

    static Sort boolSort = imt.sorts.elementAt(0);

    static Sort intSort = imt.sorts.elementAt(2);

    static Sort nzintSort = imt.sorts.elementAt(3);

    static Sort natSort = imt.sorts.elementAt(4);

    static Sort zeroSort = imt.sorts.elementAt(5);

    static Sort nznatSort = imt.sorts.elementAt(6);

    static Operation trueOp = imt.operations.elementAt(0);

    static Operation falseOp = imt.operations.elementAt(1);

    static Operation zeroOp = imt.operations.elementAt(12);

}
