
package bobj;

import java.util.Vector;

public class Cobasis {

    protected String name;

    protected Vector<Sort> sorts;

    protected Vector<Operation> ops;

    protected Module module;

    public Cobasis(String name) {
        this.name = name;
        this.sorts = new Vector<>();
        this.ops = new Vector<>();
    }

    public String getName() {
        return this.name;
    }

    public void setModule(Module module) {
        this.module = module;
    }

    public void add(Sort sort) throws CobasisException {

        if (this.module != null) {
            if (!this.module.containsSort(sort)) {
                throw new CobasisException(sort.getName() + " not defined in module "
                                           + this.module.getModuleName());
            }
        }

        boolean found = false;
        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (sort.equals(tmp)) {
                found = true;
                break;
            }
        }

        if (!found)
            this.sorts.addElement(sort);

    }

    public void add(Operation op) throws CobasisException {

        if (this.module != null) {
            Operation opr = validFor(op);
            if (opr == null) {
                throw new CobasisException(op.name + " not defined in module "
                                           + this.module.getModuleName());
            }
        }

        boolean found = false;
        for (int i = 0; i < this.ops.size(); i++ ) {
            Operation tmp = this.ops.elementAt(i);
            if (op.equals(tmp)) {
                found = true;
                break;
            }
        }

        if (!found)
            this.ops.addElement(op);

    }

    @Override
    public String toString() {
        String result = "cobasis " + this.name + " is \n";
        for (int i = 0; i < this.sorts.size(); i++ ) {
            result += "  " + this.sorts.elementAt(i) + " .\n";
        }
        for (int i = 0; i < this.ops.size(); i++ ) {
            result += " " + this.ops.elementAt(i) + " .\n";
        }
        result += "end\n";

        return result;
    }

    public Operation[] getOperations(Module module) {

        /* Vector pool = new Vector(); for (int i=0; i<ops.size(); i++) { Operation op =
         * (Operation)ops.elementAt(i); for (int j=0; j<op.argumentSorts.length; j++) { if
         * (module.containsHiddenSort(op.argumentSorts[j])) { op.argumentSorts[j] = new
         * HiddenSort(op.argumentSorts[j]); } } if (module.containsHiddenSort(op.resultSort)) {
         * op.resultSort = new HiddenSort(op.resultSort); } pool.addElement(op); } Operation[]
         * result = new Operation[pool.size()]; pool.copyInto(result); */

        Operation[] result = new Operation[this.ops.size()];
        this.ops.copyInto(result);

        return result;

    }

    public boolean validFor(Module module,
                            Vector<Operation> cops) {

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort sort = this.sorts.elementAt(i);
            if (!module.containsSort(sort)) {
                return false;
            }
        }

        for (int i = 0; i < this.ops.size(); i++ ) {
            Operation op = this.ops.elementAt(i);
            Operation[] opers = module.getOperationsWithName(op.name);
            boolean found = false;
            for (int j = 0; j < opers.length && !found; j++ ) {
                String modname = null;
                if (op.argumentSorts.length == opers[j].argumentSorts.length) {
                    boolean same = true;
                    for (int k = 0; k < op.argumentSorts.length && same; k++ ) {
                        String s1 = op.argumentSorts[k].getName();
                        String s2 = opers[j].argumentSorts[k].getName();
                        if (modname == null) {
                            if (s1.equals(s2)) {
                                same = true;
                            } else {
                                int index = s2.indexOf(".");
                                if (index == -1) {
                                    same = false;
                                } else {
                                    modname = s2.substring(index + 1);
                                    same = s1.equals(s2.substring(0, index));
                                }
                            }
                        } else if ((s1 + "." + modname).equals(s2) || s1.equals(s2)) {
                            same = true;
                        } else {
                            same = false;
                        }
                    }

                    if (same) {
                        String s1 = op.resultSort.getName();
                        String s2 = opers[j].resultSort.getName();
                        if (modname == null) {
                            if (s1.equals(s2)) {
                                same = true;
                            } else {
                                int index = s2.indexOf(".");
                                if (index == -1) {
                                    same = false;
                                } else {
                                    modname = s2.substring(index + 1);
                                    same = s1.equals(s2.substring(0, index));
                                }
                            }
                        } else if ((s1 + "." + modname).equals(s2) || s1.equals(s2)) {
                            same = true;
                        } else {
                            same = false;
                        }
                    }

                    found = same;
                    if (same) {
                        cops.addElement(opers[j]);
                    }
                }
            }

            if (!found)
                return false;

        }

        return true;
    }

    public Operation validFor(Operation op) {

        Operation result = null;

        Operation[] opers = this.module.getOperationsWithName(op.name);
        boolean found = false;
        for (int j = 0; j < opers.length && !found; j++ ) {

            String modname = null;
            if (op.argumentSorts.length == opers[j].argumentSorts.length) {
                boolean same = true;
                for (int k = 0; k < op.argumentSorts.length && same; k++ ) {
                    String s1 = op.argumentSorts[k].getName();
                    String s2 = opers[j].argumentSorts[k].getName();
                    if (modname == null) {
                        if (s1.equals(s2)) {
                            same = true;
                        } else {
                            int index = s2.indexOf(".");
                            if (index == -1) {
                                same = false;
                            } else {
                                modname = s2.substring(index + 1);
                                same = s1.equals(s2.substring(0, index));
                            }
                        }
                    } else if ((s1 + "." + modname).equals(s2) || s1.equals(s2)) {
                        same = true;
                    } else {
                        same = false;
                    }
                }

                if (same) {
                    String s1 = op.resultSort.getName();
                    String s2 = opers[j].resultSort.getName();
                    if (modname == null) {
                        if (s1.equals(s2)) {
                            same = true;
                        } else {
                            int index = s2.indexOf(".");
                            if (index == -1) {
                                same = false;
                            } else {
                                modname = s2.substring(index + 1);
                                same = s1.equals(s2.substring(0, index));
                            }
                        }
                    } else if ((s1 + "." + modname).equals(s2) || s1.equals(s2)) {
                        same = true;
                    } else {
                        same = false;
                    }
                }

                found = same;
                if (same) {
                    result = opers[j];
                }
            }
        }

        return result;
    }

}
