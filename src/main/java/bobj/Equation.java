
package bobj;

import java.io.Serializable;
import java.util.Map;

public class Equation
                      implements Serializable {

    protected Term left;

    protected Term right;

    protected Term condition;

    protected String info;

    protected String name;

    static boolean debug = false;

    public Equation(Term l,
                    Term r) {
        this.left = l;
        this.right = r;
        this.info = "";
    }

    public Equation(Term c,
                    Term l,
                    Term r) {
        this.condition = c;
        this.left = l;
        this.right = r;
        this.info = "";
    }

    @Override
    public boolean equals(Object obj) {

        if (debug) {
            System.out.println("------------equation equals --------------");
            System.out.println(this + "     " + obj);
        }

        if (!(obj instanceof Equation)) {
            if (debug)
                System.out.println(this + "     Nope!");
            return false;
        }

        Equation eq = (Equation) obj;
        if (this.left.equals(eq.left) && this.right.equals(eq.right)) {

            if (debug) {
                System.out.println("-------------------");
                System.out.println("yes. they are same");
                System.out.println("-------------------");
                System.out.println(this.condition);
                System.out.println(eq.condition);
            }

            if (isConditional() && eq.isConditional() && this.condition.equals(eq.condition)) {
                return true;
            } else if (!isConditional() && !eq.isConditional()) {
                return true;
            }
        }

        // try a new method
        /* HashMap map = new HashMap(); if (left.shift().equals(eq.left, map) &&
         * right.shift().equals(eq.right, map)) {
         *
         * if (debug) { System.out.println("-------------------");
         * System.out.println("yes again. they are same again");
         * System.out.println("-------------------"); System.out.println(this.condition);
         * System.out.println(eq.condition); System.out.println(map); }
         *
         * if (isConditional() && eq.isConditional() && condition.equals(eq.condition, map)) {
         *
         * System.out.println("bbb: "+this+"  \n      "+eq );
         *
         * return true; } else if (!isConditional() && !eq.isConditional()) { return true; } } */
        if (debug)
            System.out.println(this + "     Nope!");
        return false;
    }

    @Override
    public int hashCode() {
        return this.left.hashCode() + this.right.hashCode()
               + (isConditional() ? this.condition.hashCode()
                                  : 0);
    }

    public boolean isConditional() {
        return(this.condition != null);
    }

    public void setInfo(String info) {
        this.info = info;
    }

    public String getInfo() {
        return this.info;
    }

    @Override
    public String toString() {

        String result = "";

        if (this.name != null) {
            result += "[" + this.name + "] ";
        }

        if (isConditional()) {
            result += "cq " + this.left + " = " + this.right + " if " + this.condition;
        } else {
            result += "eq " + this.left + " = " + this.right;
        }

        return result;

    }

    public Equation subst(Signature sig,
                          Variable var,
                          Term term) {

        Term c = null;
        if (this.condition != null) {
            c = this.condition.subst(sig, var, term);
        }
        Term l = this.left.subst(sig, var, term);
        Term r = this.right.subst(sig, var, term);

        Equation eq = new Equation(c, l, r);
        if (this.name != null) {
            eq.name = this.name;
        }
        return eq;

    }

    public Equation subst(Variable var,
                          Term term) {

        Term c = null;
        if (this.condition != null) {
            c = this.condition.subst(var, term);
        }
        Term l = this.left.subst(var, term);
        Term r = this.right.subst(var, term);

        Equation eq = new Equation(c, l, r);
        if (this.name != null) {
            eq.name = this.name;
        }
        return eq;

    }

    public Equation addAnnotation(String name,
                                  Signature sig,
                                  Map<ModuleName, Integer> env) {

        Term l = this.left.addAnnotation(name, sig, env);
        Term r = this.right.addAnnotation(name, sig, env);
        if (this.condition != null) {
            Term c = this.condition.addAnnotation(name, sig, env);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation removeAnnotation(String name,
                                     Signature sig) {

        Term l = this.left.removeAnnotation(name, sig);
        Term r = this.right.removeAnnotation(name, sig);
        if (this.condition != null) {
            Term c = this.condition.removeAnnotation(name, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation changeSort(Sort olds,
                               Sort news,
                               Signature sig) {

        Term l = this.left.changeSort(olds, news, sig);
        Term r = this.right.changeSort(olds, news, sig);
        if (this.condition != null) {
            Term c = this.condition.changeSort(olds, news, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation changeModuleName(ModuleName olds,
                                     ModuleName news,
                                     Signature sig) {

        Term l = this.left.changeModuleName(olds, news, sig);
        Term r = this.right.changeModuleName(olds, news, sig);
        if (this.condition != null) {
            Term c = this.condition.changeModuleName(olds, news, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation changeAbsoluteModuleName(ModuleName olds,
                                             ModuleName news,
                                             Signature sig) {

        Term l = this.left.changeAbsoluteModuleName(olds, news, sig);
        Term r = this.right.changeAbsoluteModuleName(olds, news, sig);
        if (this.condition != null) {
            Term c = this.condition.changeAbsoluteModuleName(olds, news, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation changeParameterName(String olds,
                                        String news,
                                        Signature sig) {

        Term l = this.left.changeParameterName(olds, news, sig);
        Term r = this.right.changeParameterName(olds, news, sig);
        if (this.condition != null) {
            Term c = this.condition.changeParameterName(olds, news, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation replaceOperationName(String oldname,
                                         String newname,
                                         Signature sig) {

        Term l = this.left.replaceOperationName(oldname, newname, sig);
        Term r = this.right.replaceOperationName(oldname, newname, sig);
        if (this.condition != null) {
            Term c = this.condition.replaceOperationName(oldname, newname, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public Equation changeOperation(Operation from,
                                    Operation to,
                                    Signature sig) {

        Term l = this.left.changeOperation(from, to, sig);
        Term r = this.right.changeOperation(from, to, sig);
        if (this.condition != null) {
            Term c = this.condition.changeOperation(from, to, sig);
            Equation eq = new Equation(c, l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;

        } else {
            Equation eq = new Equation(l, r);
            if (this.name != null) {
                eq.name = this.name;
            }
            eq.info = this.info;
            return eq;
        }

    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return this.name;
    }

}
