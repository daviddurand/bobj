
package bobj;

import java.util.Vector;

public class ModuleExpression {

    protected String operation;

    protected Vector<ModuleExpression> subexps;

    protected String name;

    protected String rename;

    protected ModuleExpression() {
        this.subexps = new Vector<>();
    }

    // create an atom module expression
    public ModuleExpression(String str) {
        this.operation = "atom";
        this.name = str;
    }

    // create an addition ModuleExpression
    public ModuleExpression add(ModuleExpression mexp) {
        ModuleExpression result = new ModuleExpression();
        result.operation = "+";
        result.subexps.addElement(this);
        result.subexps.addElement(mexp);

        return result;
    }

    // create an concurrent connection ModuleExpression
    public ModuleExpression concurrent(ModuleExpression mexp) {
        ModuleExpression result = new ModuleExpression();
        result.operation = "||";
        result.subexps.addElement(this);
        result.subexps.addElement(mexp);

        return result;
    }

    // create rename expression
    public ModuleExpression rename(String str) {
        ModuleExpression result = new ModuleExpression();
        result.operation = "*";
        result.subexps.addElement(this);
        this.rename = str;

        return result;
    }

    // create parameter module expression
    public ModuleExpression parameter(ModuleExpression[] paras) {
        ModuleExpression result = new ModuleExpression();
        result.operation = "[]";
        result.subexps.addElement(this);
        for (ModuleExpression element : paras) {
            result.subexps.addElement(element);
        }

        return result;

    }

    @Override
    public String toString() {
        String result = "";

        if (this.operation.equals("+")) {

            ModuleExpression exp1 = this.subexps.elementAt(0);
            ModuleExpression exp2 = this.subexps.elementAt(1);
            result = exp1 + " + " + exp2;

        } else if (this.operation.equals("||")) {

            ModuleExpression exp1 = this.subexps.elementAt(0);
            ModuleExpression exp2 = this.subexps.elementAt(1);
            result = exp1 + " || " + exp2;

        } else if (this.operation.equals("*")) {

            ModuleExpression exp = this.subexps.elementAt(0);
            result = exp + " * (" + this.rename + ")";

        } else if (this.operation.equals("[]")) {

            ModuleExpression exp = this.subexps.elementAt(0);
            result = exp + "[";
            for (int i = 1; i < this.subexps.size(); i++ ) {
                exp = this.subexps.elementAt(i);
                if (i != this.subexps.size() - 1) {
                    result += exp + ",";
                } else {
                    result += exp + "]";
                }
            }

        } else if (this.operation.equals("atom")) {

            result = this.name;

        } else {
            System.out.println("Error: you should see this");
        }

        return result;
    }

}
