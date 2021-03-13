
package bobj;

import java.util.Vector;

public class ModuleExpression {

    protected String operation;

    protected Vector<ModuleExpression> subexps;

    protected String name;

    protected String rename;

    protected ModuleExpression() {
        subexps = new Vector<>();
    }

    // create an atom module expression
    public ModuleExpression(String str) {
        operation = "atom";
        name = str;
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
        rename = str;

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

        if (operation.equals("+")) {

            ModuleExpression exp1 = subexps.elementAt(0);
            ModuleExpression exp2 = subexps.elementAt(1);
            result = exp1 + " + " + exp2;

        } else if (operation.equals("||")) {

            ModuleExpression exp1 = subexps.elementAt(0);
            ModuleExpression exp2 = subexps.elementAt(1);
            result = exp1 + " || " + exp2;

        } else if (operation.equals("*")) {

            ModuleExpression exp = subexps.elementAt(0);
            result = exp + " * (" + rename + ")";

        } else if (operation.equals("[]")) {

            ModuleExpression exp = subexps.elementAt(0);
            result = exp + "[";
            for (int i = 1; i < subexps.size(); i++ ) {
                exp = subexps.elementAt(i);
                if (i != subexps.size() - 1) {
                    result += exp + ",";
                } else {
                    result += exp + "]";
                }
            }

        } else if (operation.equals("atom")) {

            result = name;

        } else {
            System.out.println("Error: you should see this");
        }

        return result;
    }

}
