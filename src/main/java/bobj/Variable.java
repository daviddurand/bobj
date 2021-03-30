
package bobj;

/**
 * a class representing variable in the first order term.
 *
 * @author Kai Lin
 * @version %I% %G%
 * @see Sort
 *
 */
import java.util.Map;

public class Variable
                      extends
                      VarOrCode {

    protected Sort sort;

    protected String info;

    /**
     * create a variable by the specified string and sort without information.
     *
     * @param v
     *            variable name
     * @param s
     *            sort
     * @return a variable with the specified string and sort.
     */

    public Variable(String name,
                    Sort sort) {
        super(name.trim());
        this.sort = sort;
        this.info = "no information available.";
    }

    /**
     * create a variable by the specified string and sort and information.
     *
     * @param v
     *            variable name
     * @param s
     *            sort
     * @param i
     *            information string
     * @return a variable with the specified string and sort and information.
     */
    public Variable(String name,
                    Sort sort,
                    String info) {
        super(name.trim());
        this.sort = sort;
        this.info = info;
    }

    /**
     * return the name of this variable.
     *
     */
    public String getName() {
        return this.name;
    }

    /**
     * return the sort of this variable.
     *
     */
    public Sort getSort() {
        return this.sort;
    }

    /**
     * return the sort name of this variable.
     *
     */
    public String getSortName() {
        return this.sort.getName();
    }

    /**
     * return the information of this variable.
     *
     */

    public String getInfo() {
        return this.info;
    }

    /**
     * return a string representingthis variable, and it has the form as "var N : Nat".
     *
     */
    @Override
    public String toString() {
        return "var " + this.name + " : " + this.sort.getName() + "." + this.sort.getModuleName();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Variable) {
            Variable var = (Variable) obj;
            return this.name.equals(var.name) && this.sort.equals(var.sort);
        }

        return false;
    }

    @Override
    public int hashCode() {
        return this.name.hashCode() + this.sort.hashCode();
    }

    protected Variable changeSort(Sort olds,
                                  Sort news) {
        if (this.sort.equals(olds)) {
            Variable var = new Variable(this.name, news);
            var.info = this.info;
            return var;
        } else {
            return this;
        }

    }

    protected Variable changeSortTo(Sort sort) {
        Variable var = new Variable(this.name, sort);
        var.info = this.info;
        return var;
    }

    public Variable changeModuleName(ModuleName olds,
                                     ModuleName news) {

        Variable var = new Variable(this.name, this.sort.changeModuleName(olds, news));
        var.info = this.info;
        return var;

    }

    public Variable changeAbsoluteModuleName(ModuleName olds,
                                             ModuleName news) {

        Variable var = new Variable(this.name, this.sort.changeAbsoluteModuleName(olds, news));
        var.info = this.info;
        return var;

    }

    public Variable changeParameterName(String olds,
                                        String news) {

        Variable var = new Variable(this.name, this.sort.changeParameterName(olds, news));
        var.info = this.info;
        return var;

    }

    public Variable addAnnotation(String name,
                                  Map<ModuleName, Integer> env) {
        Variable var = new Variable(this.name, this.sort.addAnnotation(name, env));
        var.info = this.info;
        return var;
    }

    public Variable removeAnnotation(String name) {
        Variable var = new Variable(this.name, this.sort.removeAnnotation(name));
        var.info = this.info;
        return var;
    }
}
