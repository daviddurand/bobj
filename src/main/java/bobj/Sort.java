
package bobj;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

/**
 * The class Sort implements the sort in the first order algebra.
 *
 * @author Kai Lin
 * @version %I% %G%
 *
 */

public class Sort
                  implements ModNameSubexp, Serializable, ViewRenamable {

    /**
     * Indicates the name of this sort.
     */
    private String name;

    /**
     * Indicates the associated information.
     */
    private ModuleName mod;

    /**
     * properties.
     */
    protected Map<String, Object> props;

    /**
     * Constructs a new visible sort by using the specified string as name and using the specified
     * module name.
     *
     * @param name
     *            string
     * @param mod
     *            module name
     * @return sort using the specified strings as name and information.
     */
    public Sort(String name,
                ModuleName mod) {
        this.name = name;
        this.mod = mod;
        this.props = new HashMap<>();
        this.props.put("info", "no information available.");
    }

    /**
     * Returns the name of this sort.
     *
     */
    public String getName() {
        return this.name;
    }

    /**
     * Returns the module name of this sort.
     *
     */
    public ModuleName getModuleName() {
        return this.mod;
    }

    /**
     * Returns the information of this sort.
     *
     */
    public String getInfo() {
        return (String) this.props.get("info");
    }

    /**
     * Set the infomation as the specified string.
     *
     */
    public void setInfo(String info) {
        this.props.put("info", info);
    }

    /* set a property with the specified name */
    public void setProperty(String name,
                            Object object) {
        this.props.put(name, object);
    }

    /* get a property with the specified name */
    public Object getProperty(String name) {
        return this.props.get(name);
    }

    /* check whether this sort is initial sort */
    public boolean isInitial() {
        return false;
    }

    /* check whether this sort is hidden sort */
    public boolean isHidden() {
        return false;
    }

    /**
     * chech whether two sorts are equals
     */
    @Override
    public boolean equals(Object object) {

        if (object instanceof Sort) {
            Sort sort = (Sort) object;
            if (sort.name.equals(this.name)) {
                if (sort.mod != null && this.mod != null && sort.mod.equals(this.mod)) {
                    return true;
                } else if (sort.mod == null && this.mod == null) {
                    return true;
                } else {
                    return false;
                }

            } else {
                return false;
            }
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.name.hashCode() + ((this.mod == null) ? 0
                                                          : this.mod.hashCode());
    }

    /**
     * Modiies the sort name.
     *
     * @param s
     *            a string used as a new name
     *
     */
    protected void setName(String name) {
        this.name = name;
    }

    /**
     * Returns a string representation of this sort, and it has the form as "sort Nat".
     *
     */
    @Override
    public String toString() {
        if (this.mod == null) {
            return "sort " + this.name;
        } else {
            return "sort " + this.name + "." + this.mod;
        }
    }

    /**
     * check whether this sort is system default sort
     */
    protected boolean isDefault() {
        return this.props.get("info")
                         .equals("system-default");
    }

    protected Sort addAnnotation(String name,
                                 Map<ModuleName, Integer> env) {
        if (!isDefault()) {

            Integer aInt = env.get(this.mod);

            if (aInt != null && aInt.intValue() == 0) {
                return this;
            }

            if (this.mod.hasNotation()) {
                return this;
            }

            if (this.isInitial()) {
                return this;
            }

            Sort sort = new Sort(this.name, this.mod.addAnnotation(name));
            sort.props = this.props;
            return sort;

        } else {
            return this;
        }
    }

    protected Sort removeAnnotation(String name) {
        if (this.mod.hasNotation(name)) {
            Sort sort = new Sort(this.name, this.mod.getOriginModuleName());
            sort.props = this.props;
            return sort;
        } else {
            return this;
        }
    }

    public Sort changeModuleName(ModuleName olds,
                                 ModuleName news) {

        Sort sort = new Sort(this.name, this.mod.changeModuleName(olds, news));
        sort.props = this.props;
        return sort;

    }

    public Sort changeAbsoluteModuleName(ModuleName olds,
                                         ModuleName news) {

        Sort sort = new Sort(this.name, this.mod.changeAbsoluteModuleName(olds, news));
        sort.props = this.props;
        return sort;

    }

    public Sort changeParameterName(String from,
                                    String to) {

        Sort sort = new Sort(this.name, this.mod.changeParameterName(from, to));
        sort.props = this.props;
        return sort;

    }

}
