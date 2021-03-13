package bobj;

public class VarOrCode {

    protected Object value;

    protected String name;

    public VarOrCode(String name) {
        super();
        this.name = name;
        this.value = null;
    }

    public VarOrCode(String name,
                     Object value) {
        super();
        this.name = name;
        this.value = value;
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof VarOrCode) || obj instanceof Variable)
            return false;
        if (name.equals(((VarOrCode) obj).name))
            return true;
        else return false;
    }

    @Override
    public String toString() {
        return "Var-tag:" + name + (value == null ? ""
                                                  : " " + value.toString());
    }
}
