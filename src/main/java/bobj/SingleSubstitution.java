package bobj;

public class SingleSubstitution {

    private Variable var;

    private Term term;

    public SingleSubstitution(Variable var,
                              Term term) {
        this.var = var;
        this.term = term;
    }

    public Variable getVariable() {
        return this.var;
    }

    public Term getTerm() {
        return this.term;
    }

}
