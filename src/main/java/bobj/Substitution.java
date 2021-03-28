
package bobj;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class Substitution
                          implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    private Map<VarOrCode, Term> substs;

    public Substitution() {
        substs = new HashMap<>();
    }

    public void addSubst(Variable v,
                         Term t)
        throws SubstitutionException {

        if (!v.getSort()
              .equals(t.sort)) {
            throw new SubstitutionException();
        }

        substs = doAdd(v, t);
    }

    private Map<VarOrCode, Term> doAdd(Variable v,
                                       Term t)
        throws SubstitutionException {
        if (substs.containsKey(v))
            throw new SubstitutionException();

        Map<VarOrCode, Term> table = new HashMap<>();
        for (VarOrCode tmp : substs.keySet()) {

            Term term = substs.get(tmp);
            term = term.subst(v, t);
            table.put(tmp, term);
        }

        table.put(v, t);
        return table;
    }

    public void addSubst(Variable v,
                         Term t,
                         Signature sig)
        throws SubstitutionException {

        if (!sig.isSubsort(t.sort, v.getSort())) {
            throw new SubstitutionException();
        }

        substs = doAdd(v, t);
    }

    public void add(Substitution sub) throws SubstitutionException {

        SingleSubstitution[] all = sub.getAll();
        for (SingleSubstitution element : all) {
            Variable var = element.getVariable();
            Term term = element.getTerm();
            addSubst(var, term);
        }

    }

    public SingleSubstitution[] getAll() {

        Vector<SingleSubstitution> pool = new Vector<>();

        for (VarOrCode var : substs.keySet()) {
            Term term = substs.get(var);
            pool.addElement(new SingleSubstitution((Variable) var, term));

        }

        SingleSubstitution[] result = new SingleSubstitution[pool.size()];
        pool.copyInto(result);

        return result;
    }

    public Term get(Variable var) {

        Term result = new Term(var);

        for (VarOrCode vtmp : substs.keySet()) {
            if (var.equals(vtmp)) {
                result = substs.get(vtmp);
                return result;
            }
        }

        return result;

    }

    public boolean contains(Variable var) {
        return substs.containsKey(var);
    }

    @Override
    public String toString() {
        String result = "";
        for (VarOrCode var : substs.keySet()) {
            Term term = substs.get(var);
            if (result.equals("")) {
                result += var + " -> " + term;
            } else {
                result += ", " + var + " -> " + term;
            }
        }
        return "{" + result + "}";
    }

}
