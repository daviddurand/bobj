
package bobj;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class ReducedTerm {

    private Operation operation;

    private ReducedTerm[] subterms;

    private Variable var;

    private Sort[] retract;

    private ReducedTerm parent;

    private ReducedTerm target;   // matched an equation?

    private Module module;

    public ReducedTerm(Term term,
                       Module module) {

        this.module = module;

        this.operation = term.getTopOperation();
        if (term.subterms != null) {
            this.subterms = new ReducedTerm[term.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                this.subterms[i] = new ReducedTerm((term.subterms)[i], module);
                this.subterms[i].parent = this;
            }
        }
        this.var = term.getVariable();
        this.retract = term.getRetract();

        // handle the information about module
        Equation[] eqs = (Equation[]) (module.equations.toArray());
        HashMap<String, Vector<Equation>> op2eq = new HashMap<>();

        for (Equation eq : eqs) {
            Term left = eq.left;
            if (left.getTopOperation() != null) {
                Vector<Equation> tmp = op2eq.get(left.getTopOperation()
                                                     .getName());
                if (tmp == null)
                    tmp = new Vector<>();
                tmp.addElement(eq);
                op2eq.put(left.getTopOperation()
                              .getName(),
                          tmp);
            }
        }

        Vector<Equation> conside;
        if (this.operation != null) {
            conside = op2eq.get(this.operation.getName());
        } else {
            conside = new Vector<>();
        }

        //System.out.println("\n======== conside for term "+term);
        //System.out.println(conside);

        for (int i = 0; i < conside.size(); i++ ) {
            Equation eq = conside.elementAt(i);
            Term left = eq.left;
            Term right = eq.right;
            Term cond = eq.condition;

            HashMap<VarOrCode, Term> var2term = getMatch(term, left);

            //System.out.println("what ==== "+var2term);

            if (var2term != null) {
                for (VarOrCode var : var2term.keySet()) {
                    Term trm = var2term.get(var);
                    right = right.subst((Variable) var, trm);
                }

                //System.out.println("--------- "+right);
                this.target = new ReducedTerm(right, module);
                break;
            }

        }

    }

    private static HashMap<VarOrCode, Term> getMatch(Term term,
                                                     Term pattern) {

        //System.out.println("\n------ match -------");
        //System.out.println(term);
        //System.out.println(pattern);

        HashMap<VarOrCode, Term> result = new HashMap<>();

        if (pattern.isVariable()) {
            result.put(pattern.getVariable(), term);
        } else if (term.getTopOperation() == null) {
            return null;
        } else if (term.getTopOperation()
                       .equals(pattern.getTopOperation())) {
                           Term[] subterms = term.subterms;
                           Term[] subpatterns = pattern.subterms;
                           for (int i = 0; i < subterms.length; i++ ) {
                               Map<VarOrCode, Term> tmp = getMatch(subterms[i], subpatterns[i]);
                               if (tmp == null) {
                                   return null;
                               } else {
                                   for (VarOrCode var : tmp.keySet()) {
                                       Term trm1 = tmp.get(var);
                                       Term trm2 = result.get(var);
                                       if (trm2 == null) {
                                           result.put(var, trm1);
                                       } else if (!trm1.equals(trm2)) {
                                           return null;
                                       }
                                   }
                               }
                           }
                       } else {
                           result = null;
                       }

        return result;
    }

    public Term toTerm() {

        Term result = null;

        if (this.var != null) {
            result = new Term(this.var);
        } else {
            Term[] terms = new Term[this.subterms.length];
            for (int i = 0; i < terms.length; i++ ) {
                terms[i] = this.subterms[i].toTerm();
            }
            try {
                result = new Term(this.operation, terms);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }

        return result;
    }

    @Override
    public String toString() {
        String result = "";

        if (this.var != null) {
            result += this.var.getName();
        } else if (this.operation.isConstant()) {
            result += this.operation.getName();
        } else if (this.operation.isMixNotation()) {

            String tmp = this.operation.getName();
            int i = tmp.indexOf("_");
            int count = 0;
            while (i != -1) {
                ReducedTerm t = this.subterms[count];
                String sub = t.toString()
                              .trim();

                if (t.subterms != null) {
                    Operation op = t.operation;
                    if (op.isMixNotation() && !op.getCleanName()
                                                 .equals("==")) {
                        // this is bogus
                        if ((op.getCleanName()
                               .equals("and")
                             || this.operation.getCleanName()
                                              .equals("=="))
                            || (this.operation.getPriority() > op.getPriority())) {
                            sub = "(" + sub + ")";    // Nov.23
                        } else {
                            sub = "(" + sub + ")";
                        }
                    }
                    ;
                }
                ;

                count++ ;
                tmp = tmp.substring(0, i)
                         .trim()
                      + " " + sub + " " + tmp.substring(i + 1)
                                             .trim();
                i = tmp.indexOf("_");
            }
            ;
            result += tmp;

        } else {
            result += this.operation.getName() + "(";
            for (int i = 0; i < this.subterms.length; i++ ) {
                result += this.subterms[i].toString();
                if (i < this.subterms.length - 1) {
                    result += " , ";
                }
                ;
            }
            ;
            result += ")";
        }
        ;
        return result.trim();
    }

    public ReducedTerm getNormalForm() {

        ReducedTerm term = this;
        Redex[] redex = term.getRedex();

        while (redex != null && redex.length != 0) {
            for (Redex element : redex) {
                term = term.replaceAt(element.getPoint(), element.getTerm());
            }
            redex = term.getRedex();
        }

        return term;
    }

    public Redex[] getRedex() {
        if (this.target != null) {
            Redex[] redex =
                {
                    new Redex(this, this.target)
                };
            return redex;
        } else if (this.subterms != null && this.subterms.length != 0) {
            Vector<Redex> pool = new Vector<>();
            for (ReducedTerm subterm : this.subterms) {
                Redex[] tmp = subterm.getRedex();
                for (Redex element : tmp) {
                    pool.addElement(element);
                }
            }
            Redex[] redex = new Redex[pool.size()];
            pool.copyInto(redex);
            return redex;
        } else {
            return new Redex[0];
        }
    }

    public ReducedTerm replaceAt(ReducedTerm point,
                                 ReducedTerm term) {

        //System.out.println("\n-----------------------------");
        //System.out.println("current: "+this);
        //System.out.println("point: "+point);
        //System.out.println("target: "+term);

        if (point.parent == null) {
            System.out.println("result: " + term);
            return term;
        } else {
            ReducedTerm[] terms = point.parent.subterms;
            for (int i = 0; i < terms.length; i++ ) {
                if (terms[i] == point) {
                    terms[i] = term;
                    term.parent = point.parent;

                    point.parent.resetTarget();

                    break;
                }
            }

            // rebulit redex in the loacl area around point

            //System.out.println("result: "+this);

            return this;
        }
    }

    private void resetTarget() {

        System.out.println("\n--------- reset redex ----------");
        //System.out.println(this);

        if (this.target == null) {

            // handle the information about module
            Equation[] eqs = (Equation[]) (this.module.equations.toArray());
            HashMap<String, Vector<Equation>> op2eq = new HashMap<>();

            for (Equation eq : eqs) {
                Term left = eq.left;
                if (left.getTopOperation() != null) {
                    Vector<Equation> tmp = op2eq.get(left.getTopOperation()
                                                         .getName());
                    if (tmp == null)
                        tmp = new Vector<>();
                    tmp.addElement(eq);
                    op2eq.put(left.getTopOperation()
                                  .getName(),
                              tmp);
                }
            }

            Vector<Equation> conside = new Vector<>();
            if (this.operation != null) {
                conside = op2eq.get(this.operation.getName());
            }

            //System.out.println("\n======== conside for term "+term);
            //System.out.println(conside);

            if (conside == null) {
                conside = new Vector<>();
            }

            for (int i = 0; i < conside.size(); i++ ) {
                Equation eq = conside.elementAt(i);
                Term left = eq.left;
                Term right = eq.right;
                Term cond = eq.condition;

                HashMap<VarOrCode, Term> var2term = getMatch(this.toTerm(), left);

                //System.out.println("what ==== "+var2term);

                if (var2term != null) {
                    for (VarOrCode var : var2term.keySet()) {
                        Term trm = var2term.get(var);
                        right = right.subst((Variable) var, trm);
                    }

                    //System.out.println("find equation: "+eq);
                    //System.out.println("right: "+right);

                    this.target = new ReducedTerm(right, this.module);
                    break;
                }

            }

        }

        System.out.println("------ done ------");
    }

    class Redex {

        ReducedTerm point;

        ReducedTerm term;

        public Redex(ReducedTerm point,
                     ReducedTerm term) {
            this.point = point;
            this.term = term;
        }

        public ReducedTerm getPoint() {
            return this.point;
        }

        public ReducedTerm getTerm() {
            return this.term;
        }
    }

}
