
package bobj;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

public class RewriteEngine {

    private Signature sig;

    private HashMap<String, Vector<Equation>> op2eq;

    private ArrayList<Equation> retracts;

    private ArrayList<Equation> varRules;

    private Term left;

    private Term right;

    static boolean trace = false;

    public static boolean turnoff2Eq = false;

    public static boolean turnoff3Eq = false;

    static boolean debug = false;

    static boolean debug_match = false;

    static boolean disable_cache = false;

    static HashMap<String, Term> cache = new HashMap<>();

    static Vector<String> hit = new Vector<>();

    static long size = 0;

    static Map<String, String> map = new HashMap<>();

    boolean nontermination = false;

    public RewriteEngine(Module module) {
        if (debug)
            System.err.println("Created new Engine for " + module.getModuleName());
        this.sig = module;
        this.retracts = new ArrayList<>();
        this.varRules = new ArrayList<>();

        this.op2eq = new HashMap<>();
        for (int i = 0; i < module.equations.size(); i++ ) {
            Equation eq = (module.equations.get(i));

            if (module.mask.contains(eq)) {
                continue;
            }

            Term left = eq.left;
            Operation op = left.getTopOperation();
            if (op != null) {
                String opName = op.getName();
                Vector<Equation> vec = op2eq.get(opName);
                if (vec == null) {
                    vec = new Vector<>();
                }
                vec.addElement(eq);
                op2eq.put(opName, vec);

                if (op.info.equals("system-retract")) {
                    retracts.add(eq);
                }

            } else {

                varRules.add(eq);

            }

        }
        module.engine = this;

    }

    public static void cleanCache() {
        if (debug)
            System.err.println("Cleared cache.");
        cache = new HashMap<>();
        hit = new Vector<>();
        size = 0;
        map.clear();
    }

    private void resort(Term input) {

        // try to find a rule as r:s1>s2(term) = ~setsort~(...) if
        // where s2 is not supersort of input.sort
        //       s1 is a supersort of input.sort

        for (Equation retEq : retracts) {

            String opname = retEq.left.operation.name.trim();
            opname = opname.substring(2);
            int p = opname.indexOf(">");
            String superName = opname.substring(0, p);
            String subname = opname.substring(p + 1);
            p = subname.indexOf("(");
            subname = subname.substring(0, p);

            Sort[] s1 = sig.getSortsByName(superName);
            Sort[] s2 = sig.getSortsByName(subname);

            Term left = retEq.left.subterms[0];
            if (!sig.isSubsort(input.sort, s2[0]) && sig.isSubsort(input.sort, s1[0])
                && left.var != null) {

                Term pattern = retEq.left.subterms[0];
                Map<VarOrCode, Term> ht = getMatch(input, pattern);

                Term cond = retEq.condition.subst(ht, sig);
                cond = reduce(cond);

                if (cond.operation.equals(BoolModule.trueOp)) {
                    input.sort = s2[0];
                }
            }
        }

    }

    public Term reduce(Term term) {

        Term result = term;
        String index = term.toString();
        boolean flag = false;
        if (debug)
            System.err.println("Reduce: " + term);

        if (!disable_cache && cache.containsKey(index)) {
            result = cache.get(index);

            Sort s1 = result.sort;
            Sort s2 = term.sort;
            if (s1.equals(s2) || sig.less(s1, s2) || sig.less(s2, s1)) {

                hit.removeElement(index);
                hit.addElement(index);
                result.parent = null;

            } else {
                result = term;
            }

        }

        Redex redex = getRedex(result, -1);

        if (redex == null) {
            redex = getSpecialRedex(result, -1);
        } else {
            flag = true;
        }

        if (redex == null) {
            result = simplifyBuiltin(result);
            redex = getRedex(result, -1);
            if (redex == null) {
                redex = getSpecialRedex(result, -1);
            } else {
                flag = true;
            }
        } else {
            flag = true;
        }

        while (redex != null) {

            result = reduce(result, redex);
            resort(result);

            redex = getRedex(result, -1);

            if (redex == null) {
                redex = getSpecialRedex(result, -1);
            }

            if (redex == null) {
                result = simplifyBuiltin(result);
                redex = getRedex(result, -1);
                if (redex == null) {
                    redex = getSpecialRedex(result, -1);
                }
            }
        }

        if (!disable_cache && flag && result != null) {
            if (size > 100000) {
                // remove the first 100 elements
                for (int i = 0; i < 100 && i < hit.size(); i++ ) {
                    String key = hit.elementAt(0);
                    Term element = cache.get(key);
                    cache.remove(key);
                    hit.removeElementAt(0);
                    size = size - element.toString()
                                         .length();
                }
            }

            if (index.length() < 300) {
                cache.put(index, result);
                hit.insertElementAt(index, 0);
                size += result.toString()
                              .length();
            }
        }
        if (debug)
            System.err.println("Reduced " + term + " ==>  " + result);

        return result;
    }

    private Term simplifyBuiltin(Term term) {

        Module imt = IntModule.imt;
        Module floatModule = FloatModule.floatt;

        Sort inte = IntModule.intSort;
        Sort nat = IntModule.natSort;
        Sort nznat = IntModule.nznatSort;

        Operation t = IntModule.trueOp;
        Operation f = IntModule.falseOp;
        Operation natZero = IntModule.zeroOp;

        Sort floatt = FloatModule.floatSort;

        if (!sig.containsSystemSort(nat) && !sig.containsSystemSort(inte)
            && !sig.containsSystemSort(floatt) && !sig.containsSystemOperation(QidlModule.lessOp)
            && !term.hasRetract) {
            return term;
        }

        if (term.isVariable()) {
            return term;
        }

        Term[] terms = new Term[term.subterms.length];
        for (int i = 0; i < terms.length; i++ ) {
            terms[i] = simplifyBuiltin(term.subterms[i]);
        }

        int index = imt.operations.indexOf(term.operation);

        if (index == -1) {

            try {

                index = floatModule.operations.indexOf(term.operation);
                if (index != -1) {

                    return simplifyFloat(term, index, terms);

                } else if (term.operation.equals(QidlModule.lessOp)
                           && term.operation.info.equals("system-default")) {

                               if (terms[0].isConstant() && terms[1].isConstant()) {
                                   String s1 = terms[0].operation.name;
                                   String s2 = terms[1].operation.name;
                                   if (s1.compareTo(s2) < 0) {
                                       return new Term(sig, t);
                                   } else {
                                       return new Term(sig, f);
                                   }
                               }

                           } else
                    if (term.operation.info.equals("system-retract")) {

                        Sort superSort = term.operation.argumentSorts[0];
                        Sort subSort = term.operation.resultSort;

                        if (sig.isSubsort(term.subterms[0].sort, subSort)) {
                            return term.subterms[0];
                        } else if (sig.isSubsort(term.subterms[0].sort, superSort)
                                   && term.parent != null) {
                                       for (int i = 0; i < term.parent.subterms.length; i++ ) {
                                           if (term.parent.subterms[i] == term) {
                                               if (term.parent.operation != null
                                                   && term.parent.operation.argumentSorts[i].equals(subSort)) {
                                                   return term.subterms[0];
                                               }
                                               break;
                                           }
                                       }
                                   }
                    }

                Term result = new Term(sig, term.operation, terms);

                if (sig.isSubsort(term.sort, result.sort)
                    || !sig.isSubsort(result.sort, term.sort)) {
                    result.sort = term.sort;
                }

                return result;

            } catch (Exception e) {
            }

        } else {

            try {
                switch (index) {
                    case 10:  // _+_ : NzNat NzNat -> NzNat

                        Vector<Term> vec = term.getAssocSubterms(sig, term.operation);
                        Vector<Term> termlist = new Vector<>();

                        // for calculating known values
                        int val = 0;

                        for (int i = 0; i < vec.size(); i++ ) {
                            Term subterm = vec.elementAt(i);
                            subterm = simplifyBuiltin(subterm);
                            if (subterm.isConstant()) {
                                try {
                                    int v = Integer.parseInt(subterm.toString());

                                    if (v > 0) {
                                        val += v;
                                    } else {
                                        termlist.addElement(subterm);
                                    }

                                } catch (Exception e) {
                                    termlist.addElement(subterm);
                                }
                            } else {
                                termlist.addElement(subterm);
                            }

                        }

                        return getTermForInt(termlist, val, term.operation);

                    case 11:  // s_  : NzNat -> NzNat

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            if (v > 0) {
                                v++ ;
                                return getTermForInt(v);
                            }
                        }
                    break;

                    case 12:  // 0   : -> Zero
                    break;

                    case 13:  // s_  : Nat -> NzNat

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            if (v >= 0) {
                                v++ ;
                                return getTermForInt(v);
                            }
                        }
                    break;

                    case 14:  // p_  : NzNat -> Nat

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            if (v > 1) {
                                v-- ;
                                return getTermForInt(v);
                            } else if (v == 1) {
                                return new Term(sig, natZero);
                            }
                        }
                    break;

                    case 15:  // >   : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 > v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 16:  // <   : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 < v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 17:  // <=  : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 <= v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 18:  // >=  : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 >= v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 19:  // _+_ : Nat Nat -> Nat

                        vec = term.getAssocSubterms(sig, term.operation);
                        termlist = new Vector<>();

                        // for calculating known values
                        val = 0;

                        for (int i = 0; i < vec.size(); i++ ) {
                            Term subterm = vec.elementAt(i);
                            subterm = simplifyBuiltin(subterm);
                            if (subterm.isConstant()) {
                                try {
                                    int v = Integer.parseInt(subterm.toString());
                                    val += v;
                                } catch (Exception e) {
                                    termlist.addElement(subterm);
                                }
                            } else {
                                termlist.addElement(subterm);
                            }

                        }

                        return getTermForInt(termlist, val, term.operation);

                    case 20:  // _*_ : Nat Nat -> Nat

                        vec = term.getAssocSubterms(sig, term.operation);
                        termlist = new Vector<>();

                        // for calculating known values
                        val = 1;

                        for (int i = 0; i < vec.size(); i++ ) {
                            Term subterm = vec.elementAt(i);
                            subterm = simplifyBuiltin(subterm);

                            if (subterm.isConstant()) {
                                try {
                                    int v = Integer.parseInt(subterm.toString());
                                    if (v >= 0) {
                                        val *= v;
                                    } else {
                                        termlist.addElement(subterm);
                                    }
                                } catch (Exception e) {
                                    termlist.addElement(subterm);
                                }
                            } else {
                                termlist.addElement(subterm);
                            }
                        }

                        if (val == 1) {
                            if (termlist.isEmpty()) {
                                Operation op = new Operation(String.valueOf(val), nznat,
                                                             nznat.getModuleName());

                                return new Term(op);
                            } else {
                                return getTermForInt(termlist, term.operation);
                            }
                        } else if (val == 0) {
                            return getTermForInt(val);
                        } else {
                            return getTermForInt(termlist, val, term.operation);
                        }

                    case 21:  // div : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v2 % v1 == 0) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 22:  // eq  : Nat Nat -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 == v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 23:  // - _ : Int -> Int

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            v = -v;
                            return getTermForInt(v);
                        }
                    break;

                    case 24:  // s _ : Int -> Int

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            v++ ;
                            return getTermForInt(v);
                        }
                    break;

                    case 25:  // p _ : Int -> Int

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            v-- ;
                            return getTermForInt(v);
                        }
                    break;

                    case 26:  // - _ : NzInt -> NzInt

                        if (terms[0].isConstant()) {
                            int v = Integer.parseInt(terms[0].toString());
                            if (v != 0) {
                                v = -v;
                                return getTermForInt(v);
                            }
                        }
                    break;

                    case 27:  // _+_ : Int Int -> Int

                        vec = term.getAssocSubterms(sig, term.operation);
                        termlist = new Vector<>();

                        // for calculating known values
                        val = 0;

                        for (int i = 0; i < vec.size(); i++ ) {
                            Term subterm = vec.elementAt(i);
                            subterm = simplifyBuiltin(subterm);
                            if (subterm.isConstant()) {
                                try {
                                    int v = Integer.parseInt(subterm.toString());
                                    val += v;
                                } catch (Exception e) {
                                    termlist.addElement(subterm);
                                }
                            } else {
                                termlist.addElement(subterm);
                            }

                        }

                        return getTermForInt(termlist, val, term.operation);

                    case 28:  // _-_ : Int Int -> Int

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            int v = v1 - v2;
                            return getTermForInt(v);
                        }
                    break;

                    case 29:  // _*_ : Int Int -> Int

                        vec = term.getAssocSubterms(sig, term.operation);
                        termlist = new Vector<>();

                        // for calculating known values
                        val = 1;

                        for (int i = 0; i < vec.size(); i++ ) {
                            Term subterm = vec.elementAt(i);
                            subterm = simplifyBuiltin(subterm);
                            if (subterm.isConstant()) {
                                try {
                                    int v = Integer.parseInt(subterm.toString());
                                    val *= v;
                                } catch (Exception e) {
                                    termlist.addElement(subterm);
                                }
                            } else {
                                termlist.addElement(subterm);
                            }

                        }

                        if (val == 1) {
                            if (termlist.isEmpty()) {
                                Operation op = new Operation(String.valueOf(val), nznat,
                                                             nznat.getModuleName());

                                return new Term(op);
                            } else {
                                return getTermForInt(termlist, term.operation);
                            }
                        } else if (val == 0) {
                            return getTermForInt(val);
                        } else {
                            return getTermForInt(termlist, val, term.operation);
                        }

                    case 30:  // _<_ : Int Int -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 < v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 31:  // _<=_ : Int Int -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 <= v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 32:  // _>_ : Int Int -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 > v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 33:  // _>=_ : Int Int -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v1 >= v2) {
                                return new Term(sig, t);
                            } else {
                                return new Term(sig, f);
                            }
                        }
                    break;

                    case 34:  // quo : Int Int -> Int

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v2 != 0) {
                                int v = v1 / v2;
                                return getTermForInt(v);
                            }
                        }
                    break;

                    case 35:  // rem : Int Int -> Int

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v2 != 0) {
                                int v = v1 % v2;
                                return getTermForInt(v);
                            }
                        }
                    break;

                    case 36:  // div : Int Int -> Bool

                        if (terms[0].isConstant() && terms[1].isConstant()) {
                            int v1 = Integer.parseInt(terms[0].toString());
                            int v2 = Integer.parseInt(terms[1].toString());
                            if (v2 != 0) {
                                int v = v1 % v2;
                                if (v == 0) {
                                    return new Term(sig, t);
                                } else {
                                    return new Term(sig, f);
                                }
                            }
                        }
                    break;

                    default:
                }
            } catch (Exception e) {
            }
        }

        try {
            return new Term(sig, term.operation, terms);
        } catch (Exception e) {
            return term;
        }

    }

    private Term simplifyFloat(Term term,
                               int index,
                               Term[] terms) {

        Operation t = BoolModule.trueOp;
        Operation f = BoolModule.falseOp;

        try {

            switch (index) {

                case 10:  // add

                    Vector<Term> vec = term.getAssocSubterms(sig, term.operation);
                    Vector<Term> termlist = new Vector<>();

                    // for calculating known values
                    double val = 0;

                    for (int i = 0; i < vec.size(); i++ ) {
                        Term subterm = vec.elementAt(i);
                        subterm = simplifyBuiltin(subterm);
                        if (subterm.isConstant()) {
                            try {
                                double v = Double.parseDouble(subterm.toString());
                                val += v;
                            } catch (Exception e) {
                                termlist.addElement(subterm);
                            }
                        } else {
                            termlist.addElement(subterm);
                        }

                    }

                    if (val == 0) {
                        return getTermForFloat(termlist, term.operation);
                    } else {
                        return getTermForFloat(termlist, val, term.operation);
                    }

                case 11:  // sub
                    vec = term.getAssocSubterms(sig, term.operation);
                    termlist = new Vector<>();

                    // for calculating known values
                    val = 0;

                    for (int i = 0; i < vec.size(); i++ ) {
                        Term subterm = vec.elementAt(i);
                        subterm = simplifyBuiltin(subterm);
                        if (subterm.isConstant()) {
                            try {
                                double v = Double.parseDouble(subterm.toString());
                                if (i == 0) {
                                    val = v;
                                } else {
                                    val = val - v;
                                }

                            } catch (Exception e) {
                                termlist.addElement(subterm);
                            }
                        } else {
                            termlist.addElement(subterm);
                        }

                    }

                    if (val == 0) {
                        return getTermForFloat(termlist, term.operation);
                    } else {
                        return getTermForFloat(termlist, val, term.operation);
                    }

                case 12:  // mult

                    vec = term.getAssocSubterms(sig, term.operation);
                    termlist = new Vector<>();

                    // for calculating known values
                    val = 1;

                    for (int i = 0; i < vec.size(); i++ ) {
                        Term subterm = vec.elementAt(i);
                        subterm = simplifyBuiltin(subterm);
                        if (subterm.isConstant()) {
                            try {
                                double v = Double.parseDouble(subterm.toString());
                                val *= v;
                            } catch (Exception e) {
                                termlist.addElement(subterm);
                            }
                        } else {
                            termlist.addElement(subterm);
                        }

                    }

                    if (val == 0) {
                        return getTermForFloat(0);
                    } else if (val == 1) {
                        return getTermForFloat(termlist, term.operation);
                    } else {
                        return getTermForFloat(termlist, val, term.operation);
                    }

                case 13:  // div

                    double v1 = 0, v2 = 0;
                    boolean b1 = true, b2 = true;

                    if (terms[0].isConstant() && terms[1].isConstant()) {
                        try {
                            v1 = Double.parseDouble(terms[0].toString());
                        } catch (Exception e) {
                            b1 = false;
                        }

                        try {
                            v2 = Double.parseDouble(terms[1].toString());
                        } catch (Exception e) {
                            b2 = false;
                        }

                        if (b1 && b2 && v2 != 0) {
                            return getTermForFloat(v1 / v2);
                        } else if (b2 && v2 == 1) {
                            return terms[0];
                        }

                    }

                break;
                case 14:  // le

                    if (terms[0].isConstant() && terms[1].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        v2 = Double.parseDouble(terms[1].toString());
                        if (v1 < v2) {
                            return new Term(sig, t);
                        } else {
                            return new Term(sig, f);
                        }
                    }

                break;
                case 15:  // leq

                    if (terms[0].isConstant() && terms[1].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        v2 = Double.parseDouble(terms[1].toString());
                        if (v1 <= v2) {
                            return new Term(sig, t);
                        } else {
                            return new Term(sig, f);
                        }
                    }

                break;
                case 16:  // gt

                    if (terms[0].isConstant() && terms[1].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        v2 = Double.parseDouble(terms[1].toString());
                        if (v1 > v2) {
                            return new Term(sig, t);
                        } else {
                            return new Term(sig, f);
                        }
                    }

                break;
                case 17:  // gte

                    if (terms[0].isConstant() && terms[1].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        v2 = Double.parseDouble(terms[1].toString());
                        if (v1 >= v2) {
                            return new Term(sig, t);
                        } else {
                            return new Term(sig, f);
                        }
                    }

                break;

                case 18:  // exp

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.exp(v1));
                    }

                break;
                case 19:  // log

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.log(v1));
                    }

                break;
                case 20:  // sqrt

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.sqrt(v1));
                    }

                break;
                case 21:  // abs

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.abs(v1));
                    }

                break;
                case 22:  // sin

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.sin(v1));
                    }

                break;
                case 23:  // cos

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.cos(v1));
                    }

                break;
                case 24:  // atan

                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(Math.atan(v1));
                    }

                break;
                case 25:  // pi
                    return getTermForFloat(Math.PI);

                case 26:  // unary subtract
                    if (terms[0].isConstant()) {
                        v1 = Double.parseDouble(terms[0].toString());
                        return getTermForFloat(-v1);
                    }

                default:
            }

        } catch (Exception e) {
        }

        return term;
    }

    private Redex getRedex(Term input,
                           int pos) {

        Sort bool = BoolModule.boolSort;
        Operation t = BoolModule.trueOp;
        Operation f = BoolModule.falseOp;
        Operation metaEq = BoolModule.metaEq;
        Operation metaNeq = BoolModule.metaNeq;

        Redex result = null;

        if (input.nocheck || input.nogcheck) {
            return null;
        }

        if (input.var != null) {
            return null;
        }

        if (input.operation.equals(metaEq)) {

            Term term0 = input.subterms[0];
            term0 = localCopy(term0);
            term0 = reduce(term0);

            Term term1 = input.subterms[1];
            term1 = localCopy(term1);
            term1 = reduce(term1);

            try {

                if (term0.equals(sig, term1)) {
                    result = new Redex(input, new Term(t));
                } else if (turnoff2Eq && term0.isGround() && term1.isGround()) {
                    return null;
                } else if (!turnoff2Eq || (term0.isGround() && term1.isGround())) {
                    result = new Redex(input, new Term(f, new Term[0]));
                    left = term0;
                    right = term1;
                } else if (term0.sort.equals(bool)) {
                    if (turnoff3Eq) {
                        return null;
                    } else {
                        result = new Redex(input, new Term(f));
                    }

                } else if (term0.equals(input.subterms[0]) && term1.equals(input.subterms[1])) {
                    return null;
                } else {
                    result = new Redex(input, new Term(sig, input.operation, term0, term1));
                }

                result.position = pos;
                return result;

            } catch (Exception e) {
            }

        } else if (input.operation.equals(metaNeq)) {

            Term term0 = localCopy(input.subterms[0]);
            term0 = reduce(term0);
            Term term1 = localCopy(input.subterms[1]);
            term1 = reduce(term1);
            try {

                if (term0.equals(term1)) {
                    result = new Redex(input, new Term(f));
                } else if (!turnoff2Eq || (term0.isGround() && term1.isGround())) {

                    result = new Redex(input, new Term(t));

                } else {
                    return null;
                }

                result.position = pos;
                return result;

            } catch (Exception e) {
            }

        } else if (input.operation.equals(IdenticalModule.eqOp)) {

            try {
                if (input.subterms[0].equals(input.subterms[1])) {
                    result = new Redex(input, new Term(t));
                } else {
                    result = new Redex(input, new Term(f));
                }
                result.position = pos;
                return result;
            } catch (Exception e) {
            }

        } else if (input.operation.equals(IdenticalModule.neqOp)) {

            try {
                if (input.subterms[0].equals(input.subterms[1])) {
                    result = new Redex(input, new Term(f));
                } else {
                    result = new Redex(input, new Term(t));
                }
                result.position = pos;
                return result;
            } catch (Exception e) {
            }

        } else if (input.operation.equals(BOBJModule.getSortOperation())
                   && input.operation.info.equals("system-default")) {

                       try {

                           Operation op =
                               new Operation("'" + input.subterms[0].sort.getName(),
                                             QidlModule.idSort, QidlModule.idSort.getModuleName());

                           Term res = new Term(op);
                           result = new Redex(input, res);
                           result.position = pos;
                           return result;
                       } catch (Exception e) {
                       }

                   } else
            if (input.operation.equals(BOBJModule.getFinalSortOperation())
                && input.operation.info.equals("system-default")) {

                    try {

                        Term tmp = input.subterms[0];
                        tmp = reduce(tmp);
                        Operation op = new Operation("'" + tmp.sort.getName(), QidlModule.idSort,
                                                     QidlModule.idSort.getModuleName());

                        Term res = new Term(op);
                        result = new Redex(input, res);
                        result.position = pos;
                        return result;
                    } catch (Exception e) {
                    }

                } else if (input.operation.equals(BOBJModule.getSetsortOperation())
                           && input.operation.info.equals("system-default")) {

                               try {

                                   Term[] tmp = input.subterms;
                                   Term res = tmp[1].copy();

                                   String sortName = tmp[0].operation.name;
                                   Sort[] sorts = sig.getSortsByName(sortName);

                                   if (sorts.length > 0) {
                                       // sorts[0] must be a part of result.sort
                                       if (sig.isSubsort(res.sort, sorts[0])) {
                                           // do nothing
                                       } else if (sig.isSubsort(sorts[0], res.sort)
                                                  || (sig.canApply(sorts[0], res.sort) != null)
                                                  || sig.hasCommonSupersort(sorts[0], res.sort)) {
                                                      res.sort = sorts[0];
                                                  }
                                   }

                                   result = new Redex(input, res);
                                   result.position = pos;
                                   return result;

                               } catch (Exception e) {
                               }

                           }

        if (input.sort.isHidden()) {

            Term term = input.parent;
            while (term != null && term.sort.isHidden()) {
                if (term.operation.isBehavorial()) {
                    term = term.parent;
                } else {
                    for (int i = 0; i < input.subterms.length && result == null; i++ ) {

                        if (input.subterms[i].var == null)
                            result = getRedex(input.subterms[i], i);
                    }

                    if (result == null) {
                        input.nogcheck = true;
                    }

                    return result;
                }
            }
        }

        boolean ahead = input.operation.strategy == null;
        if (input.operation.strategy != null) {

            for (int element : input.operation.strategy) {
                int position = element - 1;
                if (position < -1) {

                    // do nothing

                } else if (position == -1) {

                    ahead = true;
                    break;

                } else if (position < input.operation.getArity()) {

                    if (input.subterms[position].var == null) {

                        // for unknown reason, add the next line
                        input.subterms[position].parent = input;
                        result = getRedex(input.subterms[position], position);

                        if (result != null) {
                            return result;
                        }

                    }

                } else {
                    // ignore it
                }
            }

        }

        if (!ahead) {
            return null;
        }

        Vector<Equation> conside = new Vector<>();
        if (input.operation != null) {
            conside = op2eq.get(input.operation.getName());
        }

        if (conside == null) {
            conside = new Vector<>();
        }

        conside.addAll(retracts);
        conside.addAll(varRules);

        for (int i = 0; i < conside.size(); i++ ) {

            Equation eq = conside.elementAt(i);
            Term left = eq.left;
            Term right = eq.right.copy(sig);
            Term cond = eq.condition;
            Map<VarOrCode, Term> var2term = getMatch(input, left);

            if (var2term != null) {

                /* System.out.println("\n------- get redex ------- ");
                 * System.out.println("input = "+input);
                 * System.out.println("---------------------------"); System.out.println(eq);
                 * System.out.println("var2term = "+var2term); System.out.println(""); */

                if (cond != null) {

                    Term tmp = cond.subst(var2term, sig);
                    tmp = reduce(tmp.copy(sig));

                    int res = boolValue(tmp);
                    if (res != 1) {
                        continue;
                    }
                }

                right = right.subst(var2term, sig);
                if (right == null)
                    continue;
                Sort sort = right.sort;

                if (right.operation != null) {
                    try {
                        Term tmp = right;
                        right = getMinimumTerm(sig, right.operation, right.subterms);

                        if (right == null) {
                            right = new Term(sig, tmp.operation, tmp.subterms);
                        }

                        if (sig.isSubsort(sort, right.sort) || !sig.isSubsort(right.sort, sort)) {
                            right.sort = sort;
                        }

                    } catch (Exception ex) {
                    }
                }

                if (right.equals(input) && right.sort.equals(input.sort)) {

                    nontermination = true;
                    if (!turnoff2Eq && trace) {

                        System.out.println("warning: non-termination " + "corrected");
                        System.out.println("rewrite target: " + input);

                        if (eq.name != null) {
                            System.out.println("use: " + eq.toString()
                                                           .trim());
                        } else {
                            System.out.println("use: " + eq.toString()
                                                           .substring(3)
                                                           .trim());
                        }

                        System.out.println("result: " + right);
                        System.out.println("take " + right + " as normal form");
                        System.out.println("................................");
                    }

                    continue;

                } else if (map.containsKey(right.toString())) {

                    String data = map.get(right.toString());
                    if (data != null && data.trim()
                                            .equals(input.toString()
                                                         .trim())) {

                        nontermination = true;
                        resort(input);

                        if (!turnoff2Eq && trace) {

                            System.out.println("warning: non-termination " + "corrected");
                            System.out.println("rewrite target: " + input);

                            if (eq.name != null) {
                                System.out.println("use: " + eq.toString()
                                                               .trim());
                            } else {
                                System.out.println("use: " + eq.toString()
                                                               .substring(3)
                                                               .trim());
                            }

                            System.out.println("result: " + right);
                            System.out.println(right + " is already rewritten to " + input + ", "
                                               + "take " + input + " as normal form");

                            System.out.println("................." + "...............");
                        }

                        continue;
                    }
                }

                if (trace && !turnoff2Eq) {
                    System.out.println("rewrite target: " + input);

                    if (eq.name != null) {
                        System.out.println("use: " + eq.toString()
                                                       .trim());
                    } else {
                        System.out.println("use: " + eq.toString()
                                                       .substring(3)
                                                       .trim());
                    }

                    System.out.println("result: " + right);
                    System.out.println("................................");
                }

                if (map.size() > 2) {
                    map.clear();
                }
                map.put(input.toString()
                             .trim(),
                        right.toString()
                             .trim());

                sort = right.sort;
                Term tmp = reduce(right);

                if (sig.less(sort, tmp.sort)) {
                    tmp.sort = sort;
                }

                result = new Redex(input, tmp, eq);
                result.position = pos;

                break;

            }
        }

        if (result == null && input.operation.strategy == null) {

            for (int i = 0; i < input.subterms.length && result == null; i++ ) {
                if (input.subterms[i].var == null) {

                    // for unknown reason, add the next line
                    input.subterms[i].parent = input;
                    result = getRedex(input.subterms[i], i);
                }
            }

            if (result == null) {
                input.nogcheck = true;
            }
        }

        return result;
    }

    protected static int boolValue(Term input) {

        int result = -1;

        Operation t = BoolModule.trueOp;
        Operation f = BoolModule.falseOp;
        Operation and = BoolModule.and;
        Operation or = BoolModule.or;
        Operation not = BoolModule.not;

        if (input.var == null) {
            if (input.operation.isConstant() && input.operation.info.equals("system-default")) {
                if (input.operation.equals(t)) {
                    return 1;
                } else if (input.operation.equals(f)) {
                    return 0;
                } else {
                    return -1;
                }
            } else if (input.operation.info.equals("system-default")) {
                if (input.operation.equals(and)) {

                    int res1 = boolValue(input.subterms[0]);
                    if (res1 == 0) {
                        return 0;
                    } else if (res1 == 1) {
                        return boolValue(input.subterms[1]);
                    }

                } else if (input.operation.equals(or)) {

                    int res1 = boolValue(input.subterms[0]);
                    if (res1 == 1) {
                        return 1;
                    }
                    if (res1 == 0) {
                        return boolValue(input.subterms[1]);
                    }

                } else if (input.operation.equals(not)) {

                    int res1 = boolValue(input.subterms[0]);
                    if (res1 == 1) {
                        return 0;
                    }
                    if (res1 == 0) {
                        return 1;
                    }

                }
            }

        }

        return result;

    }

    private Term localCopy(Term term) {

        Term result = new Term();
        result.operation = term.operation;
        result.subterms = term.subterms;
        result.var = term.var;

        result.helper = term.helper;
        result.retract = term.retract;

        result.parent = null;
        result.nocheck = term.nocheck;
        result.nogcheck = term.nogcheck;
        result.noscheck = term.noscheck;
        result.sort = term.sort;

        return result;

    }

    public Term reduce(Term input,
                       Redex redex) {

        if (debug || trace && !turnoff2Eq) {
            System.out.println("rewrite target: " + input);
            System.out.println("rewrite point: " + redex.point);
        }

        Term point = redex.point;
        Term term = redex.term;
        term.nocheck = true;

        if (point.parent == null) {
            if (debug || trace && !turnoff2Eq) {
                System.out.println("result: " + term);
                System.out.println("................................");
            }
            return term;
        } else {

            point.parent.subterms[redex.position] = term;
            point.parent.subterms[redex.position].parent = point.parent;

            // try to get the minimum result
            Term tmp = point.parent;
            while (tmp != null) {
                Term res = getMinimumTerm(sig, tmp.operation, tmp.subterms);
                if (res != null) {

                    if (tmp.parent != null) {
                        for (int i = 0; i < tmp.parent.subterms.length; i++ ) {
                            if (tmp == tmp.parent.subterms[i]) {
                                tmp.parent.subterms[i] = res;
                                res.parent = tmp.parent;
                                break;
                            }
                        }
                    } else {
                        if (debug || trace && !turnoff2Eq) {
                            System.out.println("result: " + res);
                            System.out.println("................................");
                        }
                        return res;
                    }
                    tmp = tmp.parent;
                } else {
                    if (debug || trace && !turnoff2Eq) {
                        System.out.println("result: " + input);
                        System.out.println("................................");
                    }
                    return input;
                }
            }

        }

        if (debug || trace && !turnoff2Eq) {
            System.out.println("result: " + input);
            System.out.println("................................");
        }
        return input;
    }

    public Map<VarOrCode, Term> getMatch(Term input,
                                         Term pattern) {
        if (debug_match)
            System.err.println("Getting one match for " + input + " to " + pattern);

//        System.err.println("\n------ match  -------");
//        System.err.println("this = "+input);
//        System.err.println("------------------------");
//        System.err.println("pattern = "+pattern);
//        System.err.println("");

        Map<VarOrCode, Term> result = new HashMap<>();

        if (pattern.var != null) {
            Sort vs = pattern.sort;
            Sort ts = input.sort;
            boolean okay = false;

            if (vs.equals(ts) || sig.isSubsort(ts, vs)) {
                okay = true;
            }

//            /*
//        else {
//        if (input.parent != null) {
//            for (int i=0; i<input.parent.subterms.length; i++) {
//            if (input.parent.subterms[i] == input) {
//                if (input.parent.retract[i] != null &&
//                sig.isSubsort(input.parent.retract[i], vs)) {
//                okay = true;
//                retract = input.parent.retract[i];
//                }
//                break;
//            }
//
//            }
//        }
//        }
//        */

            if (!okay) {
                if (debug_match)
                    System.err.println("No match found.");
                return null;
            }

            if (input.var == null) {

                if (input.operation.info.equals("system-retract")) {
                    if (sig.isSubsort(input.operation.argumentSorts[0], vs)) {
                        try {
                            Term term = new Term(sig, input.operation, input.subterms);
                            result.put(pattern.var, term);
                        } catch (Exception e) {
                        }
                    } else {
                        if (debug)
                            System.err.println("No match found.");
                        if (debug)
                            System.err.println("No match found.");
                        return null;
                    }
                } else {
                    try {
                        Term term = new Term(sig, input.operation, input.subterms);
                        result.put(pattern.var, term);

                    } catch (Exception e) {
                    }
                }

//                /*
//                try {
//                    Term term = new Term(sig,
//                             input.operation,
//                             input.subterms);
//                    if (retract != null) {
//                    term.setProperty("retract", retract);
//                    }
//
//                    result.put(pattern.var, term);
//                } catch (Exception e) {}
//                */

            } else {
                Term term = new Term(input.var);
                result.put(pattern.var, term);
            }

        } else if (input.operation == null) {
            if (debug)
                System.err.println("No match found.");
            return null;

        } else if (input.operation.equals(pattern.operation)
                   || input.operation.less(sig, pattern.operation)) {

                       boolean okay = true;
                       if (input.operation.resultSort.isHidden()) {
                           Term tmp = pattern.parent;
                           while (tmp != null) {
                               if (tmp.operation.isBehavorial()) {
                                   tmp = tmp.parent;
                               } else {
                                   okay = false;
                                   break;
                               }
                           }
                       }

                       if (okay && input.operation.isAssociative
                           && !input.operation.isCommutative) {

                           try {

                               Vector<Term> data = input.getAssocSubterms(sig, input.operation);
                               Vector<Term> pats = pattern.getAssocSubterms(sig, pattern.operation);
                               Vector<Vector<Term>> possible =
                                   getAMatchPossibles(data, pats, input.operation);

                               for (int i = 0; i < possible.size(); i++ ) {

                                   Vector<Term> tmp = possible.elementAt(i);
                                   Map<VarOrCode, Term> res = new HashMap<>();

                                   for (int j = 0; j < pats.size(); j++ ) {
                                       Term pat = pats.elementAt(j);
                                       Term term = tmp.elementAt(j);

                                       if (pat.var != null) {

                                           if (sig.isSubsort(term.sort, pat.sort)) {

                                               Term target = res.get(pat.var);
                                               if (target == null) {
                                                   res.put(pat.var, term);
                                               } else if (target.equals(sig, term)) {
                                                   // do nothing
                                               } else {
                                                   res = null;
                                                   break;
                                               }
                                           } else {
                                               res = null;
                                               break;
                                           }
                                       } else {

                                           Map<VarOrCode, Term> sub = getMatch(term, pat);
                                           if (sub == null) {
                                               res = null;
                                               break;
                                           }

                                           for (VarOrCode var : sub.keySet()) {
                                               Term trm1 = sub.get(var);
                                               Term trm2 = res.get(var);

                                               if (trm2 == null) {
                                                   res.put(var, trm1);
                                               } else if (trm1.equals(sig, trm2)) {
                                                   // do nothing
                                               } else {
                                                   res = null;
                                                   break;
                                               }
                                           }
                                       }

                                       if (res == null) {
                                           break;
                                       }

                                   }

                                   if (res != null) {
                                       if (debug)
                                           System.err.println("Found: " + res);
                                       return res;
                                   }

                               }

                           } catch (Exception e) {
                           }
                           if (debug)
                               System.err.println("No match found.");
                           return null;

                       } else if (okay && input.operation.isAssociative
                                  && input.operation.isCommutative) {

                                      // this part is added on 12/5/2000
                                      Term[] subpatterns = pattern.subterms;
                                      for (int i = 0; i < input.subterms.length; i++ ) {

                                          Map<VarOrCode, Term> tmp =
                                              getMatch(input.subterms[i], subpatterns[i]);

                                          if (tmp == null) {
                                              result = null;
                                              break;
                                          } else {
                                              for (VarOrCode var : tmp.keySet()) {
                                                  Term trm1 = tmp.get(var);
                                                  Term trm2 = result.get(var);
                                                  if (trm2 == null) {
                                                      result.put(var, trm1);
                                                  } else if (!trm1.equals(trm2)) {
                                                      result = null;
                                                      break;
                                                  }
                                              }
                                          }
                                      }

                                      if (result != null) {
                                          if (debug)
                                              System.err.println("Found: " + result);
                                          return result;
                                      }
                                      //end of adding

                                      try {

                                          Vector<Term> data =
                                              input.getAssocSubterms(sig, input.operation);
                                          Vector<Term> pats =
                                              pattern.getAssocSubterms(sig, pattern.operation);

                                          Map<VarOrCode, Term> res =
                                              getACOptimizedMatch(data, pats, input.operation);

                                          // modify 11.21.2000
                                          if (res == null) {
                                              if (debug)
                                                  System.err.println("No Match found.");
                                              return null;
                                          }
                                          Vector<Term> rest = getCodeValue(res, "ac-rest");
                                          if (rest != null && rest.size() > 0) {
                                              removeCodeValue(res, "ac-rest");
                                              if (debug)
                                                  System.err.println("No Match found.");
                                              return null;
                                          }
                                          if (debug)
                                              System.err.println("Found: " + res);

                                          return res;
                                      } catch (Exception ex) {
                                      }
                                      if (debug)
                                          System.err.println("No Match found.");
                                      return null;

                                  } else
                           if (okay && input.operation.isCommutative) {

                               Term data1 = input.subterms[0];
                               Term data2 = input.subterms[1];
                               Term pat1 = pattern.subterms[0];
                               Term pat2 = pattern.subterms[1];

                               Map<VarOrCode, Term> tab1 = getMatch(data1, pat1);

                               Map<VarOrCode, Term> res = null;
                               if (tab1 != null) {
                                   Map<VarOrCode, Term> tab2 = getMatch(data2, pat2);
                                   if (tab2 != null) {
                                       res = combineSubst(tab1, tab2);
                                   }
                               }

                               if (res == null) {
                                   tab1 = getMatch(data1, pat2);
                                   if (tab1 != null) {
                                       Map<VarOrCode, Term> tab2 = getMatch(data2, pat1);
                                       if (tab2 != null)
                                           res = combineSubst(tab1, tab2);
                                   }
                               }
                               if (debug)
                                   System.err.println("Found: " + res);
                               return res;

                           } else {

                               /* it seems that this method only works for linear pattern or
                                * nonlinear pattern with depth 1. two counterexamples are given as
                                * follows: M + N > M = true M + N > M + K = true if N > K
                                *
                                * actually it is very hard to fix this bug, many methods in
                                * rewriting engine should be rewritten.
                                *
                                * the most important idea is: given a term t and a pattern pat,
                                * t.getMatch(p, sig) should return a substitution set not a single
                                * substitution. */

                               Term[] subpatterns = pattern.subterms;

                               for (int i = 0; i < input.subterms.length; i++ ) {
                                   Map<VarOrCode, Term> tmp =
                                       getMatch(input.subterms[i], subpatterns[i]);

                                   /* if (tmp == null && input.operation.strategy != null &&
                                    * input.operation.strategy[i] < -1) { Term term =
                                    * reduce(input.subterms[i]); tmp = getMatch(term,
                                    * subpatterns[i]); } */

                                   if (tmp == null && input.operation.strategy != null) {

                                       for (int element : input.operation.strategy) {
                                           if (element == -i) {
                                               Term term = reduce(input.subterms[i]);
                                               tmp = getMatch(term, subpatterns[i]);
                                               break;
                                           }
                                       }
                                   }

                                   if (tmp == null) {
                                       Vector<Map<VarOrCode, Term>> matchSet =
                                           getAllMatches(input, pattern);
                                       if (!matchSet.isEmpty()) {
                                           if (debug)
                                               System.err.println("Found: "
                                                                  + matchSet.elementAt(0));
                                           return matchSet.elementAt(0);
                                       }
                                       if (debug)
                                           System.err.println("No match found.");
                                       return null;
                                   } else {

                                       for (VarOrCode var : tmp.keySet()) {
                                           Term trm1 = tmp.get(var);
                                           Term trm2 = null;
                                           for (VarOrCode vtmp : result.keySet()) {
                                               if (vtmp.equals(var)) {
                                                   trm2 = result.get(vtmp);
                                                   break;
                                               }
                                           }
                                           if (trm2 == null) {
                                               result.put(var, trm1);
                                           } else if (!trm1.equals(trm2)) {

                                               Vector<Map<VarOrCode, Term>> matchSet =
                                                   getAllMatches(input, pattern);
                                               if (!matchSet.isEmpty()) {
                                                   if (debug)
                                                       System.err.println("Found: "
                                                                          + matchSet.elementAt(0));
                                                   return matchSet.elementAt(0);
                                               }
                                               if (debug)
                                                   System.err.println("No match found.");
                                               return null;
                                           }

                                       }
                                   }
                               }

                           }

                   } else
            if (pattern.operation != null && pattern.operation.info.equals("system-retract")) {

                if (sig.isSubsort(input.sort, pattern.operation.resultSort)) {

                    // change at 09/27/2002
                    if (input.sort.equals(pattern.operation.resultSort)) {
                        result = null;
                    } else {
                        result = getMatch(input, pattern.subterms[0]);
                    }
                    //result = getMatch(input, pattern.subterms[0]);
                    // end change

                } else {
                    if (sig.isSubsort(input.sort, pattern.operation.argumentSorts[0])
                        && input.parent != null) {

                        for (int i = 0; i < input.parent.subterms.length; i++ ) {
                            if (input == input.parent.subterms[i]) {

                                if (input.parent.retract[i] != null
                                    && sig.isSubsort(pattern.operation.resultSort,
                                                     input.parent.retract[i])) {
                                    result = getMatch(input, pattern.subterms[0]);
                                    if (result != null) {
                                        if (debug)
                                            System.err.println("Found: " + result);
                                        return result;
                                    }

                                }
                                break;

                            }
                        }

                    }

                    result = null;
                }

            } else {
                result = null;
            }
        if (debug)
            System.err.println("Found: " + result);

        return result;
    }

    /**
     *
     * find all matchs against the specified pattern
     *
     * @param pattern
     *            <code>Term</code>
     * @param sig
     *            <code>Signature</code>
     *
     */
    private Vector<Map<VarOrCode, Term>> getAllMatches(Term input,
                                                       Term pattern) {
        if (debug)
            System.err.println("Getting matches for " + input + " to " + pattern);

        // a vector containing all found matches
        Vector<Map<VarOrCode, Term>> matchSet = new Vector<>();

        // a current match substitution
        Map<VarOrCode, Term> match = new HashMap<>();

        if (pattern.var != null) {

            // if pattern is a variable, check sort
            Sort vs = pattern.sort;
            Sort ts = input.sort;
            boolean okay = false;

            if (vs.equals(ts) || sig.isSubsort(ts, vs)) {
                okay = true;
            }

            if (!okay) {

                // the sorts are not compatible
                return matchSet;
            }

            // the sorts are compatible
            if (input.var == null) {

                // this term is a composite term
                // make a local copy of this term

                if (input.operation.info.equals("system-retract")) {
                    if (sig.isSubsort(input.operation.argumentSorts[0], vs)) {
                        try {
                            Term term = new Term(sig, input.operation, input.subterms);
                            match.put(pattern.var, term);
                        } catch (Exception e) {
                        }
                    } else {
                        if (debug)
                            System.err.println("Returning " + matchSet);
                        return matchSet;
                    }
                } else {

                    try {
                        Term term = new Term(sig, input.operation, input.subterms);
                        match.put(pattern.var, term);
                    } catch (Exception e) {
                    }
                }

                /* try { Term term = new Term(sig, input.operation, input.subterms);
                 * match.put(pattern.var, term); } catch (Exception e) {} */

            } else {

                // this term is a variable
                Term term = new Term(input.var);
                match.put(pattern.var, term);

            }

            matchSet.addElement(match);
            if (debug)
                System.err.println("Returning " + matchSet);
            return matchSet;

        } else if (input.operation == null) {
            if (debug)
                System.err.println("Returning " + matchSet);
            return matchSet;

        } else if (input.operation.equals(pattern.operation)
                   || input.operation.less(sig, pattern.operation)) {

                       // the top operations of this term and pattern are matched
                       // check the validation of behavioral rewriting

                       boolean okay = true;
                       if (input.operation.resultSort.isHidden()) {
                           Term tmp = pattern.parent;
                           while (tmp != null) {
                               // all parent operations should be
                               // congruent until visible sort
                               if (tmp.operation.isBehavorial()) {
                                   tmp = tmp.parent;
                               } else {
                                   okay = false;
                                   break;
                               }
                           }
                       }

                       // case analysis according to the top operation ofthe pattern

                       if (okay && input.operation.isAssociative
                           && !input.operation.isCommutative) {

                           // the top operation is associative but not commutative
                           try {

                               // get all the direct subterms of this term
                               Vector<Term> data = input.getAssocSubterms(sig, input.operation);

                               // get all the direct subterms of this pattern
                               Vector<Term> pats = pattern.getAssocSubterms(sig, pattern.operation);

                               // get all associative matches
                               Vector<Vector<Term>> possible =
                                   getAMatchPossibles(data, pats, input.operation);

                               // handle it one by one
                               for (int i = 0; i < possible.size(); i++ ) {

                                   Vector<Term> tmp = possible.elementAt(i);

                                   // all matches for tmp
                                   @SuppressWarnings("unchecked")
                                   Vector<Map<VarOrCode, Term>>[] resForTmp =
                                       new Vector[pats.size()];
                                   boolean impossible = false;

                                   for (int j = 0; j < pats.size(); j++ ) {

                                       Term pat = pats.elementAt(j);
                                       Term term = tmp.elementAt(j);
                                       resForTmp[j] = getAllMatches(term, pat);

                                       if (resForTmp[j].isEmpty()) {

                                           // it is impossible to find a match
                                           impossible = true;
                                           break;
                                       }
                                   }

                                   if (!impossible) {
                                       // try to combine all substitutions in resForall
                                       // save them into matchSet
                                       combine(matchSet, resForTmp);
                                   }
                               }

                           } catch (Exception e) {
                           }
                           if (debug)
                               System.err.println("Returning " + matchSet);
                           return matchSet;

                       } else if (okay && input.operation.isAssociative
                                  && input.operation.isCommutative) {

                                      // the most important case: op is assoc and comm
                                      try {
                                          // get all direct subterms of this term
                                          Vector<Term> data =
                                              input.getAssocSubterms(sig, input.operation);

                                          // get all direct subterms of the pattern
                                          Vector<Term> pats =
                                              pattern.getAssocSubterms(sig, pattern.operation);

                                          // get all possible ac-match case
                                          Vector<Vector<Term>> possible =
                                              getACMatchPossibles(data, pats, input.operation);

                                          // handle it one by one
                                          for (int i = 0; i < possible.size(); i++ ) {

                                              Vector<Term> tmp = possible.elementAt(i);

                                              // all matches for tmp
                                              @SuppressWarnings("unchecked")
                                              Vector<Map<VarOrCode, Term>>[] resForTmp =
                                                  new Vector[pats.size()];
                                              boolean impossible = false;

                                              for (int j = 0; j < pats.size(); j++ ) {

                                                  Term pat = pats.elementAt(j);
                                                  Term term = tmp.elementAt(j);
                                                  resForTmp[j] = getAllMatches(term, pat);

                                                  if (resForTmp[j].isEmpty()) {

                                                      // it is impossible to find a match
                                                      impossible = true;
                                                      break;

                                                  }
                                              }

                                              if (!impossible) {

                                                  // try to combine all substitutions in resForall
                                                  // save them into matchSet
                                                  combine(matchSet, resForTmp);
                                              }
                                          }

                                      } catch (Exception ex) {
                                          ex.printStackTrace();
                                      }
                                      if (debug)
                                          System.err.println("Returning " + matchSet);
                                      return matchSet;

                                  } else
                           if (okay && input.operation.isCommutative) {

                               // this is a simple case to handle
                               // let pats=<p1, p2> and data=<t1, t2>
                               // two possible: p1<->t1 and p2<->t2
                               //               p1<->t2 and p2<->t1

                               @SuppressWarnings("unchecked")
                               Vector<Map<VarOrCode, Term>>[] res = new Vector[2];

                               Term pat0 = pattern.subterms[0];
                               Term data0 = input.subterms[0];
                               res[0] = getAllMatches(data0, pat0);

                               Term pat1 = pattern.subterms[1];
                               Term data1 = input.subterms[1];
                               res[1] = getAllMatches(data1, pat1);

                               combine(matchSet, res);

                               res[0] = getAllMatches(data0, pat1);
                               res[1] = getAllMatches(data1, pat0);
                               combine(matchSet, res);
                               if (debug)
                                   System.err.println("Returning " + matchSet);
                               return matchSet;

                           } else if (pattern.subterms.length == 0) {
                               matchSet.addElement(new HashMap<VarOrCode, Term>());
                           } else {
                               // check all subterms
                               Term[] pats = pattern.subterms;
                               @SuppressWarnings("unchecked")
                               Vector<Map<VarOrCode, Term>>[] res = new Vector[pats.length];

                               for (int i = 0; i < input.subterms.length; i++ ) {
                                   res[i] = getAllMatches(input.subterms[i], pats[i]);
                               }
                               combine(matchSet, res);
                           }
                   }
        if (debug)
            System.err.println("Returning " + matchSet);
        return matchSet;
    }

    /**
     *
     * combine several matchset togather
     *
     */
    private void combine(Vector<Map<VarOrCode, Term>> res,
                         Vector<Map<VarOrCode, Term>>[] matchset) {

        if (matchset.length == 0) {
            return;
        } else if (matchset.length == 1) {

            // copy all elments in matchset[0] into res
            for (int i = 0; i < matchset[0].size(); i++ ) {
                res.addElement(matchset[0].elementAt(i));
            }
            return;

        } else {

            // handle it recursively
            Vector<Map<VarOrCode, Term>> vec = new Vector<>();
            @SuppressWarnings("unchecked")
            Vector<Map<VarOrCode, Term>>[] smallset = new Vector[matchset.length - 1];
            System.arraycopy(matchset, 1, smallset, 0, matchset.length - 1);
            combine(vec, smallset);

            // combine with the first possible solution
            Vector<Map<VarOrCode, Term>> first = matchset[0];
            for (int i = 0; i < first.size(); i++ ) {
                for (int j = 0; j < vec.size(); j++ ) {

                    Map<VarOrCode, Term> subst1 = first.elementAt(i);
                    Map<VarOrCode, Term> subst2 = vec.elementAt(j);
                    Map<VarOrCode, Term> subst = combineSubst(subst1, subst2);
                    if (subst != null) {
                        res.addElement(subst);
                    }

                }
            }

        }

    }

    /**
     *
     * find all possible matches wrt associativity
     *
     */
    private Vector<Vector<Term>> getAMatchPossibles(Vector<Term> data,
                                                    Vector<Term> pats,
                                                    Operation op) {

        // setup a vector for result
        Vector<Vector<Term>> result = new Vector<>();

        if (pats.isEmpty()) {

            // no pattern is needed to be matched
            return result;

        } else if (pats.size() == 1 && data.size() >= 1) {

            // an optimization: only a single pattern
            // e.g.  pats = <p1>
            //       data = <t1, t2, ..., tk>
            // so p1 must match t1+t2+...+tk

            Vector<Term> tmp = new Vector<>();
            Term term = data.elementAt(0);

            for (int i = 1; i < data.size(); i++ ) {
                Term[] args =
                    {
                        term, data.elementAt(i)
                    };
                try {
                    term = getMinimumTerm(sig, op, args);
                } catch (Exception e) {
                }
            }
            tmp.addElement(term);
            result.addElement(tmp);

        } else if (pats.size() == data.size()) {

            // an optimization: the size of pats is the same as
            // the size of data
            result.addElement(data);

        } else if (pats.size() < data.size()) {

            // general case

            // a vector contains all terms in the vector data
            Vector<Term> dcopy = new Vector<>(data);

            // a vector contains all patterns
            Vector<Term> pcopy = new Vector<>(pats);

            // handle the first pattern in pcopy
            Term pat = pcopy.elementAt(0);
            pcopy.removeElementAt(0);

            if (pat.var == null) {

                // pat is not a variable
                // then pat must match the first term in dcopy

                Term term = dcopy.elementAt(0);
                dcopy.removeElementAt(0);

                Vector<Vector<Term>> res = getAMatchPossibles(dcopy, pcopy, op);
                for (int i = 0; i < res.size(); i++ ) {
                    Vector<Term> tmp = res.elementAt(i);
                    tmp.insertElementAt(term, 0);
                    result.addElement(tmp);
                }

            } else {

                // pat is a variable

                for (int i = 0; i <= (dcopy.size() - pcopy.size()); i++ ) {

                    // pat could match at most dcopy.size()-pcopy.size()+1
                    //    terms
                    // e.g.  pats=<x, p2, p3>
                    //       data=<t1, t2, t3, t4, t5>
                    // then x could match t1, t1+t2, t1+t2+t3

                    Vector<Term> ddcopy = new Vector<>(dcopy);

                    Term term = null;
                    for (int j = 0; j <= i; j++ ) {
                        Term tmp = ddcopy.elementAt(0);
                        ddcopy.removeElementAt(0);

                        // create the target term
                        if (term == null) {
                            term = tmp;
                        } else {
                            Term[] args =
                                {
                                    term, tmp
                                };
                            try {
                                //term = new Term(sig, op, args);
                                term = getMinimumTerm(sig, op, args);
                            } catch (Exception e) {
                            }
                        }
                    }

                    // handle it recursively
                    Vector<Vector<Term>> res = getAMatchPossibles(ddcopy, pcopy, op);
                    for (int k = 0; k < res.size(); k++ ) {
                        Vector<Term> tmp = res.elementAt(k);
                        tmp.insertElementAt(term, 0);
                        result.addElement(tmp);
                    }
                }
            }
        }

        return result;
    }

    /**
     *
     * find all possible matches wrt associativity and commutativity
     *
     */
    private Vector<Vector<Term>> getACMatchPossibles(Vector<Term> data,
                                                     Vector<Term> pats,
                                                     Operation op) {

        // setup a vector for result
        Vector<Vector<Term>> result = new Vector<>();

        if (pats.isEmpty()) {

            // no pattern is needed to be matched
            return result;

        } else if (pats.size() == 1 && data.size() >= 1) {

            // an optimization: only a single pattern
            // e.g.  pats = <p1>
            //       data = <t1, t2, ..., tk>
            // so p1 must match t1+t2+...+tk

            Vector<Term> tmp = new Vector<>();
            Term term = data.elementAt(0);

            for (int i = 1; i < data.size(); i++ ) {
                Term[] args =
                    {
                        term, data.elementAt(i)
                    };
                try {
                    term = getMinimumTerm(sig, op, args);
                } catch (Exception e) {
                }
            }
            tmp.addElement(term);
            result.addElement(tmp);

        } else if (pats.size() <= data.size()) {

            // general case

            // a vector contains all terms in the vector data
            Vector<Term> dcopy = new Vector<>(data);

            // a vector contains all patterns
            Vector<Term> pcopy = new Vector<>(pats);

            // handle the first pattern in pcopy
            Term pat = pcopy.elementAt(0);
            pcopy.removeElementAt(0);

            if (pat.var == null) {

                // pat is not a variable
                // then pat could match any terms in dcopy

                for (int i = 0; i < dcopy.size(); i++ ) {

                    // let pat match i-th element of dcopy
                    Vector<Term> ddcopy = new Vector<>(dcopy);
                    Term term = ddcopy.elementAt(i);
                    ddcopy.removeElementAt(i);

                    Vector<Vector<Term>> res = getACMatchPossibles(ddcopy, pcopy, op);
                    for (int j = 0; j < res.size(); j++ ) {
                        Vector<Term> tmp = res.elementAt(j);
                        tmp.insertElementAt(term, 0);
                        result.addElement(tmp);
                    }

                }

            } else {

                // pat is a variable
                // e.g.  pats=<x, p>
                //       data=<t1, t2, t3>
                // then could have the following cases
                //       <t1, t2+t3>
                //       <t2, t1+t3>
                //       <t3, t1+t2>
                //       <t1+t2, t3>
                //       <t1+t3, t2>
                //       <t2+t3, t1>

                for (int i = 0; i <= dcopy.size() - pcopy.size(); i++ ) {

                    Vector<Vector<Term>> forPat = new Vector<>();
                    Vector<Vector<Term>> forData = new Vector<>();
                    devide(dcopy, i, forPat, forData);

                    for (int j = 0; j < forPat.size(); j++ ) {

                        // let pat match the terms in forPat
                        Term term = null;

                        Vector<Term> pvec = forPat.elementAt(j);
                        Vector<Term> dvec = forData.elementAt(j);

                        for (int k = 0; k < pvec.size(); k++ ) {

                            Term tmp = pvec.elementAt(k);

                            // create the target term
                            if (term == null) {
                                term = tmp;
                            } else {
                                Term[] args =
                                    {
                                        term, tmp
                                    };
                                try {
                                    term = getMinimumTerm(sig, op, args);
                                } catch (Exception e) {
                                }
                            }
                        }

                        // recursively handling
                        Vector<Vector<Term>> res = getACMatchPossibles(dvec, pcopy, op);
                        for (int k = 0; k < res.size(); k++ ) {
                            Vector<Term> tmp = res.elementAt(k);
                            tmp.insertElementAt(term, 0);
                            result.addElement(tmp);
                        }

                    }

                }

            }
        }

        return result;
    }

    /**
     *
     * divide input vector data into two vector, one of them should have n elements
     *
     */
    private void devide(Vector<Term> data,
                        int number,
                        Vector<Vector<Term>> forPat,
                        Vector<Vector<Term>> forData) {

        if (number < data.size() && number > 0) {
            if (number == 1) {
                for (int i = 0; i < data.size(); i++ ) {
                    Vector<Term> p = new Vector<>();
                    Vector<Term> d = new Vector<>(data);
                    p.addElement(d.elementAt(i));
                    d.removeElementAt(i);

                    forPat.addElement(p);
                    forData.addElement(d);
                }

            } else {
                for (int i = 0; i < data.size(); i++ ) {

                    Vector<Term> d = new Vector<>(data);
                    Term term = d.elementAt(i);
                    d.removeElementAt(i);

                    Vector<Vector<Term>> ps = new Vector<>();
                    Vector<Vector<Term>> ds = new Vector<>();
                    devide(d, number - 1, ps, ds);

                    for (int j = 0; j < ps.size(); j++ ) {
                        Vector<Term> p = ps.elementAt(j);
                        p.insertElementAt(term, 0);

                        // check if p is in forPat already
                        //if (!contains(forPat, p)) {

                        forPat.addElement(p);

                        Vector<Term> dd = ds.elementAt(j);
                        forData.addElement(dd);
                        //}
                    }
                }
            }
        }
    }

    private Map<VarOrCode, Term> getACOptimizedMatch(Vector<Term> data,
                                                     Vector<Term> pats,
                                                     Operation op) {

        // optimization
        if (pats.size() == 2 && data.size() >= 2) {

            Term pat1 = pats.elementAt(0);
            Term pat2 = pats.elementAt(1);

            if (data.size() == 2) {

                Term data1 = data.elementAt(0);
                Term data2 = data.elementAt(1);

                Map<VarOrCode, Term> tab1 = getMatch(data1, pat1);
                Map<VarOrCode, Term> res = null;
                if (tab1 != null) {
                    Map<VarOrCode, Term> tab2 = getMatch(data2, pat2);
                    if (tab2 != null) {
                        res = combineSubst(tab1, tab2);
                    }
                }

                if (res == null) {
                    tab1 = getMatch(data1, pat2);
                    if (tab1 != null) {
                        Map<VarOrCode, Term> tab2 = getMatch(data2, pat1);
                        if (tab2 != null) {
                            res = combineSubst(tab1, tab2);
                        }
                    }
                }
                return res;

            } else {

                if (pat2.var != null) {
                    Term tmp = pat1;
                    pat1 = pat2;
                    pat2 = tmp;
                }

                if (pat1.var != null) {

                    // modified at 12/8/2000
                    if (pat1.equals(pat2)) {

                        // get a situation like: pattern = M + M
                        Vector<Term> one = new Vector<>();
                        Vector<Term> two = new Vector<>();

                        for (int i = 0; i < data.size(); i++ ) {
                            Term term = data.elementAt(i);

                            // check if term is in the vector one
                            boolean inOne = false;
                            int j = 0;
                            for (j = 0; j < one.size(); j++ ) {
                                Term aTerm = one.elementAt(j);
                                if (term.equals(aTerm)) {
                                    inOne = true;
                                    break;
                                }
                            }

                            if (inOne) {
                                two.addElement(term);
                                one.removeElementAt(j);
                            } else {
                                one.addElement(term);
                            }

                        }

                        if (one.isEmpty()) {
                            Term term = two.elementAt(0);
                            for (int i = 1; i < two.size(); i++ ) {
                                Term tmp = two.elementAt(i);
                                try {
                                    term = new Term(sig, op, term, tmp);
                                } catch (TermException e) {
                                }
                            }

                            HashMap<VarOrCode, Term> res = new HashMap<>();
                            res.put(pat1.var, term);
                            return res;

                        } else {
                            return null;
                        }
                    }

                    // end of modification

                    for (int i = 0; i < data.size(); i++ ) {

                        Term term = data.elementAt(i);
                        Map<VarOrCode, Term> res = getMatch(term, pat2);

                        if (res != null) {

                            Term tmp = res.get(pat1.var);

                            Vector<Term> dcopy = new Vector<>(data);
                            dcopy.removeElementAt(i);

                            Term t = null;
                            for (int j = 0; j < dcopy.size(); j++ ) {
                                if (t == null) {
                                    t = dcopy.elementAt(j);
                                } else {
                                    Term[] args =
                                        {
                                            t, dcopy.elementAt(j)
                                        };
                                    t = getMinimumTerm(sig, op, args);
                                }
                            }

                            if (tmp == null) {
                                res.put(pat1.var, t);
                                return res;
                            } else if (tmp.equals(sig, t)) {
                                return res;
                            } else {
                                res = null;
                            }
                        }
                    }
                }
            }

        } else if (pats.size() > 2 && data.size() >= pats.size()) {

            Map<Term, Vector<Integer>> p2d = new HashMap<>();
            Map<Term, Vector<Map<VarOrCode, Term>>> p2s = new HashMap<>();

            for (int i = 0; i < pats.size(); i++ ) {

                // take a pattern
                Term pterm = pats.elementAt(i);

                // check which data can be matched by this pattern
                for (int j = 0; j < data.size(); j++ ) {
                    Term dterm = data.elementAt(j);
                    Map<VarOrCode, Term> subst = getMatch(dterm, pterm);

                    if (subst != null) {
                        Vector<Integer> d = p2d.get(pterm);
                        if (d == null)
                            d = new Vector<>();
                        d.addElement(j);
                        p2d.put(pterm, d);

                        Vector<Map<VarOrCode, Term>> s = p2s.get(pterm);
                        if (s == null)
                            s = new Vector<>();
                        s.addElement(subst);
                        p2s.put(pterm, s);
                    }
                }
            }

            // handle some patterns like M + M + M = ...
            boolean same = true;
            Term sample = null;
            for (int i = 0; i < pats.size(); i++ ) {
                Term pterm = pats.elementAt(i);
                if (pterm.var != null) {

                    if (sample != null) {
                        if (!sample.equals(pterm)) {
                            same = false;
                            break;
                        }

                    } else {
                        sample = pterm;
                    }

                } else {
                    same = false;
                    break;
                }

            }

            if (same) {

                Map<Term, Integer> count = new HashMap<>();
                for (int i = 0; i < data.size(); i++ ) {
                    Term dterm = data.elementAt(i);

                    Iterator<Term> itor = count.keySet()
                                               .iterator();
                    boolean found = false;
                    while (itor.hasNext()) {
                        Term key = itor.next();
                        if (dterm.equals(key)) {
                            Integer aInt = count.get(key);
                            count.put(key, aInt.intValue() + 1);
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        count.put(dterm, 1);
                    }

                }

                Iterator<Term> itor = count.keySet()
                                           .iterator();
                Vector<Term> vec = new Vector<>();
                Term target = null;

                while (itor.hasNext()) {
                    Term key = itor.next();
                    Integer aInt = count.get(key);
                    if (target == null && aInt.intValue() >= pats.size()) {

                        for (int i = 0; i < aInt.intValue() - pats.size(); i++ ) {
                            vec.addElement(key);
                        }

                        target = key;

                    } else {

                        for (int i = 0; i < aInt.intValue(); i++ ) {
                            vec.addElement(key);
                        }

                    }
                }

                if (target == null) {
                    return null;
                } else {
                    Map<VarOrCode, Term> result = new HashMap<>();
                    result.put(sample.var, target);
                    result.put(new VarOrCode("ac-rest", vec), new Term());
                    return result;
                }
            }

            Vector<Map<VarOrCode, Term>> vec = fastACMatch(pats, data);
            if (vec.size() > 0) {
                Map<VarOrCode, Term> result = vec.elementAt(0);
                return result;
            }

//            /*  IMPORTANT
//            Hashtable result = new Hashtable();
//            result = ACMatchDispatch(pats, data, p2d, p2s, op, sig, result);
//            return result;
//                */
        }

        return null;
    }

//    private HashMap ACMatchDispatch(Vector pats,
//                                    Vector data,
//                                    HashMap<Term, Vector<Integer>> p2d,
//                                    HashMap<Term, Vector> p2s,
//                                    Operation op,
//                                    Signature sig,
//                                    HashMap result) {
//
//        if (pats.size() == 0 && data.size() != 0) {
//            result.put("ac-rest", data);
//            return result;
//        }
//
//        Vector<Term> vpat = new Vector<Term>();
//        Vector<Term> dpat = new Vector<Term>();
//
//        for (int i = 0; i < pats.size(); i++ ) {
//            Term pterm = (Term) pats.elementAt(i);
//            if (pterm.var != null) {
//                vpat.addElement(pterm);
//            } else {
//                dpat.addElement(pterm);
//            }
//        }
//
//        HashMap res = null;
//
//        if (dpat.size() == 0) {
//            res = new HashMap();
//        }
//
//        for (int i = 0; i < dpat.size(); i++ ) {
//
//            Term pterm = dpat.elementAt(i);
//            Vector d = p2d.get(pterm);
//            Vector s = p2s.get(pterm);
//            p2d.remove(pterm);
//            p2s.remove(pterm);
//
//            boolean found = false;
//            for (int j = 0; j < d.size() && !found; j++ ) {
//
//                Integer aInt = (Integer) d.elementAt(j);
//                int pos = aInt.intValue();
//                Term dterm = (Term) data.elementAt(pos);
//                HashMap subst = (HashMap) s.elementAt(j);
//                res = combineSubst(result, subst);
//
//                if (res != null) {
//
//                    // remove processing
//
//                    Vector patscopy = (Vector) pats.clone();
//                    patscopy.remove(pterm);
//
//                    Vector datacopy = (Vector) data.clone();
//                    datacopy.remove(dterm);
//
//                    HashMap<Term, Vector<Integer>> p2dcopy = new HashMap<Term, Vector<Integer>>();
//                    HashMap<Term, Vector> p2scopy = new HashMap<Term, Vector>();
//
//                    Enumeration<Term> e = p2d.keys();
//                    while (e.hasMoreElements()) {
//                        Term tmp = e.nextElement();
//                        if (tmp != pterm) {
//                            Vector<Integer> dv = p2d.get(tmp);
//                            Vector sv = p2s.get(tmp);
//
//                            dv = (Vector<Integer>) dv.clone();
//                            sv = (Vector) sv.clone();
//
//                            for (int k = 0; k < dv.size(); k++ ) {
//                                Integer p = dv.elementAt(k);
//                                if (p.intValue() == pos) {
//                                    dv.removeElementAt(k);
//                                    sv.removeElementAt(k);
//                                    k-- ;
//                                } else if (p.intValue() > pos) {
//                                    dv.removeElementAt(k);
//                                    dv.insertElementAt(Integer.valueOf(p.intValue() - 1), k);
//                                }
//                            }
//
//                            p2dcopy.put(tmp, dv);
//                            p2scopy.put(tmp, sv);
//
//                        }
//                    }
//
//                    res = ACMatchDispatch(patscopy, datacopy, p2dcopy, p2scopy, op, sig, res);
//
//                    if (res != null) {
//                        return res;
//                    }
//                }
//            }
//
//            if (!found) {
//                return null;
//            }
//        }
//
//        if (vpat.size() == 1 && dpat.size() == 0) {
//
//            Term term = null;
//            for (int i = 0; i < data.size(); i++ ) {
//                if (i == 0) {
//                    term = (Term) data.elementAt(i);
//                } else {
//                    try {
//                        term = new Term(sig, op, term, (Term) data.elementAt(i));
//                    } catch (Exception e) {
//                    }
//                }
//            }
//            HashMap tab = new HashMap();
//            tab.put(vpat.elementAt(0).var, term);
//            res = combineSubst(res, tab);
//
//        }
//
//        return res;
//
//    }

    private Vector<Map<VarOrCode, Term>> fastACMatch(Vector<Term> patterns,
                                                     Vector<Term> data) {

        Vector<Map<VarOrCode, Term>> result = new Vector<>();

        if (patterns.size() == 0) {

            if (data.size() > 0) {
                Map<VarOrCode, Term> subst = new HashMap<>();
                subst.put(new VarOrCode("ac-rest", data), new Term());
                result.addElement(subst);
            } else {
                result.addElement(new HashMap<VarOrCode, Term>());
            }
        } else {

            Term pat = patterns.elementAt(0);

            for (int i = 0; i < data.size(); i++ ) {
                Term dat = data.elementAt(i);

                Map<VarOrCode, Term> subst = getMatch(dat, pat);
                if (subst != null) {

                    Vector<Term> p = new Vector<>(patterns);
                    p.removeElementAt(0);

                    Vector<Term> d = new Vector<>(data);
                    d.removeElementAt(i);

                    Vector<Map<VarOrCode, Term>> vec = fastACMatch(p, d);
                    for (int j = 0; j < vec.size(); j++ ) {
                        Map<VarOrCode, Term> tmp = vec.elementAt(j);
                        tmp = combineSubst(tmp, subst);

                        if (tmp != null) {
                            result.addElement(tmp);
                        }
                    }

                }
            }
        }

        return result;

    }

    protected Map<VarOrCode, Term> combineSubst(Map<VarOrCode, Term> tab1,
                                                Map<VarOrCode, Term> tab2) {
// TODO Check if early exit would be OK
        HashMap<VarOrCode, Term> result = new HashMap<>(tab1);
        for (VarOrCode var : tab2.keySet()) {
            Term term = tab2.get(var);
            Term tmp = tab1.get(var);
            if (tmp == null) {
                result.put(var, term);
            } else if (!tmp.equals(term)) {
                return null;
            }
        }

        return result;
    }

    private Term subst(Term input,
                       Map<VarOrCode, Term> ht) {

        Term result = null;

        if (ht.isEmpty()) {
            return input;
        }

        try {
            if (input.var != null) {
                Term term = ht.get(input.var);
                // this ought to be useless
                if (term == null) {
                    for (VarOrCode v : ht.keySet()) {
                        if (v instanceof Variable) {
                            if (input.var.equals(v)) {
                                term = ht.get(v);
                                break;
                            }
                        }
                    }
                }

                if (term != null && term.var != null) {
                    result = new Term(term.var);
                } else if (term != null && term.operation != null) {
                    result = new Term(sig, term.operation, term.subterms);
                }

                if (result == null) {
                    result = new Term(input.var);
                }

            } else {
                Term[] tmp = new Term[input.subterms.length];
                for (int i = 0; i < input.subterms.length; i++ ) {
                    tmp[i] = input.subterms[i].subst(ht, sig);

                }
                result = getMinimumTerm(sig, input.operation, tmp);
                if (result == null) {
                    result = new Term(sig, input.operation, tmp);
                }
            }
        } catch (TermException e) {
        }

        return result;
    }

    private Redex getSpecialRedex(Term input,
                                  int pos) {

        Redex result = null;

        if (input.nocheck || input.noscheck || input.var != null) {
            return null;
        }

        if (input.sort.isHidden()) {
            Term term = input.parent;
            while (term != null && term.sort.isHidden()) {
                if (term.operation.isBehavorial()) {
                    term = term.parent;
                } else {
                    for (int i = 0; i < input.subterms.length && result == null; i++ ) {

                        if (input.subterms[i].var == null)
                            result = getSpecialRedex(input.subterms[i], i);
                    }

                    if (result == null) {

                        System.out.println(" >>>>>>> SET NOGCHECK: " + input);

                        input.nogcheck = true;
                    }
                    return result;
                }
            }
        }

        Vector<Equation> conside = null;
        if (input.operation != null) {
            conside = op2eq.get(input.operation.getName());
        }
        if (conside == null) {
            conside = new Vector<>();
        }

        if (input.operation.isCommutative) {
            if (input.operation.isAssociative) {

                for (int i = 0; i < conside.size(); i++ ) {

                    Equation eq = conside.elementAt(i);
                    Term left = eq.left;
                    Term right = eq.right;
                    Term cond = eq.condition;

                    Map<VarOrCode, Term> var2term = getACMatch(input, left);

                    if (var2term != null) {

                        Vector<Term> dterms = getCodeValue(var2term, "secret");

                        Term term = null;
                        if (dterms != null && dterms.size() > 0) {
                            removeCodeValue(var2term, "secret");

                            term = dterms.elementAt(0);
                            for (int j = 1; j < dterms.size(); j++ ) {
                                Term tmp = dterms.elementAt(j);
                                Term[] args =
                                    {
                                        term, tmp
                                    };
                                try {
                                    term = new Term(sig, input.operation, args);
                                } catch (Exception e) {
                                }
                            }
                        }

                        if (cond != null) {

                            Term tmp = cond.subst(var2term, sig);
                            tmp = reduce(tmp);
                            int res = boolValue(tmp);

                            if (res != 1) {
                                continue;
                            }
                        }

                        right = right.subst(var2term, sig);

                        if (right.operation != null) {
                            try {
                                right = new Term(sig, right.operation, right.subterms);
                                if (term != null) {
                                    Term[] args =
                                        {
                                            right, term
                                        };
                                    right = getMinimumTerm(sig, input.operation, args);
                                    if (right == null) {
                                        right = new Term(sig, input.operation, args);
                                    }
                                }
                            } catch (Exception ex) {
                            }
                        }

                        if (right.equals(input)) {
                            continue;
                        }

                        right = reduce(right);
                        result = new Redex(input, right);
                        result.position = pos;
                        break;
                    }
                }
            } else {

                for (int i = 0; i < conside.size(); i++ ) {
                    Equation eq = conside.elementAt(i);
                    Term left = eq.left;
                    Term right = eq.right;
                    Term cond = eq.condition;

                    Map<VarOrCode, Term> var2term = getCommutativeMatch(input, left);

                    if (var2term != null) {

                        if (cond != null) {

                            Term tmp = cond.subst(var2term, sig);
                            tmp = reduce(tmp);
                            int res = boolValue(tmp);

                            if (res != 1) {
                                continue;
                            }
                        }

                        right = right.subst(var2term, sig);
                        if (right.operation != null) {
                            try {
                                right = new Term(sig, right.operation, right.subterms);
                            } catch (Exception ex) {
                            }
                        }

                        right = reduce(right);
                        result = new Redex(input, right);
                        result.position = pos;
                        break;
                    }
                }

            }

        } else if (input.operation.isAssociative) {

            for (int i = 0; i < conside.size(); i++ ) {
                Equation eq = conside.elementAt(i);
                Term left = eq.left;
                Term right = eq.right;
                Term cond = eq.condition;

                Map<VarOrCode, Term> var2term = getAMatch(input, left);
                if (var2term != null) {

                    Term bterm = getCodeValue(var2term, "bterm");
                    Term eterm = getCodeValue(var2term, "eterm");

                    if (bterm != null) {
                        removeCodeValue(var2term, "bterm");
                    }

                    if (eterm != null) {
                        removeCodeValue(var2term, "eterm");
                    }

                    if (cond != null) {

                        Term tmp = cond.subst(var2term, sig);
                        tmp = reduce(tmp);
                        int res = boolValue(tmp);

                        if (res != 1) {
                            continue;
                        }
                    }

                    right = right.subst(var2term, sig);
                    if (right.equals(input)) {
                        continue;
                    }

                    if (right.operation != null) {
                        try {
                            right = new Term(sig, right.operation, right.subterms);
                        } catch (Exception ex) {
                        }
                    }

                    try {
                        if (bterm != null) {
                            Term[] args =
                                {
                                    bterm, right
                                };
                            right = getMinimumTerm(sig, input.operation, args);
                        }

                        if (eterm != null) {
                            Term[] args =
                                {
                                    right, eterm
                                };
                            right = getMinimumTerm(sig, input.operation, args);
                        }
                    } catch (Exception ex) {
                    }

                    right = reduce(right);
                    result = new Redex(input, right);
                    result.position = pos;
                    break;
                }
            }
        }

        if (result == null) {
            for (int i = 0; i < input.subterms.length && result == null; i++ ) {
                if (input.subterms[i].var == null)
                    result = getSpecialRedex(input.subterms[i], i);
            }
        }

        return result;
    }

    protected static Term getMinimumTerm(Signature sig,
                                         Operation op,
                                         Term[] terms) {

        Term result = null;
        Operation[] ops = sig.getSortedOperationsCompatibleWith(op);

        for (Operation op2 : ops) {

            try {
                result = new Term(sig, op2, terms);
                if (!result.needRetract()) {
                    return result;
                } else {
                    result = null;
                }

            } catch (Exception e) {
            }
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    private <T> T getCodeValue(Map<VarOrCode, Term> subst,
                               String codeName) {
        for (VarOrCode test : subst.keySet()) {
            if (!(test instanceof Variable) && test.name.equals(codeName))
                return (T) test.value;
        }
        return null;
    }

    private void removeCodeValue(Map<VarOrCode, Term> subst,
                                 String codeName) {
        VarOrCode codeKey = new VarOrCode(codeName);
        Term term = subst.get(codeKey);
        if (term != null)
            subst.remove(codeKey);
    }

    private Map<VarOrCode, Term> getCommutativeMatch(Term input,
                                                     Term pattern) {

        Map<VarOrCode, Term> result = new HashMap<>();

        if (input.operation.equals(pattern.operation)) {

            Term subpat0 = pattern.subterms[0];
            Term subpat1 = pattern.subterms[1];

            Term term0 = input.subterms[0];
            Term term1 = input.subterms[1];

            Map<VarOrCode, Term> ht0 = getMatch(term0, subpat1);
            Map<VarOrCode, Term> ht1 = getMatch(term1, subpat0);
            // put matches
            if (ht0 != null && ht1 != null) {
                result = ht0;
                for (VarOrCode var : ht1.keySet()) {
                    Term var1 = result.get(var);
                    Term trm1 = ht1.get(var);
                    Term trm2 = null;
                    if (var1 != null && var1.isVariable()) {
                        trm2 = result.get(var1.var);
                    }
                    if (trm2 == null) {
                        result.put(var, trm1);
                    } else if (!trm1.equals(trm2)) {
                        return null;
                    }
                }
            } else {
                result = null;
            }

        } else {
            result = null;
        }
        return result;
    }

    private Map<VarOrCode, Term> getACMatch(Term input,
                                            Term pattern) {

        Map<VarOrCode, Term> result = null;

        if (input.operation.equals(pattern.operation)) {

            try {
                Vector<Term> dterms = input.getAssocSubterms(sig, input.operation);
                Vector<Term> pterms = pattern.getAssocSubterms(sig, input.operation);

                if (pterms.size() == 2) {

                    Term p1 = pterms.elementAt(0);
                    Term p2 = pterms.elementAt(1);

                    if (p1.var != null && p1.equals(p2)) {

                        // find a term occuring in dterms two time2
                        for (int i = 0; i < dterms.size(); i++ ) {
                            Term term = dterms.elementAt(i);

                            for (int j = i + 1; j < dterms.size(); j++ ) {
                                Term tmp = dterms.elementAt(j);

                                if (term.equals(tmp)) {

                                    dterms.removeElementAt(j);
                                    dterms.removeElementAt(i);

                                    result = new HashMap<>();
                                    result.put(p1.var, term);
                                    result.put(new VarOrCode("secret", dterms), null);

                                    return result;

                                }
                            }
                        }
                    }

                }

                @SuppressWarnings("unchecked")
                Vector<Term>[] count = new Vector[dterms.size() + 1];

                for (int i = 0; i < count.length; i++ ) {
                    count[i] = new Vector<>();
                }

                Map<Term, Vector<Term>> recordTerms = new HashMap<>();
                Map<Term, Vector<Map<VarOrCode, Term>>> recordSubst = new HashMap<>();

                for (int i = 0; i < pterms.size(); i++ ) {
                    Term tmp = pterms.elementAt(i);
                    Vector<Term> terms = new Vector<>();
                    Vector<Map<VarOrCode, Term>> subst = new Vector<>();
                    recordTerms.put(tmp, terms);
                    recordSubst.put(tmp, subst);

                    for (int j = 0; j < dterms.size(); j++ ) {
                        Term term = dterms.elementAt(j);

                        Map<VarOrCode, Term> ht = getMatch(term, tmp);
                        if (ht != null) {
                            terms.addElement(term);
                            subst.addElement(ht);
                        }
                    }
                    count[terms.size()].addElement(tmp);
                }

                result = dispatch(count, recordTerms, recordSubst, dterms,
                                  new HashMap<VarOrCode, Term>());

            } catch (Exception e) {
                return null;
            }
        } else {
            result = null;
        }

        return result;
    }

    private Map<VarOrCode, Term> dispatch(Vector<Term>[] count,
                                          Map<Term, Vector<Term>> terms,
                                          Map<Term, Vector<Map<VarOrCode, Term>>> subst,
                                          Vector<Term> dterms) {

        Map<VarOrCode, Term> result = null;

        if (count[0].isEmpty()) {
            int i;
            for (i = 1; i < count.length && count[i].isEmpty(); i++ ) {
            }

            if (i < count.length) {
                Term pat = count[i].elementAt(0);
                count[i].removeElementAt(0);

                Vector<Term> candidate = terms.get(pat);
                Vector<Map<VarOrCode, Term>> sub = subst.get(pat);
                terms.remove(pat);
                subst.remove(pat);

                for (i = 0; i < candidate.size(); i++ ) {
                    Term term = candidate.elementAt(i);
                    Map<VarOrCode, Term> ht = sub.elementAt(i);

                    dterms.remove(term);

                    // remove term from other records

                    for (Term tmpPat : terms.keySet()) {
                        Vector<Term> matchs = terms.get(tmpPat);
                        Vector<Map<VarOrCode, Term>> subs = subst.get(tmpPat);
                        int k = matchs.indexOf(term);
                        if (k != -1) {
                            count[matchs.size()].remove(tmpPat);
                            count[matchs.size() - 1].addElement(tmpPat);
                            matchs.removeElementAt(k);
                            subs.removeElementAt(k);
                        }
                    }

                    result = dispatch(count, new HashMap<>(terms), new HashMap<>(subst), dterms);
                    if (result != null) {
                        for (VarOrCode var : ht.keySet()) {
                            Term trm1 = ht.get(var);
                            Term trm2 = result.get(var);
                            if (trm2 == null) {
                                result.put(var, trm1);
                            } else if (!trm1.equals(trm2)) {
                                result = null;
                                break;
                            }
                        }

                        if (result != null) {
                            result.put(new VarOrCode("secret", dterms), new Term());
                            return result;
                        } else {

                        }
                    }
                    dterms.addElement(term);

                }

            } else {
                return new HashMap<>();
            }
        }

        return result;

    }

    private Map<VarOrCode, Term> dispatch(Vector<Term>[] count,
                                          Map<Term, Vector<Term>> recordTerms,
                                          Map<Term, Vector<Map<VarOrCode, Term>>> recordSubst,
                                          Vector<Term> dterms,
                                          Map<VarOrCode, Term> ref) {

        Map<VarOrCode, Term> result = null;

        if (count[0].size() == 0) {

            int i;

            // find the min i such that count[i].size() != 0
            for (i = 1; i < count.length && count[i].size() == 0; i++ ) {
            }

            if (i < count.length) {

                Term pat = count[i].elementAt(0);
                count[i].removeElementAt(0);

                Vector<Term> candidate = recordTerms.get(pat);
                Vector<Map<VarOrCode, Term>> sub = recordSubst.get(pat);
                recordTerms.remove(pat);
                recordSubst.remove(pat);

                if (candidate != null)
                    for (i = 0; i < candidate.size(); i++ ) {

                        Term term = candidate.elementAt(i);
                        Map<VarOrCode, Term> ht = sub.elementAt(i);

                        // check if pat => term is compatible in ref
                        HashMap<VarOrCode, Term> mid = new HashMap<>(ref);
                        for (VarOrCode var : ht.keySet()) {
                            Term trm1 = ht.get(var);
                            Term trm2 = mid.get(var);
                            if (trm2 == null) {
                                mid.put(var, trm1);
                            } else if (!trm1.equals(trm2)) {
                                mid = null;
                                break;
                            }

                        }

                        if (mid == null) {
                            //System.out.println("compatible ");
                            continue;
                        } else {
                            //System.out.println("not compatible ");
                        }

                        dterms.remove(term);

                        // remove term from other records

                        for (Term tmpPat : recordTerms.keySet()) {
                            Vector<Term> matchs = recordTerms.get(tmpPat);
                            Vector<Map<VarOrCode, Term>> subs = recordSubst.get(tmpPat);
                            int k = matchs.indexOf(term);
                            if (k != -1) {
                                count[matchs.size()].remove(tmpPat);
                                count[matchs.size() - 1].addElement(tmpPat);
                                matchs.removeElementAt(k);
                                subs.removeElementAt(k);
                            }
                        }

                        result = dispatch(count, new HashMap<>(recordTerms),
                                          new HashMap<>(recordSubst), dterms, mid);

                        if (result != null) {
                            for (VarOrCode var : ht.keySet()) {
                                Term trm1 = ht.get(var);
                                Term trm2 = result.get(var);
                                if (trm2 == null) {
                                    result.put(var, trm1);
                                } else if (!trm1.equals(trm2)) {
                                    result = null;
                                    break;
                                }
                            }

                            if (result != null) {
                                result.put(new VarOrCode("secret", dterms), new Term());
                                return result;
                            } else {

                            }
                        }
                        dterms.addElement(term);

                    }

            } else {
                return new HashMap<>();
            }
        }

        return result;

    }

    private Map<VarOrCode, Term> getAMatch(Term input,
                                           Term pattern) {

        Map<VarOrCode, Term> result = null;

        if (input.operation.equals(pattern.operation)
            || input.operation.less(sig, pattern.operation)) {

            try {
                Vector<Term> dterms = input.getAssocSubterms(sig, input.operation);
                Vector<Term> pterms = pattern.getAssocSubterms(sig, pattern.operation);
                for (int i = 0; i < dterms.size() - pterms.size() + 1; i++ ) {

                    Map<VarOrCode, Term> res = new HashMap<>();
                    for (int j = 0; j < pterms.size(); j++ ) {
                        Term pat = pterms.elementAt(j);
                        Term data = dterms.elementAt(i + j);

                        Map<VarOrCode, Term> tmp = getMatch(data, pat);
                        if (tmp != null) {
                            for (VarOrCode var : tmp.keySet()) {
                                Term trm1 = tmp.get(var);
                                Term trm2 = res.get(var);
                                if (trm2 == null) {
                                    res.put(var, trm1);
                                } else if (!trm1.equals(trm2)) {
                                    res = null;
                                    break;
                                }
                            }

                        } else {
                            res = null;
                            break;
                        }
                    }

                    if (res != null) {

                        Term bterm = null;
                        for (int j = 0; j < i; j++ ) {
                            if (bterm == null) {
                                bterm = dterms.elementAt(j);
                            } else {
                                try {
                                    Term[] args =
                                        {
                                            bterm, dterms.elementAt(j)
                                        };
                                    bterm = getMinimumTerm(sig, input.operation, args);
                                } catch (Exception e) {
                                    //e.printStackTrace();
                                }
                            }
                        }

                        Term eterm = null;
                        for (int j = i + pterms.size(); j < dterms.size(); j++ ) {
                            if (eterm == null) {
                                eterm = dterms.elementAt(j);
                            } else {
                                try {
                                    Term[] args =
                                        {
                                            eterm, dterms.elementAt(j)
                                        };
                                    //eterm = new Term(sig, operation, args);
                                    eterm = getMinimumTerm(sig, input.operation, args);
                                } catch (Exception e) {
                                    //e.printStackTrace();
                                }
                            }
                        }

                        if (bterm != null) {
                            res.put(new VarOrCode("bterm", bterm), new Term());
                        }

                        if (eterm != null) {
                            res.put(new VarOrCode("eterm", eterm), new Term());
                        }

                        return res;
                    }
                }

                // not matched
                Map<VarOrCode, Term> tab = getAMatchPossible(dterms, pterms, input.operation);

                if (tab != null)
                    return tab;

            } catch (Exception e) {
                return null;
            }
        } else {
            result = null;
        }

        return result;
    }

    private Map<VarOrCode, Term> getAMatchPossible(Vector<Term> dterms,
                                                   Vector<Term> pterms,
                                                   Operation op) {

        for (int i = 0; i < dterms.size(); i++ ) {
            for (int j = i + pterms.size(); j < dterms.size(); j++ ) {

                // check from i <= x < j
                Vector<Term> d = new Vector<>();
                for (int k = i; k < j; k++ ) {
                    d.addElement(dterms.elementAt(k));
                }

                ArrayList<ArrayList<Term>> list = getAMatchPossibleHelp(d, pterms, op);
                for (ArrayList<Term> al : list) {

                    try {

                        Map<VarOrCode, Term> res = new HashMap<>();
                        for (int k = 0; k < al.size(); k++ ) {
                            Term pat = pterms.elementAt(k);
                            Term data = al.get(k);
                            Map<VarOrCode, Term> tmp = getMatch(data, pat);
                            if (tmp != null) {
                                for (VarOrCode var : tmp.keySet()) {
                                    Term trm1 = tmp.get(var);
                                    Term trm2 = res.get(var);
                                    if (trm2 == null) {
                                        res.put(var, trm1);
                                    } else if (!trm1.equals(trm2)) {
                                        res = null;
                                        break;
                                    }
                                }

                            } else {
                                res = null;
                                break;
                            }
                        }

                        if (res != null) {

                            // begin: 0 <= y < i
                            Term begin = null;
                            for (int k = 0; k < i; k++ ) {
                                Term tmp = dterms.elementAt(k);
                                if (begin == null) {
                                    begin = tmp;
                                } else {
                                    begin = new Term(sig, op, begin, tmp);

                                }
                            }
                            res.put(new VarOrCode("bterm", begin), new Term());

                            // end: j <= z < dterms.size()
                            Term end = null;
                            for (int k = j; k < dterms.size(); k++ ) {
                                Term tmp = dterms.elementAt(k);
                                if (end == null) {
                                    end = tmp;
                                } else {
                                    end = new Term(sig, op, end, tmp);

                                }
                            }
                            res.put(new VarOrCode("eterm", end), new Term());

                            return res;

                        }

                    } catch (Exception e) {
                    }
                }
            }
        }

        return null;

    }

    private ArrayList<ArrayList<Term>> getAMatchPossibleHelp(Vector<Term> dterms,
                                                             Vector<Term> pterms,
                                                             Operation op) {
        ArrayList<ArrayList<Term>> result = new ArrayList<>();

        if (dterms.size() > 0 && pterms.size() > 0) {
            Term dat = dterms.elementAt(0);
            Term pat = pterms.elementAt(0);

            if (!pat.isVariable()) {
                Vector<Term> nd = new Vector<>(dterms);
                nd.removeElementAt(0);

                Vector<Term> np = new Vector<>(pterms);
                np.removeElementAt(0);

                ArrayList<ArrayList<Term>> res = getAMatchPossibleHelp(nd, np, op);

                for (int i = 0; i < res.size(); i++ ) {
                    ArrayList<Term> l = res.get(i);
                    l.add(0, dat);
                    result.add(l);
                }

            } else {

                for (int j = 1; j < dterms.size() - pterms.size() + 1; j++ ) {

                    try {

                        // create a term from 0 to j
                        Vector<Term> nd = new Vector<>(dterms);
                        Term term = null;
                        for (int k = 0; k <= j; k++ ) {
                            Term tmp = nd.elementAt(k);

                            if (term == null) {
                                term = tmp;
                            } else {
                                term = new Term(sig, op, term, tmp);
                            }

                        }

                        for (int k = 0; k <= j; k++ ) {
                            nd.removeElementAt(0);
                        }

                        Vector<Term> np = new Vector<>(pterms);
                        np.removeElementAt(0);

                        ArrayList<ArrayList<Term>> res = getAMatchPossibleHelp(nd, np, op);

                        for (int i = 0; i < res.size(); i++ ) {
                            ArrayList<Term> l = res.get(i);
                            l.add(0, term);
                            result.add(l);
                        }

                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }

            }

        } else if (dterms.size() == 0 && pterms.size() == 0) {
            result.add(new ArrayList<Term>());
        }

        return result;
    }

    static public void setTrace(boolean flag) {
        trace = flag;
    }

    private Term getTermForInt(int val) throws TermException, SignatureException {
        if (val > 0) {
            Operation op = new Operation(String.valueOf(val), IntModule.nznatSort,
                                         IntModule.nznatSort.getModuleName());
            return new Term(sig, op);

        } else if (val == 0) {

            Operation op = new Operation(String.valueOf(val), IntModule.zeroSort,
                                         IntModule.zeroSort.getModuleName());
            return new Term(sig, op);

        } else {

            Operation op = new Operation(String.valueOf(val), IntModule.intSort,
                                         IntModule.intSort.getModuleName());
            return new Term(sig, op);
        }
    }

    private Term getTermForInt(Vector<Term> vec,
                               int val,
                               Operation oper)
        throws TermException, SignatureException {
        if (val > 0) {

            Operation op = new Operation(String.valueOf(val), IntModule.nznatSort,
                                         IntModule.nznatSort.getModuleName());
            Term res = new Term(sig, op);
            for (int i = 0; i < vec.size(); i++ ) {
                Term tmp = vec.elementAt(i);
                res = new Term(sig, oper, res, tmp);
            }
            return res;

        } else if (val == 0) {

            Operation op = new Operation(String.valueOf(val), IntModule.zeroSort,
                                         IntModule.zeroSort.getModuleName());
            Term res = new Term(sig, op);
            if (vec.isEmpty()) {
                return res;
            } else {
                for (int i = 0; i < vec.size(); i++ ) {
                    Term tmp = vec.elementAt(i);
                    if (i == 0) {
                        res = tmp;
                    } else {
                        res = new Term(sig, oper, res, tmp);
                    }
                }
                return res;
            }

        } else {

            Operation op = new Operation(String.valueOf(val), IntModule.intSort,
                                         IntModule.intSort.getModuleName());
            Term res = new Term(sig, op);

            for (int i = 0; i < vec.size(); i++ ) {
                Term tmp = vec.elementAt(i);
                res = new Term(sig, oper, res, tmp);
            }
            return res;
        }

    }

    private Term getTermForInt(Vector<Term> vec,
                               Operation oper)
        throws TermException, SignatureException {
        Term res = null;
        for (int i = 0; i < vec.size(); i++ ) {
            Term tmp = vec.elementAt(i);
            if (i == 0) {
                res = tmp;
            } else {
                res = new Term(sig, oper, res, tmp);
            }
        }
        return res;

    }

    private Term getTermForFloat(Vector<Term> vec,
                                 double val,
                                 Operation oper) {
        try {
            Operation op = new Operation(String.valueOf(val), FloatModule.floatSort,
                                         FloatModule.floatt.getModuleName());
            Term res = new Term(sig, op);
            for (int i = 0; i < vec.size(); i++ ) {
                Term tmp = vec.elementAt(i);
                res = new Term(sig, oper, res, tmp);
            }
            return res;
        } catch (Exception e) {
            return null;
        }

    }

    private Term getTermForFloat(Vector<Term> vec,
                                 Operation oper) {
        try {
            if (vec.size() == 0) {
                Sort floatSort = FloatModule.floatSort;
                Operation zero = new Operation("0.0", floatSort, floatSort.getModuleName());
                return new Term(sig, zero);

            }

            Term res = null;
            for (int i = 0; i < vec.size(); i++ ) {
                Term tmp = vec.elementAt(i);
                if (res == null) {
                    res = tmp;
                } else {
                    res = new Term(sig, oper, res, tmp);
                }
            }
            return res;
        } catch (Exception e) {
            return null;
        }
    }

    private Term getTermForFloat(double val) {
        try {
            Operation op = new Operation(String.valueOf(val), FloatModule.floatSort,
                                         FloatModule.floatt.getModuleName());
            return new Term(sig, op);
        } catch (Exception e) {
            return null;
        }
    }

    public Term apply(Term input,
                      Equation eq,
                      boolean reverse,
                      TermSelection select,
                      Map<VarOrCode, Term> map2)
        throws EquationApplyException {

        if (debug)
            System.err.println("Applying " + eq + " to " + input);

        SelectedTerm result = select(input, select);
        Term left, right, cond, shift = null;
        if (reverse) {
            left = subst(eq.right, map2);
            right = subst(eq.left, map2);
        } else {
            left = subst(eq.left, map2);
            right = subst(eq.right, map2);
        }

        if (eq.condition != null) {
            cond = subst(eq.condition.copy(sig), map2);
        } else {
            cond = null;
        }

        if (result != null) {

            // check behavorial condition
            if (result.selected.sort.isHidden()) {
                Term t = result.selected.parent;
                while (t != null && t.sort.isHidden()) {
                    if (t.operation.isBehavorial()) {
                        t = t.parent;
                    } else {
                        throw new EquationApplyException("the equation can't be applied at the specified "
                                                         + "position since "
                                                         + t.operation.getCleanName()
                                                         + " is not congruent");
                    }
                }
            }

            Map<VarOrCode, Term> var2term = getMatch(result.selected, left);

            if (var2term != null) {
                if (cond != null) {
                    Term tmp = cond.subst(var2term, sig);
                    int res = boolValue(tmp);
                    if (res != 1) {
                        shift = tmp;
                    }
                }

                right = right.subst(var2term, sig);
                if (right.operation != null) {
                    try {
                        Term tmp = right;
                        right = getMinimumTerm(sig, right.operation, right.subterms);
                        if (right == null) {
                            right = new Term(sig, tmp.operation, tmp.subterms);
                        }

                    } catch (Exception ex) {
                    }
                }

                if (result.position != -1) {
                    result.selected.parent.subterms[result.position] = right;
                    right.parent = result.selected.parent;
                    if (sig.isSubsort(right.sort,
                                      result.selected.parent.operation.argumentSorts[result.position])) {

                    } else
                        if (sig.isSubsort(result.selected.parent.operation.argumentSorts[result.position],
                                          right.sort)) {
                                              result.selected.parent.retract[result.position] =
                                                  result.selected.parent.operation.argumentSorts[result.position];
                                          }

                    Term output = result.top;

                    if (shift != null) {
                        output.setProperty("cond", shift);
                    }
                    if (debug)
                        System.err.println("result " + output);

                    return output;
                } else {

                    Term output = right;
                    if (shift != null) {
                        output.setProperty("cond", shift);
                    }
                    if (debug)
                        System.err.println("Result " + output);

                    return output;
                }

            } else
                if (result.selected.operation != null && result.selected.operation.isAssociative()
                    && result.selected.operation.isCommutative()) {

                        var2term = getACMatch(result.selected, left);
                        if (var2term != null) {

                            Vector<Term> secret = getCodeValue(var2term, "secret");
                            removeCodeValue(var2term, "secret");

                            if (cond != null) {
                                Term tmp = cond.subst(var2term, sig);
                                //tmp = reduce(tmp);

                                int res = boolValue(tmp);
                                if (res != 1) {
                                    shift = tmp;
                                }

                            }

                            right = right.subst(var2term, sig);
                            if (right.operation != null) {
                                try {
                                    Term tmp = right;
                                    right = getMinimumTerm(sig, right.operation, right.subterms);
                                    if (right == null) {
                                        right = new Term(sig, tmp.operation, tmp.subterms);
                                    }

                                } catch (Exception ex) {
                                }
                            }

                            try {

                                for (int i = 0; i < secret.size(); i++ ) {
                                    Term tmp = secret.elementAt(i);
                                    right = new Term(sig, result.selected.operation, right, tmp);
                                }
                            } catch (Exception ex) {
                                throw new EquationApplyException(ex.getMessage());
                            }

                            if (result.position != -1) {

                                result.selected.parent.subterms[result.position] = right;
                                right.parent = result.selected.parent;

                                if (sig.isSubsort(right.sort,
                                                  result.selected.parent.operation.argumentSorts[result.position])) {

                                } else
                                    if (sig.isSubsort(result.selected.parent.operation.argumentSorts[result.position],
                                                      right.sort)) {
                                                          result.selected.parent.retract[result.position] =
                                                              result.selected.parent.operation.argumentSorts[result.position];
                                                      }

                                Term output = result.top;
                                if (shift != null) {
                                    output.setProperty("cond", shift);
                                }
                                if (debug)
                                    System.err.println("Result " + output);
                                return output;
                            } else {

                                Term output = right;
                                if (shift != null) {
                                    output.setProperty("cond", shift);
                                }
                                if (debug)
                                    System.err.println("Result " + output);
                                return output;
                            }

                        } else {
                            throw new EquationApplyException("the equation can't be "
                                                             + "applied at the "
                                                             + "specified position");
                        }

                    } else if (result.selected.operation != null
                               && result.selected.operation.isAssociative()
                               && !result.selected.operation.isCommutative()) {

                                   var2term = getAMatch(result.selected, left);
                                   if (var2term != null) {

                                       Term bterm = getCodeValue(var2term, "bterm");
                                       Term eterm = getCodeValue(var2term, "eterm");

                                       if (cond != null) {
                                           Term tmp = cond.subst(var2term, sig);

                                           int res = boolValue(tmp);
                                           if (res != 1) {
                                               shift = tmp;
                                           }

                                       }

                                       right = right.subst(var2term, sig);
                                       if (right.operation != null) {
                                           try {
                                               Term tmp = right;
                                               right = getMinimumTerm(sig, right.operation,
                                                                      right.subterms);
                                               if (right == null) {
                                                   right =
                                                       new Term(sig, tmp.operation, tmp.subterms);
                                               }

                                           } catch (Exception ex) {
                                           }
                                       }

                                       try {
                                           if (bterm != null) {
                                               right = new Term(sig, result.selected.operation,
                                                                bterm, right);
                                           }

                                           if (eterm != null) {
                                               right = new Term(sig, result.selected.operation,
                                                                right, eterm);
                                           }

                                       } catch (Exception ex) {
                                           throw new EquationApplyException(ex.getMessage());
                                       }

                                       if (result.position != -1) {
                                           result.selected.parent.subterms[result.position] = right;
                                           right.parent = result.selected.parent;

                                           if (sig.isSubsort(right.sort,
                                                             result.selected.parent.operation.argumentSorts[result.position])) {

                                           } else
                                               if (sig.isSubsort(result.selected.parent.operation.argumentSorts[result.position],
                                                                 right.sort)) {
                                                                     result.selected.parent.retract[result.position] =
                                                                         result.selected.parent.operation.argumentSorts[result.position];
                                                                 }

                                           Term output = result.top;
                                           if (shift != null) {
                                               output.setProperty("cond", shift);
                                           }
                                           if (debug)
                                               System.err.println("Result " + output);
                                           return output;
                                       } else {

                                           Term output = right;
                                           if (shift != null) {
                                               output.setProperty("cond", shift);
                                           }
                                           if (debug)
                                               System.err.println("Result " + output);
                                           return output;
                                       }

                                   } else {
                                       throw new EquationApplyException("the equation can't be "
                                                                        + "applied at the "
                                                                        + "specified position");
                                   }

                               }

        } else if (select.kind == TermSelection.WITHIN) {

            Term term = reduceBy(input, left, right, cond);
            if (debug)
                System.err.println("Result " + term);

            return term;

        }

        throw new EquationApplyException("the equation can't be applied");

    }

    private Term reduceBy(Term input,
                          Term left,
                          Term right,
                          Term cond)
        throws EquationApplyException {

        // check behavorial rewrite condition
        if (input.sort.isHidden()) {
            Term t = input.parent;
            while (t != null && t.sort.isHidden()) {
                if (t.operation.isBehavorial()) {
                    t = t.parent;
                } else {
                    throw new EquationApplyException("the term can't be reduce since "
                                                     + t.operation.getCleanName()
                                                     + " is not congruent");
                }
            }
        }

        Term shift = null;
        Map<VarOrCode, Term> var2term = getMatch(input, left);
        if (var2term != null) {

            boolean okay = true;
            if (cond != null) {
                Term tmp = cond.subst(var2term, sig);
                int res = boolValue(tmp);
                if (res != 1) {
                    shift = tmp;
                }
            }

            if (okay) {
                right = right.subst(var2term, sig);
                if (right.operation != null) {
                    try {
                        Term tmp = right;
                        right = getMinimumTerm(sig, right.operation, right.subterms);
                        if (right == null) {
                            right = new Term(sig, tmp.operation, tmp.subterms);
                        }
                    } catch (Exception ex) {
                    }
                }

                if (shift != null) {
                    right.setProperty("cond", shift);
                }

                return right;
            }

        } else if (input.operation != null && input.operation.isAssociative()
                   && input.operation.isCommutative()) {

                       // try AC match
                       var2term = getACMatch(input, left);
                       if (var2term != null) {

                           Vector<Term> secret = getCodeValue(var2term, "secret");
                           removeCodeValue(var2term, "secret");

                           if (cond != null) {
                               Term tmp = cond.subst(var2term, sig);

                               int res = boolValue(tmp);
                               if (res != 1) {
                                   shift = tmp;
                               }

                           }

                           right = right.subst(var2term, sig);
                           if (right.operation != null) {
                               try {
                                   Term tmp = right;
                                   right = getMinimumTerm(sig, right.operation, right.subterms);
                                   if (right == null) {
                                       right = new Term(sig, tmp.operation, tmp.subterms);
                                   }

                               } catch (Exception ex) {
                               }
                           }

                           try {

                               for (int i = 0; i < secret.size(); i++ ) {
                                   Term tmp = secret.elementAt(i);
                                   right = new Term(sig, input.operation, right, tmp);
                               }
                           } catch (Exception ex) {
                               throw new EquationApplyException(ex.getMessage());
                           }

                           if (shift != null) {
                               right.setProperty("cond", shift);
                           }

                           return right;

                       }

                   } else
            if (input.operation != null && input.operation.isAssociative()
                && !input.operation.isCommutative()) {

                    // try A match
                    var2term = getAMatch(input, left);
                    if (var2term != null) {

                        Term bterm = getCodeValue(var2term, "bterm");
                        Term eterm = getCodeValue(var2term, "eterm");

                        if (cond != null) {
                            Term tmp = cond.subst(var2term, sig);

                            int res = boolValue(tmp);
                            if (res != 1) {
                                shift = tmp;
                            }

                        }

                        right = right.subst(var2term, sig);
                        if (right.operation != null) {
                            try {
                                Term tmp = right;
                                right = getMinimumTerm(sig, right.operation, right.subterms);
                                if (right == null) {
                                    right = new Term(sig, tmp.operation, tmp.subterms);
                                }

                            } catch (Exception ex) {
                            }
                        }

                        try {
                            if (bterm != null) {
                                right = new Term(sig, input.operation, bterm, right);
                            }

                            if (eterm != null) {
                                right = new Term(sig, input.operation, right, eterm);
                            }

                        } catch (Exception ex) {
                            throw new EquationApplyException(ex.getMessage());
                        }

                        if (shift != null) {
                            right.setProperty("cond", shift);
                        }

                        return right;

                    }

                }

        if (input.operation != null) {

            Term[] args = new Term[input.subterms.length];
            boolean done = false;
            for (int i = 0; i < input.subterms.length; i++ ) {

                if (done) {
                    args[i] = input.subterms[i];
                } else {
                    try {
                        args[i] = reduceBy(input.subterms[i], left, right, cond);
                        shift = (Term) args[i].getPropertyBy("cond");
                        if (shift != null) {
                            args[i].removePropertyBy("cond");
                        }

                        done = true;
                    } catch (Exception e) {
                        args[i] = input.subterms[i];
                    }
                }
            }

            if (done) {
                try {
                    Term result = new Term(sig, input.operation, args);
                    if (shift != null) {
                        result.setProperty("cond", shift);
                    }
                    return result;
                } catch (Exception e) {
                }
            }
        }

        throw new EquationApplyException("the equation can't be applied");

    }

    protected Term applyReductionAt(Term input,
                                    TermSelection select)
        throws EquationApplyException {
        if (select.kind == TermSelection.WITHIN) {
            return reduce(input);
        } else {

            SelectedTerm result = select(input, select);
            if (result != null) {
                Term term = reduce(result.selected);
                if (result.position == -1) {
                    return term;
                } else {
                    result.selected.parent.subterms[result.position] = term;
                    term.parent = result.selected.parent;

                    if (sig.isSubsort(term.sort,
                                      result.selected.parent.operation.argumentSorts[result.position])) {

                    } else
                        if (sig.isSubsort(result.selected.parent.operation.argumentSorts[result.position],
                                          term.sort)) {
                                              result.selected.parent.retract[result.position] =
                                                  result.selected.parent.operation.argumentSorts[result.position];
                                          }

                    return result.top;
                }
            }
            throw new EquationApplyException("can't apply reduction.");
        }
    }

    public SelectedTerm select(Term term,
                               TermSelection select)
        throws EquationApplyException {

        SelectedTerm result = null;

        Term topTerm = term, selectedTerm = term;
        int position;

        switch (select.kind) {

            case TermSelection.TOP:

                topTerm = term;
                selectedTerm = term;
                position = -1;
                result = new SelectedTerm(topTerm, selectedTerm, position);
            break;

            case TermSelection.RANGE:

                try {

                    if (term.operation != null && term.operation.isAssociative()) {

                        Vector<Term> data = term.getAssocSubterms(sig, term.operation);
                        Term[] terms = new Term[select.end - select.begin + 1];
                        Term[] before = new Term[select.begin - 1];
                        Term[] after = new Term[data.size() - select.end];

                        int j = 0, k = 0, l = 0;
                        for (int i = 0; i < data.size(); i++ ) {
                            Term tmp = data.elementAt(i);
                            if (i >= select.begin - 1 && i <= select.end - 1) {
                                terms[j] = tmp;
                                j++ ;
                            } else if (i < select.begin - 1) {
                                before[k] = tmp;
                                k++ ;
                            } else {
                                after[l] = tmp;
                                l++ ;
                            }
                        }

                        if (terms.length == 0) {
                            throw new EquationApplyException("incorrect selection range");
                        } else {

                            selectedTerm = terms[0];
                            for (int i = 1; i < terms.length; i++ ) {
                                selectedTerm =
                                    new Term(sig, term.operation, selectedTerm, terms[i]);
                            }

                            position = 0;

                            if (before.length > 0) {
                                Term b = before[0];
                                for (int i = 1; i < before.length; i++ ) {
                                    b = new Term(sig, term.operation, b, before[i]);
                                }

                                topTerm = new Term(sig, term.operation, b, selectedTerm);
                                position = 1;
                            } else {
                                topTerm = selectedTerm;
                            }

                            if (after.length > 0) {
                                for (Term element : after) {
                                    topTerm = new Term(sig, term.operation, topTerm, element);
                                }
                            }

                            if (before.length == 0 && after.length == 0) {
                                position = -1;
                                selectedTerm.parent = term.parent;

                            }

                            result = new SelectedTerm(topTerm, selectedTerm, position);

                        }

                    } else if (!term.operation.isAssociative()) {
                        throw new EquationApplyException("expect an associative operator, "
                                                         + "but found "
                                                         + term.operation.getCleanName());
                    } else {
                        throw new EquationApplyException("expect an associative operator, "
                                                         + "but found a variable " + term.var);
                    }
                } catch (TermException e) {
                    throw new EquationApplyException("the equation can't be applied");
                }

            break;

            case TermSelection.SEQ:

                topTerm = term;
                selectedTerm = term;
                for (int element : select.seq) {
                    if (selectedTerm.operation != null
                        && element <= selectedTerm.operation.getArity()) {
                        selectedTerm = selectedTerm.subterms[element - 1];
                    } else {
                        throw new EquationApplyException("can't select specified term");
                    }
                }

                if (selectedTerm.parent != null) {
                    position = select.seq[select.seq.length - 1] - 1;
                } else {
                    position = -1;
                }

                result = new SelectedTerm(topTerm, selectedTerm, position);
            break;

            case TermSelection.SUB:

                try {

                    List<Term> terms = new ArrayList<>();
                    List<Term> rest = new ArrayList<>();

                    if (term.operation != null && term.operation.isAssociative()
                        && term.operation.isCommutative()) {

                        Vector<Term> data = term.getAssocSubterms(sig, term.operation);
                        for (int element : select.seq) {
                            if (element < data.size()) {
                                terms.add(data.elementAt(element));
                            } else {
                                throw new EquationApplyException("incorrect selection range");
                            }
                        }

                        for (int i = 0; i < data.size(); i++ ) {
                            boolean in = false;
                            for (int element : select.seq) {
                                if (i == element) {
                                    in = true;
                                    break;
                                }
                            }
                            if (!in) {
                                rest.add(data.elementAt(i));
                            }
                        }

                        selectedTerm = terms.get(0);
                        for (int i = 1; i < terms.size(); i++ ) {
                            selectedTerm =
                                new Term(sig, term.operation, selectedTerm, terms.get(i));
                        }

                        topTerm = selectedTerm;
                        for (Term element : rest) {
                            topTerm = new Term(sig, term.operation, topTerm, element);
                        }

                        if (rest.size() == 0) {
                            selectedTerm.parent = term.parent;
                            result = new SelectedTerm(topTerm, selectedTerm, -1);
                        } else {
                            result = new SelectedTerm(topTerm, selectedTerm, 0);
                        }

                    } else if (!term.operation.isAssociative() || !term.operation.isCommutative()) {
                        throw new EquationApplyException("expect an associative and "
                                                         + "commutative operator, " + "but found "
                                                         + term.operation.getCleanName());
                    } else {
                        throw new EquationApplyException("expect an associative and "
                                                         + "commutative operator, "
                                                         + "but found a variable " + term.var);
                    }

                } catch (TermException e) {
                    throw new EquationApplyException("the equation can't be applied");
                }

            break;

            case TermSelection.WITHIN:

                result = null;
            break;

            default:
                result = null;
            break;
        }

        if (result != null) {

            if (select.next != null) {

                SelectedTerm tmp = select(result.selected, select.next);
                if (result.position != -1) {
                    result.selected.parent.subterms[result.position] = tmp.top;
                    result.selected = tmp.selected;
                    if (tmp.position != -1) {
                        result.position = tmp.position;
                    }
                } else {
                    result = tmp;
                }

                return result;

            } else {
                return result;
            }

        } else {
            return null;
        }
    }

}
