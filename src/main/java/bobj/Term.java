
package bobj;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

public class Term
                  implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    Operation operation;

    Term[] subterms;

    Variable var;

    Map<String, Object> helper;

    Sort[] retract;

    Sort sort;

    Term parent;

    boolean nocheck = false;

    boolean nogcheck = false;

    boolean noscheck = false;

    boolean hasRetract = false;

    static boolean debug = true;

    static boolean showRetract = true;

    protected Term() {
    }

    public Term(Variable v) {
        this.var = v;
        this.helper = new HashMap<>();

        this.retract = new Sort[1];
        this.retract[0] = null;
        this.sort = v.sort;
        this.subterms = new Term[0];
    }

    public Term(Signature sig,
                Operation op,
                Term ... args)
        throws TermException {

        if (op.getArity() == args.length) {

            // check the consistence between o and args
            Sort[] s = op.argumentSorts;
            this.retract = new Sort[s.length];

            for (int i = 0; i < s.length; i++ ) {

                if (sig == null) {

                    if (args[i].sort.equals(s[i])) {
                        this.retract[i] = null;
                    } else {
                        throw new TermException("The " + i + "-th arguments of " + op.getName()
                                                + " should be " + s[i].getName() + ".");
                    }

                } else if (sig.isSubsort(args[i].sort, s[i])) {
                    this.retract[i] = null;
                } else if (sig.isSubsort(s[i], args[i].sort)) {
                    this.retract[i] = s[i];
                } else {
                    Sort tmp = sig.canApply(s[i], args[i].sort);
                    if (tmp != null) {
                        this.retract[i] = tmp;
                    } else {

                        Sort[] s1 = sig.getDirectSupersorts(s[i]);
                        Sort[] s2 = sig.getDirectSupersorts(args[i].sort);
                        if (s1.length == 1 && s2.length == 1 && s1[0].equals(s1[0])) {
                            this.retract[i] = s[i];
                        } else {
                            throw new TermException("The " + i + "-th arguments of " + op.getName()
                                                    + " should be " + s[i].getName() + ".");
                        }

                    }
                }

                this.hasRetract = this.hasRetract || args[i].hasRetract;

            }

            this.operation = op;
            this.subterms = args;
            this.helper = new HashMap<>();

            for (int i = 0; i < args.length; i++ ) {
                args[i].parent = this;
            }

            this.sort = op.resultSort;

            if (op.info.equals("system-retract")) {
                this.hasRetract = true;
            }

        } else {
            throw new TermException(op.getName() + " expects " + op.getArity() + " arguments.");
        }
    }

    public Term(Operation op,
                Term ... args)
        throws TermException {
        this(null, op, args);
    }

    public Term(Operation op)
        throws TermException {
        this(null, op);
    }

    public Term copy() {
        return copy(null);
    }

    public Term copy(Signature sig) {
        if (this.var != null) {
            return new Term(this.var);
        } else {
            Term[] terms = new Term[this.subterms.length];
            for (int i = 0; i < terms.length; i++ ) {
                terms[i] = this.subterms[i].copy(sig);
            }
            try {
                if (sig != null)
                    return new Term(sig, this.operation, terms);
                else return new Term(this.operation, terms);
            } catch (Exception e) {
                return null;
            }
        }
    }

    public Term[] getSubterms() {
        return this.subterms;
    }

    public Variable getVariable() {
        return this.var;
    }

    public boolean isVariable() {
        return(this.var != null);
    }

    public boolean isConstant() {
        return(this.operation != null && this.operation.isConstant());
    }

    public Operation getTopOperation() {
        return this.operation;
    }

    protected Sort[] getRetract() {
        return this.retract;
    }

    public void setProperty(String index,
                            Object obj) {
        this.helper.put(index, obj);
    }

    public Object getPropertyBy(Object index) {
        return this.helper.get(index);
    }

    public Object removePropertyBy(Object index) {
        return this.helper.remove(index);
    }

    @Override
    public boolean equals(Object obj) {

        if (!(obj instanceof Term)) {
            System.err.println("*** Weird: Term compared equal to " + obj);
            return true;
        }

        Term term = (Term) obj;
        boolean result = true;
        if (this.isVariable() && term.isVariable()) {
            result = this.getVariable()
                         .equals(term.getVariable());
        } else if (!this.isVariable() && !term.isVariable()) {
            Operation op1 = this.getTopOperation();
            Operation op2 = term.getTopOperation();
            if (op1.equals(op2)) {
                if (op1.isAssociative() && !op1.isCommutative()) {
                    try {
                        Vector<Term> v1 = this.getAssocSubterms(op1);
                        Vector<Term> v2 = term.getAssocSubterms(op2);

                        if (v1.size() == v2.size()) {
                            boolean same = true;
                            for (int i = 0; i < v1.size(); i++ ) {
                                Term tm1 = v1.elementAt(i);
                                Term tm2 = v2.elementAt(i);
                                same = same && tm1.equals(tm2);
                            }
                            result = same;
                        } else {
                            result = false;
                        }
                    } catch (TermException e) {
                    }

                } else if (op1.isAssociative() && op1.isCommutative()) {

                    try {
                        Vector<Term> v1 = this.getAssocSubterms(op1);
                        Vector<Term> v2 = term.getAssocSubterms(op2);

                        if (v1.size() == v2.size()) {
                            boolean same = true;
                            for (int i = 0; i < v1.size(); i++ ) {
                                Term tm1 = v1.elementAt(i);
                                boolean found = false;
                                for (int j = 0; j < v2.size(); j++ ) {
                                    Term tm2 = v2.elementAt(j);
                                    if (tm1.equals(tm2)) {
                                        v2.remove(tm2);
                                        found = true;
                                        break;
                                    }
                                }
                                if (!found) {
                                    same = false;
                                    break;
                                }
                            }
                            result = same;
                        } else {
                            result = false;
                        }
                    } catch (TermException e) {
                    }

                } else {

                    Term[] tm1 = this.subterms;
                    Term[] tm2 = term.subterms;
                    boolean same = true;
                    for (int i = 0; i < tm1.length; i++ ) {
                        same &= tm1[i].equals(tm2[i]);
                    }
                    result = same;
                }
            } else {
                result = false;
            }
        } else {
            result = false;
        }

        return result;
    }

    @Override
    public int hashCode() {
        if (this.isVariable()) {
            return this.getVariable()
                       .hashCode();
        } else {
            Operation op1 = this.getTopOperation();
            return op1.hashCode() + this.subterms.length;
        }
    }

    public boolean equals(Signature sig,
                          Term term) {

        boolean result = true;
        if (this.isVariable() && term.isVariable()) {
            result = this.getVariable()
                         .equals(term.getVariable());
        } else if (!this.isVariable() && !term.isVariable()) {
            Operation op1 = this.getTopOperation();
            Operation op2 = term.getTopOperation();

            if (op1.equals(op2) || op1.less(sig, op2) || op2.less(sig, op1)) {

                if (op1.isAssociative() && !op1.isCommutative()) {

                    boolean okay = true;
                    if (this.sort.isHidden()) {
                        Term tmp = this.parent;
                        while (tmp != null) {
                            if (tmp.operation.isBehavorial()) {
                                tmp = tmp.parent;
                            } else {
                                okay = false;
                                break;
                            }
                        }
                    }

                    if (okay) {

                        try {
                            Vector<Term> v1 = this.getAssocSubterms(sig, op1);
                            Vector<Term> v2 = term.getAssocSubterms(sig, op2);

                            if (v1.size() == v2.size()) {
                                boolean same = true;
                                for (int i = 0; i < v1.size() && same; i++ ) {
                                    Term tm1 = v1.elementAt(i);
                                    Term tm2 = v2.elementAt(i);
                                    same &= tm1.equals(sig, tm2);
                                }

                                if (!same) {
                                    result = false;
                                }

                            } else {
                                result = false;
                            }

                        } catch (TermException e) {
                        }

                    } else {
                        result = this.subterms[0].equals(sig, term.subterms[0])
                                 && this.subterms[1].equals(sig, term.subterms[1]);
                    }

                } else if (op1.isAssociative() && op1.isCommutative()) {

                    boolean okay = true;
                    if (this.sort.isHidden()) {
                        Term tmp = this.parent;
                        while (tmp != null) {
                            if (tmp.operation.isBehavorial()) {
                                tmp = tmp.parent;
                            } else {
                                okay = false;
                                break;
                            }
                        }
                    }

                    if (okay) {

                        try {
                            Vector<Term> v1 = this.getAssocSubterms(sig, op1);
                            Vector<Term> v2 = term.getAssocSubterms(sig, op2);

                            if (v1.size() == v2.size()) {
                                for (int i = 0; i < v1.size() && result; i++ ) {
                                    Term tm1 = v1.elementAt(i);

                                    boolean found = false;
                                    for (int j = 0; j < v2.size(); j++ ) {
                                        Term tm2 = v2.elementAt(j);
                                        if (tm1.equals(sig, tm2)) {
                                            v2.removeElementAt(j);
                                            found = true;
                                            break;
                                        }
                                    }

                                    if (!found) {
                                        result = false;
                                        break;
                                    }
                                }

                            } else {
                                result = false;
                            }

                        } catch (TermException e) {
                        }

                    } else {
                        result = this.subterms[0].equals(sig, term.subterms[0])
                                 && this.subterms[1].equals(sig, term.subterms[1]);
                    }

                } else if (op1.isCommutative()) {

                    result = this.subterms[0].equals(sig, term.subterms[0])
                             && this.subterms[1].equals(sig, term.subterms[1]);

                    if (!result) {

                        boolean okay = true;
                        if (this.sort.isHidden()) {
                            Term tmp = this.parent;
                            while (tmp != null) {

                                if (tmp.operation.isBehavorial()) {
                                    tmp = tmp.parent;
                                } else {
                                    okay = false;
                                    break;
                                }
                            }
                        }

                        if (okay)
                            result = this.subterms[0].equals(sig, term.subterms[1])
                                     && this.subterms[1].equals(sig, term.subterms[0]);

                    }

                } else {

                    Term[] tm1 = this.subterms;
                    Term[] tm2 = term.subterms;
                    boolean same = true;
                    for (int i = 0; i < tm1.length; i++ ) {
                        same &= tm1[i].equals(sig, tm2[i]);
                    }
                    result = same;
                }
            } else {
                result = false;
            }
        } else {
            result = false;
        }

        if (!result) {

            if (this.sort.equals(BoolModule.boolSort) && term.sort.equals(BoolModule.boolSort)
                && this.sort.isDefault() && term.sort.isDefault()) {

                try {

                    Vector<Term> termlist = new Vector<>();
                    Term l = this.extract(termlist);

                    int len = termlist.size();
                    Term r = term.extract(termlist);

                    if (len == termlist.size() && (!l.equals(this) || !r.equals(term))) {

                        if (checkBoolEquality(l, r, len)) {
                            result = true;
                        }
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }

        return result;
    }

    private boolean checkBoolEquality(Term term1,
                                      Term term2,
                                      int len) {

        if (len == 0) {

            boolean old = RewriteEngine.trace;
            RewriteEngine.trace = false;

            term1 = BoolModule.bool.getNormalForm(term1);
            term2 = BoolModule.bool.getNormalForm(term2);

            RewriteEngine.trace = old;
            return term1.equals(term2);
        } else {
            try {

                Sort bool = BoolModule.boolSort;
                Operation trueOp = BoolModule.trueOp;
                Operation falseOp = BoolModule.falseOp;

                Term t = new Term(trueOp);
                Term f = new Term(falseOp);
                Variable var = new Variable("B" + (len - 1), bool);

                Term l1 = term1.subst(var, t);
                Term r1 = term2.subst(var, t);

                if (checkBoolEquality(l1, r1, len - 1)) {

                    Term l2 = term1.subst(var, f);
                    Term r2 = term2.subst(var, f);

                    return checkBoolEquality(l2, r2, len - 1);

                } else {
                    return false;
                }
            } catch (Exception e) {
                return false;
            }
        }
    }

    @Override
    public String toString() {
        String result = "";

        if (isVariable()) {
            String tmp = this.var.name;
            result += tmp;
        } else if (this.operation.isConstant()) {
            result += this.operation.getName();
        } else if (this.operation.isMixNotation()) {

            if (this.operation.isAssociative() && this.operation.getName()
                                                                .trim()
                                                                .startsWith("_")
                && this.operation.getName()
                                 .trim()
                                 .endsWith("_")) {

                String mid = this.operation.getName()
                                           .trim()
                                           .substring(1);
                mid = mid.substring(0, mid.length() - 1)
                         .trim();

                Vector<Term> vec = null;
                try {
                    vec = this.getAssocSubterms(this.operation);
                } catch (Exception e) {
                }
                for (int i = 0; i < vec.size(); i++ ) {
                    Term t = vec.elementAt(i);
                    String sub = t.toFullString()
                                  .trim();
                    if (t.isComposite() && t.operation.isMixNotation()) {
                        sub = "(" + sub + ")";
                    }
                    if (mid.length() == 0) {
                        result += sub + " ";
                    } else {
                        result += sub + " " + mid + " ";
                    }
                }

                if (mid.length() != 0) {
                    return result.substring(0, result.length() - mid.length() - 2)
                                 .trim();
                } else {
                    return result.trim();
                }
            }

            String tmp = this.operation.getName();
            int i = tmp.indexOf("_");
            int count = 0;
            while (i != -1) {
                Term t = this.subterms[count];
                String sub = t.toString()
                              .trim();

                if (t.isComposite()) {
                    Operation op = t.getTopOperation();
                    if (op.isMixNotation() && !op.getCleanName()
                                                 .equals("==")) {
                        if (op.getCleanName()
                              .equals("and")
                            || this.operation.getCleanName()
                                             .equals("==")) {
                            //sub = "("+sub+")";    // Nov.23
                        } else if (this.operation.getPriority() > op.getPriority()) {
                            sub = "(" + sub + ")";    // Nov.23
                        } else {
                            sub = "(" + sub + ")";
                        }
                    }
                }

                count++ ;

                String first = tmp.substring(0, i)
                                  .trim();
                String second = tmp.substring(i + 1)
                                   .trim();

                if (!tmp.substring(0, i)
                        .trim()
                        .endsWith("[")
                    && !tmp.substring(0, i)
                           .trim()
                           .endsWith("(")) {
                    first = first + " ";
                }

                if (!tmp.substring(i + 1)
                        .trim()
                        .startsWith("]")
                    && !tmp.substring(i + 1)
                           .trim()
                           .startsWith(")")) {

                    second = " " + second;

                }

                tmp = first + sub + second;
                i = tmp.indexOf("_");

            }
            result += tmp;

        } else {
            result += this.operation.getName() + "(";
            for (int i = 0; i < this.subterms.length; i++ ) {
                result += this.subterms[i].toString();
                if (i < this.subterms.length - 1) {
                    result += ", ";
                }
            }
            result += ")";
        }
        return result.trim();
    }

    public String toFullString() {

        String result = "";

        if (isVariable()) {
            result += this.var.getName();
        } else if (this.operation.isConstant()) {
            result += this.operation.getName();
        } else if (this.operation.isMixNotation()) {

            if (this.operation.isAssociative() && this.operation.getName()
                                                                .equals("_  _")) {
                try {
                    Vector<Term> terms = getAssocSubterms(this.operation);
                    for (int i = 0; i < terms.size(); i++ ) {
                        Term term = terms.elementAt(i);

                        if (term.isComposite()) {
                            result += " (" + term.toString() + ")";
                        } else {
                            result += " " + term.toString();
                        }

                    }
                    return result.trim();
                } catch (TermException e) {
                }
            }

            if (this.operation.isAssociative() && this.operation.getName()
                                                                .equals("_ _")) {
                try {
                    Vector<Term> terms = getAssocSubterms(this.operation);
                    for (int i = 0; i < terms.size(); i++ ) {
                        Term term = terms.elementAt(i);

                        if (term.isComposite()) {
                            result += " (" + term.toString() + ")";
                        } else {
                            result += " " + term.toString();
                        }

                    }
                    return result.trim();
                } catch (TermException e) {
                }
            }

            if (this.operation.isAssociative() && this.operation.getName()
                                                                .trim()
                                                                .startsWith("_")
                && this.operation.getName()
                                 .trim()
                                 .endsWith("_")) {

                String mid = this.operation.getName()
                                           .trim()
                                           .substring(1);
                mid = mid.substring(0, mid.length() - 1)
                         .trim();

                Vector<Term> vec = null;
                try {
                    vec = this.getAssocSubterms(this.operation);
                } catch (Exception e) {
                }

                for (int i = 0; i < vec.size(); i++ ) {
                    Term t = vec.elementAt(i);
                    String sub = t.toFullString()
                                  .trim();
                    if (t.isComposite() && t.operation.isMixNotation()) {
                        sub = "(" + sub + ")";
                    }
                    result += sub + " " + mid + " ";
                }
                return result.substring(0, result.length() - mid.length() - 2)
                             .trim();

            }

            String tmp = this.operation.getName();
            int i = tmp.indexOf("_");
            int count = 0;
            while (i != -1) {
                Term t = this.subterms[count];
                String sub = t.toFullString()
                              .trim();
                if (showRetract && this.retract[count] != null) {
                    sub = "r:" + t.sort.getName() + ">" + this.retract[count].getName() + "(" + sub
                          + ")";
                }

                if (t.isComposite()) {

                    Operation op = t.getTopOperation();
                    if (op.isMixNotation() && !op.getCleanName()
                                                 .equals("==")) {
                        if ((op.getCleanName()
                               .equals("and")
                             || this.operation.getCleanName()
                                              .equals("=="))
                            || (this.operation.getPriority() <= op.getPriority())) {
                            sub = "(" + sub + ")";    // Nov.23
                        } else {

                        }
                    }
                }

                count++ ;

                String first = tmp.substring(0, i)
                                  .trim();
                String second = tmp.substring(i + 1)
                                   .trim();

                if (!tmp.substring(0, i)
                        .trim()
                        .endsWith("[")
                    && !tmp.substring(0, i)
                           .trim()
                           .endsWith("(")) {
                    first = first + " ";
                }

                if (!tmp.substring(i + 1)
                        .trim()
                        .startsWith("]")
                    && !tmp.substring(i + 1)
                           .trim()
                           .startsWith(")")) {
                    second = " " + second;

                }

                tmp = first + sub + second;
                i = tmp.indexOf("_");
            }
            result += tmp;

        } else {
            result += this.operation.getName() + "(";
            for (int i = 0; i < this.subterms.length; i++ ) {
                if (this.retract[i] == null || !showRetract) {
                    result += this.subterms[i].toFullString();
                } else {
                    result +=
                        "r:" + this.subterms[i].sort.getName() + ">" + this.retract[i].getName()
                              + "(" + this.subterms[i].toFullString() + ")";
                }
                if (i < this.subterms.length - 1) {
                    result += ", ";
                }
            }
            result += ")";
        }
        return result.trim();
    }

    public String showStructure() {
        return showStructure("");
    }

    private String showStructure(String st) {
        String result = "";

        if (isVariable()) {
            result += st + "var: " + this.var.getName() + "   " + this.var.getSort() + "\n";
        } else {

            result += st + this.operation.toString()
                                         .substring(2)
                      + "   " + this.operation.modName + "\n";
            for (Term subterm : this.subterms) {
                result += st + subterm.showStructure(st + "  ");
            }

        }
        return result;
    }

    public String showStructure(Module module) {
        return showStructure(module, "");
    }

    private String showStructure(Module module,
                                 String st) {

        String result = "";

        if (isVariable()) {
            result += st + module.toString(this.var) + "\n";
        } else {

            result += st + module.toString(this.operation)
                                 .substring(3)
                      + "\n";
            for (Term subterm : this.subterms) {
                result += subterm.showStructure(module, st + "  ");
            }

        }
        return result;
    }

    public String showStructureWithModuleName(Module module) {
        return showStructureWithModuleName(module, "");
    }

    private String showStructureWithModuleName(Module module,
                                               String st) {

        String result = "";

        if (isVariable()) {
            result += st + module.toString(this.var) + "\n";
        } else {

            result += st + module.toString(this.operation)
                                 .substring(3)
                      + " in " + this.operation.modName + "\n";
            for (Term subterm : this.subterms) {
                result += subterm.showStructureWithModuleName(module, st + "  ");
            }

        }
        return result;
    }

    public static Term parse(Signature sig,
                             String st)
        throws TermException {

        String s = st;
        FastTermParser ftp = new FastTermParser(sig, s);
        List<Term> res = ftp.parse();

        if (res.size() == 0) {
            String[] etks = ftp.getUnknownTokens();
            String msg = "";
            for (int i = 0; i < etks.length; i++ ) {
                if (i < etks.length - 1)
                    msg += etks[i] + ", ";
                else msg += etks[i];
            }

            if (msg.length() > 0) {
                msg = "Errors at the following token(s): " + msg;
                throw new TermException(Module.format(msg + ", when parsing \"" + s.trim() + "\" ",
                                                      0));
            } else {
                throw new TermException(Module.format("No parse for " + s.trim(), 0));
            }

        } else if (res.size() == 1) {
            Term term = res.get(0);
            return term;
        } else {

            // check whether something wrong there
            res = checkPriority(res);
            if (res.size() == 1) {
                return res.get(0);
            }

            // check retraction
            List<Term> list = checkRetract(res);
            if (list.size() == 1) {
                return list.get(0);
            }

            // check default if_then_else_fi
            list = checkDefaultIf(res);
            if (list.size() == 1) {
                return list.get(0);
            }

            // check whether overloading is possible
            list = checkOverloading((Module) sig, res);
            if (list.size() == 1) {
                Term result = list.get(0);
                return result;
            }

            String msg = "multiple parsing results:\n";

            Term term1 = res.get(0);
            Term term2 = res.get(1);

            String msg1 = term1.showStructure((Module) sig);
            String msg2 = term2.showStructure((Module) sig);

            if (msg1.equals(msg2)) {
                msg += "------------------------------------------\n";
                msg += term1.showStructureWithModuleName((Module) sig);
                msg += "------------------------------------------\n";
                msg += term2.showStructureWithModuleName((Module) sig);
                msg += "------------------------------------------";
            } else {
                msg += "------------------------------------------\n";
                msg += msg1;
                msg += "------------------------------------------\n";
                msg += msg2;
                msg += "------------------------------------------";
            }
            throw new TermException(msg, res.size());
        }

    }

    public static Term parse(Signature sig,
                             String st,
                             Sort expect)
        throws TermException {

        String s = st;

        FastTermParser ftp = new FastTermParser(sig, s);
        List<Term> res = ftp.parse();

        Term possible = null;
        if (res.size() == 1) {
            possible = res.get(0);
        }

        for (int i = res.size() - 1; i > -1; i-- ) {
            Term term = res.get(i);

            if (!sig.less(term.sort, expect) && !sig.less(expect, term.sort)
                && !sig.hasCommonSubsort(expect, term.sort)
                && !sig.hasCommonSupersort(expect, term.sort)) {

                res.remove(i);
            }
        }

        if (res.size() == 0) {

            if (possible != null) {
                throw new TermException(s + "is not on the sort " + expect.getName());
            }

            String[] etks = ftp.getUnknownTokens();
            String msg = "";
            for (int i = 0; i < etks.length; i++ ) {
                if (i < etks.length - 1)
                    msg += etks[i] + ", ";
                else msg += etks[i];

            }

            if (msg.length() > 0) {
                msg = "Errors at the following token(s): \"" + msg + "\", when parsing \""
                      + s.trim() + "\" ";

                throw new TermException(Module.format(msg, 0));
            } else {
                throw new TermException(Module.format("No parse for " + s.trim() + " ", 0));
            }

        } else if (res.size() == 1) {

            Term term = res.get(0);
            return term;

        } else {

            // check whether something wrong there
            res = checkPriority(res);
            if (res.size() == 1) {
                return res.get(0);
            }

            // check retraction
            List<Term> list = checkRetract(res);
            if (list.size() == 1) {
                return list.get(0);
            }

            // check default if_then_else_fi
            list = checkDefaultIf(res);
            if (list.size() == 1) {
                Term result = list.get(0);
                return result;
            }

            // check whether overloading is possible
            list = checkOverloading((Module) sig, res);
            if (list.size() == 1) {
                Term result = list.get(0);
                return result;
            }

            String msg = "multiple parsing results:\n";
            Term t1 = res.get(0);
            Term t2 = res.get(1);

            msg += "------------------------------------------\n";
            String m1 = t1.showStructure((Module) sig);
            String m2 = t2.showStructure((Module) sig);
            if (m1.equals(m2)) {
                m1 = t1.showStructureWithModuleName((Module) sig);
                m2 = t2.showStructureWithModuleName((Module) sig);
            }
            msg += m1 + "------------------------------------------\n" + m2;
            msg += "------------------------------------------";
            throw new TermException(msg, res.size());
        }

    }

    private static List<Term> checkOverloading(Module module,
                                               List<Term> list) {

        ArrayList<Term> result = new ArrayList<>();

        Term res = null;
        for (Term term : list) {
            if ((res == null) || term.laterThan(module, res)) {
                res = term;
            } else if (res.laterThan(module, term)) {

            } else {
                result.add(term);
                break;
            }

        }
        result.add(res);

        return result;
    }

    private boolean laterThan(Module module,
                              Term term) {

        if (this.var != null) {
            return false;
        } else if (term.var != null) {
            if (this.operation.resultSort.equals(term.var.sort)) {
                return true;
            } else {
                return false;
            }
        } else if (this.operation.name.equals(term.operation.name)
                   && this.operation.resultSort.equals(term.operation.resultSort)
                   && this.operation.argumentSorts.length == term.operation.argumentSorts.length) {

                       for (int i = 0; i < this.operation.argumentSorts.length; i++ ) {
                           if (!this.operation.argumentSorts[i].equals(term.operation.argumentSorts[i])) {
                               return false;
                           }
                       }

                       if (module.modName.equals(this.operation.modName)
                           && !module.modName.equals(term.operation.modName)) {

                           for (int i = 0; i < this.operation.argumentSorts.length; i++ ) {

                               if (this.subterms[i].laterThan(module, term.subterms[i])
                                   || this.subterms[i].equals(term.subterms[i])) {

                               } else {
                                   return false;
                               }
                           }

                           return true;

                       } else if (this.operation.modName.equals(term.operation.modName)) {

                           boolean later = false;
                           for (int i = 0; i < this.operation.argumentSorts.length; i++ ) {

                               if (this.subterms[i].laterThan(module, term.subterms[i])) {
                                   later = true;
                               } else if (this.subterms[i].equals(term.subterms[i])) {

                               } else {
                                   return false;
                               }
                           }

                           return later;

                       } else {
                           return false;
                       }

                   } else {
                       return false;
                   }
    }

    private static List<Term> checkDefaultIf(List<Term> list) {

        ArrayList<Term> result = new ArrayList<>();

        for (Term term : list) {
            if (term.contains(BoolModule.metaIf)) {
                result.add(term);
            }
        }

        return result;
    }

    protected static List<Term> checkRetract(List<Term> list) {

        ArrayList<Term> result = new ArrayList<>();

        for (Term term : list) {
            if (!term.needRetract()) {
                result.add(term);
            }
        }

        return result;
    }

    protected static List<Term> checkPriority(List<Term> list) {

        List<Term> result = new ArrayList<>();
        List<List<List<Integer>>> pathes = getPathes(list);

        for (int i = 0; i < pathes.size(); i++ ) {
            List<List<Integer>> source = pathes.get(i);
            boolean okay = true;
            for (int j = 0; j < pathes.size(); j++ ) {

                if (j == i)
                    continue;

                List<List<Integer>> target = pathes.get(j);
                if (hasLessPriorities(target, source)) {
                    okay = false;
                    break;
                }

            }

            if (okay) {
                result.add(list.get(i));
            }

        }

        // another checking
        ArrayList<Term> tmp = new ArrayList<>();
        for (Term t1 : result) {
            Operation op1 = t1.getTopOperation();

            boolean okay = true;
            for (int j = 0; j < tmp.size(); j++ ) {
                Term t2 = tmp.get(j);
                Operation op2 = t2.getTopOperation();

                if (op1 != null && op2 != null) {

                    if (op1.priority < op2.priority) {
                        // insert op1, remove op2
                        tmp.remove(j);
                        break;
                    } else if (op2.priority < op1.priority) {
                        // ignore op1
                        okay = false;
                        break;
                    }

                }

            }

            if (okay) {
                tmp.add(t1);
            }

        }

        result = tmp;

        return result;
    }

    private static boolean hasLessPriorities(List<List<Integer>> list1,
                                             List<List<Integer>> list2) {

        boolean less = false;

        if (list1.size() != list2.size()) {
            return false;
        }

        for (int i = 0; i < list1.size(); i++ ) {
            List<Integer> l = list1.get(i);
            List<Integer> r = list2.get(i);

            int min = Math.min(l.size(), r.size());
            for (int j = 0; j < min; j++ ) {
                int a = l.get(j);
                int b = r.get(j);
                if (a > b) {
                    return false;
                } else if (a < b) {
                    less = true;
                }

            }
        }

        return less;

    }

    private static List<List<List<Integer>>> getPathes(List<Term> list) {

        List<List<List<Integer>>> result = new ArrayList<>();

        for (Term term : list) {
            result.add(term.getLabelledBranches());
        }

        return result;
    }

    private List<List<Integer>> getLabelledBranches() {

        List<List<Integer>> result = new ArrayList<>();

        if (this.isVariable() || this.isConstant()) {
            result.add(new ArrayList<Integer>());
        } else {

            for (Term subterm : this.subterms) {
                List<List<Integer>> list = subterm.getLabelledBranches();

                for (int j = 0; j < list.size(); j++ ) {
                    List<Integer> tmp = list.get(j);
                    tmp.add(this.operation.getPriority());
                    result.add(tmp);
                }
            }

        }

        return result;

    }

    private Vector<Term> getAssocSubterms(Operation op) throws TermException {

        Vector<Term> result = new Vector<>();

        if (!op.isAssociative()) {
            throw new TermException();
        }

        if (isVariable()) {
            result.addElement(this);
        } else {
            Operation o = this.getTopOperation();
            if (o.equals(op)) {
                Term[] sub = this.subterms;
                result = sub[0].getAssocSubterms(op);
                Vector<Term> v = sub[1].getAssocSubterms(op);
                for (int i = 0; i < v.size(); i++ ) {
                    Term tmp = v.elementAt(i);
                    result.addElement(tmp);
                }
            } else {
                result.addElement(this);
            }
        }
        return result;
    }

    protected Vector<Term> getAssocSubterms(Signature sig,
                                            Operation op)
        throws TermException {

        Vector<Term> result = new Vector<>();

        if (!op.isAssociative()) {
            throw new TermException();
        }

        if (isVariable()) {
            result.addElement(this);
        } else {
            Operation o = this.getTopOperation();

            if (o.equals(op) || o.less(sig, op) || op.less(sig, o)) {
                Term[] sub = this.subterms;
                result = sub[0].getAssocSubterms(sig, op);
                Vector<Term> v = sub[1].getAssocSubterms(sig, op);
                for (int i = 0; i < v.size(); i++ ) {
                    Term tmp = v.elementAt(i);
                    result.addElement(tmp);
                }
            } else {
                result.addElement(this);
            }
        }
        return result;
    }

    protected boolean isComposite() {
        boolean result = true;

        if (isVariable()) {
            result = false;
        } else {
            result = !this.operation.isConstant();
        }

        return result;
    }

    public Term subst(Signature sig,
                      VarOrCode var2,
                      Term t) {

        Term result = null;

        try {
            if (isVariable()) {
                if (this.var.equals(var2)) {
                    result = t;
                } else {
                    result = new Term(this.var);
                }
            } else {
                Term[] tmp = new Term[this.subterms.length];
                for (int i = 0; i < this.subterms.length; i++ ) {
                    tmp[i] = this.subterms[i].subst(sig, var2, t);
                }
                result = new Term(sig, this.operation, tmp);
            }
        } catch (TermException e) {
            //System.out.println(e.getMessage());
            e.printStackTrace();
        }

        return result;
    }

    public Term subst(Variable v,
                      Term t) {

        Term result = null;

        try {
            if (isVariable()) {
                if (this.var.equals(v)) {
                    result = t;
                } else {
                    result = new Term(this.var);
                }
            } else {
                Term[] tmp = new Term[this.subterms.length];
                for (int i = 0; i < this.subterms.length; i++ ) {
                    tmp[i] = this.subterms[i].subst(v, t);
                }

                result = new Term(this.operation, tmp);
            }
        } catch (Exception e) {
        }

        return result;
    }

    public boolean isDefinedOn(Signature sig) {
        boolean result = true;

        if (this.var != null) {
            result = sig.containsVariable(this.var);
        } else {
            result = sig.containsOperation(this.operation);

            for (int i = 0; i < this.subterms.length && result; i++ ) {
                result = this.subterms[i].isDefinedOn(sig);
            }

        }

        return result;
    }

    public Term extract(Vector<Term> termlist) throws TermException {

        Term result = null;

        if (this.var != null) {
            boolean found = false;
            int index = -1;
            for (int i = 0; i < termlist.size() && !found; i++ ) {
                Term tmp = termlist.elementAt(i);
                if (this.equals(tmp)) {
                    found = true;
                    index = i;
                }
            }

            ModuleName modName = new ModuleName("TRUTH-VALUE");
            if (!found) {
                Sort sort = new Sort("Bool", modName);
                Variable var = new Variable("B" + termlist.size(), sort);
                result = new Term(var);
                termlist.addElement(this);
            } else {
                Sort sort = new Sort("Bool", modName);
                Variable var = new Variable("B" + index, sort);
                result = new Term(var);
            }
            return result;

        }

        Operation op = this.operation;
        if (op.equals(BoolModule.trueOp) || op.equals(BoolModule.falseOp)) {
            result = new Term(op);
            return result;
        } else if (op.equals(BoolModule.and) || op.equals(BoolModule.or)) {
            Term[] subs = new Term[this.subterms.length];
            ;
            subs[0] = this.subterms[0].extract(termlist);
            subs[1] = this.subterms[1].extract(termlist);
            result = new Term(op, subs);
            return result;
        } else if (op.equals(BoolModule.not)) {
            Term[] subs = new Term[this.subterms.length];
            subs[0] = this.subterms[0].extract(termlist);
            result = new Term(op, subs);
            return result;
        } else {
            boolean found = false;
            int index = -1;
            for (int i = 0; i < termlist.size() && !found; i++ ) {
                Term tmp = termlist.elementAt(i);
                if (this.equals(tmp)) {
                    found = true;
                    index = i;
                }
            }

            ModuleName modName = new ModuleName("TRUTH-VALUE");
            if (!found) {
                Sort sort = new Sort("Bool", modName);
                Variable var = new Variable("B" + termlist.size(), sort);
                result = new Term(var);
                termlist.addElement(this);
            } else {
                Sort sort = new Sort("Bool", modName);
                Variable var = new Variable("B" + index, sort);
                result = new Term(var);
            }
            return result;
        }

    }

    public Variable[] getVariables() {

        Variable[] result = new Variable[0];

        if (this.var != null) {
            result = new Variable[1];
            result[0] = this.var;
        } else {
            Vector<Variable> mid = new Vector<>();
            for (Term subterm : this.subterms) {
                Variable[] tmp = subterm.getVariables();

                for (Variable element : tmp) {
                    boolean found = false;
                    for (int k = 0; k < mid.size() && !found; k++ ) {
                        Variable vtmp = mid.elementAt(k);
                        if (vtmp.equals(element)) {
                            found = true;
                        }
                    }
                    if (!found) {
                        mid.addElement(element);
                    }
                }

            }

            result = new Variable[mid.size()];
            mid.copyInto(result);

        }

        return result;
    }

    public static boolean subsume(Term[] targets,
                                  Term[] samples,
                                  Substitution subst) {

        try {
            if (targets.length != samples.length) {
                return false;
            }

            if (targets.length == 0) {
                return true;
            } else {

                Term tar = targets[0];
                Term sam = samples[0];

                if (sam.var != null) {
                    if (tar.contains(sam.var)) {
                        return false;
                    } else {
                        subst.addSubst(sam.var, tar);
                        Term[] ntargets = new Term[targets.length - 1];
                        Term[] nsamples = new Term[samples.length - 1];

                        for (int i = 0; i < ntargets.length; i++ ) {
                            ntargets[i] = targets[i + 1].subst(sam.var, tar);
                            nsamples[i] = samples[i + 1].subst(sam.var, tar);
                        }

                        return subsume(ntargets, nsamples, subst);
                    }
                } else if (tar.operation != null && tar.operation.equals(sam.operation)) {
                    int arity = tar.operation.getArity();
                    int len = targets.length - 1 + arity;
                    Term[] ntargets = new Term[len];
                    Term[] nsamples = new Term[len];

                    if (tar.operation.getArity() > 0) {
                        System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
                        System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
                    }
                    System.arraycopy(targets, 1, ntargets, arity, targets.length - 1);
                    System.arraycopy(samples, 1, nsamples, arity, samples.length - 1);

                    return subsume(ntargets, nsamples, subst);

                } else {
                    return false;
                }
            }
        } catch (SubstitutionException e) {
            return false;
        }
    }

    public boolean contains(Variable v) {

        boolean result = false;

        if (this.var != null && this.var.equals(v)) {
            result = true;
        } else if (this.operation != null) {
            for (int i = 0; i < this.subterms.length && !result; i++ ) {
                result = this.subterms[i].contains(v);
            }
        }

        return result;
    }

    public Substitution subsume(Term term) {

        Substitution subst = new Substitution();

        Term[] targets = new Term[1];
        targets[0] = this;

        Term[] samples = new Term[1];
        samples[0] = term;

        boolean res = subsume(targets, samples, subst);

        if (res) {
            return subst;
        } else {
            return null;
        }

    }

    public static Substitution unify(Term[] targets,
                                     Term[] samples,
                                     Substitution subst)
        throws NoUnifierException {

        if (targets.length != samples.length) {
            throw new NoUnifierException();
        }

        if (targets.length == 0) {
            return subst;
        } else {

            Term tar = targets[0];
            Term sam = samples[0];

            if (sam.var != null) {
                if (tar.contains(sam.var)) {
                    throw new NoUnifierException();
                } else {
                    try {
                        subst.addSubst(sam.var, tar);
                    } catch (SubstitutionException e) {
                    }
                    Term[] ntargets = new Term[targets.length - 1];
                    Term[] nsamples = new Term[samples.length - 1];

                    for (int i = 0; i < ntargets.length; i++ ) {
                        ntargets[i] = targets[i + 1].subst(sam.var, tar);
                        nsamples[i] = samples[i + 1].subst(sam.var, tar);
                    }

                    return unify(ntargets, nsamples, subst);
                }

            } else if (tar.var != null) {

                if (sam.contains(tar.var)) {
                    throw new NoUnifierException();
                } else {

                    try {
                        subst.addSubst(tar.var, sam);
                    } catch (SubstitutionException e) {
                    }

                    Term[] ntargets = new Term[targets.length - 1];
                    Term[] nsamples = new Term[samples.length - 1];

                    for (int i = 0; i < ntargets.length; i++ ) {
                        ntargets[i] = targets[i + 1].subst(tar.var, sam);
                        nsamples[i] = samples[i + 1].subst(tar.var, sam);
                    }

                    return unify(ntargets, nsamples, subst);
                }

            } else if (tar.operation != null && tar.operation.equals(sam.operation)) {

                int arity = tar.operation.getArity();
                int len = targets.length - 1 + arity;
                Term[] ntargets = new Term[len];
                Term[] nsamples = new Term[len];

                if (tar.operation.getArity() > 0) {
                    System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
                    System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
                }
                System.arraycopy(targets, 1, ntargets, arity, targets.length - 1);
                System.arraycopy(samples, 1, nsamples, arity, samples.length - 1);
                return unify(ntargets, nsamples, subst);

            } else {
                throw new NoUnifierException();
            }
        }

    }

    // unify two arrays of terms wrt the given substitution and signature
    public static Substitution unify(Term[] targets,
                                     Term[] samples,
                                     Substitution subst,
                                     Signature sig)
        throws NoUnifierException {

        if (targets.length != samples.length) {
            throw new NoUnifierException();
        }

        if (targets.length == 0) {
            return subst;
        } else {

            Term tar = targets[0];
            Term sam = samples[0];

            if (sam.var != null) {
                if (tar.contains(sam.var)) {
                    throw new NoUnifierException();
                } else {
                    try {
                        subst.addSubst(sam.var, tar, sig);
                    } catch (SubstitutionException e) {
                    }

                    Term[] ntargets = new Term[targets.length - 1];
                    Term[] nsamples = new Term[samples.length - 1];

                    HashMap<VarOrCode, Term> ht = new HashMap<>();
                    ht.put(tar.var, sam);

                    for (int i = 0; i < ntargets.length; i++ ) {
                        ntargets[i] = targets[i + 1].subst(ht, sig);
                        nsamples[i] = samples[i + 1].subst(ht, sig);
                    }

                    return unify(ntargets, nsamples, subst, sig);
                }

            } else if (tar.var != null) {

                if (sam.contains(tar.var)) {
                    throw new NoUnifierException();
                } else {

                    try {
                        subst.addSubst(tar.var, sam, sig);
                    } catch (SubstitutionException e) {
                    }

                    Term[] ntargets = new Term[targets.length - 1];
                    Term[] nsamples = new Term[samples.length - 1];

                    HashMap<VarOrCode, Term> ht = new HashMap<>();
                    ht.put(tar.var, sam);

                    for (int i = 0; i < ntargets.length; i++ ) {
                        ntargets[i] = targets[i + 1].subst(ht, sig);
                        nsamples[i] = samples[i + 1].subst(ht, sig);
                    }

                    return unify(ntargets, nsamples, subst, sig);
                }

            } else if (tar.operation != null && tar.operation.equals(sam.operation)) {

                int arity = tar.operation.getArity();
                int len = targets.length - 1 + arity;
                Term[] ntargets = new Term[len];
                Term[] nsamples = new Term[len];

                if (tar.operation.getArity() > 0) {
                    System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
                    System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
                }
                System.arraycopy(targets, 1, ntargets, arity, targets.length - 1);
                System.arraycopy(samples, 1, nsamples, arity, samples.length - 1);
                return unify(ntargets, nsamples, subst, sig);

            } else {
                throw new NoUnifierException();
            }
        }

    }

    // unify two terms wrt the given substitution
    public Substitution unify(Term term,
                              Substitution subst)
        throws NoUnifierException {
        Term[] targets = new Term[]
            {
                this
            };
        Term[] samples = new Term[]
            {
                term
            };
        return unify(targets, samples, new Substitution());
    }

    // unify two arrays of terms wrt the given  substitution and signature
    public Substitution unify(Term term,
                              Substitution subst,
                              Signature sig)
        throws NoUnifierException {
        Term[] targets = new Term[]
            {
                this
            };
        Term[] samples = new Term[]
            {
                term
            };
        return unify(targets, samples, new Substitution(), sig);
    }

    // unify this term and an input term
    public Substitution unify(Term term) throws NoUnifierException {
        return unify(term, new Substitution());
    }

    // unify this term and an input term wrt a signature
    public Substitution unify(Term term,
                              Signature sig)
        throws NoUnifierException {
        return unify(term, new Substitution(), sig);
    }

    public Term apply(Substitution subst) {

        Term result = this;
        SingleSubstitution[] ss = subst.getAll();
        for (SingleSubstitution element : ss) {
            Variable var = element.getVariable();
            Term term = element.getTerm();
            result = result.subst(var, term);
        }

        return result;

    }

    public boolean isGround() {

        Variable[] vs = getVariables();

        return(vs.length == 0);

    }

    public boolean contains(Operation op) {

        if (this.var == null) {
            if (this.operation.equals(op)) {
                return true;
            } else {
                for (Term t : this.subterms) {
                    if (t.contains(op))
                        return true;
                }
            }
        }

        return false;
    }

    /* public boolean containsMiddle(Operation op, ArrayList nocrashed) {
     *
     * if (var == null) {
     *
     * boolean found = false; for (int i=0; i<nocrashed.size(); i++) { Operation opr =
     * (Operation)nocrashed.get(i); if (this.operation.equals(opr)) { found = true; break; } }
     *
     *
     * if (found) { for (int i=0; i<subterms.length; i++) { if (subterms[i].contains(op)) { return
     * true; } } }
     *
     * }
     *
     * return false; } */

    public boolean madeBy(Operation[] ops) {

        boolean result = true;

        if (this.var == null) {
            boolean found = false;
            if (!this.operation.isBehavorial()) {
                found = true;
            } else {
                for (int i = 0; i < ops.length && !found; i++ ) {
                    found = this.operation.equals(ops[i]);
                }
            }

            if (!found) {
                result = false;
            } else {
                for (int i = 0; i < this.subterms.length && result; i++ ) {
                    result = this.subterms[i].madeBy(ops);
                }
            }
        }

        return result;
    }

    public Term getBooleanSubterm() {

        Term result = null;

        if (this.sort.getName()
                     .equals("Bool")) {
            result = this;
        } else if (this.operation != null) {
            for (Term subterm : this.subterms) {
                result = subterm.getBooleanSubterm();
                if (result != null)
                    break;
            }
        }
        return result;

    }

    public boolean needRetract() {

        boolean result = false;

        for (Sort element : this.retract) {
            result = element != null;
            if (result)
                return true;
        }

        if (this.subterms != null) {
            for (Term subterm : this.subterms) {
                result = subterm.needRetract();
                if (result)
                    return true;
            }
        }

        return result;
    }

    public boolean needExplicitRetract() {

        if (this.operation != null) {

            if (this.operation.info.equals("system-retract")) {
                return true;
            } else {
                for (Term subterm : this.subterms) {
                    if (subterm.needExplicitRetract())
                        return true;
                }
            }
        }

        return false;
    }

    public boolean needHeadRetract() {

        boolean result = false;

        for (Sort element : this.retract) {
            result = element != null;
            if (result)
                return true;
        }

        return result;
    }

    public Term addAnnotation(String name,
                              Signature sig,
                              Map<ModuleName, Integer> env) {

        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.addAnnotation(name, env));
        } else {
            Operation op = this.operation.addAnnotation(name, env);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].addAnnotation(name, sig, env);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {

                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.out.println(op);
                System.out.println("--------------------------");
                System.out.println(args[0].showStructure());
                System.out.println("--------------------------");
                System.out.println(args[1].showStructure());
                System.out.println("--------------------------");
                System.out.println(sig.subsorts);
                System.out.println("--------------------------");
                e.printStackTrace();
                System.exit(0);
            }

        }

        return term;

    }

    public Term removeAnnotation(String name,
                                 Signature sig) {

        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.removeAnnotation(name));
        } else {
            Operation op = this.operation.removeAnnotation(name);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].removeAnnotation(name, sig);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.out.println(op);
                System.out.println(args[0].showStructure());
                System.out.println(args[1].showStructure());
                System.out.println(sig.subsorts);
                e.printStackTrace();
                System.exit(0);
            }

        }

        return term;

    }

    public Term changeSort(Sort olds,
                           Sort news,
                           Signature sig) {

        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.changeSort(olds, news));
        } else {
            Operation op = this.operation.changeSort(olds, news);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].changeSort(olds, news, sig);
            }

            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                throw new Error();
            }

        }

        return term;

    }

    public Term changeModuleName(ModuleName olds,
                                 ModuleName news,
                                 Signature sig) {
        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.changeModuleName(olds, news));
        } else {
            Operation op = this.operation.changeModuleName(olds, news);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].changeModuleName(olds, news, sig);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                e.printStackTrace();
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.exit(0);
            }
        }
        return term;
    }

    public Term changeAbsoluteModuleName(ModuleName olds,
                                         ModuleName news,
                                         Signature sig) {
        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.changeAbsoluteModuleName(olds, news));
        } else {

            Operation op = this.operation.changeAbsoluteModuleName(olds, news);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].changeAbsoluteModuleName(olds, news, sig);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                e.printStackTrace();
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.exit(0);
            }

        }

        return term;

    }

    public Term changeParameterName(String olds,
                                    String news,
                                    Signature sig) {
        Term term = this;
        if (this.var != null) {
            term = new Term(this.var.changeParameterName(olds, news));
        } else {

            Operation op = this.operation.changeParameterName(olds, news);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].changeParameterName(olds, news, sig);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                e.printStackTrace();
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.exit(0);
            }

        }

        return term;

    }

    public Term replaceOperationName(String oldname,
                                     String newname,
                                     Signature sig) {
        Term term = this;
        if (this.var != null) {
            term = new Term(this.var);
        } else {

            Operation op = this.operation.replaceOperationName(oldname, newname);
            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].replaceOperationName(oldname, newname, sig);
            }
            try {
                term = new Term(sig, op, args);
            } catch (Exception e) {
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.exit(0);
            }

        }

        return term;

    }

    public Term changeOperation(Operation from,
                                Operation to,
                                Signature sig) {

        Term term = this;

        if (this.var != null) {
            term = new Term(this.var);
        } else {

            Operation o = this.operation.copy();
            if (o.equals(from)) {
                o = to;
            }

            if (o.id != null && o.id.equals(from)) {
                o.id = to;
            }

            if (o.implicitId != null && o.implicitId.equals(from)) {
                o.implicitId = to;
            }

            Term[] args = new Term[this.subterms.length];
            for (int i = 0; i < this.subterms.length; i++ ) {
                args[i] = this.subterms[i].changeOperation(from, to, sig);
            }
            try {
                term = new Term(sig, o, args);
            } catch (Exception e) {
                System.out.println("got a bug. please email klin@cs.ucsd.edu");
                System.exit(0);
            }

        }

        return term;

    }

    public boolean isSubterm(Term term) {

        boolean result = false;

        if (this.equals(term)) {
            return true;
        } else if (term.operation != null) {
            for (int i = 0; i < term.subterms.length && !result; i++ ) {
                result = isSubterm(term.subterms[i]);
            }
        }

        return result;
    }

    protected boolean equalsIgnoreVariableName(Term term,
                                               HashMap<Variable, Variable> varMap) {

        if (this.var != null) {
            if (term.var != null) {
                // find mapping from varMap
                for (Variable v : varMap.keySet()) {
                    if (this.var.equals(v)) {
                        v = varMap.get(v);
                        if (v.equals(term.var)) {
                            return true;
                        } else {
                            return false;
                        }
                    }
                }
                varMap.put(this.var, term.var);
                return true;
            } else {
                return false;
            }
        } else if (term.var == null && this.operation.equals(term.operation)) {
            for (int i = 0; i < this.subterms.length; i++ ) {
                if (!this.subterms[i].equalsIgnoreVariableName(term.subterms[i], varMap)) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }

    }

    public Term subst(Map<VarOrCode, Term> ht,
                      Signature sig) {

        Term result = null;

        /* if (ht.isEmpty()) { return this; } */

        try {
            if (this.var != null) {
                Term term = ht.get(this.var);
                if (term == null) {
                    for (VarOrCode obj : ht.keySet()) {
                        if (obj instanceof Variable) {
                            Variable v = (Variable) obj;
                            if (this.var.equals(v)) {
                                term = ht.get(v);
                                break;
                            }
                        }
                    }
                }

                if (term != null && term.var != null) {
                    //Sort limit = (Sort)term.getPropertyBy("retract");
                    result = new Term(term.var);
                } else if (term != null && term.operation != null) {

                    result = new Term(sig, term.operation, term.subterms);

                    /* Sort limit = (Sort)term.getPropertyBy("retract"); if (limit != null) { if
                     * (this.parent == null) { // add retract: current to limit
                     *
                     * Sort[] args = new Sort[] { result.sort }; Sort res = limit; Operation retOp =
                     * new Operation("r:"+ result.sort.getName()+ ">"+limit.getName()+ "(_)", args,
                     * res); retOp.info = "system-retract";
                     *
                     * result = new Term(sig, retOp, new Term[] {result});
                     *
                     * } } */

                }

                if (result == null) {
                    result = new Term(this.var);
                }

            } else {

                Term[] tmp = new Term[this.subterms.length];
                for (int i = 0; i < this.subterms.length; i++ ) {
                    tmp[i] = this.subterms[i].subst(ht, sig);
                }

                if (sig.explicitRetract && this.operation.info.equals("system-retract")) {

                    if (sig.isSubsort(tmp[0].sort, this.operation.resultSort)) {
                        result = tmp[0];
                    } else {
                        result = new Term(sig, this.operation, tmp);
                    }

                } else if (this.operation.equals(BOBJModule.getSetsortOperation())
                           && this.operation.info.equals("system-default")) {

                               result = tmp[1];
                               String sortName = tmp[0].operation.name;
                               Sort[] sorts = sig.getSortsByName(sortName);

                               // sorts[0] must be a part of result.sort
                               if (sig.isSubsort(result.sort, sorts[0])) {
                                   // do nothing
                               } else if (sig.isSubsort(sorts[0], result.sort)
                                          || (sig.canApply(sorts[0], result.sort) != null)
                                          || sig.hasCommonSupersort(sorts[0], result.sort)) {
                                              result.sort = sorts[0];
                                          } else {

                                              throw new Error("Sort casting error when cast "
                                                              + result.sort.getName() + " to "
                                                              + sorts[0].getName());
                                          }

                           } else {
                               result = getMinimumTerm(sig, this.operation, tmp);
                               if (result == null) {
                                   result = new Term(sig, this.operation, tmp);
                               }
                           }
            }
        } catch (Exception e) {
            //e.printStackTrace();
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

    public Map<VarOrCode, Term> getMatch(Term pattern,
                                         Signature sig) {

        Map<VarOrCode, Term> result = new HashMap<>();

        if (pattern.var != null) {

            Sort vs = pattern.sort;
            Sort ts = this.sort;

            if (!vs.equals(ts) && !sig.isSubsort(ts, vs)) {
                //System.out.println("my god! "+ts+"  "+vs);
                //System.out.println(this.showStructure());
                //System.out.println(pattern.showStructure());

                if (sig.hasCommonSupersort(ts, vs)) {

                } else {
                    return null;
                }

            }

            if (this.var == null) {
                try {
                    Term term = new Term(sig, this.operation, this.subterms);
                    result.put(pattern.var, term);
                } catch (Exception e) {
                }

            } else {
                Term term = new Term(this.var);
                try {
                    result.put(pattern.var, term);
                } catch (Exception e) {
                }
            }

        } else if (this.operation == null) {

            return null;

        } else if (this.operation.equals(pattern.operation)) {

            Term[] subpatterns = pattern.subterms;
            for (int i = 0; i < this.subterms.length; i++ ) {
                Map<VarOrCode, Term> tmp = this.subterms[i].getMatch(subpatterns[i], sig);

                if (tmp == null) {
                    return null;
                } else {
                    for (VarOrCode v : tmp.keySet()) {
                        if (v instanceof Variable) {
                            Term trm1 = tmp.get(v);

                            Term trm2 = null;
                            for (VarOrCode vtmp : result.keySet()) {
                                if (vtmp.equals(v)) {
                                    trm2 = result.get(vtmp);
                                    break;
                                }
                            }

                            if (trm2 == null) {
                                result.put(v, trm1);
                            } else if (!trm1.equals(trm2)) {
                                return null;
                            }
                        }
                    }
                }
            }
        } else {
            result = null;
        }

        //System.out.println("return match result = "+result+"  "+
        //this+"  "+pattern);
        return result;
    }

    public Variable getVariableWithName(String varname) {
        Variable[] vars = getVariables();
        for (Variable var2 : vars) {
            if (var2.name.equals(varname)) {
                return var2;
            }
        }

        return null;
    }

    public void cleanFlag() {
        this.nocheck = false;
        this.nogcheck = false;
        this.noscheck = false;

        if (this.var == null) {
            for (Term subterm : this.subterms) {
                subterm.cleanFlag();
            }

        }

    }

    public boolean equals(Term term,
                          HashMap<Variable, Variable> map) {

        boolean result = true;
        ;

        if (this.isVariable() && term.isVariable()) {
            if (this.getVariable()
                    .equals(term.getVariable())) {
                return true;
            } else {

                boolean found = false;
                boolean consistent = false;

                Iterator<Variable> itor = map.keySet()
                                             .iterator();
                while (itor.hasNext()) {
                    Variable key = itor.next();
                    if (key.equals(this.var)) {
                        Variable val = map.get(key);
                        found = true;

                        if (val.equals(term.var)) {
                            consistent = true;
                        }

                        break;
                    }
                }

                if (found) {
                    return consistent;
                } else {
                    map.put(this.var, term.var);
                    return true;
                }
            }

        } else if (!this.isVariable() && !term.isVariable()) {

            Operation op1 = this.getTopOperation();
            Operation op2 = term.getTopOperation();
            if (op1.equals(op2)) {
                if (op1.isAssociative() && !op1.isCommutative()) {
                    try {
                        Vector<Term> v1 = this.getAssocSubterms(op1);
                        Vector<Term> v2 = term.getAssocSubterms(op2);

                        if (v1.size() == v2.size()) {
                            boolean same = true;
                            for (int i = 0; i < v1.size(); i++ ) {
                                Term tm1 = v1.elementAt(i);
                                Term tm2 = v2.elementAt(i);
                                same = same && tm1.equals(tm2);
                            }
                            result = same;
                        } else {
                            result = false;
                        }
                    } catch (TermException e) {
                    }

                } else if (op1.isAssociative() && op1.isCommutative()) {

                    try {
                        Vector<Term> v1 = this.getAssocSubterms(op1);
                        Vector<Term> v2 = term.getAssocSubterms(op2);

                        if (v1.size() == v2.size()) {
                            boolean same = true;
                            for (int i = 0; i < v1.size(); i++ ) {
                                Term tm1 = v1.elementAt(i);
                                boolean found = false;
                                for (int j = 0; j < v2.size(); j++ ) {
                                    Term tm2 = v2.elementAt(j);
                                    if (tm1.equals(tm2)) {
                                        v2.remove(tm2);
                                        found = true;
                                        break;
                                    }
                                }
                                if (!found) {
                                    same = false;
                                    break;
                                }
                            }
                            result = same;
                        } else {
                            result = false;
                        }
                    } catch (TermException e) {
                    }

                } else if (op1.equals(BoolModule.metaEq) || op1.equals(BoolModule.metaNeq)) {

                    if (Equation.debug) {
                        System.out.println("what happen: " + this + "  =?=  " + term);
                    }

                    Term[] tm1 = this.subterms;
                    Term[] tm2 = term.subterms;

                    HashMap<Variable, Variable> hm = new HashMap<>(map);
                    if (tm1[0].equals(tm2[0], hm) && tm1[1].equals(tm2[1], hm)) {
                        map = hm;
                        return true;
                    }

                    hm = new HashMap<>(map);
                    if (tm1[0].equals(tm2[1], hm) && tm1[1].equals(tm2[0], hm)) {
                        map = hm;
                        return true;
                    }

                    result = false;

                } else {

                    Term[] tm1 = this.subterms;
                    Term[] tm2 = term.subterms;
                    boolean same = true;
                    for (int i = 0; i < tm1.length; i++ ) {
                        same &= tm1[i].equals(tm2[i], map);
                    }
                    result = same;
                }
            } else {
                result = false;
            }
        } else {
            result = false;
        }

        return result;

    }

}
