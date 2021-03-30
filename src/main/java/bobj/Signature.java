package bobj;

import java.util.*;
import java.io.*;

/**
 * a class representing the signature in the first order theory.
 *
 * @author Kai Lin
 * @version %I% %G%
 *
 */
public class Signature
                       implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    Vector<Sort> sorts = new Vector<>();

    Vector<Variable> vars = new Vector<>();

    Subsort subsorts = new Subsort();

    Vector<Operation> operations = new Vector<>();

    Vector<Object> tokens = new Vector<>();

    Map<Operation, Vector<Operation>> compatible = new HashMap<>();

    // data for parsing optimization
    ArrayList<String> firsts = new ArrayList<>();

    ArrayList<String> lasts = new ArrayList<>();

    boolean balancedBrackets = true;

    boolean explicitRetract = true;

    // alias for system modules QID, NAT or INT
    HashMap<String, List<Sort>> alias = new HashMap<>();

    int parameters = 0;

    public Signature() {
        this.tokens.addElement("=");
        this.firsts.add("(");
        this.lasts.add(")");
    }

    public boolean containsSort(Sort s) {
        return this.sorts.contains(s);
    }

    public boolean containsSystemSort(Sort s) {
        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort sort = this.sorts.elementAt(i);
            if (sort.equals(s) && sort.getInfo()
                                      .equals("system-default")) {
                return true;
            }
        }
        return false;
    }

    public boolean containsSystemOperation(Operation op) {

        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation o = this.operations.elementAt(i);
            if (op.equals(o) && o.info.equals("system-default")) {
                return true;
            }
        }
        return false;

    }

    public boolean containsVariable(Variable v) {
        return this.vars.contains(v);
    }

    public boolean containsOperation(Operation op) {

//        for (int i = 0; i < operations.size(); i++ ) {
//            Operation o = (Operation) operations.elementAt(i);
//
//            if (op.equals(o)) {
//                return true;
//            }
//        }
//        return false;

        return this.operations.contains(op);
    }

    public Variable[] getVariablesOnSort(Sort s) {

        Vector<Variable> v = new Vector<>();

        for (Variable tmp : this.vars) {
            if (tmp.getSort()
                   .equals(s)) {
                v.addElement(tmp);
            }
        }

        Variable[] result = new Variable[v.size()];
        v.copyInto(result);
        return result;
    }

    public Variable[] getVariables() {

        Variable[] result = new Variable[this.vars.size()];
        this.vars.copyInto(result);
        return result;
    }

    public Operation[] getOperations() {

        Operation[] result = new Operation[this.operations.size()];
        this.operations.copyInto(result);
        return result;
    }

    public Operation[] getOperationsIn(ModuleName modName) {

        Vector<Operation> vec = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation tmp = this.operations.elementAt(i);
            if (tmp.modName.equals(modName)) {
                vec.addElement(tmp);
            }
        }

        Operation[] result = new Operation[vec.size()];
        vec.copyInto(result);

        return result;

    }

    public Operation getOperation(Operation op) {

        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation tmp = this.operations.elementAt(i);
            if (tmp.equals(op))
                return tmp;
        }

        return null;
    }

    public Operation[] getBehavorialOperations() {

        Vector<Operation> v = new Vector<>();

        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation tmp = this.operations.elementAt(i);
            if (tmp.isBehavorial()) {
                v.addElement(tmp);
            }
        }

        Operation[] result = new Operation[v.size()];
        v.copyInto(result);
        return result;
    }

    public Operation[] getOperations(Sort[] args,
                                     Sort res) {

        Vector<Operation> tmp = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);

            if (op.getArity() == args.length && this.isSubsort(op.resultSort, res)) {

                boolean same = true;
                for (int j = 0; j < args.length; j++ ) {
                    same = args[j].equals(op.argumentSorts[j]);
                    if (!same)
                        break;
                }

                if (same) {
                    tmp.addElement(op);
                }

            }

        }

        Operation[] result = new Operation[tmp.size()];
        tmp.copyInto(result);
        return result;
    }

    public Operation[] getOperationsWithCleanName(String na) {

        Vector<Operation> tmp = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.getCleanName()
                  .equals(na)) {
                tmp.addElement(op);
            }
        }

        Operation[] result = new Operation[tmp.size()];
        tmp.copyInto(result);
        return result;
    }

    public Operation[] getOperationsWithName(String na) {

        Vector<Operation> tmp = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);

            if (op.getName()
                  .equals(na)) {
                tmp.addElement(op);
            } else {

                String nname = na;
                Vector<Object> prod = op.getTokens();

                boolean samename = true;
                for (int j = 0; j < prod.size() && samename; j++ ) {
                    Object obj = prod.elementAt(j);
                    if (obj instanceof Sort) {

                        if (nname.startsWith("_")) {
                            nname = nname.substring(1)
                                         .trim();
                        } else if (nname.equals("") && (j == prod.size() - 1)) {
                        } else {
                            samename = false;
                        }
                    } else {

                        String piece = (String) obj;

                        if ((nname.startsWith(piece + " ") || nname.startsWith(piece + "_"))
                            || (j == prod.size() - 2 && nname.equals(piece))) {
                            nname = nname.substring(piece.length())
                                         .trim();
                        } else {
                            samename = false;
                        }
                    }
                }

                if (samename && nname.trim()
                                     .equals("")) {
                    tmp.addElement(op);
                }
            }
        }

        Operation[] result = new Operation[tmp.size()];
        tmp.copyInto(result);
        return result;
    }

    public Operation[] getConstants() {

        Vector<Operation> res = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isConstant()) {
                res.addElement(op);
            }
        }

        Operation[] result = new Operation[res.size()];
        res.copyInto(result);
        return result;

    }

    public Operation[] getConstants(String cname) {

        Vector<Operation> res = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isConstant() && op.getName()
                                     .equals(cname)) {
                res.addElement(op);
            }
        }

        Operation[] result = new Operation[res.size()];
        res.copyInto(result);
        return result;

    }

    public boolean hasOperation(String opname,
                                Sort[] args,
                                Sort res) {
        opname = Operation.normalize(opname);
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (opname.equals(op.name) && res.equals(op.resultSort)
                && args.length == op.argumentSorts.length) {

                boolean same = true;
                for (int j = 0; j < args.length; j++ ) {
                    if (!args[j].equals(op.argumentSorts[j])) {
                        same = false;
                        break;
                    }
                }

                if (same)
                    return true;

            }

        }

        return false;

    }

    public boolean hasCompatibleOperation(Operation op) {
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation tmp = this.operations.elementAt(i);

            boolean compatible = tmp.name.equals(op.name) && tmp.getArity() == op.getArity();

            if (compatible) {
                compatible = hasCommonSubsort(op.resultSort, tmp.resultSort)
                             || hasCommonSupersort(op.resultSort, tmp.resultSort);
            }

            if (compatible) {
                for (int j = 0; j < op.argumentSorts.length; j++ ) {
                    compatible = hasCommonSubsort(op.argumentSorts[j], tmp.argumentSorts[j])
                                 || hasCommonSupersort(op.argumentSorts[j], tmp.argumentSorts[j]);
                    if (!compatible)
                        break;

                }
            }

            if (compatible && !tmp.modName.equals(op.modName)) {
                return true;
            }
        }

        return false;

    }

    public Subsort getSubsorts() {
        return this.subsorts;
    }

    public void addSort(Sort sort) {
        if (!containsSort(sort)) {

            if (this.parameters > 1 && this.parameters == this.sorts.size()) {
                this.sorts.insertElementAt(sort, 2);
            } else {
                this.sorts.addElement(sort);
            }
        }
    }

    public Sort getSuperSort(Sort s1,
                             Sort s2) {
        Sort result = null;

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (isSubsort(s1, tmp) && isSubsort(s2, tmp)) {
                if ((result == null) || isSubsort(tmp, result)) {
                    result = tmp;
                }
            }
        }

        return result;
    }

    public boolean hasCommonSubsort(Sort s1,
                                    Sort s2) {
        boolean result = false;

        for (int i = 0; i < this.sorts.size() && !result; i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            result = isSubsort(tmp, s1) && isSubsort(tmp, s2);
        }

        return result;
    }

    public void addVariable(Variable v) throws SignatureException {

        if (!containsSort(v.getSort())) {
            throw new SignatureException("Variable " + v.getName() + " has an unknown sort: "
                                         + v.getSort()
                                            .getName());
        }

        this.vars.addElement(v);

        String name = v.getName()
                       .trim();

        // insert the name of this variable into tokens
        if (this.tokens.indexOf(name) == -1) {
            boolean found = false;
            for (int i = 0; i < this.tokens.size() && !found; i++ ) {
                String st = (String) this.tokens.elementAt(i);
                if (st.length() < name.length()) {
                    this.tokens.insertElementAt(name, i);
                    found = true;
                }
            }

            if (!found) {
                this.tokens.addElement(name);
            }
        }

        this.firsts.add(name);
        this.lasts.add(name);

    }

    protected void addTokens(ModuleName modName) {

        if (modName.op == ModuleName.ATOM) {
            String name = modName.atom;
            if (this.tokens.indexOf(name) == -1) {
                boolean found = false;
                for (int i = 0; i < this.tokens.size() && !found; i++ ) {
                    String st = (String) this.tokens.elementAt(i);
                    if (st.length() < name.length()) {
                        this.tokens.insertElementAt(name, i);
                        found = true;
                    }
                }

                if (!found) {
                    this.tokens.addElement(name);
                }
            }
        }
    }

    public void addOperation(Operation op) throws SignatureException {

        // check if all sorts in this signature
        Sort[] args = op.getArgumentSorts();
        Sort rs = op.getResultSort();

        for (Sort arg : args) {
            if (!containsSort(arg)) {
                throw new SignatureException("Unknown sort: " + arg);
            }
        }

        if (!containsSort(rs)) {
            throw new SignatureException("Unknown sort: " + rs);
        }

        // check if op is already in this signature
        if (!containsOperation(op)) {

            // check properties
            if (op.getArity() == 2) {
                if (op.isAssociative()) {

                } else {
                    Operation[] ops = getOperationsWithName(op.getName());
                    for (Operation op2 : ops) {
                        if (op.less(this, op2) && op2.isAssociative()) {
                            op.setAssociativity(this);
                            break;
                        }
                    }
                }
            }

            // end checking

            this.operations.addElement(op);

            //begin of adding compatible

            Vector<Operation> pool = new Vector<>();
            boolean foundOp = false;
            for (int i = 0; i < this.operations.size() && !foundOp; i++ ) {
                Operation tmp = this.operations.elementAt(i);
                if (!tmp.equals(op) && (tmp.less(this, op) || op.less(this, tmp))) {
                    foundOp = true;
                    for (Operation optmp : this.compatible.keySet()) {
                        if (optmp.equals(tmp)) {
                            pool = this.compatible.get(optmp);
                            break;
                        }
                    }
                }
            }

            if (foundOp) {
                boolean insert = false;
                for (int j = 0; j < pool.size() && !insert; j++ ) {
                    Operation o = pool.elementAt(j);
                    if (op.less(this, o)) {
                        pool.insertElementAt(op, j);
                        insert = true;
                    }
                }
                if (!insert) {
                    pool.addElement(op);
                }

                for (int i = 0; i < pool.size(); i++ ) {
                    Operation o = pool.elementAt(i);
                    this.compatible.put(o, pool);
                }

            } else {
                pool.addElement(op);
                this.compatible.put(op, pool);
            }

            //end of adding compatible

            if (op.getArity() == 2 && op.id == null && op.implicitId == null) {

                Operation[] ops = getGreaterCompatible(op);
                for (Operation op2 : ops) {
                    Operation id = op2.getIdentity();
                    if (id != null) {
                        if (isSubsort(id.resultSort, op.argumentSorts[0])
                            || isSubsort(id.resultSort, op.argumentSorts[1])) {
                            op.implicitId = id;
                        }
                    }
                }
            }

            if (op.getArity() == 2 && op.id != null) {

                for (int i = 0; i < this.operations.size(); i++ ) {
                    Operation otmp = this.operations.elementAt(i);
                    if (otmp.less(this, op)) {

                        if (otmp.id == null && otmp.implicitId == null
                            && (isSubsort(op.id.resultSort, otmp.argumentSorts[0])
                                || isSubsort(op.id.resultSort, otmp.argumentSorts[1]))) {

                            otmp.implicitId = op.id;

                        }
                    }
                }
            }

            // insert the tokens of this operation into tokens vector
            String name = op.getName()
                            .trim();
            StringTokenizer st = new StringTokenizer(name, " \n\t_");
            while (st.hasMoreTokens()) {
                String tmp = st.nextToken()
                               .trim();

                if (this.tokens.indexOf(tmp) == -1) {
                    boolean found = false;
                    for (int i = 0; i < this.tokens.size() && !found; i++ ) {
                        String str = (String) this.tokens.elementAt(i);
                        if (str.length() < tmp.length()) {
                            this.tokens.insertElementAt(tmp, i);
                            found = true;
                        }
                    }

                    if (!found) {
                        this.tokens.addElement(tmp);
                    }
                }

            }

        } else {

            Operation oper = getOperation(op);
            if (op.isAssociative()) {
                oper.isAssociative = true;
            } else if (op.isCommutative()) {
                oper.setCommutativity();
            } else if (op.isIdempotent()) {
                oper.setIdempotence();
            }
        }

        // check consistence

        // handle firsts and lasts
        Vector<Object> tks = op.getTokens();
        Object obj1 = tks.elementAt(0);
        if (obj1 instanceof String) {
            String symbol = (String) obj1;
            symbol = symbol.trim();

            if (!this.firsts.contains(symbol)) {
                this.firsts.add(symbol);
            }
        }

        Object obj2 = tks.elementAt(tks.size() - 1);
        if (obj2 instanceof String) {
            String symbol = (String) obj2;
            symbol = symbol.trim();

            if (!this.lasts.contains(symbol)) {
                this.lasts.add(symbol);
            }
        }

        if (this.balancedBrackets && !op.hasBalancedBrackets()) {
            this.balancedBrackets = false;
        }

    }

    public void addSubsort(Sort parent,
                           Sort child)
        throws SignatureException {

        //check if parent and child are in this signature

        if (containsSort(parent)) {
            if (containsSort(child)) {
                try {
                    this.subsorts.addSubsort(parent, child);
                } catch (SubsortException e) {
                    throw new SignatureException(e.getMessage());
                }
            } else {
                throw new SignatureException("Unknown sort: " + child.getName());
            }
        } else {
            throw new SignatureException("Unknown sort: " + parent.getName());
        }

    }

    public void addSubsorts(Subsort sub) throws SignatureException {

        Map<Sort, Vector<Sort>> tab = new HashMap<>(sub.subsorts);

        for (Sort p : tab.keySet()) {
            Vector<Sort> v = tab.get(p);
            for (int i = 0; i < v.size(); i++ ) {
                Sort c = v.elementAt(i);
                addSubsort(p, c);
            }
        }

    }

    @Override
    public String toString() {

        String result = "";

        for (Sort tmp : this.sorts) {
            result += tmp + "\n";
        }

        String stmp = this.subsorts.toString();
        StringTokenizer st = new StringTokenizer(stmp, "\n");
        while (st.hasMoreTokens()) {
            result += st.nextToken()
                        .trim()
                      + "\n";
        }

        for (Variable tmp : this.vars) {
            result += tmp + "\n";
        }

        for (Operation tmp : this.operations) {
            result += tmp + "\n";
        }

        return result;
    }

    public Sort[] getSorts() {
        Sort[] result = new Sort[this.sorts.size()];
        this.sorts.copyInto(result);
        return result;
    }

    public Sort getSort(Sort sort) {

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (tmp.equals(sort)) {
                return tmp;
            }
        }

        return null;
    }

    public Sort getPrincipalSort() {
        Sort first = this.sorts.elementAt(0);
        if (first.equals(BoolModule.boolSort) && first.getInfo()
                                                      .equals("system-default")
            && this.sorts.size() > 2) {
            return this.sorts.elementAt(2);
        } else {
            return first;
        }
    }

    public Sort[] getHiddenSorts() {

        Vector<Sort> v = new Vector<>();

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (tmp.isHidden()) {
                v.addElement(tmp);
            }
        }

        Sort[] result = new Sort[v.size()];
        v.copyInto(result);
        return result;

    }

    public Sort[] getInitialSorts() {

        Vector<Sort> v = new Vector<>();

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (tmp.isInitial()) {
                v.addElement(tmp);
            }
        }

        Sort[] result = new Sort[v.size()];
        v.copyInto(result);
        return result;

    }

    public Sort[] getHiddenSortsByName(String name) {
        Vector<Sort> vec = new Vector<>();

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort sort = this.sorts.elementAt(i);
            if (sort.isHidden() && sort.getName()
                                       .equals(name)) {
                vec.addElement(sort);
            }
        }

        Sort[] result = new Sort[vec.size()];
        vec.copyInto(result);
        return result;

    }

    public Sort[] getSortsByName(String name) {
        Vector<Sort> vec = new Vector<>();

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort sort = this.sorts.elementAt(i);
            if (sort.getName()
                    .equals(name)) {
                vec.addElement(sort);
            }
        }

        Sort[] result = new Sort[vec.size()];
        vec.copyInto(result);
        return result;

    }

    public Sort[] getVisibleSorts() {

        Vector<Sort> v = new Vector<>();

        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (!tmp.isHidden() && !tmp.getName()
                                       .equals("Universal")) {
                v.addElement(tmp);
            }
        }

        Sort[] result = new Sort[v.size()];
        v.copyInto(result);
        return result;

    }

    public Operation getConstant(String on) {
        Operation op = null;

        for (Operation tmp : this.operations) {
            if (tmp.getName()
                   .equals(on)
                && tmp.getArgumentSorts().length == 0) {
                op = tmp;
                break;
            }
        }

        return op;
    }

    public Operation getConstant(String on,
                                 Sort sort) {

        for (Operation tmp : this.operations) {
            if (tmp.getName()
                   .equals(on)
                && tmp.getArgumentSorts().length == 0 && tmp.getResultSort()
                                                            .equals(sort)) {
                return tmp;
            }
        }

        return null;
    }

    public Operation[] getOperationsWithPriority(int p) {

        Vector<Operation> res = new Vector<>();

        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            int pri = op.getPriority();
            if (p == pri) {
                res.addElement(op);
            }
        }

        Operation[] result = new Operation[res.size()];
        res.copyInto(result);
        return result;
    }

    public boolean isSubsort(Sort child,
                             Sort parent) {
        return child.equals(parent) || this.subsorts.isSubsort(parent, child);
    }

    public boolean less(Sort child,
                        Sort parent) {
        return this.subsorts.isSubsort(parent, child);
    }

    protected Vector<Object> getTokens() {
        return new Vector<>(this.tokens);
    }

    protected String decomposeToken(String st) {

        String result = null;

        if (st.trim()
              .equals("")) {
            return "";
        }

        if (st.startsWith("(") || st.startsWith(")") || st.startsWith(",")) {
            if (st.length() > 1) {
                String tmp = st.substring(1);
                tmp = decomposeToken(tmp);
                if (tmp == null) {
                    return null;
                } else {
                    return st.substring(0, 1) + " " + tmp;
                }
            } else {
                return st;
            }
        }

        // decompose by tokens
        boolean found = false;
        String sample = "";
        for (int i = 0; i < this.tokens.size() && !found; i++ ) {
            sample = (String) this.tokens.elementAt(i);
            if (st.startsWith(sample)) {
                found = true;
            }
        }

        if (found) {

            String tmp = st.substring(sample.length());
            tmp = decomposeToken(tmp);

            if (tmp != null) {
                result = sample + " " + tmp;
            }
        } else {

            try {
                int num = Integer.parseInt(st);
                if ((containsSystemSort(new Sort("Nat", new ModuleName("NAT"))) && num >= 0)
                    || (containsSystemSort(new Sort("Int", new ModuleName("INT"))) && num < 0)) {
                    result = st + " ";
                }

            } catch (Exception e) {
            }
        }

        if (result == null) {

            // handle module expression here
            if (st.startsWith(".")) {
                String stmp = st.substring(1);
                String tmp = decomposeToken(stmp);
                if (tmp != null) {
                    result = ". " + tmp;
                } else {
                    result = ". " + stmp;
                }
            }
        }

        return result;
    }

    public boolean containsToken(String st) {
        return(st.equals("=") || this.tokens.indexOf(st) != -1);
    }

    public boolean contains(Signature signature) {
        boolean result = true;

        for (int i = 0; i < signature.sorts.size(); i++ ) {
            Sort sort = signature.sorts.elementAt(i);
            result = this.containsSort(sort);
            if (!result)
                return false;
        }

        for (int i = 0; i < signature.operations.size(); i++ ) {
            Operation op = signature.operations.elementAt(i);
            result = this.containsOperation(op);
            if (!result)
                return false;
        }

        result = this.subsorts.contains(signature.subsorts);

        return result;
    }

    public Sort canApply(Sort s1,
                         Sort s2) {
        return this.subsorts.canApply(s1, s2);
    }

    public Operation[] getSortedOperationsCompatibleWith(Operation op) {
        Vector<Operation> pool = this.compatible.get(op);

        if (pool == null) {
            for (Operation tmp : this.compatible.keySet()) {
                if (op.equals(tmp)) {
                    pool = this.compatible.get(tmp);
                }
            }
        }

        if (pool == null) {
            pool = new Vector<>();
            pool.addElement(op);
        }
        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;
    }

    protected Operation[] getGreaterCompatible(Operation op) {

        Vector<Operation> pool = this.compatible.get(op);
        if (pool == null) {
            return new Operation[0];
        } else {
            pool = new Vector<>(pool);
            for (int i = 0; i < pool.size(); i++ ) {
                Operation tmp = pool.elementAt(i);
                pool.removeElementAt(0);
                if (tmp.equals(op)) {
                    break;
                }
            }
        }

        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;

    }

    public Signature copy() {

        Signature result = new Signature();

        result.sorts = new Vector<>(this.sorts);
        result.vars = new Vector<>(this.vars);
        result.subsorts = (Subsort) this.subsorts.clone();
        result.operations = new Vector<>(this.operations);
        result.tokens = new Vector<>(this.tokens);
        result.compatible = new HashMap<>(this.compatible);
        result.firsts = new ArrayList<>(this.firsts);
        result.lasts = new ArrayList<>(this.lasts);
        result.balancedBrackets = this.balancedBrackets;
        result.explicitRetract = this.explicitRetract;

        return result;
    }

    public Operation[] getAttributes() {

        Vector<Operation> pool = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isAttribute() && !op.isConstant()) {
                pool.addElement(op);
            }
        }

        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;
    }

    public Operation[] getMethods() {
        Vector<Operation> pool = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isMethod() && !op.isConstant()) {
                pool.addElement(op);
            }
        }

        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;
    }

    public Operation[] getNonBehavorialOperations() {

        Vector<Operation> pool = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isNonBehavorial() && !op.isConstant()) {
                pool.addElement(op);
            }
        }

        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;
    }

    public Operation[] getOperationsOnInitial() {

        Vector<Operation> pool = new Vector<>();
        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            if (op.isDefinedOnInitial()) {
                pool.addElement(op);
            }
        }

        Operation[] result = new Operation[pool.size()];
        pool.copyInto(result);
        return result;

    }

    protected Operation getUniqueOperation(String begin,
                                           String end,
                                           Sort expect) {

        Vector<Operation> pool = new Vector<>();

        for (int i = 0; i < this.operations.size(); i++ ) {
            Operation op = this.operations.elementAt(i);
            String name = op.getName();
            if (name.startsWith(begin) && name.endsWith(end) && op.getResultSort()
                                                                  .equals(expect)) {
                pool.addElement(op);
            }
        }

        if (pool.size() == 1) {
            return pool.elementAt(0);
        }

        return null;

    }

    public void addQidAlias(Sort sort) {
        List<Sort> list = this.alias.get("QID");
        if (list == null) {
            list = new ArrayList<>();
        }

        if (!list.contains(sort)) {
            list.add(sort);
        }

        this.alias.put("QID", list);

    }

    public Sort[] getQidAlias() {
        List<Sort> list = this.alias.get("QID");
        if (list != null) {

            Object[] objs = list.toArray();
            Sort[] sorts = new Sort[objs.length];
            for (int i = 0; i < objs.length; i++ ) {
                sorts[i] = (Sort) objs[i];
            }

            return sorts;
        } else {
            return null;
        }
    }

    public boolean hasUniqueNameFor(Sort sort) {

        int count = 0;
        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (tmp.getName()
                   .equals(sort.getName())) {

                count++ ;
                if (count > 1) {
                    return false;
                }
            }
        }

        if (count == 1)
            return true;
        else return false;

    }

    protected ArrayList<String> getFirsts() {

        ArrayList<String> result = new ArrayList<>();

        result.add("(");

        for (int k = 0; k < this.operations.size(); k++ ) {
            Operation op = this.operations.elementAt(k);

            this.tokens = op.getTokens();
            Object obj = this.tokens.elementAt(0);

            if (obj instanceof String) {

                String symbol = (String) obj;
                symbol = symbol.trim();

                if (!result.contains(symbol)) {
                    result.add(symbol);
                }
            }
        }

        for (int k = 0; k < this.vars.size(); k++ ) {
            Variable var = this.vars.elementAt(k);
            result.add(var.name);
        }

        return result;

    }

    protected ArrayList<String> getLasts() {

        ArrayList<String> result = new ArrayList<>();

        result.add(")");

        for (int k = 0; k < this.operations.size(); k++ ) {
            Operation op = this.operations.elementAt(k);
            Vector<Object> tokens = op.getTokens();
            Object obj = tokens.elementAt(tokens.size() - 1);

            if (obj instanceof String) {

                String symbol = (String) obj;
                symbol = symbol.trim();

                if (!result.contains(symbol)) {
                    result.add(symbol);
                }
            }
        }

        for (int k = 0; k < this.vars.size(); k++ ) {
            Variable var = this.vars.elementAt(k);
            result.add(var.name);
        }

        return result;

    }

    public boolean hasCommonSupersort(Sort s1,
                                      Sort s2) {
        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort sort = this.sorts.elementAt(i);
            if (!sort.equals(BoolModule.univSort) && this.isSubsort(s1, sort)
                && this.isSubsort(s2, sort)) {

                return true;
            }
        }

        return false;
    }

    public Sort[] getDirectSupersorts(Sort sort) {
        ArrayList<Sort> list = new ArrayList<>();
        for (int i = 0; i < this.sorts.size(); i++ ) {
            Sort tmp = this.sorts.elementAt(i);
            if (!tmp.equals(BoolModule.univSort) && !tmp.equals(sort) && isSubsort(sort, tmp)) {
                // tmp is candidate, but make sure tmp is not a supersort
                // of a sort in list

                ArrayList<Sort> buf = new ArrayList<>();
                boolean add = true;
                for (int j = 0; j < list.size(); j++ ) {
                    Sort s = list.get(j);
                    if (isSubsort(s, tmp)) {
                        buf.add(s);
                        add = false;
                    } else if (isSubsort(tmp, s)) {

                    }
                }

                if (add) {
                    buf.add(tmp);
                }
                list = buf;
            }

        }

        Sort[] result = new Sort[list.size()];
        for (int i = 0; i < result.length; i++ ) {
            result[i] = list.get(i);
        }

        return result;

    }

    public Sort[] getDirectSubsorts(Sort sort) {
        ArrayList<Sort> list = new ArrayList<>();
        Vector<Sort> vec = this.subsorts.subsorts.get(sort);
        if (vec != null) {
            for (int i = 0; i < vec.size(); i++ ) {
                Sort tmp = vec.elementAt(i);

                ArrayList<Sort> buf = new ArrayList<>();
                boolean add = true;
                for (int j = 0; j < list.size(); j++ ) {
                    Sort s = list.get(j);
                    if (isSubsort(s, tmp)) {

                    } else if (isSubsort(tmp, s)) {
                        buf.add(s);
                        add = false;
                    }
                }

                if (add) {
                    buf.add(tmp);
                }
                list = buf;

            }
        }

        Sort[] result = new Sort[list.size()];
        for (int i = 0; i < result.length; i++ ) {
            result[i] = list.get(i);
        }

        return result;

    }

}
