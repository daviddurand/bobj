package bobj;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.Vector;

public class View
                  implements ViewRenamable {

    boolean morphism = false;

    String name;

    Module main, source, target, smodule, tmodule;

    Map<Sort, Sort> sortMap;

    Map<Operation, Operation> opMap;

    Map<Variable, Variable> varMap;

    Map<Term, Term> trans;

    boolean allowSortDef = true;

    ArrayList<View> views = new ArrayList<>();

    Map<Object, Object> record = new HashMap<>();

    boolean debug = false;

    public void setAsMorphism() {
        this.morphism = true;
    }

    public void record() {
        this.record.putAll(this.sortMap);
        this.record.putAll(this.opMap);
        this.record.putAll(this.varMap);
        this.record.putAll(this.trans);
    }

    public View copy(String newName) {

        View result = new View(newName, this.source, this.target);
        result.main = this.main;
        result.smodule = this.smodule;
        result.smodule = this.smodule;
        result.sortMap = this.sortMap;
        result.opMap = this.opMap;
        result.varMap = this.varMap;
        result.trans = this.trans;
        result.allowSortDef = this.allowSortDef;
        result.views = this.views;
        result.record = this.record;
        return result;

    }

    /**
     *
     * create a new view from the source to target
     *
     */
    public View(Module source,
                Module target) {
        this(null, source, target);
        throw new Error("don't allow empty view name");
    }

    /**
     *
     * create a view with the specified name
     *
     */
    public View(String name,
                Module source,
                Module target) {

        this.name = name;
        this.source = source;
        this.target = target;
        this.smodule = new Module(source.type, source.modName);
        this.tmodule = new Module(target.type, target.modName);

        try {
            this.smodule.importModule(source);
            this.tmodule.importModule(target);
        } catch (SignatureException e) {
        }

        this.sortMap = new HashMap<>();
        this.opMap = new HashMap<>();
        this.varMap = new HashMap<>();
        this.trans = new HashMap<>();
    }

    public String getName() {
        return this.name;
    }

    public Module getSource() {
        return this.source;
    }

    public Module getTarget() {
        return this.target;
    }

    public Module getEnrichedSource() {
        return this.smodule;
    }

    public Module getEnrichedTarget() {
        return this.tmodule;
    }

    public Sort getTarget(Sort sort) {
        for (Sort tmp : this.sortMap.keySet()) {
            if (sort.equals(tmp)) {
                return this.sortMap.get(tmp);
            }
        }

        return null;
    }

    public Operation getTarget(Operation op) {
        for (Operation oper : this.opMap.keySet()) {
            if (op.equals(oper)) {
                return this.opMap.get(oper);
            }
        }

        return null;
    }

    public void addVariable(Variable var) throws ViewException {

        try {
            this.smodule.addVariable(var);

            Sort sort = var.getSort();
            sort = getTarget(sort);

            if (sort != null) {

                // there is a mapping in sortMap
                Variable targetVar = new Variable(var.getName(), sort);
                try {
                    this.tmodule.addVariable(targetVar);
                    this.varMap.put(var, targetVar);
                } catch (SignatureException e) {
                }

            } else if (this.tmodule.containsSort(var.sort)) {

                // no mapping, but sort is contained in target
                this.tmodule.addVariable(var);
                this.varMap.put(var, var);

            } else if (this.smodule.getPrincipalSort()
                                   .equals(var.sort)
                       && this.sortMap.size() == 0) {

                           // use the mapping between the principle sorts
                           sort = this.tmodule.getPrincipalSort();
                           Variable tvar = new Variable(var.name, sort);
                           this.tmodule.addVariable(tvar);
                           this.varMap.put(var, tvar);
                       }

        } catch (SignatureException e) {
            throw new ViewException(e.getMessage());
        }

    }

    public boolean isMapTo(Sort from,
                           Sort to) {

        Sort sort = getTarget(from);
        if (sort != null) {
            return this.target.isSubsort(to, sort);
        } else if (from.equals(to)) {
            return true;
        } else {
            // not defined yet for sort mapping of from
            sort = this.target.getSort(from);
            if (sort != null) {
                return this.target.isSubsort(to, sort) || this.target.isSubsort(sort, to);
            } else {
                return from.equals(to);
            }
        }

    }

    public void addSortMap(Sort from,
                           Sort to)
        throws ViewException {

        if (!this.allowSortDef) {
            String msg =
                "A default mapping is defined alreday, no more " + " sort mapping can be defined";
            throw new ViewException(msg);
        }

        if (!this.source.containsSort(from)) {
            String msg = "Sort " + from.getName() + " not in source " + this.source.getModuleName();
            throw new ViewException(msg);
        }

        if (!this.target.containsSort(to)) {
            String msg = "Sort " + to.getName() + " not in target " + this.target.getModuleName();
            throw new ViewException(msg);
        }

        Sort tmp = getTarget(from);
        if (tmp != null) {
            if (!tmp.equals(to)) {
                throw new ViewException("A mapping for " + from.getName() + " already exists");
            }
        } else {
            this.sortMap.put(from, to);
        }

    }

    public void addOperationMap(Operation from,
                                Operation to)
        throws ViewException {

        if (!this.source.containsOperation(from)) {
            String msg =
                "Operation " + from.getName() + " not in the source " + this.source.getModuleName();
            throw new ViewException(msg);
        }

        if (!this.target.containsOperation(to)) {
            String msg =
                "Operation " + to.getName() + " not in the target " + this.target.getModuleName();
            throw new ViewException(msg);
        }

        Operation tmp = getTarget(from);
        if (tmp != null) {
            if (!tmp.equals(to)) {
                throw new ViewException("A mapping for " + from.getName() + " already exists");
            }
        } else {
            if (this.sortMap.isEmpty()) {

                // use the mapping between the principal sorts
                if (this.allowSortDef) {

                    this.allowSortDef = false;

                    // set sort mapping here
                    this.sortMap.put(this.source.getPrincipalSort(),
                                     this.target.getPrincipalSort());

                }

            }

            Sort[] args1 = from.getArgumentSorts();
            Sort[] args2 = to.getArgumentSorts();

            if (args1.length != args2.length) {
                throw new ViewException("The arities of the opeartions " + from.getCleanName()
                                        + " and " + to.getCleanName() + " are different");
            } else {

                for (int i = 0; i < args1.length; i++ ) {
                    Sort sort1 = args1[i];
                    Sort sort2 = args2[i];
                    if (!isMapTo(sort1, sort2)) {
                        this.sortMap.put(sort1, sort2);
                        /* throw new ViewException("Sort "+sort1.getName()+
                         * " is not mapped into "+sort2.getName()); */
                    }
                }

                Sort resSort1 = from.getResultSort();
                Sort resSort2 = to.getResultSort();

                if (!isMapTo(resSort1, resSort2)) {

                    /* if (resSort1.getName().equals(resSort2.getName())) { sortMap.put(resSort1,
                     * resSort2); opMap.put(from, to); return; }
                     *
                     * throw new ViewException(to.getCleanName()+
                     * " is not of sort "+resSort1.getName()+"    "+resSort1.getModuleName()); */
                    this.sortMap.put(resSort1, resSort2);
                }
            }
            this.opMap.put(from, to);
        }

    }

    public void addTransformation(Term left,
                                  Term right) {
        this.trans.put(left, right);
    }

    @Override
    public String toString() {
        String result = "";

        String sname = this.source.getModuleName()
                                  .toString();
        String tname = this.target.getModuleName()
                                  .toString();

        if (this.name == null) {
            this.name = "";
        }

        String header = this.morphism ? "   morph "
                                      : "   view ";

        if (sname.length() + tname.length() + this.name.length() + 12 > 80) {
            result += header + this.name + "\n" + "         from " + sname + "\n" + "         to "
                      + tname;
        } else if (this.name.length() > 0) {
            result += header + this.name + " from " + sname + " to " + tname;
        } else {
            result += header + "from " + sname + " to " + tname;
        }

        result += " is \n";

        if (this.views.size() > 0 && this.morphism) {

            result += "      [ \n";
            for (Object view : this.views) {
                View v = (View) view;

                String str = v.toString();
                StringTokenizer st = new StringTokenizer(str, "\n");
                while (st.hasMoreTokens()) {
                    result += "      " + st.nextToken() + "\n";
                }

            }
            result += "      ]\n";
        }

        if (this.record.size() != 0) {

            Iterator<Object> itor = this.record.keySet()
                                               .iterator();
            while (itor.hasNext()) {
                Object key = itor.next();
                Object val = this.record.get(key);
                if (key instanceof Sort) {

                    Sort from = (Sort) key;
                    Sort to = (Sort) val;
                    result += "      sort " + this.source.toString(from) + " to "
                              + this.target.toString(to) + " .\n";
                }
            }

            itor = this.record.keySet()
                              .iterator();
            while (itor.hasNext()) {
                Object key = itor.next();
                Object val = this.record.get(key);
                if (key instanceof Operation) {
                    Operation from = (Operation) key;
                    Operation to = (Operation) val;
                    result += "      op " + from.getName() + " to " + to.getName() + " .\n";
                }
            }

            itor = this.record.keySet()
                              .iterator();
            while (itor.hasNext()) {
                Object key = itor.next();
                Object val = this.record.get(key);
                if (key instanceof Term) {
                    Term from = (Term) key;
                    Term to = (Term) val;
                    result += "      op " + from + " to " + to + " .\n";
                }
            }

            result += "   endv\n";

            return result;
        }

        Variable[] vars = this.smodule.getVariables();
        for (Variable var : vars) {
            result += "      var " + var.getName() + " : " + var.getSort()
                                                                .getName()
                      + ".\n";
        }

        for (Sort from : this.sortMap.keySet()) {
            Sort to = this.sortMap.get(from);
            if (from.getInfo()
                    .equals("system-default")
                && from.equals(to)) {

            } else {
                //result += "      sort "+source.toString(from)+
                //    " to "+target.toString(to)+" .\n";

                result += "      " + from + " to " + to + " .\n";
            }
        }

        for (Operation from : this.opMap.keySet()) {
            Operation to = this.opMap.get(from);
            if (from.info.equals("system-default") && from.equals(to)) {

            } else {
                result += "      op " + from.getName() + " to " + to.getName() + " .\n";

                //result += "      "+from+"   "+from.modName+
                //          " to "+to+"    "+to.modName+" .\n";

            }
        }

        for (Term left : this.trans.keySet()) {
            Term right = this.trans.get(left);
            result += "      op " + left + " to " + right + " .\n";
        }

        result += "   endv\n";

        return result;
    }

    public void validate() throws ViewException {

        for (int i = 0; i < this.source.sorts.size(); i++ ) {
            Sort from = this.source.sorts.elementAt(i);

            if (this.sortMap.containsKey(from)) {
                continue;

            } else if (from.equals(this.source.getPrincipalSort())) {

                this.sortMap.put(from, this.target.getPrincipalSort());
                continue;

            } else if (this.target.containsSort(from)) {

                this.sortMap.put(from, from);
                continue;

            } else {

                Sort[] sorts = this.target.getSortsByName(from.getName());
                if (sorts.length == 1) {
                    this.sortMap.put(from, sorts[0]);
                } else {

                    Sort[] s = this.source.getDirectSubsorts(from);
                    if (s.length == 1) {
                        Sort tmp = getTarget(s[0]);
                        if (tmp != null) {
                            s = this.target.getDirectSupersorts(tmp);
                            if (s.length == 1) {
                                this.sortMap.put(from, s[0]);
                                continue;
                            }
                        }
                    }

                    int count = -1;
                    boolean done = false;
                    for (int j = 2; j < this.target.sorts.size(); j++ ) {
                        Sort to = this.target.sorts.elementAt(j);
                        ModuleName modName = to.getModuleName();

                        if (!modName.hasNotation()) {

                            if (modName.op == ModuleName.ATOM
                                && (modName.atom.equals("INT") || modName.atom.equals("NAT"))
                                && (this.target.containsSystemSort(IntModule.intSort)
                                    || this.target.containsSystemSort(IntModule.natSort))) {
                                continue;
                            }

                            count++ ;

                            if (count == i - 2) {
                                this.sortMap.put(from, to);
                                done = true;
                                break;
                            }

                        } else {

                            Sort tmp = this.source.sorts.elementAt(j);
                            ModuleName tmpName = tmp.getModuleName();

                            if (tmpName.hasNotation() && tmpName.atom.equals(modName.atom)) {
                                count++ ;
                            }

                        }

                    }

                    if (!done) {
                        throw new ViewException("no mapping for " + from + " in "
                                                + this.source.getModuleName(), this);
                    }
                }
            }

        }

        // check operations
        for (int i = 0; i < this.source.operations.size(); i++ ) {
            Operation from = this.source.operations.elementAt(i);

            boolean got = false;
            for (Operation o : this.opMap.keySet()) {
                if (o.equals(from)) {
                    got = true;
                    break;
                }
            }

            if (!got) {
                for (Term left : this.trans.keySet()) {
                    if (left.operation.equals(from)) {
                        got = true;
                        break;
                    }
                }
            }

            // check mapping is defined
            if (got) {
                continue;
            } else {

                Operation[] ops = this.target.getOperationsWithName(from.getName());
                ArrayList<Operation> list = new ArrayList<>();
                for (Operation op : ops) {

                    if (isAbleToMap(from, op)) {
                        list.add(op);
                    }

                }

                if (list.size() == 1) {
                    this.opMap.put(from, list.get(0));
                    continue;
                } else {

                    if (list.size() == 0) {

                        // search by the from's signature
                        Sort[] args = new Sort[from.getArity()];
                        for (int k = 0; k < args.length; k++ ) {
                            args[k] = getTarget(from.argumentSorts[k]);
                        }
                        Sort resSort = getTarget(from.resultSort);
                        ops = this.target.getOperations(args, resSort);

                        if (ops.length == 1) {
                            this.opMap.put(from, ops[0]);
                            continue;
                        }
                    } else {

                        boolean done = false;
                        for (Operation tmp : list) {
                            if (getTarget(from.getResultSort()).equals(tmp.getResultSort())) {
                                this.opMap.put(from, tmp);
                                done = true;
                                break;
                            }
                        }

                        if (done)
                            continue;

                    }

                    boolean found = false;
                    for (Term term : this.trans.keySet()) {
                        if (!term.isVariable() && term.getTopOperation()
                                                      .equals(from)) {
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        throw new ViewException("no mapping for " + from, this);
                    }

                }
            }

        }

    }

    private boolean isAbleToMap(Operation from,
                                Operation to) {

        if (from.getArity() == to.getArity()) {
            for (int i = 0; i < from.getArity(); i++ ) {
                try {

                    Sort s1 = getTarget(from.getArgumentSortAt(i));
                    Sort s2 = getTarget(to.getArgumentSortAt(i));

                    if (s1 == null) {
                        this.sortMap.put(s1, s2);
                    } else if (s2 == null) {

                    } else if (!s1.equals(s2)) {
                        return false;
                    }

                } catch (SignatureException e) {
                }
            }

            return getTarget(from.getResultSort()).equals(to.getResultSort());

            // return true;
        } else {
            return false;
        }

    }

    public Sort getImage(Sort sort) {
        Sort result = getTarget(sort);
        if (result == null) {
            return sort;
        } else {
            return result;
        }

    }

    public Variable getImage(Variable var) {
        return new Variable(var.getName(), getImage(var.getSort()));
    }

    public Operation getImage(Operation op) {

        Operation result = getTarget(op);
        if (result != null) {
            return result;
        }

        Sort[] args = new Sort[op.getArity()];
        for (int i = 0; i < args.length; i++ ) {
            args[i] = getTarget(op.argumentSorts[i]);
            if (args[i] == null) {
                args[i] = op.argumentSorts[i];
            }
        }

        Sort res = getTarget(op.resultSort);
        if (res == null) {
            res = op.resultSort;
        }

        try {
            result = new Operation(op.getName(), args, res, op.modName);
            result.priority = op.priority;
            result.info = op.info;
            result.isAssociative = op.isAssociative;
            result.isCommutative = op.isCommutative;
            result.isIdempotent = op.isIdempotent;
            if (op.id != null)
                result.id = getImage(op.id);
            if (op.implicitId != null)
                result.implicitId = getImage(op.implicitId);
            result.behavorial = op.behavorial;
            result.gather = op.gather;
            result.strategy = op.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Subsort getImage(Subsort subsort) throws SubsortException {

        Subsort result = new Subsort();

        for (Sort superSort : subsort.subsorts.keySet()) {
            Vector<Sort> subs = subsort.subsorts.get(superSort);
            for (int i = 0; i < subs.size(); i++ ) {
                Sort subSort = subs.elementAt(i);
                result.addSubsort(getImage(superSort), getImage(subSort));
            }
        }

        return result;

    }

    public Term getImage(Signature sig,
                         Term term)
        throws TermException {

        if (this.trans.size() != 0) {
            for (Term left : this.trans.keySet()) {
                Term right = this.trans.get(left);
                Map<VarOrCode, Term> subst = term.getMatch(left, sig);
                if (subst != null) {
                    Hashtable<VarOrCode, Term> newSubst = new Hashtable<>();
                    for (VarOrCode var : subst.keySet()) {
                        Term trm = subst.get(var);
                        trm = getImage(sig, trm);
                        if (this.varMap.containsKey(var))
                            newSubst.put(this.varMap.get(var), trm);
                    }
                    return right.subst(newSubst, this.tmodule);
                }
           }
        }

        if (term.isVariable()) {
            return new Term(getImage(term.var));
        } else {
            Term[] terms = new Term[term.subterms.length];
            for (int i = 0; i < terms.length; i++ ) {
                terms[i] = getImage(sig, term.subterms[i]);
            }

            Operation op = getImage(term.operation);
            return new Term(sig, op, terms);
        }

    }

    public Equation getImage(Signature sig,
                             Equation eq)
        throws TermException {
        if (eq.condition != null) {
            Equation tmp = new Equation(getImage(sig, eq.condition), getImage(sig, eq.left),
                                        getImage(sig, eq.right));
            if (eq.name != null) {
                tmp.name = eq.name;
            }
            tmp.info = eq.info;
            return tmp;

        } else {
            Equation tmp = new Equation(getImage(sig, eq.left), getImage(sig, eq.right));
            if (eq.name != null) {
                tmp.name = eq.name;
            }
            tmp.info = eq.info;
            return tmp;
        }
    }

    public Module getImage(Module module)
        throws SubsortException, TermException, SignatureException {

        Module result = new Module(module.type, module.modName);

        // add sort
        for (int i = 0; i < module.sorts.size(); i++ ) {
            Sort sort = module.sorts.elementAt(i);
            sort = getImage(sort);

            if (!result.containsSort(sort)) {
                result.addSort(sort);
            }
        }

        // add subsorts
        result.subsorts = getImage(module.subsorts);

        // add variables
        for (int i = 0; i < module.vars.size(); i++ ) {
            Variable var = module.vars.elementAt(i);
            var = getImage(var);

            if (!result.containsVariable(var)) {
                result.addVariable(var);
            }
        }

        // add operations
        for (int i = 0; i < module.operations.size(); i++ ) {
            Operation op = module.operations.elementAt(i);

            if (op.isConstant()) {
                try {
                    Term term = new Term(op);
                    boolean done = false;
                    for (Term tmp : this.trans.keySet()) {
                        if (term.equals(tmp)) {
                            done = true;
                            break;
                        }
                    }

                    if (done)
                        continue;
                } catch (Exception e) {
                }
            } else {
                boolean done = false;
                for (Term tmp : this.trans.keySet()) {
                    if (tmp.operation.equals(op)) {
                        done = true;
                    }
                }
                if (done)
                    continue;
            }

            op = getImage(op);

            if (!result.containsOperation(op)) {
                result.addOperation(op);
            }
        }

        // add equation
        for (int i = 0; i < module.equations.size(); i++ ) {
            Equation eq = module.equations.get(i);

            eq = getImage(result, eq);
            if (!result.containsEquation(eq)) {
                result.equations.add(eq);
            }
        }

        // add general equations
        for (int i = 0; i < module.generalEquations.size(); i++ ) {
            Equation eq = module.generalEquations.get(i);
            eq = getImage(result, eq);
            if (!result.generalEquations.contains(eq)) {
                result.generalEquations.add(eq);
            }
        }

        for (String key : module.alias.keySet()) {
            List<Sort> list = module.alias.get(key);
            List<Sort> res = new ArrayList<>();

            for (Sort sort: list) {
                res.add(getImage(sort));
            }

            result.alias.put(key, res);
        }

        return result;

    }

    public View getImage(View view)
        throws TermException, SignatureException, SubsortException, ViewException {

        Module newSource = this.getImage(view.source);
        Module newTarget = this.getImage(view.target);
        View result = new View("", newSource, newTarget);

        for (Sort from : view.sortMap.keySet()) {
            Sort to = view.sortMap.get(from);
            result.addSortMap(getImage(from), getImage(to));
        }

        for (Operation from : view.opMap.keySet()) {
            Operation to = view.opMap.get(from);
            result.addOperationMap(getImage(from), getImage(to));
        }

        for (Term left : view.trans.keySet()) {
            Term right = view.trans.get(left);
            result.addTransformation(getImage(newSource, left), getImage(newTarget, right));
        }

        return result;
    }

    protected View addNotation(String notation,
                               String flag,
                               Map<ModuleName, Integer> env)
        throws ViewException, SignatureException {

        View result;

        if (flag == null) {
            result = new View(this.name, this.source.addAnnotation(notation, env), this.target);
        } else {
            result = new View(this.name, this.source.addAnnotation(notation, env),
                              this.target.addAnnotation(flag, env));
        }

        Variable[] vars = this.smodule.getVariables();
        for (Variable var : vars) {
            result.addVariable(var.addAnnotation(notation, env));
        }

        for (Sort from : this.sortMap.keySet()) {
            Sort to = this.sortMap.get(from);

            from = from.addAnnotation(notation, env);
            if (flag != null) {
                to = to.addAnnotation(flag, env);
            }
            result.addSortMap(from, to);

        }

        for (Operation from : this.opMap.keySet()) {
            Operation to = this.opMap.get(from);

            from = from.addAnnotation(notation, env);
            if (flag != null) {
                to = to.addAnnotation(flag, env);
            }

            try {
                result.addOperationMap(from, to);
            } catch (Exception e) {
            }

        }

        for (Term left : this.trans.keySet()) {
            Term right = this.trans.get(left);
            left = left.addAnnotation(notation, this.smodule, env);
            result.addTransformation(left, right);
        }

        return result;
    }

    protected void record(Module module) {
        this.main = module;
    }

    public View instanceBy(Module[] mods,
                           String[] notations,
                           Map<ModuleName, Integer> env)
        throws ViewException {

        try {

            List<ViewRenamable> list = new ArrayList<>();

            // create new module name
            ModuleName[] modNames = new ModuleName[mods.length];
            for (int i = 0; i < mods.length; i++ ) {
                if (notations[i] != null) {
                    modNames[i] = new ModuleName(notations[i]);
                } else {
                    //modNames[i] = mods[i].getModuleName();
                    View view = (View) mods[i].getProperty("view");
                    modNames[i] = new ModuleName(view.name);
                    modNames[i].view = view;

                }

                list.add(modNames[i]);
            }

            ModuleName modName1 = this.source.modName;
            if (this.source.modName.subexps.size() > 0) {
                modName1 = (ModuleName) this.source.modName.subexps.get(0);
            }
            ModuleName sourceModName = modName1.instance(list);

            ModuleName modName2 = (ModuleName) target.modName.subexps.get(0);
            ModuleName targetModName = modName2.instance(list);

            // check the size of actual parameters
            if (mods.length != this.main.paraModules.size()
                || notations.length != this.main.paraModules.size()) {
                throw new ViewException("expect " + this.main.paraModules.size() + " parameters");
            }

            // create new source and target
            Module newSource = this.source.clone();
            Module newTarget = this.target.clone();

            View[] views = new View[mods.length];
            for (int i = 0; i < mods.length; i++ ) {

                // get parameter and its name
                Module parameter = this.main.paraModules.get(i);
                String paraName = this.main.paraNames.get(i);

                // create an view
                views[i] = (View) mods[i].getProperty("view");

                if (views[i] == null) {
                    views[i] = mods[i].getViewFor(parameter);
                }

                if (views[i] == null) {
                    throw new ViewException(mods[i].getModuleName() + " is not an instance of "
                                            + parameter.getModuleName());
                }

                views[i] = views[i].addNotation(paraName, notations[i], env);
                newSource = views[i].getImage(newSource);
                newTarget = views[i].getImage(newTarget);

                ModuleName tmpName = parameter.modName.addAnnotation(paraName);
                ModuleName newSourceName = newSource.modName.changeModuleName(tmpName, modNames[i]);
                newSource = newSource.changeModuleName(tmpName, modNames[i], newSourceName);

                ModuleName newTargetName = newTarget.modName.changeModuleName(tmpName, modNames[i]);
                newTarget = newTarget.changeModuleName(tmpName, modNames[i], newTargetName);

                if (notations[i] == null) {
                    newSource.importModule(mods[i]);
                    newTarget.importModule(mods[i]);
                }

                // notations[i] is not null, it simply means
                // the actual parameter is a parameter of this module
                // thus, do nothing in this case

            }

            String viewName = this.name + "[";
            for (int i = 0; i < mods.length; i++ ) {
                if (i == 0) {
                    viewName += ((View) mods[i].getProperty("view")).name;
                } else {
                    viewName += ", " + ((View) mods[i].getProperty("view")).name;
                }
            }
            viewName += "]";

            View result = new View(viewName, newSource, newTarget);

            // handle sort mapping
            for (Sort from : this.sortMap.keySet()) {
                Sort to = this.sortMap.get(from);

                // change module names
                for (int i = 0; i < mods.length; i++ ) {

                    // get parameter and its name
                    Module parameter = this.main.paraModules.get(i);
                    String paraName = this.main.paraNames.get(i);

                    ModuleName tmpName = parameter.modName.addAnnotation(paraName);

                    from = views[i].getImage(from);
                    from = from.changeModuleName(tmpName, modNames[i]);

                    to = views[i].getImage(to);
                    to = to.changeModuleName(tmpName, modNames[i]);

                }

                result.addSortMap(from, to);
            }

            for (Operation from : this.opMap.keySet()) {
                Operation to = this.opMap.get(from);

                for (int i = 0; i < mods.length; i++ ) {

                    // get parameter and its name
                    Module parameter = this.main.paraModules.get(i);
                    String paraName = this.main.paraNames.get(i);

                    ModuleName tmpName = parameter.modName.addAnnotation(paraName);
                    from = views[i].getImage(from);
                    from = from.changeModuleName(tmpName, modNames[i]);

                    to = views[i].getImage(to);
                    to = to.changeModuleName(tmpName, modNames[i]);

                }
                result.addOperationMap(from, to);
            }

            for (Term from : this.trans.keySet()) {
                Term to = this.trans.get(from);

                for (int i = 0; i < views.length; i++ ) {

                    // get parameter and its name
                    Module parameter = this.main.paraModules.get(i);
                    String paraName = this.main.paraNames.get(i);

                    ModuleName tmpName = parameter.modName.addAnnotation(paraName);
                    from = views[i].getImage(newSource, from);
                    from = from.changeModuleName(tmpName, modNames[i], newSource);

                    to = views[i].getImage(newTarget, to);
                    to = to.changeModuleName(tmpName, modNames[i], newTarget);

                }

                result.addTransformation(from, to);

            }
            return result;

        } catch (Exception e) {
            //e.printStackTrace();
            throw new ViewException(e.getMessage());
        }

    }

    public View aliasModuleName(String alias) throws SignatureException, ViewException {
        ModuleName modName = new ModuleName(alias);
        modName.subexps.add(this.source.modName);
        Module newSource = this.source.changeModuleName(this.source.modName, modName, modName);
        Module newTarget = this.target.changeModuleName(this.target.modName, modName, modName);

        View result = new View("", newSource, newTarget);

        for (Sort from : this.sortMap.keySet()) {
            Sort to = this.sortMap.get(from);

            from = from.changeModuleName(this.source.modName, modName);
            to = to.changeModuleName(this.target.modName, modName);

            result.addSortMap(from, to);

        }

        for (Operation from : this.opMap.keySet()) {
            Operation to = this.opMap.get(from);
            Operation from1 = from.changeModuleName(this.source.modName, modName);
            to = to.changeModuleName(this.target.modName, modName);
            result.addOperationMap(from1, to);
        }

        for (Term left : this.trans.keySet()) {
            Term right = this.trans.get(left);
            Term left1 = left.changeModuleName(this.source.modName, modName, newSource);
            right = right.changeModuleName(this.target.modName, modName, newTarget);
            result.addTransformation(left1, right);
        }

        return result;

    }

    public View sum(View view) throws ViewException, SignatureException {
        Module resSource = this.source.sum(view.source);
        Module resTarget = this.target.sum(view.target);

        View result = new View("", resSource, resTarget);

        // copy all in this to resView

        for (Sort from : this.sortMap.keySet()) {
            Sort to = this.sortMap.get(from);
            result.addSortMap(from, to);
        }

        for (Operation from : this.opMap.keySet()) {
            Operation to = this.opMap.get(from);
            result.addOperationMap(from, to);
        }

        for (Term left : this.trans.keySet()) {
            Term right = this.trans.get(left);
            result.addTransformation(left, right);
        }

        for (Sort from : view.sortMap.keySet()) {
            Sort to = view.sortMap.get(from);

            Sort tmp = this.sortMap.get(from);
            if (tmp != null && !tmp.equals(to)) {
                throw new ViewException("inconsistent sort mapping for " + from.getName());
            }

            result.addSortMap(from, to);
        }
        for (Operation from : view.opMap.keySet()) {
            Operation to = view.opMap.get(from);

            Operation tmp = this.opMap.get(from);
            if (tmp != null && !tmp.equals(to)) {
                throw new ViewException("inconsistent operator mapping for " + from.getName());
            }

            result.addOperationMap(from, to);
        }

        for (Term left : view.trans.keySet()) {
            Term right = view.trans.get(left);

            Term tmp = this.trans.get(left);
            if (tmp != null && !tmp.equals(right)) {
                throw new ViewException("inconsistent mapping for " + left);
            }

            result.addTransformation(left, right);
        }

        return result;
    }

    public View rename(Map<ViewRenamable, ViewRenamable> map)
        throws SignatureException, ViewException {
        Module resSource = this.source.clone();
        Module resTarget = this.target.clone();

        RenamingMap map1 = new RenamingMap();
        RenamingMap map2 = new RenamingMap();
        RenamingMap record = new RenamingMap();

        for (ViewRenamable obj : map.keySet()) {
            if (obj instanceof Sort) {

                // do something on resSource
                Sort from = (Sort) obj;
                Sort to = (Sort) map.get(from);
                resSource = resSource.changeSort(resSource.modName, from, to);
                map1.put(from, to);
                Sort sort = to;

                // do something on resTarget
                from = this.getTarget(from);
                to = new Sort(to.getName(), from.getModuleName());
                resTarget = resTarget.changeSort(resTarget.modName, from, to);
                map2.put(from, to);

                record.put(sort, to);

            } else {
                // do something on resSource
                Operation from = (Operation) obj;
                Operation to = (Operation) map.get(from);
                resSource = resSource.replaceOperation(resSource.modName, from, to);
                map1.put(from, to);
                Operation op = to;

                // do something on resTarget
                from = this.getTarget(from);
                to = new Operation(to.getName(), from.getArgumentSorts(), from.getResultSort(),
                                   from.modName);

                resTarget = resTarget.replaceOperation(resTarget.modName, from, to);
                map2.put(from, to);
                record.put(op, to);
            }

        }

        ModuleName name1 = resSource.modName.renaming(map1);
        ModuleName name2 = resTarget.modName.renaming(map2);

        resSource = resSource.changeModuleName(resSource.modName, name1, name1);

        resTarget = resTarget.changeModuleName(resTarget.modName, name2, name2);

        View result = new View("", resSource, resTarget);

        Iterator<ViewRenamable> itor = record.keySet()
                                             .iterator();
        while (itor.hasNext()) {
            ViewRenamable obj = itor.next();
            if (obj instanceof Sort) {
                Sort from = (Sort) obj;
                Sort to = (Sort) record.get(from);
                from = from.changeModuleName(this.source.modName, name1);
                to = to.changeModuleName(this.target.modName, name2);
                result.sortMap.put(from, to);
            } else {
                Operation from = (Operation) obj;
                Operation to = (Operation) record.get(from);
                from = from.changeModuleName(this.source.modName, name1);
                to = to.changeModuleName(this.target.modName, name2);
                result.opMap.put(from, to);
            }

        }

        for (Sort from : this.sortMap.keySet()) {
            Sort to = this.sortMap.get(from);


            if (!map.containsKey(from)) {
                from = from.changeModuleName(this.source.modName, name1);
                to = to.changeModuleName(this.target.modName, name2);
                result.addSortMap(from, to);
            }

        }

        for (Operation from : this.opMap.keySet()) {
            Operation to = this.opMap.get(from);

            if (!map.containsKey(from)){

                for (Object tmp : map1.keySet()) {
                    if (tmp instanceof Sort) {
                        Sort sort = (Sort) tmp;
                        Sort dest = (Sort) map1.get(sort);
                        from = from.changeSort(sort, dest);
                    } else {
                        Operation op = (Operation) tmp;
                        Operation dest = (Operation) map1.get(op);
                        from = dest;
                    }
                }

                for (Object tmp : map2.keySet()) {
                    if (tmp instanceof Sort) {
                        Sort sort = (Sort) tmp;
                        Sort dest = (Sort) map2.get(sort);
                        to = to.changeSort(sort, dest);
                    } else {
                        Operation op = (Operation) tmp;
                        Operation dest = (Operation) map2.get(op);
                        to = dest;
                    }
                }

                from = from.changeModuleName(this.source.modName, name1);
                to = to.changeModuleName(this.target.modName, name2);
                result.addOperationMap(from, to);

            }
        }

        for (Term left : this.trans.keySet()) {
             Term right =this.trans.get(left);
            // following commmented-out in in original
            //result.addTransformation(left, right);

        }

        return result;

    }

    public View composite(View view) throws ViewException, TermException {
        if (this.target.modName.equals(view.source.modName)) {

            String resName;

            if (this.name != null && !this.name.equals("")) {

                if (this.isIdentity()) {

                    resName = view.name;

                } else if (this.name.equals(this.target.modName.toString())
                           && this.target.modName.op == ModuleName.ANNOTATE
                           && this.source.modName.equals(this.target.modName.subexps.get(0))) {
                               if (view.name != null && !view.name.equals("")) {
                                   resName = view.name;
                               } else {
                                   resName = view.target.modName.toString();
                               }
                           } else
                    if (view.name != null && !view.name.equals("")) {
                        resName = this.name + " * " + view.name;
                    } else {
                        resName = this.name;
                    }

            } else if (view.name != null && !view.name.equals("")) {
                resName = view.name;
            } else {
                resName = view.target.modName.toString();
            }

            View result = new View(resName, this.source, view.target);

            for (Sort from : this.sortMap.keySet()) {
                Sort to = this.sortMap.get(from);
                result.addSortMap(from, view.getTarget(to));
            }

            for (Operation from : this.opMap.keySet()) {
                Operation to = this.opMap.get(from);
                Operation newTo = view.getTarget(to);
                if (newTo == null) {

//		    /*
//		    Iterator it = view.trans.keySet().iterator();
//		    Term left=null, right=null;
//		    while (it.hasNext()) {
//			Term left = (Term)itor.next();
//			Term right = (Term)view.trans.get(left);
//			if (left.operation.equals(newTo)) {
//			    break;
//			}
//		    }
//		    */

                    Term fromTerm = null, toTerm = null;
                    if (from.isConstant()) {
                        fromTerm = new Term(from);
                        toTerm = new Term(to);
                    }

                    toTerm = view.getImage(result.smodule, toTerm);
                    result.addTransformation(fromTerm, toTerm);

                } else {
                    result.addOperationMap(from, newTo);
                }

            }

            for (Term left : this.trans.keySet()) {
                Term right = this.trans.get(left);
                result.addTransformation(left, view.getImage(result.smodule, right));
            }

            return result;

        } else {
            throw new ViewException("can not make composition of the views: " + this.target.modName
                                    + " with " + view.source.modName);
        }

    }

    public boolean isIdentity() {

        if (this.name.equals(this.target.modName.toString())) {

            ModuleName mn1 = this.source.modName;
            ModuleName mn2 = this.target.modName;
            if (this.source.modName.op == ModuleName.ANNOTATE) {
                mn1 = (ModuleName) this.source.modName.subexps.get(0);
            }

            if (this.target.modName.op == ModuleName.ANNOTATE) {
                mn2 = (ModuleName) this.target.modName.subexps.get(0);
            }

            if (mn1.equals(mn2)) {
                return true;
            } else {
                return false;
            }

        } else {
            return false;
        }

    }


//    /*
//    public View changeNotation(String from, String to) {
//        
//        Module nsrc = source.changeParameterName(from, to);
//	Module ntgt = target.changeParameterName(from, to);
//        
//        String nname = name;
//	if (name.equals(target.modName().toString())) {
//	    nname = target.modName().toString();
//	}
//
//	View result = new View(nname, nsrc, ntgt);
//	result.nmain = main.changeParameterName(from, to);
//        result.morphism = morphism;
//        result.smodule = smodule.changeParameterName(from, to);
//	result.tmodule = tmodule.changeParameterName(from, to);
//	result.allowSortDef = allowSortDef;
//
//    Map sortMap, opMap, varMap, trans;
//    ArrayList views = new ArrayList();
//    HashMap record = new HashMap();
//  
//    }
//    */

}
