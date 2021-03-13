package bobj;

import java.io.IOException;
import java.io.Serializable;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.Vector;

public class Module
                    extends
                    Signature
                    implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    final public static int INITIAL = 0;

    final public static int LOOSE = 1;

    final public static int BEHAVORIAL = 2;

    ModuleName modName;             // the module name

    List<Module> paraModules;          // map : names to modules

    List<String> paraNames;            // parameter names

    List<ModuleName> protectImportList;

    List<ModuleName> extendImportList;

    List<ModuleName> useImportList;

    Map<ModuleName, Module> bindings;

    int[] levels;

    List<Equation> mask;

    List<Equation> equations;                  // save equations

    List<Equation> generalEquations;           // save ignored equations

    int type;                        // INITIAL, LOOSE or BEHAVORIAL

    Map<String, Object> props;                   // properties

    RewriteEngine engine;

    static Writer writer;

    /**
     *
     * create a new module with specified module name
     *
     */
    public Module(int type,
                  ModuleName modName) {

        if (type > 2 || type < 0) {
            type = 1;
        }
        this.type = type;
        this.modName = modName;
        this.paraModules = new ArrayList<>();
        this.paraNames = new ArrayList<>();
        this.protectImportList = new ArrayList<>();
        this.extendImportList = new ArrayList<>();
        this.useImportList = new ArrayList<>();
        this.equations = new ArrayList<>();
        this.generalEquations = new ArrayList<>();
        this.props = new HashMap<>();
        this.mask = new ArrayList<>();
        addTokens(modName);
    }

    /**
     *
     * return the module name of this module
     *
     */
    public ModuleName getModuleName() {
        return modName;
    }

    public int getType() {
        return type;
    }

    public boolean isBehavorial() {
        return type == BEHAVORIAL;
    }

    public boolean isInitial() {
        return type == INITIAL;
    }

    public boolean isLoose() {
        return type == LOOSE;
    }

    public boolean isParameterized() {
        return paraNames.size() != 0;
    }

    public boolean isSecondOrder() {
        if (isParameterized()) {
            for (Module paraModule : paraModules) {
                Module parameter = paraModule;
                if (parameter.isParameterized()) {
                    return true;
                }
            }
        }
        return false;
    }

    public Module[] getParameters() {
        return (Module[]) (paraModules.toArray());
    }

    public Module getParameter(String name) throws ModuleParameterException {
        int i = paraNames.indexOf(name);
        if (i != -1) {
            return(paraModules.get(i));
        }
        throw new ModuleParameterException("No parameter for " + name);
    }

    public Module getParameterAt(int index) throws ModuleParameterException {

        if (index > -1 && index < paraModules.size()) {
            return(paraModules.get(index));
        }
        try {

            throw new ModuleParameterException("module " + modName + " has no " + (index + 1)
                                               + "-th parameter");
        } catch (Exception e) {
            //e.printStackTrace();
            throw new ModuleParameterException("module " + modName + " has no " + (index + 1)
                                               + "-th parameter");
        }

    }

    public String getParameterNameAt(int index) throws ModuleParameterException {

        if (index > -1 && index < paraNames.size()) {
            return(paraNames.get(index));
        }
        throw new ModuleParameterException("module " + modName + " has no " + (index + 1)
                                           + "-th parameter");
    }

    public String[] getParameterNames() {
        String[] result = new String[paraNames.size()];
        for (int i = 0; i < result.length; i++ ) {
            result[i] = paraNames.get(i);
        }
        return result;
    }

    public String[] getSecondOrderParameterNames() {
        ArrayList<String> list = new ArrayList<>();
        for (int i = 0; i < paraModules.size(); i++ ) {
            Module parameter = paraModules.get(i);
            if (parameter.isParameterized()) {
                list.add(paraNames.get(i));
            }
        }

        String[] result = new String[list.size()];
        for (int i = 0; i < result.length; i++ ) {
            result[i] = list.get(i);
        }
        return result;
    }

    public void addParameter(String name,
                             Module module,
                             Map<ModuleName, Integer> env)
        throws ModuleParameterException, SignatureException {

        validateParameterName(name);
        paraNames.add(name);
        paraModules.add(module);

        if (!module.isParameterized()) {
            Module mod = module.addAnnotation(name, env);
            importModule(mod);
        }

        parameters = sorts.size();

    }

    public boolean hasParameter(String name) {
        return paraNames.contains(name);
    }

    private void validateParameterName(String name) throws ModuleParameterException {
        if (paraNames.contains(name)) {
            throw new ModuleParameterException("repeated module name " + name);
        }

        ModuleName testName = new ModuleName(name);
        if (modName.equals(testName)) {
            throw new ModuleParameterException("parameter name can't be same "
                                               + "as the module name");
        }
        /* reserve probably bad lookupin case */
        if (protectImportList.contains(testName) || extendImportList.contains(testName)
            || useImportList.contains(testName)) {
            throw new ModuleParameterException("name " + name + " is used in "
                                               + "this module already");
        }

    }

    public boolean containsEquation(Equation eq) {
        return equations.contains(eq);
    }

    public void addEquation(Equation eq) {

        completeEquation(eq);

        if (!containsEquation(eq)) {
            equations.add(eq);
        } else {

            int i = equations.indexOf(eq);
            Equation equat = equations.get(i);

            if (!equat.equals(eq)) {
                equations.add(eq);
            } else {
                equat.equals(eq);
            }
        }

    }

    public void addGeneralEquation(Equation eq) {

        if (!generalEquations.contains(eq)) {
            generalEquations.add(eq);
        }

    }

    public void add(Operation op) throws SignatureException {

        addOperation(op);

        if (op.isIdempotent()) {
            addIdempotence(op);
        }

        if (op.id != null) {
            addIdentity(op, op.id);
        }

    }

    private void addIdentity(Operation op,
                             Operation id) {

        try {
            Sort sort = op.getResultSort();
            Variable var = new Variable("..." + sort.getName()
                                                    .toUpperCase(),
                                        sort);
            Term l1 = new Term(this, op, new Term(this, id), new Term(var));
            Term r1 = new Term(var);
            Equation eq1 = new Equation(l1, r1);
            eq1.info = "system-introduced";
            equations.add(eq1);

            Term l2 = new Term(this, op, new Term(var), new Term(this, id));
            Term r2 = new Term(var);
            Equation eq2 = new Equation(l2, r2);
            eq2.info = "system-introduced";
            equations.add(eq2);
        } catch (Exception e) {
        }
    }

    private void addIdempotence(Operation op) {
        try {
            Sort sort = op.getResultSort();
            Variable var = new Variable("..." + sort.getName()
                                                    .toUpperCase(),
                                        sort);
            Term r = new Term(var);
            Term l = new Term(this, op, r, r);
            Equation eq = new Equation(l, r);
            eq.info = "system-default";
            equations.add(eq);
        } catch (Exception e) {
        }
    }

    public boolean isBuiltIn() {

        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            if (!sort.getInfo()
                     .equals("system-default")) {
                return false;
            }
        }

        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            if (!op.info.equals("system-default")) {
                return false;
            }
        }

        for (Equation equation : equations) {
            if (!equation.info.equals("system-default")) {
                return false;
            }
        }

        for (Equation eq : generalEquations) {
            if (!eq.info.equals("system-default")) {
                return false;
            }
        }

        if (modName.op != ModuleName.ATOM) {
            return false;
        }

        if (!modName.atom.equals("TRUTH-VALUE") && !modName.atom.equals("TRUTH")
            && !modName.atom.equals("IDENTICAL") && !modName.atom.equals("BOOL")
            && !modName.atom.equals("QID") && !modName.atom.equals("NZNAT")
            && !modName.atom.equals("NAT") && !modName.atom.equals("INT")
            && !modName.atom.equals("FLOAT")) {

            return false;
        }
        return true;
    }

    /**
     * this method returns a string presentation of this module. in which the builtins are usually
     * not included, except this module is a built-in module
     */
    @Override
    public String toString() {

        if (isBuiltIn()) {
            return builtInToString();
        }

        String result = "";

        switch (type) {
            case INITIAL:
                result += "dth ";
            break;
            case LOOSE:
                result += "th ";
            break;
            case BEHAVORIAL:
                result += "dth ";
            break;
            default:
        }

        result += modName;

        if (levels != null) {
            int l = 0;
            result += " [ ";
            for (int i = 0; i < paraNames.size(); i++ ) {

                if (i == levels[l]) {
                    result += " ]";
                    l++ ;

                    if (l < levels.length) {
                        result += " [ ";
                    }

                }

                String pname = paraNames.get(i);
                Module pmod = paraModules.get(i);

                if (l == 0) {
                    if (i != 0) {
                        result += ", " + pname + " :: " + pmod.modName;
                    } else {
                        result += pname + " :: " + pmod.modName;
                    }
                } else if (i != levels[l - 1]) {
                    result += ", " + pname + " :: " + pmod.modName;
                } else {
                    result += pname + " :: " + pmod.modName;
                }

            }

            result += " ]";
        }

        result += " is \n";

        if (!protectImportList.isEmpty()) {
            result += "   protecting";
            for (ModuleName element : protectImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        if (!extendImportList.isEmpty()) {
            result += "   extending";
            for (ModuleName element : extendImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        if (!useImportList.isEmpty()) {
            result += "   including";
            for (ModuleName element : useImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        // handle sorts
        String s = "";
        int count = 0;
        for (Sort tmp : sorts) {
            if (tmp.getInfo()
                   .equals("system-default")) {
                continue;
            }
            s += toString(tmp) + " ";
            count++ ;
        }
        if (count == 1) {
            result += "   sort " + s + " .\n";
        } else if (count > 1) {
            result += "   sorts " + s + " .\n";
        }

        // handle subsorts
        String stmp = toStringWithoutBuiltIn(subsorts);
        StringTokenizer st = new StringTokenizer(stmp, "\n");
        while (st.hasMoreTokens()) {
            result += "   " + st.nextToken()
                                .trim()
                      + "\n";
        }

        // handle variables
        for (Sort tmp : sorts) {
            if (tmp.getInfo()
                   .equals("system-default")) {
                continue;
            }
            Variable[] vars = getVariablesOnSort(tmp);
            if (vars.length == 1) {
                result += "   var ";
            } else if (vars.length > 1) {
                result += "   vars ";
            }

            for (Variable var : vars) {
                result += var.name + " ";
            }

            if (vars.length > 0) {
                result += ": " + toString(tmp) + " .\n";
            }
        }

        // handle constants
        Operation[] cs = getConstants();
        Map<Operation, List<Operation>> map = sort(cs);
        for (Operation c : map.keySet()) {
            List<Operation> list = map.get(c);

            if (list.size() == 1) {
                result += "   op ";
            } else {
                result += "   ops ";
            }

            for (Operation op : list) {
                if (op.name.indexOf(" ") != -1) {
                    result += "(" + op.name + ") ";
                } else {
                    result += op.name + " ";
                }
            }

            String tmp = toString(c);
            result += tmp.substring(4 + c.name.length()) + ".\n";

        }

        // handle non-constants
        for (Operation tmp : operations) {
            if (tmp.info.equals("system-default") || tmp.isConstant()) {
                continue;
            }
            result += "   " + toString(tmp) + ".\n";
        }

        // handle equations
        for (Equation tmp : equations) {
            if (tmp.info.equals("system-default") || tmp.info.equals("system-introduced")) {
                continue;
            }
            result += "   " + tmp + " .\n";
        }

        for (Equation tmp : generalEquations) {
            if (tmp.info.equals("system-default") || tmp.info.equals("system-introduced")) {
                continue;
            }
            result += "   general " + tmp + " .\n";
        }

        result += "end\n";

        return result;
    }

    private Map<Operation, List<Operation>> sort(Operation[] cs) {
        Map<Operation, List<Operation>> map = new HashMap<>();
        for (Operation element : cs) {
            if (element.info.equals("system-default")) {
                continue;
            }
            boolean done = false;
            for (Operation key : map.keySet()) {

                if (element.priority == key.priority && element.resultSort.equals(key.resultSort)) {

                    List<Operation> list = map.get(key);
                    list.add(element);
                    done = true;
                    break;
                }

            }

            if (!done) {
                List<Operation> list = new ArrayList<>();
                list.add(element);
                map.put(element, list);
            }

        }

        return map;
    }

    public String allToString() {

        String result = "";

        switch (type) {
            case INITIAL:
                result += "dth ";
            break;
            case LOOSE:
                result += "th ";
            break;
            case BEHAVORIAL:
                result += "dth ";
            break;
            default:
        }

        result += modName;
        result += " is \n";

        for (Sort tmp : sorts) {
            result += "   sort " + toString(tmp) + "  " + tmp.getModuleName() + " .\n";
        }

        String stmp = toString(subsorts);
        StringTokenizer st = new StringTokenizer(stmp, "\n");
        while (st.hasMoreTokens()) {
            result += "   " + st.nextToken()
                                .trim()
                      + "\n";
        }

        for (Variable tmp : vars) {
            result += "   " + toString(tmp) + " .\n";
        }

        for (Operation tmp : operations) {
            //result += "   "+toString(tmp)+".\n";
            result += "   " + tmp + "   " + tmp.modName + ".\n";
        }

        for (Equation tmp : equations) {
            if (tmp.right.operation == null) {
                result += "   " + tmp + "     " + tmp.left.operation.modName + " .\n";
            } else {
                result += "   " + tmp + "     " + tmp.left.operation.modName + "    "
                          + tmp.right.operation.modName + "    " + " .\n";
            }

            if (tmp.left.toString()
                        .equals("base")) {
                System.out.println(tmp.right.showStructure());
            }

        }

        for (Equation tmp : generalEquations) {
            result += "  general " + tmp + " .\n";
        }

        result += "end\n";

        return result;
    }

    private String builtInToString() {
        String result = "";

        if (modName.atom.equals("TRUTH-VALUE")) {
            result += "dth TRUTH-VALUE is\n";
            result += "   sort Bool .\n";
            result += "   op true : -> Bool  .\n";
            result += "   op false : -> Bool .\n";
            result += "end\n";

        } else if (modName.atom.equals("TRUTH")) {

            result += "dth TRUTH is\n";
            result += "   protecting TRUTH-VALUE .\n";
            result += "   sort Universal .\n";
            result += "   subsorts Bool < Universal\n";
            result += "   vars X Y : Universal .\n";
            result += "   var B : Bool .\n";
            result += "   ops true false : -> Bool .\n";
            result += "   op _ == _ : Universal Universal -> Bool .\n";
            result += "   op _ =/= _ : Universal Universal -> Bool .\n";
            result += "   op if _ then _ else _ fi : Bool Universal Universal -> Universal .\n";
            result += "   eq X == X = true .\n";
            result += "   eq if true then X else Y fi = X .\n";
            result += "   eq if false then X else Y fi = Y .\n";
            result += "   eq if B then X else X fi = X .\n";
            result += "end\n";

        } else if (modName.atom.equals("IDENTICAL")) {

            result += "th IDENTICAL is\n";
            result += "   protecting TRUTH .\n";
            result += "   op _===_ : Universal Universal -> Bool . \n";
            result += "   op _=/==_ : Universal Universal -> Bool . \n";
            result += "end\n";

        } else if (modName.atom.equals("BOOL")) {

            result += "dth BOOL is\n";
            result += "   protecting TRUTH .\n";
            result += "   op _ and _ : Bool Bool -> Bool [assoc comm prec 20] .\n";
            result += "   op _ or _ : Bool Bool -> Bool [assoc comm prec 30] .\n";
            result += "   op _ xor _ : Bool Bool -> Bool [assoc comm ] .\n";
            result += "   op _ implies _ : Bool Bool -> Bool  .\n";
            result += "   op not _ : Bool -> Bool [prec 10] .\n";
            result += "   eq not true = false .\n";
            result += "   eq not false = true .\n";
            result += "   eq true and B = B .\n";
            result += "   eq false and B = false .\n";
            result += "   eq true or B = true .\n";
            result += "   eq false or B = B .\n";
            result += "   eq B1 implies B2 = (not B1) or B2 .\n";
            result += "end\n";

        } else if (modName.atom.equals("QID")) {

            result += "dth QID is\n";
            result += "   protecting BOOL .\n";
            result += "   sort Id .\n";
            result += "end\n";

        } else if (modName.atom.equals("NZNAT")) {

        } else if (modName.atom.equals("NAT")) {

            result += "dth NAT is\n";
            result += "   protecting BOOL .\n";
            result += "   sorts Nat Zero NzNat .\n";
            result += "   subsorts NzNat Zero < Nat\n";
            result += "   vars N M : Nat .\n";
            result += "   op _ + _ : NzNat NzNat -> NzNat [assoc comm ] .\n";
            result += "   op s _ : NzNat -> NzNat [prec 15] .\n";
            result += "   op 0 : -> Zero [prec 0] .\n";
            result += "   op s _ : Nat -> NzNat [prec 15] .\n";
            result += "   op p _ : NzNat -> Nat [prec 15] .\n";
            result += "   op _ > _ : Nat Nat -> Bool [prec 41] .\n";
            result += "   op _ < _ : Nat Nat -> Bool [prec 41] .\n";
            result += "   op _ <= _ : Nat Nat -> Bool [prec 41] .\n";
            result += "   op _ >= _ : Nat Nat -> Bool [prec 41] .\n";
            result += "   op _ + _ : Nat Nat -> Nat [assoc comm ] .\n";
            result += "   op _ * _ : Nat Nat -> Nat [assoc comm prec 30] .\n";
            result += "   op _ div _ : Nat Nat -> Bool [prec 30] .\n";
            result += "   op eq : Nat Nat -> Bool [prec 0] .\n";
            result += "   eq 0 > N = false .\n";
            result += "   eq (s N) > 0 = true .\n";
            result += "   eq (s N) > (s M) = N > M .\n";
            result += "   eq eq(N , N) = true .\n";
            result += "   eq eq(0 , s N) = false .\n";
            result += "   eq eq(s N , 0) = false .\n";
            result += "   eq eq(s N , s M) = eq(N , M) .\n";
            result += "   cq eq(N , M) = false if (N < M) or (M < N) .\n";
            result += "   eq M < 0 = false .\n";
            result += "   eq 0 < (s N) = true .\n";
            result += "   eq (s N) < (s M) = N < M .\n";
            result += "   eq (s M) <= N = M < N .\n";
            result += "   eq N <= M = eq(N , M) or (N < M) .\n";
            result += "   eq (s M) > 0 = true .\n";
            result += "   eq N >= 0 = true .\n";
            result += "   eq (s N) >= (s M) = N >= M .\n";
            result += "   eq 0 >= (s N) = false .\n";
            result += "   eq N >= N = true .\n";
            result += "end\n";

        } else if (modName.atom.equals("INT")) {

            result += "dth INT is\n";
            result += "   protecting NAT .\n";
            result += "   sort Int NzInt Nat Zero NzNat .\n";
            result += "   subsorts Nat NzNat Zero NzInt < Int\n";
            result += "   subsorts NzNat Zero < Nat\n";
            result += "   subsorts NzNat < NzInt\n";
            result += "   vars I J K : Int .\n";
            result += "   op - _ : Int -> Int [prec 20] .\n";
            result += "   op s _ : Int -> Int [prec 15] .\n";
            result += "   op p _ : Int -> Int [prec 20] .\n";
            result += "   op - _ : NzInt -> NzInt [prec 20] .\n";
            result += "   op _ + _ : Int Int -> Int [assoc comm prec 40] .\n";
            result += "   op _ - _ : Int Int -> Int [assoc prec 20] .\n";
            result += "   op _ * _ : Int Int -> Int [assoc prec 30] .\n";
            result += "   op _ < _ : Int Int -> Bool .\n";
            result += "   op _ <= _ : Int Int -> Bool .\n";
            result += "   op _ > _ : Int Int -> Bool .\n";
            result += "   op _ >= _ : Int Int -> Bool .\n";
            result += "   op _ quo _ : Int Int -> Int .\n";
            result += "   op _ rem _ : Int Int -> Int .\n";
            result += "   op _ divides _ : Int Int -> Int .\n";
            result += "   eq s (p I) = I .\n";
            result += "   eq p (s I) = I .\n";
            result += "   eq I + 0 = I .\n";
            result += "   eq I + (s J) = s (I + J) .\n";
            result += "   eq I + (p J) = p (I + J) .\n";
            result += "   eq I * 0 = 0 .\n";
            result += "   eq I * (s J) = (I * J) + I .\n";
            result += "   eq I * (p J) = (I * J) - I .\n";
            result += "   eq I * (J + K) = (I * J) + (I * K) .\n";
            result += "   eq - (- I) = I .\n";
            result += "   eq - (s I) = p (- I) .\n";
            result += "   eq - (p I) = s (- I) .\n";
            result += "   eq I - J = I + (- J) .\n";
            result += "   eq I + (- I) = 0 .\n";
            result += "   eq - (I + J) = (- I) - J .\n";
            result += "   eq I * (- J) = - (I * J) .\n";
            result += "end\n";

        } else if (modName.atom.equals("FLOAT")) {

            result += "dth FLOAT is \n";
            result += "   sort Float .\n";
            result += "   op not _ : Bool -> Bool  [ prec 10 ]  .\n";
            result += "   op _ + _ : Float Float -> Float " + " [ assoc comm prec 40 ]  .\n";
            result += "   op _ - _ : Float Float -> Float " + " [ assoc prec 40 ]  .\n";
            result += "   op _ * _ : Float Float -> Float " + " [ assoc prec 30 ]  .\n";
            result += "   op _ / _ : Float Float -> Float  " + "[ assoc prec 30 ]  .\n";
            result += "   op _ < _ : Float Float -> Bool .\n";
            result += "   op _ <= _ : Float Float -> Bool .\n";
            result += "   op _ > _ : Float Float -> Bool .\n";
            result += "   op _ >= _ : Float Float -> Bool .\n";
            result += "   op exp : Float -> Float .\n";
            result += "   op log : Float -> Float .\n";
            result += "   op sqrt : Float -> Float .\n";
            result += "   op abs : Float -> Float .\n";
            result += "   op sin : Float -> Float .\n";
            result += "   op cos : Float -> Float .\n";
            result += "   op atan : Float -> Float .\n";
            result += "   op pi : -> Float .\n";
            result += "   op - _ : Float -> Float  [ prec 20 ]  .\n";
            result += "end\n";

        } else {
            System.out.println("BOBJ system error");
            System.exit(0);
        }

        return result;
    }

    protected String toString(Sort sort) {
        if (this.hasUniqueNameFor(sort)) {
            return sort.getName();
        } else {
            return sort.getName() + "." + sort.getModuleName();
        }
    }

    protected String toString(Variable var) {
        return "var " + var.name + " : " + toString(var.sort);
    }

    protected String toString(Operation op) {

        String result = "op ";

        result += op.name + " :";

        for (Sort tmp : op.argumentSorts) {
            result += " " + toString(tmp);
        }

        result += " -> " + toString(op.resultSort) + " ";

        result += "[";

        if (op.isAssociative)
            result += "assoc ";
        if (op.isCommutative)
            result += "comm ";
        if (op.isIdempotent)
            result += "idem ";
        if (op.id != null)
            result += "idr: " + op.id.name + " ";
        if (!op.behavorial)
            result += "ncong ";

        if (op.priority != Integer.MAX_VALUE && op.priority != 0) {
            result += "prec " + op.priority + " ";
        }

        if (op.gather != null) {
            result += "gather(";
            for (int i = 0; i < op.gather.length; i++ ) {
                if (i != 0) {
                    result += ", ";
                }
                result += op.gather[i];
            }
            result += ") ";
        }

        if (op.strategy != null) {
            result += "strat (";
            for (int i = 0; i < op.strategy.length; i++ ) {
                if (i != 0) {
                    result += ", ";
                }
                result += op.strategy[i];
            }
            result += ") ";
        }

        if (result.endsWith("[")) {
            result = result.substring(0, result.length() - 1);
        } else {
            result = result.substring(0, result.length() - 1) + "] ";
        }

        //result += op.modName;

        return result;

    }

    private String toStringWithoutBuiltIn(Subsort sub) {

        String result = "";
        for (Sort parent : sub.subsorts.keySet()) {
            Vector<Sort> v = sub.subsorts.get(parent);
            if (!parent.getInfo()
                       .equals("system-default")) {
                ArrayList<Sort> list = new ArrayList<>();
                for (int i = 0; i < v.size(); i++ ) {
                    Sort s1 = v.elementAt(i);
                    if (s1.getInfo()
                          .equals("system-default")
                        || (s1.getName()
                              .equals("Elt")
                            && s1.getModuleName()
                                 .toString()
                                 .indexOf("TRIV") != -1)) {
                        boolean done = false;
                        for (int j = 0; j < list.size(); j++ ) {
                            Sort s2 = list.get(j);
                            if (sub.isSubsort(s2, s1)) {
                                // ignore s1
                                done = true;
                                break;
                            } else if (sub.isSubsort(s1, s2)) {
                                // delete s2 from list, add s1
                                list.remove(j);
                                list.add(s1);
                                done = true;
                                break;
                            }
                        }

                        if (!done) {
                            list.add(s1);
                        }
                    } else {
                        list.add(s1);
                    }
                }

                if (list.size() != 0) {
                    result += "  subsorts ";
                    for (Sort kid : list) {
                        result += toString(kid) + " ";
                    }
                    result += "< " + toString(parent) + " .\n";
                }

            } else if (!parent.getName()
                              .equals("Universal")) {
                                  String tmp = "";
                                  if (v != null && v.size() != 0) {
                                      for (int i = 0; i < v.size(); i++ ) {
                                          Sort kid = v.elementAt(i);
                                          if (!kid.getInfo()
                                                  .equals("system-default")) {
                                              tmp += toString(kid) + " ";
                                          }
                                      }
                                  }

                                  if (tmp.length() > 0) {
                                      result +=
                                          "subsorts " + tmp + " < " + toString(parent) + " .\n";
                                  }
                              }
        }

        return result;

    }

    private String toString(Subsort sub) {
        String result = "";
        for (Sort parent : sub.subsorts.keySet()) {
            Vector<Sort> v = sub.subsorts.get(parent);

            if (v != null && v.size() != 0) {
                result += "  subsorts ";
                for (int i = 0; i < v.size(); i++ ) {
                    Sort kid = v.elementAt(i);
                    //result += toString(kid)+" ";
                    result += "(" + kid + ") ";

                }
                result += "< " + toString(parent) + " .\n";
            }
        }

        return result;

    }

    public void importModule(Module module) throws SignatureException {

        // import sorts
        Sort[] sorts = module.getSorts();
        for (Sort sort : sorts) {
            if (!containsSort(sort)) {
                addSort(sort);
            }
        }

        // import subsorts
        addSubsorts(module.getSubsorts());

        // import operations
        Operation[] ops = module.getOperations();
        for (Operation op : ops) {
            if (!containsOperation(op)) {
                addOperation(op);
            }
        }

        // import equations
        for (Equation eq : module.equations) {
            if (!equations.contains(eq)) {
                equations.add(eq);
            }
        }

        // import generalEquations
        for (Equation eq : module.generalEquations) {
            if (!generalEquations.contains(eq)) {
                generalEquations.add(eq);
            }
        }

        addTokens(module.modName);

        // handle alias
        for (String key : module.alias.keySet()) {
            List<Sort> list = module.alias.get(key);
            List<Sort> res = alias.get(key);
            if (res == null) {
                res = new ArrayList<>();
            }
            res.addAll(list);
            alias.put(key, res);
        }

    }

    public void protectedImport(Module module) throws SignatureException {
        protectImportList.add(module.modName);
        importModule(module);
    }

    public void usedImport(Module module) throws SignatureException {
        useImportList.add(module.modName);
        importModule(module);
    }

    public void extendedImport(Module module) throws SignatureException {
        extendImportList.add(module.modName);
        importModule(module);
    }

    public Sort[] getSortByName(String sortName) {
        List<Sort> list = new ArrayList<>();
        for (Sort sort : sorts) {
            if (sort.getName()
                    .equals(sortName)) {
                list.add(sort);
            }
        }

        return (Sort[]) (list.toArray());
    }

    protected Module addAnnotation(String name,
                                   Map<ModuleName, Integer> env)
        throws SignatureException {

        if (modName.op == ModuleName.ANNOTATE) {
            return this.clone();
        }

        Module result = new Module(type, modName.addAnnotation(name));

        // clone module parts
        result.protectImportList = new ArrayList<>(protectImportList);
        result.paraModules = new ArrayList<>(paraModules);
        result.paraNames = new ArrayList<>(paraNames);
        result.levels = this.levels;

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            sort = sort.addAnnotation(name, env);
            result.addSort(sort);
        }

        // subsorts
        result.addSubsorts(subsorts.addAnnotation(name, env));

        // variable
        for (int i = 0; i < vars.size(); i++ ) {
            Variable var = vars.elementAt(i);
            var = var.addAnnotation(name, env);
            result.addVariable(var);
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            op = op.addAnnotation(name, env);
            result.addOperation(op);
        }

        // import equations
        for (Equation eq : equations) {
            eq = eq.addAnnotation(name, result, env);
            if (!result.equations.contains(eq))
                result.addEquation(eq);
        }

        // import general equations
        for (Equation eq : generalEquations) {
            eq = eq.addAnnotation(name, result, env);
            if (!result.generalEquations.contains(eq))
                result.generalEquations.add(eq);
        }

        if (bindings != null) {
            result.bindings = new Hashtable<>(this.bindings);
        }

        return result;

    }

    public Module removeAnnotation(String name) throws SignatureException {
        Module result = new Module(type, modName.getOriginModuleName());

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            sort = sort.removeAnnotation(name);
            if (!result.containsSort(sort)) {
                result.addSort(sort);
            }
        }

        // subsorts
        result.addSubsorts(subsorts.removeAnnotation(name));

        // variable
        for (int i = 0; i < vars.size(); i++ ) {
            Variable var = vars.elementAt(i);
            var = var.removeAnnotation(name);
            if (!result.containsVariable(var)) {
                result.addVariable(var);
            }
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            op = op.removeAnnotation(name);
            if (!result.containsOperation(op)) {
                result.addOperation(op);
            }
        }

        // equations
        for (Equation eq : equations) {
            eq = eq.removeAnnotation(name, this);
            if (!result.containsEquation(eq))
                result.addEquation(eq);
        }

        // general equations
        for (Equation eq : generalEquations) {
            eq = eq.removeAnnotation(name, this);
            if (!result.generalEquations.contains(eq))
                result.generalEquations.add(eq);
        }

        return result;

    }

    protected boolean containsAnnotation(String name) throws SignatureException {

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            if (sort.getModuleName()
                    .hasNotation(name)) {
                return true;
            }
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            if (op.modName.hasNotation(name)) {
                return true;
            }
        }

        return false;

    }

    public Module instanceBy(Module[] mods,
                             String[] notations,
                             Map<ModuleName, Integer> env,
                             boolean highOrder)
        throws ModuleInstanceException {

        try {
            Module cmod = this.clone();
            for (int i = 0; i < mods.length; i++ ) {

                String paraName = paraNames.get(i);

                boolean found = false;
                for (Module mod : mods) {
                    if (mod.containsAnnotation(paraName)) {
                        found = true;
                        break;
                    }
                }

                if (found) {
                    cmod = cmod.changeParameterName(paraName, "M" + Math.random());
                }
            }

            return cmod.instanceBy1(mods, notations, env, highOrder);

        } catch (SignatureException e) {
            throw new ModuleInstanceException(e.getMessage());
        }
    }

    public Module instanceBy1(Module[] mods,
                              String[] notations,
                              Map<ModuleName, Integer> env,
                              boolean highOrder)
        throws ModuleInstanceException {

        // decide module name
        List<Object> list = new ArrayList<>();
        for (Module mod : mods) {
            View view = (View) mod.getProperty("view");
            if (view == null) {
                list.add(mod.modName);
            } else if (view.name == null || view.name.equals("")) {

                if (!highOrder && levels == null) {
                    Module source = new Module(view.source.type, view.source.modName);
                    Module target = new Module(view.source.type, view.target.modName);
                    view = new View(view.name, source, target);
                }

                list.add(view);

            } else {

                if (!highOrder && levels == null) {
                    Module source = new Module(view.source.type, view.source.modName);
                    Module target = new Module(view.source.type, view.target.modName);
                    view = new View(view.name, source, target);

                }
                list.add(view);

            }
        }
        ModuleName resModName = this.modName.instance(list);

        // import this module into the result module
        Module result = new Module(type, resModName);

        try {
            result.importModule(this);
        } catch (SignatureException e) {
        }

        // check the size of actual parameters
//	if (mods.length != paraModules.size() ||
//	    notations.length != paraModules.size() ) {
//
//	    throw new ModuleInstanceException("expect "+paraModules.size()+
//					     " parameters when instanciate "+
//					      modName);
//	}

        if (mods.length != levels[0] || notations.length != levels[0]) {
            throw new ModuleInstanceException("expect " + levels[0]
                                              + " parameters when instantiate " + modName);
        }

        View[] views = new View[mods.length];

        HashMap<String, String> rename = new HashMap<>();
        int count = 0;
        for (int i = 0; i < mods.length; i++ ) {
            Module parameter = paraModules.get(i);
            String paraName = paraNames.get(i);

            for (int j = 0; j < i; j++ ) {
                try {
                    if (mods[j].containsAnnotation(paraName)) {
                        rename.put(paraName, "%#@" + count + "@#%");
                        count++ ;
                        break;
                    }
                } catch (Exception e) {
                }
            }

            // test
            if (parameter.isParameterized()) {
                continue;
            } else {
                try {
                    result.importModule(mods[i]);
                } catch (Exception e) {
                    //e.printStackTrace();
                }
                //end test
            }
        }

        if (rename.size() != 0) {
            // begin to rename some parameters
            for (String paraName : rename.keySet()) {
                String newName = rename.get(paraName);
                try {
                    result = result.changeParameterName(paraName, newName);
                } catch (SignatureException e) {
                    throw new ModuleInstanceException(e.getMessage());
                }
            }
        }

        if (bindings != null) {

            // check import list
            Map<ModuleName, Module> newenv = new HashMap<>(bindings);
            Map<ModuleName, Module> oldenv = new HashMap<>(bindings);

            for (int i = 0; i < mods.length; i++ ) {
                // get parameter and its name
                Module parameter = paraModules.get(i);
                String paraName = paraNames.get(i);

                if (parameter.isParameterized()) {

                    if (mods[i].isParameterized()) {

                    } else {
                        String msg = mods[i].modName + " can not be used to "
                                     + "instanciate the parameter " + parameter.modName;
                        throw new ModuleInstanceException(msg);
                    }
                }

                try {
                    ModuleName newName = parameter.modName.addAnnotation(paraName);
                    Module tmp = parameter.changeModuleName(parameter.modName, newName, newName);

                    /* there is a problem: "parameter.modName => newName" is not enough
                     *
                     * in parameter, there are many other imported modules all of them should be
                     * changed as well */

                    for (ModuleName im : parameter.protectImportList) {
                        newName = im.addAnnotation(paraName);
                        tmp = parameter.changeModuleName(im, newName, tmp.modName);

                    }
                    // end modification

                    newenv.put(new ModuleName(paraName), mods[i]);
                    oldenv.put(new ModuleName(paraName), tmp);

                } catch (Exception e) {
                    e.printStackTrace();
                }

            }

            // do instantiation for higher order modules

            View[] pviews = new View[protectImportList.size()];
            for (int i = 0; i < protectImportList.size(); i++ ) {
                ModuleName mname = protectImportList.get(i);
                try {
                    ArrayList<View> rec = new ArrayList<>();
                    Module tmp = getModule(mname, newenv, oldenv, rec);
                    pviews[i] = rec.get(0);

                    for (int j = 0; j < i; j++ ) {
                        pviews[i] = pviews[j].getImage(pviews[i]);
                    }
                    //debug
//                    System.err.println("\n----- instanceBy : view -----\n");
//                    System.err.println(pviews[i]);
//
//                    System.err.println("\n----- instanceBy : main 1-----\n");
//                    System.err.println(result.allToString());
//
                    result = pviews[i].getImage(result);

//                    System.err.println("\n--- instanceBy : main 2 ---\n");
//                    System.err.println(result.allToString());

                    result.importModule(tmp);

//                    System.err.println("\n--- instanceBy : main 3 ---\n");
//                    System.err.println(result.allToString());

                } catch (Exception e) {
                    e.printStackTrace();
                    throw new ModuleInstanceException(e.getMessage());
                }

            }
        }

//        System.err.println("\n-------------------------------------");
//        System.err.println("instanceBy middle:   " + this.modName + "\n");
//        System.err.println(result.allToString());

        for (int i = 0; i < mods.length; i++ ) {

            // get parameter and its name
            Module parameter = paraModules.get(i);
            String paraName = paraNames.get(i);
            String newName = rename.get(paraName);

            if (mods[i].type > parameter.type) {
                throw new ModuleInstanceException("can't instanciate " + this.modName + " because "
                                                  + mods[i].getModuleName()
                                                  + " is more general than "
                                                  + parameter.getModuleName());
            }

            // create an view
            views[i] = (View) mods[i].getProperty("view");

            String vname = views[i].name;
            boolean inputName = vname != null && !vname.equals("") && vname.indexOf(":") == -1;

            if (views[i] == null) {
                views[i] = mods[i].getViewFor(parameter);
                inputName = false;
            }

            if (views[i] == null) {
                throw new ModuleInstanceException(mods[i].getModuleName()
                                                  + " is not an instance of "
                                                  + parameter.getModuleName());
            }

            if (parameter.isParameterized()) {
                continue;
            }

            try {
                //result.importModule(mods[i]);
                if (newName == null) {
                    views[i] = views[i].addNotation(paraName, notations[i], env);
                } else {
                    views[i] = views[i].addNotation(newName, notations[i], env);
                }

                result = views[i].getImage(result);

                if (notations[i] == null && mods[i].isBuiltIn()
                    && !result.protectImportList.contains(mods[i].modName)) {
                    result.protectImportList.add(mods[i].modName);
                }

                ModuleName tmpName;
                if (newName == null) {
                    tmpName = parameter.modName.addAnnotation(paraName);
                } else {
                    tmpName = parameter.modName.addAnnotation(newName);
                }

                if (!inputName) {
                    View tmpView = views[i];
                    if (!highOrder && levels == null) {
                        tmpView =
                            new View(views[i].name,
                                     new Module(views[i].source.type, views[i].source.modName),
                                     new Module(views[i].target.type, views[i].target.modName));
                    }
                    mods[i].modName.view = tmpView;

                    result = result.changeModuleName(tmpName, mods[i].modName, result.modName);

                } else {

                    result =
                        result.changeModuleName(tmpName, new ModuleName(vname), result.modName);

                }

            } catch (Throwable e) {
                e.printStackTrace();
                throw new ModuleInstanceException(e.getMessage());
            }

        }

        try {
            result = result.changeAbsoluteModuleName(this.modName, resModName, resModName);
        } catch (Exception e) {
            throw new ModuleInstanceException(e.getMessage());
        }

        if (levels.length > 1) {

            // setup paraNames
            for (int i = levels[0]; i < paraNames.size(); i++ ) {

                String paraName = paraNames.get(i);
                Module paraModule = paraModules.get(i);

                result.paraNames.add(paraName);

                // paraModule need to change
                for (int j = 0; j < levels[0]; j++ ) {

                    try {
                        String str = paraNames.get(j);
                        if (paraModule.containsAnnotation(str)) {

                            paraModule = paraModule.clone();
                            View vi = (View) mods[j].getProperty("view");

                            String vname = vi.name;
                            vi = vi.addNotation(str, null, env);

                            paraModule.importModule(vi.target);
                            paraModule = vi.getImage(paraModule);
                            ModuleName tmpName = paraModule.modName;

                            ModuleName tname = vi.target.modName;
                            if (vname != null && !vname.equals("") && vname.indexOf(":") == -1) {
                                tname = new ModuleName(vname);
                                vi.name = vname;
                                tname.view = vi;
                            }

                            tmpName = tmpName.changeModuleName(vi.source.modName, tname);

                            paraModule = paraModule.changeModuleName(vi.source.modName,
                                                                     vi.target.modName, tmpName);

                        }

                    } catch (Exception e) {
                        throw new Error("system error");
                    }
                }

                result.paraModules.add(paraModule);
            }

            // setup bindings
            result.bindings = this.bindings;

            // setup levels
            result.levels = new int[levels.length - 1];
            for (int i = 0; i < result.levels.length; i++ ) {
                result.levels[i] = levels[i + 1] - levels[0];
            }

        }

//        System.err.println("\n-------------------------------------");
//        System.err.println("instanceBy final:   " + this.modName + "\n");
//        System.err.println(result.allToString());

        return result;
    }

    public View getViewFor(Module module) {

        // create a default view
        //View view = new View("default-view", module, this);
        View view = new View(this.modName.toString(), module, this);
        try {
            view.validate();
        } catch (ViewException e) {
            view = null;
        }

        return view;
    }

    public static Module getModule(ModuleName modName,
                                   Map<ModuleName, Module> newenv,
                                   Map<ModuleName, Module> oldenv,
                                   ArrayList<View> list)
        throws ModuleException {

        try {

            switch (modName.op) {
                case ModuleName.ATOM:

                    Module newModule = newenv.get(modName);
                    if (newModule == null) {

                        if (modName.subexps.size() == 0) {

                            newModule = ModuleFactory.getDefaultModule(modName.atom);
                            if (newModule == null) {
                                throw new ModuleException("unknown module " + modName);
                            } else {
                                View view = new View("", newModule, newModule);
                                view.validate();
                                list.add(view);
                                return newModule.clone();
                            }

                        }

                        // renamed module
                        ModuleName name = (ModuleName) modName.subexps.get(0);
                        if (name != null) {
                            newModule = getModule(name, newenv, oldenv, list);

                            View view = list.get(0);
                            list.remove(0);
                            view = view.aliasModuleName(modName.atom);
                            list.add(view);

                            ModuleName nname = new ModuleName(modName.atom);
                            nname.subexps.add(newModule.modName);
                            newModule = newModule.changeModuleName(newModule.modName, nname, nname);
                            newenv.put(nname, newModule);

                            return newModule.clone();
                        } else {
                            throw new ModuleException("unknown module " + modName);
                        }

                    } else {

                        View view = new View("", newModule, newModule);
                        view.validate();
                        list.add(view);
                        return newModule.clone();
                    }

                case ModuleName.ANNOTATE:

                    //System.out.println("\n============================");
                    //System.out.println("in annotate: "+modName);

                    Map<ModuleName, Integer> map = new HashMap<>();
                    for (ModuleName tmpName : oldenv.keySet()) {
                        Module tmpModule = oldenv.get(tmpName);
                        map.put(tmpName, tmpModule.type);
                    }

                    ModuleName name = (ModuleName) modName.subexps.get(0);
                    ArrayList<View> l = new ArrayList<>();
                    Module module = getModule(name, newenv, oldenv, l);
                    module = module.addAnnotation(modName.atom, map);

                    View tmpV = l.get(0);

                    // try to get new module directly
                    ModuleName tname = new ModuleName(modName.atom);
                    Module tmodule = module.clone();
                    for (ModuleName n : newenv.keySet()) {
                        Module tmp = newenv.get(n);
                        if (n.equals(tname)) {
                            tmodule = tmp.clone();
                            break;
                        }
                    }

                    //System.out.println("\ntarget module = "+tmodule.modName);
                    //System.out.println("source module = "+module.modName);

                    View view = (View) tmodule.getProperty("view");
                    if (view == null) {
                        view = new View("", module, tmodule);
                        view.validate();
                    }

                    if (name.op != ModuleName.ATOM) {
                        if (!view.source.modName.equals(modName.subexps.get(0))) {
                            view = tmpV.composite(view);
                        }
                        view = view.addNotation(modName.atom, null, map);

                    } else {
                        String tmpName = view.name;
                        view = view.addNotation(modName.atom, null, map);
                        view.name = tmpName;
                    }

                    tmodule.setProperty("view", view);
                    list.clear();
                    list.add(view);

                    return tmodule;

                case ModuleName.SUM:

                    ModuleName name1 = (ModuleName) modName.subexps.get(0);
                    ModuleName name2 = (ModuleName) modName.subexps.get(0);

                    ArrayList<View> list1 = new ArrayList<>();
                    ArrayList<View> list2 = new ArrayList<>();

                    Module module1 = getModule(name1, newenv, oldenv, list1);
                    Module module2 = getModule(name2, newenv, oldenv, list2);

                    name = name1.sum(name2);

                    int type = module1.getType();
                    if (module2.getType() > type) {
                        type = module2.getType();
                    }
                    module = new Module(type, name);
                    module.protectedImport(module1);
                    module.protectedImport(module2);

                    // handle list here
                    View view1 = list1.get(0);
                    View view2 = list2.get(0);

                    view = view1.sum(view2);
                    list.clear();
                    list.add(view);

                    return module;

                case ModuleName.INSTANCE:

                    throw new ModuleException("");

                case ModuleName.GENERAL_INSTANCE:

                    //System.out.println("\n---- handle GENERAL_INSTANCE -----\n");
                    //System.out.println(modName);

                    // first look for new and old main modules

                    ModuleName mainName = (ModuleName) modName.subexps.get(0);

                    Module oldModule = null;
                    name1 = null;
                    if (mainName.hasNotation()) {

                        name1 = new ModuleName(mainName.atom);
                        name2 = (ModuleName) mainName.subexps.get(0);

                        newModule = newenv.get(name1);
                        oldModule = oldenv.get(name1);

                    } else {
                        newModule = newenv.get(mainName);
                        oldModule = oldenv.get(mainName);
                    }

                    if (newModule == null || oldModule == null) {
                        throw new ModuleException("unknown module " + mainName);
                    }

                    // get main view
                    View mainView = (View) newModule.getProperty("view");
                    if (mainView == null) {
                        mainView = new View("", oldModule, newModule);
                        mainView.validate();
                    } else if (!mainView.source.modName.equals(oldModule.modName)) {

                        // in this case, we get a dependent type
                        // i.e. plaese check oldModule.modName and
                        // mainView.source.modName

                        // need create a view from oldModule.modName
                        // to mainView.source.modName

                        ArrayList<View> tmpList = new ArrayList<>();
                        Module tmpModule = getModule(oldModule.modName, newenv, oldenv, tmpList);
                        // System.out.println("\n---- load oldModule -----");
                        // System.out.println(oldModule.modName);
                        // System.out.println(tmpModule);

                        View tmpView = tmpList.get(0);

                        // System.out.println("\n====== get main view ======");
                        // System.out.println(tmpView);

                        mainView = tmpView;

                    }

                    // create environment
                    map = new HashMap<>();
                    for (ModuleName tmpName : oldenv.keySet()) {
                        Module tmpModule = oldenv.get(tmpName);
                        map.put(tmpName, tmpModule.type);
                    }

                    if (name1 != null) {
                        mainView = mainView.addNotation(name1.atom, null, map);
                        mainView.name = "";
                    }

                    /* System.out.println("\n---- old module ----\n");
                     * System.out.println(oldModule.allToString());
                     *
                     * System.out.println("\n---- new module ----\n");
                     * System.out.println(newModule.allToString());
                     *
                     * System.out.println("\n---- main view ----\n");
                     * System.out.println(mainView); */

                    // get old actual modules and new actual modules

                    Module[] newMods = new Module[modName.subexps.size() - 1];
                    View[] newViews = new View[newMods.length];

                    Module[] oldMods = new Module[modName.subexps.size() - 1];
                    View[] oldViews = new View[oldMods.length];

                    View[] views = new View[oldMods.length];

                    for (int i = 1; i < modName.subexps.size(); i++ ) {
                        Object obj = modName.subexps.get(i);
                        if (obj instanceof View) {

                            oldViews[i - 1] = (View) obj;
                            oldViews[i - 1].validate();
                            oldMods[i - 1] = oldViews[i - 1].target;

                            /* System.out.println("\n---- old parameter ---");
                             * System.out.println(oldMods[i-1]);
                             * System.out.println("\n----- old view -----");
                             * System.out.println(oldViews[i-1]); */

                            ArrayList<View> tmpList = new ArrayList<>();
                            newMods[i - 1] =
                                getModule(oldMods[i - 1].modName, newenv, oldenv, tmpList);
                            newMods[i - 1] = newMods[i - 1].clone();
                            newViews[i - 1] = tmpList.get(0);

                            /* System.out.println("\n--- new parameter ---");
                             * System.out.println(newMods[i-1]);
                             * System.out.println("\n----- new view -----");
                             * System.out.println(newViews[i-1]); */

                            views[i - 1] = newViews[i - 1].copy("");

                            // newMods[i-1] is always correct,
                            // but newViews might not be correct
                            // because of dependent type

                            // if it is a dependent type
                            // we should instanciate oldViews[i-1] to get tmpView
                            // then compose them

                            // check dependency first

                            Module m1 = oldModule.getParameterAt(i - 1);
                            Module m2 = newModule.getParameterAt(i - 1);

                            if (!m1.modName.equals(m2.modName)) {

                                tmpList.clear();
                                Module mmm = getModule(m1.modName, newenv, oldenv, tmpList);
                                View vvv = tmpList.get(0);
                                View www = oldViews[i - 1].composite(newViews[i - 1]);
                                View xyz = getView(vvv, www);

                                newViews[i - 1] = xyz;
                                newMods[i - 1] = xyz.source;
                                newMods[i - 1].setProperty("view", newViews[i - 1]);

                            } else {

                                /* System.out.println("\n-- new view before comp--");
                                 * System.out.println(newViews[i-1]);
                                 *
                                 * System.out.println("\n-- compose with --");
                                 * System.out.println(oldViews[i-1]); */

                                newViews[i - 1] = oldViews[i - 1].composite(newViews[i - 1]);

                                /* System.out.println("\n---- new parameter -----");
                                 * System.out.println(newMods[i-1]);
                                 *
                                 * System.out.println("\n----- new view -----");
                                 * System.out.println(newViews[i-1]); */
                                newMods[i - 1].setProperty("view", newViews[i - 1]);

                            }

                        } else if (obj instanceof ModuleName) {
                            throw new Error("system error");
                        }

                    }

                    // create a newResultModule

                    Module newResultModule, oldResultModule;
                    newResultModule =
                        newModule.instanceBy(newMods, new String[newMods.length], map, false);
                    oldResultModule =
                        oldModule.instanceBy(oldMods, new String[oldMods.length], map, false);

//                      System.err.println("\n---- old result module ----\n");
//                      System.err.println(oldResultModule.allToString());
//
//                      System.err.println("\n---- new result module ----\n");
//                      System.err.println(newResultModule.allToString());
//
//                      System.err.println("\n---- main view again ----\n");
//                      System.err.println(mainView);

                    // create a view from oldResultModule to newResultModule
                    view = new View("", oldResultModule, newResultModule);

                    for (View view3 : views) {

                        for (Sort from : view3.sortMap.keySet()) {
                            Sort to = view3.sortMap.get(from);
                            view.addSortMap(from, to);
                        }

                        for (Operation from : view3.opMap.keySet()) {
                            Operation to = view3.opMap.get(from);
                            view.addOperationMap(from, to);
                        }

                        for (Term left : view3.trans.keySet()) {
                            Term right = view3.trans.get(left);
                            view.addTransformation(left, right);
                        }

                    }

                    for (Sort from : mainView.sortMap.keySet()) {
                        Sort to = mainView.sortMap.get(from);
                        if (from.getModuleName()
                                .hasNotation()) {
                            // modification: 2002-Jul-02
                            Sort[] fsorts = view.source.getSortsByName(from.getName());
                            Sort[] tsorts = view.target.getSortsByName(to.getName());

                            if (fsorts.length == 1 && tsorts.length == 1) {
                                view.addSortMap(fsorts[0], tsorts[0]);
                            }
                            // end modification

                            continue;
                        }

                        for (int i = 0; i < newViews.length; i++ ) {

                            String oldParaName = oldModule.getParameterNameAt(i);
                            View tmpView = oldViews[i].addNotation(oldParaName, null, map);
                            from = tmpView.getImage(from);
                            String newParaName = newModule.getParameterNameAt(i);
                            tmpView = newViews[i].addNotation(newParaName, null, map);
                            to = tmpView.getImage(to);
                        }

                        from = from.changeModuleName(oldModule.modName, oldResultModule.modName);
                        to = to.changeModuleName(newModule.modName, newResultModule.modName);
                        view.addSortMap(from, to);

                    }

                    // handle operation mapping
                    for (Operation from : mainView.opMap.keySet()) {
                        Operation to = mainView.opMap.get(from);

                        if (from.modName.hasNotation()) {

                            // modification: 2002-Jul-02
                            Operation[] fops = view.source.getOperationsWithName(from.getName());
                            Operation[] tops = view.target.getOperationsWithName(to.getName());

                            if (fops.length == 1 && tops.length == 1) {
                                view.addOperationMap(fops[0], tops[0]);
                            }
                            // end modification

                            continue;
                        }

                        for (int i = 0; i < newViews.length; i++ ) {

                            String oldParaName = oldModule.getParameterNameAt(i);
                            View tmpView = oldViews[i].addNotation(oldParaName, null, map);
                            from = tmpView.getImage(from);

                            String newParaName = newModule.getParameterNameAt(i);
                            tmpView = newViews[i].addNotation(newParaName, null, map);
                            to = tmpView.getImage(to);
                        }

                        from = from.changeModuleName(oldModule.modName, oldResultModule.modName);
                        to = to.changeModuleName(newModule.modName, newResultModule.modName);

                        if (oldResultModule.isParameterized()) {

                            for (int i = 0; i < oldResultModule.paraNames.size(); i++ ) {
                                Module oldPara = oldModule.getParameterAt(oldMods.length + i);
                                String oldName = oldModule.getParameterNameAt(oldMods.length + i);
                                ModuleName oldModName = oldPara.modName.addAnnotation(oldName);

                                Module oldResPara = oldResultModule.getParameterAt(i);
                                String oldResName = oldResultModule.getParameterNameAt(i);
                                ModuleName newModName =
                                    oldResPara.modName.addAnnotation(oldResName);

                                from = from.changeModuleName(oldModName, newModName);

                            }

                            for (int i = 0; i < newResultModule.paraNames.size(); i++ ) {
                                Module newPara = newModule.getParameterAt(newMods.length + i);
                                String newName = newModule.getParameterNameAt(newMods.length + i);
                                ModuleName oldModName = newPara.modName.addAnnotation(newName);

                                Module newResPara = newResultModule.getParameterAt(i);
                                String newResName = newResultModule.getParameterNameAt(i);
                                ModuleName newModName =
                                    newResPara.modName.addAnnotation(newResName);

                                to = to.changeModuleName(oldModName, newModName);

                            }
                        }

                        view.addOperationMap(from, to);

                    }

                    for (Term left : mainView.trans.keySet()) {
                        Term right = mainView.trans.get(left);

                        for (int i = 0; i < newViews.length; i++ ) {

                            String oldParaName = oldModule.getParameterNameAt(i);
                            View tmpView = oldViews[i].addNotation(oldParaName, null, map);

                            left = tmpView.getImage(oldResultModule, left);

                            String newParaName = newModule.getParameterNameAt(i);
                            tmpView = newViews[i].addNotation(newParaName, null, map);
                            right = tmpView.getImage(oldResultModule, right);

                        }

                        left = left.changeModuleName(oldModule.modName, oldResultModule.modName,
                                                     oldResultModule);
                        right = right.changeModuleName(newModule.modName, newResultModule.modName,
                                                       newResultModule);

                        left = view.source.normalize(left);
                        right = view.target.normalize(right);

                        view.addTransformation(left, right);
                    }

                    for (Variable key : mainView.varMap.keySet()) {
                        Variable val = mainView.varMap.get(key);

                        Sort[] sSorts = view.source.getSortsByName(key.sort.getName());
                        Sort[] tSorts = view.target.getSortsByName(val.sort.getName());

                        if (sSorts.length != 1) {
                            throw new ModuleInstanceException(key.toString());
                        }

                        if (tSorts.length != 1) {
                            throw new ModuleInstanceException(val.toString());
                        }

                        view.varMap.put(new Variable(key.name, sSorts[0]),
                                        new Variable(val.name, tSorts[0]));

                    }

                    view.validate();
                    list.clear();
                    list.add(view);

                    /* System.out.println("\n----- returned view ------\n");
                     * System.out.println(view);
                     *
                     * System.out.println("\n----- returned module -----\n");
                     * System.out.println(newResultModule); */

                    newResultModule.setProperty("view", view);

                    return newResultModule;

                case ModuleName.RENAMING:
                    name = (ModuleName) modName.subexps.get(0);
                    @SuppressWarnings("unchecked")
                    Map<ViewRenamable, ViewRenamable> renaming =
                        (Map<ViewRenamable, ViewRenamable>) modName.subexps.get(1);

                    list.clear();
                    module = getModule(name, newenv, oldenv, list);

                    view = list.get(0);
                    view.validate();

                    list.clear();
                    view = view.rename(renaming);
                    list.add(view);

                    return view.target;

                default:
                    throw new ModuleException("");
            }
        } catch (Exception e) {
            //e.printStackTrace();
            throw new ModuleException(e.getMessage());
        }

    }

    private Term normalize(Term term) throws TermException {

        if (term.var != null) {

            if (this.containsSort(term.var.sort)) {
                return term;
            } else {
                Sort[] sorts = this.getSortsByName(term.var.sort.getName());
                if (sorts.length == 1) {
                    return new Term(new Variable(term.var.name, sorts[0]));
                } else {
                    throw new TermException(term.var.toString());
                }
            }

        } else {

            Operation op;
            if (this.containsOperation(term.operation)) {
                op = term.operation;
            } else {
                Operation[] ops = this.getOperationsWithName(term.operation.getName());
                if (ops.length == 1) {
                    op = ops[0];
                } else {
                    throw new TermException(term.operation.toString());
                }
            }

            Term[] terms = new Term[term.subterms.length];
            for (int i = 0; i < terms.length; i++ ) {
                terms[i] = this.normalize(term.subterms[i]);
            }

            return new Term(this, op, terms);

        }

    }

    static public void getExtraViews(ModuleName m1,
                                     ModuleName m2,
                                     Map<Object, Object> map) {

        switch (m1.op) {
            case ModuleName.ANNOTATE:
                map.put(m1, m2);
            case ModuleName.GENERAL_INSTANCE:
                ModuleName main1 = (ModuleName) m1.subexps.get(0);
                if (m2.op == m1.op) {
                    ModuleName main2 = (ModuleName) m2.subexps.get(0);
                    if (main1.equals(main2)) {
                        for (int i = 1; i < m1.subexps.size(); i++ ) {
                            Object tmp1 = m1.subexps.get(i);
                            Object tmp2 = m2.subexps.get(i);
                            if ((tmp1 instanceof ModuleName) && (tmp2 instanceof ModuleName)) {
                                getExtraViews((ModuleName) tmp1, (ModuleName) tmp2, map);
                            } else {
                                map.put(tmp1, tmp2);
                            }
                        }
                    } else {
                        System.out.println("something is wrong");
                        System.exit(0);
                    }
                } else {
                    System.out.println("something is wrong");
                    System.exit(0);
                }
            break;
            default:
        }

    }

    static public View getView(View from,
                               View to)
        throws ViewException {

        View result = new View(to.target.modName.toString(), from.target, to.target);

        for (int i = 0; i < from.source.sorts.size(); i++ ) {
            Sort sort = from.source.sorts.elementAt(i);
            Sort fromSort = from.getTarget(sort);
            Sort toSort = to.getTarget(sort);
            result.addSortMap(fromSort, toSort);
        }

        for (int i = 0; i < from.source.operations.size(); i++ ) {
            Operation op = from.source.operations.elementAt(i);
            Operation fromOp = from.getTarget(op);
            Operation toOp = to.getTarget(op);

            if (fromOp == null) {
                throw new ViewException("failed to create a view from " + from.target.modName
                                        + " to " + to.target.modName);
            }

            if (toOp == null) {
                if (op.isConstant()) {
                    try {
                        Term term = new Term(op);
                        term = to.getImage(to.target, term);
                        result.addTransformation(new Term(fromOp), term);
                    } catch (TermException e) {
                    }
                } else {
                    throw new ViewException("failed to create a view from " + from.target.modName
                                            + " to " + to.target.modName);
                }
            } else {
                result.addOperationMap(fromOp, toOp);
            }

        }

        return result;
    }

    public Module changeSort(ModuleName name,
                             Sort from,
                             Sort to)
        throws SignatureException {

        if (containsSort(from)) {

            Module result = new Module(type, name);

            // setup parameters
            for (int i = 0; i < paraModules.size(); i++ ) {
                Module module = this.paraModules.get(i);
                result.paraModules.add(module);

                String paraName = this.paraNames.get(i);
                result.paraNames.add(paraName);

            }

            result.levels = this.levels;

            // sorts
            for (int i = 0; i < sorts.size(); i++ ) {
                Sort sort = sorts.elementAt(i);
                if (sort.equals(from)) {
                    result.addSort(to);
                } else {
                    result.addSort(sort);
                }
            }

            // subsorts
            result.addSubsorts(subsorts.changeSort(from, to));

            // variable
            for (int i = 0; i < vars.size(); i++ ) {
                Variable var = vars.elementAt(i);
                var = var.changeSort(from, to);
                result.addVariable(var);
            }

            //operations
            for (int i = 0; i < operations.size(); i++ ) {
                Operation op = operations.elementAt(i);
                op = op.changeSort(from, to);
                result.addOperation(op);
            }

            // equations
            for (Equation eq : equations) {
                eq = eq.changeSort(from, to, result);
                if (!result.equations.contains(eq)) {
                    result.equations.add(eq);
                }
            }

            // dgd: general equations  was wrong in original looped over equations as above
            for (Equation eq : generalEquations) {
                eq = eq.changeSort(from, to, result);
                if (!result.generalEquations.contains(eq)) {
                    result.generalEquations.add(eq);
                }
            }

            ArrayList<Sort> list = (ArrayList<Sort>) alias.get("QID");
            if (list != null) {
                for (int i = 0; i < list.size(); i++ ) {
                    Sort s = list.get(i);
                    if (s.equals(from)) {
                        list.remove(i);
                        list.add(to);
                        break;
                    }
                }

                result.alias.put("QID", list);

            }

            return result;

        } else {

            return this;

        }

    }

    public Module replaceOperation(ModuleName name,
                                   Operation from,
                                   Operation to)
        throws SignatureException {

        if (containsOperation(from)) {

            Module result = new Module(type, name);

            // setup parameters
            for (int i = 0; i < paraModules.size(); i++ ) {
                Module module = this.paraModules.get(i);
                result.paraModules.add(module);

                String paraName = this.paraNames.get(i);
                result.paraNames.add(paraName);

            }

            result.levels = this.levels;

            // sorts
            for (int i = 0; i < sorts.size(); i++ ) {
                Sort sort = sorts.elementAt(i);
                result.addSort(sort);
            }

            // subsorts
            result.addSubsorts(subsorts);

            // variable
            for (int i = 0; i < vars.size(); i++ ) {
                Variable var = vars.elementAt(i);
                result.addVariable(var);
            }

            //operations
            for (int i = 0; i < operations.size(); i++ ) {
                Operation op = operations.elementAt(i);

                if (op.equals(from)) {
                    result.addOperation(to);
                } else {

                    Operation nop = op.copy();

                    if (op.id != null && op.id.equals(from)) {
                        nop.id = to;
                    }

                    if (op.implicitId != null && op.implicitId.equals(from)) {
                        nop.implicitId = to;
                    }

                    result.addOperation(nop);
                }

            }

            // equations
            for (Equation eq : equations) {
                eq = eq.changeOperation(from, to, this);

                if (!result.equations.contains(eq)) {
                    result.equations.add(eq);
                }

            }

            for (Equation eq : generalEquations) {
                eq = eq.changeOperation(from, to, this);

                if (!result.generalEquations.contains(eq)) {
                    result.generalEquations.add(eq);
                }

            }

            // handle alias
            for (String key : alias.keySet()) {
                List<Sort> list = alias.get(key);

                List<Sort> res = new ArrayList<>();
                for (int i = 0; i < list.size(); i++ ) {
                    Sort s = list.get(i);
                    res.add(s);
                }

                result.alias.put(key, res);
            }

            return result;

        } else {

            return this;

        }

    }

    public Module changeModuleName(ModuleName from,
                                   ModuleName to,
                                   ModuleName name)
        throws SignatureException {

        Module result = new Module(type, name);

        // setup parameters
        for (int i = 0; i < paraModules.size(); i++ ) {
            Module module = this.paraModules.get(i);
            result.paraModules.add(module);

            String paraName = this.paraNames.get(i);
            result.paraNames.add(paraName);

        }

        if (this.bindings != null) {
            result.bindings = this.bindings;
        }

        result.levels = this.levels;

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            sort = sort.changeModuleName(from, to);
            result.addSort(sort);
        }

        // subsorts
        result.addSubsorts(subsorts.changeModuleName(from, to));

        // variable
        for (int i = 0; i < vars.size(); i++ ) {
            Variable var = vars.elementAt(i);
            var = var.changeModuleName(from, to);
            result.addVariable(var);
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            op = op.changeModuleName(from, to);
            result.addOperation(op);
        }

        // equations
        for (Equation eq : equations) {
            eq = eq.changeModuleName(from, to, result);
            if (!result.equations.contains(eq)) {
                result.equations.add(eq);
            }

        }

        for (Equation eq : generalEquations) {
            eq = eq.changeModuleName(from, to, result);
            if (!result.generalEquations.contains(eq)) {
                result.generalEquations.add(eq);
            }

        }

        // handle alias
        for (String key : alias.keySet()) {
            List<Sort> list = alias.get(key);

            List<Sort> res = new ArrayList<>();
            for (int i = 0; i < list.size(); i++ ) {
                Sort s = list.get(i);
                res.add(s.changeModuleName(from, to));
            }

            result.alias.put(key, res);
        }

        return result;
    }

    public Module changeAbsoluteModuleName(ModuleName from,
                                           ModuleName to,
                                           ModuleName name)
        throws SignatureException {

        Module result = new Module(type, name);

        // setup parameters
        for (int i = 0; i < paraModules.size(); i++ ) {
            Module module = this.paraModules.get(i);
            result.paraModules.add(module);

            String paraName = this.paraNames.get(i);
            result.paraNames.add(paraName);
        }

        // protect import list
        for (int i = 0; i < protectImportList.size(); i++ ) {
            ModuleName mname = protectImportList.get(i);
            result.protectImportList.add(mname.changeAbsoluteModuleName(from, to));

        }

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            sort = sort.changeAbsoluteModuleName(from, to);
            result.addSort(sort);
        }

        // subsorts
        result.addSubsorts(subsorts.changeAbsoluteModuleName(from, to));

        // variable
        for (int i = 0; i < vars.size(); i++ ) {
            Variable var = vars.elementAt(i);
            var = var.changeAbsoluteModuleName(from, to);
            result.addVariable(var);
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            op = op.changeAbsoluteModuleName(from, to);
            result.addOperation(op);
        }

        // equations
        for (Equation eq : equations) {
            eq = eq.changeAbsoluteModuleName(from, to, result);
            if (!result.equations.contains(eq)) {
                result.equations.add(eq);
            }

        }

        for (Equation eq : generalEquations) {
            eq = eq.changeAbsoluteModuleName(from, to, result);
            if (!result.generalEquations.contains(eq)) {
                result.generalEquations.add(eq);
            }

        }

        // handle alias
        for (String key : alias.keySet()) {
            List<Sort> list = alias.get(key);

            List<Sort> res = new ArrayList<>();
            for (int i = 0; i < list.size(); i++ ) {
                Sort s = list.get(i);
                res.add(s.changeAbsoluteModuleName(from, to));
            }

            result.alias.put(key, res);
        }

        return result;
    }

    static int pcount = 1;

    public Module rename() {

        if (!isParameterized()) {
            return this;
        }

        Module mod = this;
        for (String from : paraNames) {
            String to = "___P" + pcount;
            try {
                mod = mod.changeParameterName(from, to);
            } catch (Exception e) {
            }
        }

        return mod;

    }

    public Module changeParameterName(String from,
                                      String to)
        throws SignatureException {

        Module result = new Module(type, modName);

        // setup parameters
        for (int i = 0; i < paraModules.size(); i++ ) {
            Module module = this.paraModules.get(i);
            result.paraModules.add(module);

            String paraName = this.paraNames.get(i);
            if (paraName.equals(from)) {
                result.paraNames.add(to);
            } else {
                result.paraNames.add(paraName);
            }
        }

        // sorts
        for (int i = 0; i < sorts.size(); i++ ) {
            Sort sort = sorts.elementAt(i);
            sort = sort.changeParameterName(from, to);
            result.addSort(sort);
        }

        // subsorts
        result.addSubsorts(subsorts.changeParameterName(from, to));

        // variable
        for (int i = 0; i < vars.size(); i++ ) {
            Variable var = vars.elementAt(i);
            var = var.changeParameterName(from, to);
            result.addVariable(var);
        }

        //operations
        for (int i = 0; i < operations.size(); i++ ) {
            Operation op = operations.elementAt(i);
            op = op.changeParameterName(from, to);
            result.addOperation(op);
        }

        // equations
        for (Equation eq : equations) {
            eq = eq.changeParameterName(from, to, result);
            if (!result.equations.contains(eq)) {
                result.equations.add(eq);
            }

        }

        for (Equation eq : generalEquations) {
            eq = eq.changeParameterName(from, to, result);
            if (!result.generalEquations.contains(eq)) {
                result.generalEquations.add(eq);
            }

        }

        // handle alias
        for (String key : alias.keySet()) {
            List<Sort> aliases = alias.get(key);

            List<Sort> res = new ArrayList<>();
            for (int i = 0; i < aliases.size(); i++ ) {
                Sort s = aliases.get(i);
                res.add(s.changeParameterName(from, to));
            }

            result.alias.put(key, res);
        }

        // copy level
        if (levels != null) {
            result.levels = new int[levels.length];
            System.arraycopy(levels, 0, result.levels, 0, levels.length);
        }

        return result;
    }

    @Override
    public Module clone() {

        Module result = new Module(type, modName);

        // clone signature part
        result.sorts = new Vector<>(sorts);
        result.vars = new Vector<>(vars);
        result.subsorts = (Subsort) subsorts.clone();
        result.operations = new Vector<>(operations);
        result.tokens = new Vector<>(tokens);
        result.compatible = new Hashtable<>(compatible);
        result.alias = new HashMap<>(alias);
        result.parameters = parameters;
        result.firsts = new ArrayList<>(firsts);
        result.lasts = new ArrayList<>(lasts);
        result.balancedBrackets = balancedBrackets;
        result.explicitRetract = explicitRetract;

        // clone module parts
        result.paraModules = new ArrayList<>(paraModules);
        result.paraNames = new ArrayList<>(paraNames);
        result.protectImportList = new ArrayList<>(protectImportList);
        result.extendImportList = new ArrayList<>(extendImportList);
        result.useImportList = new ArrayList<>(useImportList);
        result.bindings = bindings;
        result.levels = levels;
        result.equations = new ArrayList<>();
        result.equations.addAll(equations);
        result.generalEquations = new ArrayList<>();
        result.generalEquations.addAll(generalEquations);

        result.props = new HashMap<>(props);

        return result;
    }

    public static Module makeTuple(ModuleName modName,
                                   List<Module> list)
        throws SignatureException {

        // change list to array for reusing old code
        Object[] objs = list.toArray();
        Module[] modules = new Module[objs.length];

        for (int i = 0; i < objs.length; i++ ) {
            modules[i] = (Module) objs[i];
        }

        // create an empty framework
        Module result = new Module(Module.BEHAVORIAL, modName);
        result.importModule(BoolModule.bool);

        // create the sort for tuple
        HiddenSort tuple = new HiddenSort("Tuple", modName);
        result.addSort(tuple);

        // note: tuple becomes the principal sort

        // import all components
        for (Module module : modules) {
            result.importModule(module);
        }

        // create tuple operation name <_, ..., _>
        String opName = "<";
        for (int i = 0; i < modules.length; i++ ) {
            if (i == 0) {
                opName += "_";
            } else {
                opName += ",_";
            }
        }
        opName += ">";

        // create tuple operation and add it into result
        Sort[] argSorts = new Sort[modules.length];
        for (int i = 0; i < modules.length; i++ ) {
            argSorts[i] = modules[i].getPrincipalSort();
        }

        Operation op = new Operation(opName, argSorts, tuple, modName);
        result.addOperation(op);

        // create projection operations for each components
        Operation[] ops = new Operation[modules.length];
        for (int i = 0; i < modules.length; i++ ) {
            ops[i] = new Operation((i + 1) + "* _", new Sort[]
                {
                    tuple
                }, argSorts[i], modName);
            ops[i].setBehavorial(false);
            result.addOperation(ops[i]);
        }

        // add projection equations

        // first create terms for variables
        Term[] args = new Term[argSorts.length];
        for (int i = 0; i < argSorts.length; i++ ) {
            Variable var =
                new Variable("~tuplevar~" + argSorts[i].getName() + (i + 1), argSorts[i]);
            args[i] = new Term(var);
        }

        try {
            Term term = new Term(op, args);
            for (int i = 0; i < argSorts.length; i++ ) {
                Term left = new Term(ops[i], term);
                Term right = args[i];
                result.addEquation(new Equation(left, right));
            }

            Term tupleVar = new Term(new Variable("~tuplevar~Tuple", tuple));

            args = new Term[args.length];
            for (int i = 0; i < modules.length; i++ ) {
                args[i] = new Term(ops[i], tupleVar);
            }

            result.addEquation(new Equation(new Term(op, args), tupleVar));

        } catch (TermException e) {
        }

        return result;

    }

    public void setProperty(String name,
                            Object object) {
        props.put(name, object);
    }

    public Object getProperty(String name) {
        return props.get(name);
    }

    public void removeProperty(String name) {
        props.remove(name);
    }

    public Term getNormalForm(Term term) {
        RewriteEngine engine = new RewriteEngine(this);
        Term t = engine.reduce(term);
        return t;
    }

    public void completeEquation(Equation eq) {

        /* handle identity completion for each l = r if c , check if there is an operation which has
         * identity. if so, check whether condition is true, and LHS is not the same as RHS, then
         * add equation LHS -> RHS */

        RewriteEngine engine = new RewriteEngine(this);
        engine.turnoff2Eq = true;

        Term left = eq.getLeft();
        Term right = eq.getRight();
        Term cond = eq.getCondition();
        Vector<Map<Variable, Operation>> vars = getIdentityCompletionVariables(left);

        if (vars.size() > 0) {

            try {

                Vector<Equation> pool = new Vector<>();
                for (int i = 0; i < vars.size(); i++ ) {
                    Map<Variable, Operation> tab = vars.elementAt(i);

                    Iterator<Variable> ee = tab.keySet()
                                               .iterator();
                    Variable var = ee.next();
                    Operation id = tab.get(var);
                    Term term = new Term(id);

                    // Term l = getNormalForm(left.subst(this, var, term)) ;
                    Term l = engine.reduce(left.subst(this, var, term));

                    //Term r = getNormalForm(right.subst(this, var, term));
                    Term r = engine.reduce(right.subst(this, var, term));

                    int c = -1;

                    Term cd = cond;
                    if (cond != null) {
                        cd = getNormalForm(cond.subst(this, var, term));
                        c = RewriteEngine.boolValue(cd);
                    }

                    if ((cond == null || c == 1) && !l.equals(r) && !l.isSubterm(r)) {

                        Equation eqtmp = new Equation(l, r);

                        if (!equations.contains(eq)) {
                            pool.addElement(eqtmp);
                        }
                    }

                    if (cond != null && c != 1 && !l.equals(r) && !l.isSubterm(r)) {

                        Equation eqtmp = new Equation(cd, l, r);

                        if (!equations.contains(eq)) {
                            pool.addElement(eqtmp);
                        }
                    }
                }
                if (vars.size() == 2) {

                    Map<Variable, Operation> tab1 = vars.elementAt(0);
                    Iterator<Variable> ee1 = tab1.keySet()
                                                 .iterator();
                    Variable var1 = ee1.next();
                    Operation id1 = tab1.get(var1);
                    Term term1 = new Term(id1);

                    Map<Variable, Operation> tab2 = vars.elementAt(1);
                    Iterator<Variable> ee2 = tab2.keySet()
                                                 .iterator();
                    Variable var2 = ee2.next();
                    Operation id2 = tab2.get(var2);
                    Term term2 = new Term(id2);

                    Term l = left.subst(this, var1, term1);
                    l = l.subst(this, var2, term2);
                    l = getNormalForm(l);

                    Term r = right.subst(this, var1, term1);
                    r = r.subst(this, var2, term2);
                    r = getNormalForm(r);

                    int c = -1;

                    Term cd = cond;
                    if (cond != null) {
                        cd = getNormalForm(cond.subst(this, var1, term1)
                                               .subst(this, var2, term2));
                        c = RewriteEngine.boolValue(cd);
                    }

                    if ((cond == null || c == 1) && !l.equals(r) && !l.isSubterm(r)) {
                        Equation eqtmp = new Equation(l, r);

                        if (!equations.contains(eq)) {
                            pool.addElement(eqtmp);
                        }
                    }

                    if (cond == null && c != 1 && !l.equals(r) && !l.isSubterm(r)) {
                        Equation eqtmp = new Equation(cd, l, r);

                        if (!equations.contains(eq)) {
                            pool.addElement(eqtmp);
                        }
                    }

                }

                if (vars.size() == 3) {

                    Map<Variable, Operation> tab1 = vars.elementAt(0);
                    Iterator<Variable> ee1 = tab1.keySet()
                                                 .iterator();
                    Variable var1 = ee1.next();
                    Operation id1 = tab1.get(var1);
                    Term term1 = new Term(id1);

                    Map<Variable, Operation> tab2 = vars.elementAt(1);
                    Iterator<Variable> ee2 = tab2.keySet()
                                                 .iterator();
                    Variable var2 = ee2.next();
                    Operation id2 = tab2.get(var2);
                    Term term2 = new Term(id2);

                    Map<Variable, Operation> tab3 = vars.elementAt(2);
                    Iterator<Variable> ee3 = tab3.keySet()
                                                 .iterator();
                    Variable var3 = ee3.next();
                    Operation id3 = tab3.get(var3);
                    Term term3 = new Term(id3);

                    // there are 4 possible cases
                    Map<VarOrCode, Term> subst1 = new Hashtable<>();
                    subst1.put(var1, term1);
                    subst1.put(var2, term2);
                    Equation equ1 = instance(eq, subst1);
                    if (equ1 != null) {
                        pool.addElement(equ1);
                    }

                    Map<VarOrCode, Term> subst2 = new Hashtable<>();
                    subst2.put(var1, term1);
                    subst2.put(var3, term3);
                    Equation equ2 = instance(eq, subst2);
                    if (equ2 != null) {
                        pool.addElement(equ2);
                    }

                    Map<VarOrCode, Term> subst3 = new Hashtable<>();
                    subst3.put(var2, term2);
                    subst3.put(var3, term3);
                    Equation equ3 = instance(eq, subst3);
                    if (equ3 != null) {
                        pool.addElement(equ3);
                    }

                    Map<VarOrCode, Term> subst4 = new Hashtable<>();
                    subst4.put(var1, term1);
                    subst4.put(var2, term2);
                    subst4.put(var3, term3);
                    Equation equ4 = instance(eq, subst4);
                    if (equ4 != null) {
                        pool.addElement(equ4);
                    }

                }

                for (int i = 0; i < pool.size(); i++ ) {
                    eq = pool.elementAt(i);

                    if (eq.right.toString()
                                .indexOf(eq.left.toString()) != -1) {
                        continue;
                    }

                    eq.info = "system-introduced";
                    if (!equations.contains(eq)) {
                        equations.add(eq);
                    }

                }

            } catch (Exception e) {
                e.printStackTrace();
            }
        }

        engine.turnoff2Eq = false;

    }

    private Vector<Map<Variable, Operation>> getIdentityCompletionVariables(Term term) {

        Vector<Map<Variable, Operation>> result = new Vector<>();
        if (term.isVariable()) {
            return result;
        } else {
            Operation op = term.getTopOperation();
            Operation id = op.getIdentity();

            if (id != null) {
                Term[] subterms = term.getSubterms();
                if (subterms[0].isVariable()) {

                    if (subterms[0].getSort()
                                   .equals(id.getResultSort())
                        || this.less(id.getResultSort(), subterms[0].getSort())) {
                        Hashtable<Variable, Operation> tab = new Hashtable<>();
                        tab.put(subterms[0].getVariable(), id);
                        addElement(result, tab);
                    }
                } else {
                    Vector<Map<Variable, Operation>> mid =
                        getIdentityCompletionVariables(subterms[0]);
                    for (int i = 0; i < mid.size(); i++ ) {
                        Map<Variable, Operation> tab = mid.elementAt(i);
                        addElement(result, tab);
                    }
                }

                if (subterms[1].isVariable()) {
                    if (subterms[1].getSort()
                                   .equals(id.getResultSort())
                        || this.less(id.getResultSort(), subterms[1].getSort())) {
                        Map<Variable, Operation> tab = new Hashtable<>();
                        tab.put(subterms[1].getVariable(), id);
                        addElement(result, tab);
                    }
                } else {
                    Vector<Map<Variable, Operation>> mid =
                        getIdentityCompletionVariables(subterms[1]);
                    for (int i = 0; i < mid.size(); i++ ) {
                        Map<Variable, Operation> tab = mid.elementAt(i);
                        addElement(result, tab);
                    }
                }
            } else {
                Term[] subterms = term.getSubterms();
                for (Term subterm : subterms) {
                    Vector<Map<Variable, Operation>> mid = getIdentityCompletionVariables(subterm);
                    for (int j = 0; j < mid.size(); j++ ) {
                        Map<Variable, Operation> tab = mid.elementAt(j);
                        addElement(result, tab);
                    }
                }
            }

            return result;
        }
    }

    // XXXX This may be a problem
    private void addElement(Vector<Map<Variable, Operation>> vect,
                            Map<Variable, Operation> tab) {
        Iterator<Variable> e = tab.keySet()
                                  .iterator();
        Variable var = e.next();

        for (Map<Variable, Operation> tmp : vect) {
            if (tmp.containsKey(var)) {
                return;
            }
        }

        vect.addElement(tab);
    }

    private Equation instance(Equation eq,
                              Map<VarOrCode, Term> subst) {

        Term l = eq.left;
        Term r = eq.right;
        Term c = eq.condition;

        for (VarOrCode var : subst.keySet()) {
            Term term = subst.get(var);

            l = l.subst(this, var, term);
            r = r.subst(this, var, term);
            if (c != null) {
                c = c.subst(this, var, term);
            }
        }

        l = getNormalForm(l);
        r = getNormalForm(r);

        if (c != null) {
            c = getNormalForm(c);
        }

        if ((c == null || RewriteEngine.boolValue(c) == 1) && !l.equals(r) && !l.isSubterm(r)) {
            if (!equations.contains(eq)) {
                return new Equation(l, r);
            }
        }

        if (c != null && RewriteEngine.boolValue(c) != 1 && !l.equals(r) && !l.isSubterm(r)) {
            Equation eqtmp = new Equation(c, l, r);
            if (!equations.contains(eq)) {
                return eqtmp;
            }
        }
        return null;
    }

    public Operation[] getCobasisFor(Sort sort) {
        Operation[] ops = getCobasis();
        Vector<Operation> vec = new Vector<>();
        for (Operation op : ops) {
            for (Sort argumentSort : op.argumentSorts) {
                if (this.isSubsort(sort, argumentSort)) {
                    vec.addElement(op);
                    break;
                }
            }
        }

        Operation[] result = new Operation[vec.size()];
        vec.copyInto(result);
        return result;
    }

    private Hashtable<Sort, Equation> getHiddenSortPresentation() {
        Hashtable<Sort, Equation> result = new Hashtable<>();

        for (Equation eq : equations) {
            if (eq.left.sort.isHidden() && eq.right.sort.isHidden() && eq.condition == null
                && eq.right.var != null) {

                Variable[] vars = eq.left.getVariables();
                if (vars.length == 1 && vars[0].equals(eq.right.var)) {
                    result.put(eq.left.sort, eq);
                }
            }
        }

        return result;

    }

    private Term createTerm(Operation op,
                            Hashtable<String, Integer> varlist) {
        try {
            if (op.argumentSorts == null || op.argumentSorts.length == 0) {

                return new Term(op);

            } else {

                Term[] args = new Term[op.argumentSorts.length];
                for (int i = 0; i < args.length; i++ ) {
                    Sort sort = op.argumentSorts[i];
                    String sortName = sort.getName();
                    Object aInt = varlist.get(sortName);
                    if (aInt == null) {
                        Variable var = new Variable("~sysvar~" + sortName + "-" + 1, sort);
                        varlist.put(sortName, 1);
                        args[i] = new Term(var);
                    } else {
                        int k = ((Integer) aInt);
                        Variable var = new Variable("~sysvar~" + sortName + "-" + (k + 1), sort);
                        varlist.put(sortName, k + 1);
                        args[i] = new Term(var);
                    }
                }
                return new Term(op, args);

            }
        } catch (TermException e) {
            //System.out.println("bobj bug");
            return null;
        }

    }

    public Operation[] getCobasis() {

        Operation[] atts = getAttributes();
        Operation[] mths = getMethods();
        Hashtable<Sort, Equation> hsortPresent = getHiddenSortPresentation();

        // get all candidate operations for cobasis
        Vector<Operation> cobasis = new Vector<>();

        for (Operation mth : mths) {

            Hashtable<String, Integer> varlist = new Hashtable<>();
            Term mterm = createTerm(mth, varlist);
            Term orig = mterm;

            // handle hidden sort presentation
            for (int k = 0; k < mth.argumentSorts.length; k++ ) {
                Enumeration<Sort> ee = hsortPresent.keys();
                while (ee.hasMoreElements()) {
                    Sort sort = ee.nextElement();
                    if (sort.equals(mth.argumentSorts[k])) {
                        Equation eq = hsortPresent.get(sort);
                        Term term = eq.left.subst(this, eq.right.var, mterm.subterms[k]);
                        mterm = mterm.subst(this, mterm.subterms[k].var, term);
                        break;
                    }
                }
            }
            // end of handling

            for (Operation att : atts) {

                // check atts[j] (mths[i]), put all mths in pool

                if (!att.isConstant() && !att.info.equals("system-default")) {

                    for (int k = 0; k < att.argumentSorts.length; k++ ) {
                        if (this.isSubsort(mterm.sort, att.argumentSorts[k])) {

                            boolean done = false;

                            if (orig != mterm) {
                                Term tmp = createTerm(att, new Hashtable<>(varlist));
                                tmp = tmp.subst(this, tmp.subterms[k].var, orig);

                                boolean old = RewriteEngine.trace;
                                RewriteEngine.trace = false;
                                tmp = getNormalForm(tmp);
                                RewriteEngine.trace = old;

                                done = getMethods(tmp, cobasis);
                            }

                            if (!done) {
                                Term aterm = createTerm(att, new Hashtable<>(varlist));

                                aterm = aterm.subst(this, aterm.subterms[k].var, mterm);

                                boolean old = RewriteEngine.trace;
                                RewriteEngine.trace = false;
                                aterm = getNormalForm(aterm);
                                RewriteEngine.trace = old;

                                int index = cobasis.size();
                                if (!getMethods(aterm, cobasis) && !cobasis.contains(mth)) {

                                    cobasis.addElement(mth);

                                    if (orig != mterm) {
                                        // should remove some operations
                                        // from cobasis
                                        for (int p = index; p < cobasis.size(); p++ ) {
                                            cobasis.removeElementAt(index);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        for (int j = 0; j < cobasis.size(); j++ ) {
            Operation cop = cobasis.elementAt(j);
            if (!cop.isConstant()) {
                for (Operation mth : mths) {

                    if (!cobasis.contains(mth)) {

                        Hashtable<String, Integer> varlist = new Hashtable<>();
                        Term mterm = createTerm(mth, varlist);

                        // handle hidden sort presentation
                        for (int k = 0; k < mth.argumentSorts.length; k++ ) {

                            for (Sort sort : hsortPresent.keySet()) {
                                if (sort.equals(mth.argumentSorts[k])) {

                                    Equation eq = hsortPresent.get(sort);

                                    Term term =
                                        eq.left.subst(this, eq.right.var, mterm.subterms[k]);
                                    mterm = mterm.subst(this, mterm.subterms[k].var, term);

                                    break;
                                }
                            }
                        }
                        // end of handling

                        for (int k = 0; k < cop.argumentSorts.length; k++ ) {
                            if (isSubsort(mterm.sort, cop.argumentSorts[k])) {

                                Term aterm = createTerm(cop, new Hashtable<>(varlist));
                                aterm = aterm.subst(this, aterm.subterms[k].var, mterm);

                                aterm = getNormalForm(aterm);

                                if (!cobasisJudge(aterm, cobasis)) {
                                    cobasis.addElement(mth);
                                }
                            }
                        }
                    }
                }
            }
        }

        for (Operation att : atts) {
            if (!att.info.equals("system-default")) {
                for (Sort argumentSort : att.argumentSorts) {
                    if (argumentSort.isHidden()) {
                        cobasis.insertElementAt(att, 0);
                        break;
                    }
                }
            }
        }

        Operation[] result = new Operation[cobasis.size()];
        cobasis.copyInto(result);

        return result;
    }

    public Operation[] getCobasis(Vector<Operation> validOps) {

        Operation[] atts = getAttributes();
        Operation[] mths = getMethods();
        Hashtable<Sort, Equation> hsortPresent = getHiddenSortPresentation();

        // get all candidate operations for cobasis
        Vector<Operation> cobasis = new Vector<>();

        List<Operation> cols = new ArrayList<>();
        Map<Operation, List<Operation>> depend = new HashMap<>();
        Map<Operation, ArrayList<Term>> termMap = new HashMap<>();

        for (Operation mth : mths) {

            Hashtable<String, Integer> varlist = new Hashtable<>();
            Term mterm = createTerm(mth, varlist);

            // handle hidden sort presentation
            for (int k = 0; k < mth.argumentSorts.length; k++ ) {
                Enumeration<Sort> ee = hsortPresent.keys();
                while (ee.hasMoreElements()) {
                    Sort sort = ee.nextElement();
                    if (sort.equals(mth.argumentSorts[k])) {
                        Equation eq = hsortPresent.get(sort);
                        Term term = eq.left.subst(this, eq.right.var, mterm.subterms[k]);
                        mterm = mterm.subst(this, mterm.subterms[k].var, term);
                        break;
                    }
                }
            }
            // end of handling

            for (Operation att : atts) {

                // check atts[j] (mths[i]), put all mths in pool
                if (!att.isConstant() && !att.info.equals("system-default")) {

                    for (int k = 0; k < att.argumentSorts.length; k++ ) {
                        if (this.isSubsort(mterm.sort, att.argumentSorts[k])) {

                            Term aterm = createTerm(att, new Hashtable<>(varlist));
                            aterm = aterm.subst(this, aterm.subterms[k].var, mterm);

                            boolean old = RewriteEngine.trace;
                            RewriteEngine.trace = false;
                            aterm = getNormalForm(aterm);
                            RewriteEngine.trace = old;

                            if (!getMethods(aterm, cobasis) && !cobasis.contains(mth)) {
                                cobasis.addElement(mth);
                            } else if (isDirectObservation(aterm)) {
                                cols.add(mth);
                            }

                        }
                    }
                }
            }
        }

        for (int j = 0; j < cobasis.size(); j++ ) {
            Operation cop = cobasis.elementAt(j);
            if (!cop.isConstant()) {
                for (int i = 0; i < mths.length; i++ ) {

                    if (!cobasis.contains(mths[i])) {

                        Hashtable<String, Integer> varlist = new Hashtable<>();
                        Term mterm = createTerm(mths[i], varlist);

                        // handle hidden sort presentation
                        for (int k = 0; k < mths[i].argumentSorts.length; k++ ) {
                            for (Sort sort : hsortPresent.keySet()) {
                                if (sort.equals(mths[i].argumentSorts[k])) {
                                    Equation eq = hsortPresent.get(sort);
                                    Term term =
                                        eq.left.subst(this, eq.right.var, mterm.subterms[k]);
                                    mterm = mterm.subst(this, mterm.subterms[k].var, term);
                                    break;
                                }
                            }
                        }
                        // end of handling

                        for (int k = 0; k < cop.argumentSorts.length; k++ ) {
                            if (this.isSubsort(mterm.sort, cop.argumentSorts[k])) {

                                Term aterm = createTerm(cop, new Hashtable<>(varlist));
                                aterm = aterm.subst(this, aterm.subterms[k].var, mterm);

                                boolean old = RewriteEngine.trace;
                                RewriteEngine.trace = false;
                                aterm = getNormalForm(aterm);
                                RewriteEngine.trace = old;

                                Vector<String> flag = new Vector<>();
                                if (!cobasisJudge(aterm, cobasis, flag)) {
                                    cobasis.addElement(mths[i]);

                                } else if (flag.isEmpty() && !validOps.contains(mths[i])) {

                                    validOps.addElement(mths[i]);

                                    List<Operation> ops = new ArrayList<>();
                                    if (getDependent(aterm, cols, ops)) {
                                        List<Operation> obj = depend.get(mths[i]);
                                        if (obj != null) {
                                            ArrayList<Operation> tmp = (ArrayList<Operation>) obj;
                                            for (int q = 1; q < ops.size(); q++ ) {
                                                if (!tmp.contains(ops.get(i))) {
                                                    tmp.add(ops.get(i));
                                                }
                                            }
                                        } else {
                                            depend.put(mths[i], ops);
                                        }

                                    } else {
                                    }

                                    // save into termMap
                                    Object obj = termMap.get(mths[i]);
                                    if (obj == null) {
                                        ArrayList<Term> list = new ArrayList<>();
                                        list.add(aterm);
                                        termMap.put(mths[i], list);
                                    } else {
                                        @SuppressWarnings("unchecked")
                                        List<Term> list = (List<Term>) obj;
                                        list.add(aterm);
                                    }

                                }
                            }
                        }
                    }
                }
            }
        }

        for (Operation att : atts) {
            if (!att.info.equals("system-default")) {
                for (Sort argumentSort : att.argumentSorts) {
                    if (argumentSort.isHidden()) {
                        cobasis.insertElementAt(att, 0);
                        break;
                    }
                }
            }
        }

        Operation[] result = new Operation[cobasis.size()];
        cobasis.copyInto(result);

        // validOps is not correct, we need to check it again.

        //System.out.println("\ncols = "+cols);

        //System.out.println("\ndepend = "+depend);

        cols = new ArrayList<>();

        while (getCollapse(depend, cols)) {
        }
        ;

        //System.out.println("\nreal = "+cols);

        // get context preserved operations
        for (Operation col : cols) {
            termMap.remove(col);
        }

        //System.out.println("\ntermMap = "+termMap);

        ArrayList<Operation> pres = new ArrayList<>();
        Iterator<Operation> itor = termMap.keySet()
                                          .iterator();
        while (itor.hasNext()) {
            Operation key = itor.next();
            List<Term> terms = termMap.get(key);

            boolean all = true;
            for (Term term : terms) {
                if (!isValidForPreserved(term, key, cols, result)) {
                    all = false;
                    break;
                }
            }

            if (all) {
                pres.add(key);
            }

        }

        //System.out.println("\npres = "+pres);

        validOps.removeAllElements();
        for (Operation col : cols) {
            validOps.addElement(col);
        }

        for (Operation pre : pres) {
            validOps.addElement(pre);
        }

        //System.out.println("\nvalidOps = "+validOps);

        return result;
    }

    private static boolean isValidForPreserved(Term term,
                                               Operation op,
                                               List<Operation> cols,
                                               Operation[] cobasis) {

        if (term.var != null)
            return true;

        if (term.operation.equals(op)) {

            for (Term subterm : term.subterms) {

                if (subterm.sort.isHidden()) {

                    if (subterm.var != null) {

                    } else if (isFlatten(subterm)) {

                        boolean found = false;
                        for (Operation element : cobasis) {
                            if (element.equals(subterm.operation)) {
                                found = true;
                                break;
                            }
                        }

                        if (!found) {
                            return false;
                        }

                    } else {
                        return false;
                    }
                }
            }
            return true;

        } else if (cols.contains(term.operation)) {
            for (Term subterm : term.subterms) {
                if (subterm.sort.isHidden()) {
                    if (!isValidForPreserved(subterm, op, cols, cobasis)) {
                        return false;
                    }
                }
            }
            return true;

        } else {
            return false;
        }

    }

    private static boolean isFlatten(Term term) {

        if (term.var != null)
            return true;

        for (Term subterm : term.subterms) {
            if (subterm.sort.isHidden()) {
                if (subterm.var != null) {

                } else {
                    return false;
                }
            } else {

            }
        }

        return true;
    }

    private static boolean getCollapse(Map<Operation, List<Operation>> map,
                                       List<Operation> list) {

        for (Operation key : map.keySet()) {
            List<Operation> ops = map.get(key);

            boolean all = true;
            for (int i = 0; i < ops.size(); i++ ) {
                Operation op = ops.get(i);
                all = list.contains(op);
                if (!all) {
                    break;
                }
            }

            if (all) {
                list.add(key);
                map.remove(key);
                return true;
            }

        }

        return false;
    }

    private static boolean getDependent(Term term,
                                        List<Operation> list,
                                        List<Operation> result) {

        if (term.var == null) {

            boolean found = false;
            for (Term subterm : term.subterms) {

                if (!getDependent(subterm, list, result)) {
                    return false;
                }

                if (subterm.getSort()
                           .isHidden()) {
                    found = true;
                    break;
                }
            }

            if (found || term.operation.resultSort.isHidden()) {
                // check if term.operation is in the list
                if (list.contains(term.operation)) {
                    if (!result.contains(term.operation)) {
                        result.add(term.operation);
                    }
                } else {
                    return false;
                }
            }
        }

        return true;

    }

    private static boolean isDirectObservation(Term term) {

        if (term.var != null) {
            return true;
        } else if (term.operation.isBehavorial()) {

            // check whether it has hidden varable
            boolean found = false;
            for (Term subterm : term.subterms) {
                if (subterm.var != null && subterm.var.sort.isHidden()) {
                    found = true;
                    break;
                }
            }

            if (found) {
                return !term.operation.resultSort.isHidden();
            } else {
                for (Term subterm : term.subterms) {
                    if (!isDirectObservation(subterm)) {
                        return false;
                    }
                }
                return true;
            }

        } else {
            return false;
        }
    }

    private static boolean getMethods(Term term,
                                      Vector<Operation> vect) {

        boolean result = true;
        if (term.var != null) {
            return result;
        } else if (!term.operation.behavorial) {
            return false;
        } else if (term.operation.isMethod()) {
            boolean found = false;
            for (int i = 0; i < vect.size(); i++ ) {
                Operation op = vect.elementAt(i);
                if (op.equals(term.operation)) {
                    found = true;
                }
            }
            if (!found) {
                vect.addElement(term.operation);
            }

        }

        for (Term subterm : term.subterms) {
            result = getMethods(subterm, vect);
            if (!result) {
                return false;
            }
        }

        return result;

    }

    private boolean cobasisJudge(Term term,
                                 Vector<Operation> vect) {

        boolean result = true;

        if (term.var != null) {
            return true;
        } else if (!term.operation.behavorial) {
            return false;
        } else {
            boolean found = false;
            for (int i = 0; i < vect.size(); i++ ) {
                Operation op = vect.elementAt(i);
                if (op.equals(term.operation)) {
                    found = true;
                }
            }
            if (!found) {
                for (Term subterm : term.subterms) {
                    result = cobasisJudge(subterm, vect);
                    if (!result)
                        break; //return result;
                }
            } else {

                for (Term subterm : term.subterms) {
                    result = cobasisJudgeIn(subterm, vect);
                    if (!result) {
                        break; //return result;
                    }
                }
            }
        }
        return result;
    }

    private static boolean cobasisJudgeIn(Term term,
                                          Vector<Operation> vect) {

        boolean result = true;

        if (term.var != null) {
            return true;
        } else {
            boolean found = false;
            for (int i = 0; i < vect.size(); i++ ) {
                Operation op = vect.elementAt(i);
                if (op.equals(term.operation)) {
                    found = true;
                }
            }
            if (!found) {

                if (term.operation.info.equals("system-default")
                    || term.operation.name.equals("eq")) {
                    found = true;
                }

            }

            if (!found) {
                return false;
            } else {
                for (Term subterm : term.subterms) {
                    result = cobasisJudgeIn(subterm, vect);
                    if (!result)
                        return result;
                }
            }
        }

        return result;
    }

    private boolean cobasisJudge(Term term,
                                 Vector<Operation> vect,
                                 Vector<String> flag) {

        boolean result = true;

        if (term.var != null) {
            return true;
        } else if (!term.operation.behavorial) {
            return false;
        } else {
            boolean found = false;
            for (int i = 0; i < vect.size(); i++ ) {
                Operation op = vect.elementAt(i);
                if (op.equals(term.operation)) {
                    found = true;
                }
            }
            if (!found) {
                for (Term subterm : term.subterms) {
                    result = cobasisJudge(subterm, vect);
                    if (!result)
                        return result;
                }
            } else {
                for (Term subterm : term.subterms) {
                    result = cobasisJudgeIn(subterm, vect);
                    if (!result) {
                        return result;
                    } else {
                        boolean okay = true;
                        for (int j = 0; j < term.subterms.length && okay; j++ ) {
                            if (term.subterms[j].sort.isHidden()) {
                                okay = term.subterms[j].var != null;
                            }
                        }
                        if (okay) {
                            flag.addElement("*");
                        }
                    }
                }
            }
        }

        return result;
    }

    public boolean behavioralReduce(Term left,
                                    Term right,
                                    Operation[] cobasis,
                                    boolean trace,
                                    CaseModule cm)
        throws BReduceException, IOException {

        Term oldLeft = left.copy(this);
        left.parent = null;
        left = getNormalForm(left);

        Term oldRight = right.copy(this);
        right.parent = null;
        right = getNormalForm(right);

        engine.cleanCache();

        if (left.equals(this, right)) {
            return true;
        } else if (left.sort.equals(right.sort) && left.sort.isHidden()) {

            Vector<BTerm> bterms = new Vector<>();
            bterms.addElement(new BTerm(left.sort, left, right, oldLeft, oldRight,
                                        new HashMap<String, Integer>()));

            Module module = this;
            Vector<Operation> validOps = new Vector<>();

            Operation[] mths = getMethods();
            for (Operation mth : mths) {
                boolean found = false;
                for (Operation element : cobasis) {
                    if (mth.equals(element)) {
                        found = true;
                    }
                }
                if (!found) {
                    validOps.addElement(mth);
                }
            }

            Equation eq = new Equation(left, right);
            Vector<Equation> assume = new Vector<>();
            assume.addElement(eq);

            if (trace) {
                String msg = "reduced to: " + left + " == " + right;
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                msg = "add rule (C" + assume.size() + ") : " + eq.toString()
                                                                 .substring(3);
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                writer.flush();
            }

            boolean result = module.behavioralReduce(bterms, assume, cobasis, validOps, trace, cm);

            return result;

        } else {
            return false;
        }
    }

    public boolean behavioralReduce(Term left,
                                    Term right,
                                    Term cterm,
                                    boolean trace,
                                    CaseModule cm)
        throws BReduceException, IOException {

        Module mod = this.clone();
        Map<VarOrCode, Term> v2t = new HashMap<>();
        if (cterm != null) {

            engine.cleanCache();
            engine.turnoff2Eq = true;

            cterm.parent = null;
            cterm.copy(this);

            cterm = getNormalForm(cterm);

            Variable[] vars = cterm.getVariables();
            for (Variable var : vars) {
                try {
                    Operation op = new Operation(var.name.toLowerCase(), var.sort);
                    mod.addOperation(op);
                    Term tmp = new Term(op);
                    v2t.put(var, tmp);
                } catch (Exception e) {
                }
            }

            Term cond = cterm.subst(v2t, mod);
            try {
                mod = mod.toRules(cond);
            } catch (ModuleException e) {
                throw new BReduceException(e.getMessage());
            }
        }

        Term oldLeft, oldRight;
        if (cterm == null) {

            left.parent = null;
            oldLeft = left.copy(this);
            left = getNormalForm(left);

            right.parent = null;
            oldRight = right.copy(this);
            right = getNormalForm(right);

            engine.cleanCache();
            engine.turnoff2Eq = false;

        } else {

            left.parent = null;
            oldLeft = left.copy(this);
            left = mod.getNormalForm(left.subst(v2t, mod));

            right.parent = null;
            oldRight = right.copy(this);
            right = mod.getNormalForm(right.subst(v2t, mod));

            engine.cleanCache();
            engine.turnoff2Eq = false;

        }

        if (left.equals(this, right)) {
            return true;
        } else if (left.sort.equals(right.sort) && left.sort.isHidden()) {

            if (cm != null) {
                cm.cond = cterm;
                String string = caseAnalyse(left, right, cm, new Vector<Equation>(), true);
                cm.cond = null;

                if (string != null) {
                    if (trace) {
                        writer.write("-------------------------------\n");
                        writer.flush();
                    }

                    return true;
                } else if (CaseModule.errMsg != null) {

                    if (trace) {
                        writer.flush();
                    }

                    CaseModule.errMsg = null;
                }

            }

            if (cterm != null) {
                left = getNormalForm(oldLeft);
                right = getNormalForm(oldRight);
            }

            Vector<BTerm> bterms = new Vector<>();
            BTerm bt = new BTerm(left.sort, left, right, oldLeft, oldRight,
                                 new Hashtable<String, Integer>());
            if (cterm != null) {
                bt.cond = cterm;
            }

            bterms.addElement(bt);
            Module module = this;
            Vector<Operation> validOps = new Vector<>();
            Operation[] cobasis = module.getCobasis(validOps);

            // add Nov.19, 2002
//	    /*
//	    Operation[] mths = getMethods();
//	    validOps = new Vector();
//	    for (int i=0; i<mths.length; i++) {
//		boolean found = false;
//		for (int j=0; j<cobasis.length; j++) {
//		    if (mths[i].equals(cobasis[j])) {
//			found = true;
//		    }
//		}
//		if (!found) {
//		    validOps.addElement(mths[i]);
//		}
//	    }
//	    */
            // end

            // check validOps again
//               validOps = getValidOperation(cobasis, validOps);

            Equation eq = new Equation(left, right);

            if (cterm != null) {
                eq.condition = cterm;
            }

            Vector<Equation> assume = new Vector<>();
            assume.addElement(eq);

            if (trace) {
                String msg = "reduced to: " + left + " == " + right;
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                msg = "add rule (C" + assume.size() + ") : " + eq.toString()
                                                                 .substring(3);
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                writer.flush();
            }

            boolean result = module.behavioralReduce(bterms, assume, cobasis, validOps, trace, cm);

            return result;

        } else {

            // try case analyis here
            if (cm != null) {

                cm.cond = cterm;
                String string = caseAnalyse(oldLeft, oldRight, cm, new Vector<Equation>(), trace);
                cm.cond = null;

                if (string != null) {
                    if (trace) {
                        //writer.write(string);
                        writer.write("-------------------------------\n");
                        writer.flush();
                    }

                    return true;
                } else if (CaseModule.errMsg != null) {

                    if (trace) {
                        //writer.write(cm.errMsg);
                        writer.flush();
                    }

                    CaseModule.errMsg = null;
                }

            }
            System.out.println("--------> cccc");
            return false;
        }

    }

    public boolean behavioralReduce(Term left,
                                    Term right,
                                    Term cterm,
                                    Operation[] cobasis,
                                    boolean trace,
                                    CaseModule cm)
        throws BReduceException, IOException {

        Module mod = this.clone();
        Hashtable<VarOrCode, Term> v2t = new Hashtable<>();
        Term oldCond = null;

        if (cterm != null) {

            RewriteEngine re = new RewriteEngine(this);
            re.cleanCache();
            re.turnoff2Eq = true;
            re.turnoff3Eq = true;
            cterm.parent = null;
            oldCond = cterm.copy(this);

            cterm = re.reduce(cterm);
            re.turnoff2Eq = false;
            re.turnoff3Eq = false;

            Variable[] vars = cterm.getVariables();
            for (Variable var : vars) {
                try {
                    Operation op = new Operation(var.name.toLowerCase(), var.sort);
                    mod.addOperation(op);
                    Term tmp = new Term(op);
                    v2t.put(var, tmp);
                } catch (Exception e) {
                }
            }

            Term cond = cterm.subst(v2t, mod);
            try {
                mod = mod.toRules(cond);
            } catch (ModuleException e) {
                throw new BReduceException(e.getMessage());
            }
        }

        Term oldLeft, oldRight;
        if (cterm == null) {

            left.parent = null;
            oldLeft = left.copy(this);
            left = getNormalForm(left);

            right.parent = null;
            oldRight = right.copy(this);
            right = getNormalForm(right);

            engine.cleanCache();
            engine.turnoff2Eq = false;
        } else {

            left.parent = null;
            oldLeft = left.copy(this);
            left = mod.getNormalForm(left.subst(v2t, mod));

            right.parent = null;
            oldRight = right.copy(this);
            right = mod.getNormalForm(right.subst(v2t, mod));

            engine.cleanCache();
            engine.turnoff2Eq = false;
        }

        if (left.equals(this, right)) {
            return true;
        } else if (left.sort.equals(right.sort) && left.sort.isHidden()) {

            if (cterm != null) {
                left = getNormalForm(oldLeft);
                right = getNormalForm(oldRight);
            }

            Vector<BTerm> bterms = new Vector<>();
            BTerm bt = new BTerm(left.sort, left, right, oldLeft, oldRight,
                                 new Hashtable<String, Integer>());
            if (cterm != null) {
                bt.cond = oldCond;

                if (cm != null)
                    cm.cond = oldCond;
            }

            bterms.addElement(bt);
            Module module = this;
            Vector<Operation> validOps = new Vector<>();

            // add Nov.19, 2002
            Operation[] mths = getMethods();
            for (Operation mth : mths) {
                boolean found = false;
                for (Operation element : cobasis) {
                    if (mth.equals(element)) {
                        found = true;
                    }
                }
                if (!found) {
                    validOps.addElement(mth);
                }
            }
            // end

            Equation eq = new Equation(left, right);

            if (cterm != null) {
                eq.condition = oldCond;
            }

            Vector<Equation> assume = new Vector<>();
            assume.addElement(eq);

            if (trace) {
                String msg = "reduced to: " + left + " == " + right;
                if (cterm != null) {
                    msg += " if " + oldCond;
                }
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                msg = "add rule (C" + assume.size() + ") : " + eq.toString()
                                                                 .substring(3);
                writer.write(format(msg, 0) + "\n");
                writer.write("-----------------------------------------\n");
                writer.flush();
            }

            boolean result = module.behavioralReduce(bterms, assume, cobasis, validOps, trace, cm);
            if (cm != null) {
                cm.cond = null;
            }

            return result;

        } else {
            // try case analyis here
            if (cm != null) {
                cm.cond = cterm;
                String string = caseAnalyse(oldLeft, oldRight, cm, new Vector<Equation>(), trace);

                if (string != null) {
                    if (trace) {
                        //writer.write(string);
                        writer.write("-------------------------------\n");
                        writer.flush();
                    }

                    return true;
                } else if (CaseModule.errMsg != null) {

                    if (trace) {
                        //writer.write(cm.errMsg);
                        writer.flush();
                    }

                    CaseModule.errMsg = null;
                }

            }
            return false;
        }
    }

    private boolean behavioralReduce(Vector<BTerm> bterms,
                                     Vector<Equation> assume,
                                     Operation[] cobasis,
                                     Vector<Operation> validOps,
                                     boolean trace,
                                     CaseModule cm)
        throws BReduceException, IOException {

        Vector<Equation> eqs = new Vector<>();
        long startTime = new Date().getTime();

        while (!bterms.isEmpty()) {

            BTerm pair = bterms.firstElement();
            bterms.removeElementAt(0);

            BTerm[] res = stepBehavioralDedudction(pair, assume, cobasis, validOps, trace, cm);

            if (res == null) {

                for (int i = 0; i < eqs.size(); i++ ) {
                    equations.remove(eqs.elementAt(i));
                }
                return false;

            } else {
                for (BTerm re : res) {
                    Equation eq;
                    if (re.cond == null) {
                        eq = new Equation(re.left, re.right);
                    } else {
                        eq = new Equation(re.cond, re.left, re.right);
                    }
                    assume.addElement(eq);
                    bterms.addElement(re);

                    if (trace) {
                        String msg = "add rule (C" + assume.size() + ") : " + eq.toString()
                                                                                .substring(3);
                        writer.write(format(msg, 0) + "\n");
                        writer.write("--------------------" + "---------------------\n");
                        writer.flush();
                    }
                }
            }

            long now = new Date().getTime();
            if (now - startTime > 600000) {
                throw new BReduceException();
            }
        }

        for (int i = 0; i < eqs.size(); i++ ) {
            equations.remove(eqs.elementAt(i));
        }
        return true;

    }

    private BTerm[] stepBehavioralDedudction(BTerm pair,
                                             Vector<Equation> assume,
                                             Operation[] cobasis,
                                             Vector<Operation> validOps,
                                             boolean trace,
                                             CaseModule cm)
        throws IOException {

        Vector<BTerm> pool = new Vector<>();

        for (Operation element : cobasis) {
            BTerm[] pairs = stepBehavioralDedudction(pair, assume, element, validOps, trace, cm);
            if (pairs == null) {
                return null;
            } else {
                for (BTerm pair2 : pairs) {
                    pool.addElement(pair2);
                }
            }
        }

        BTerm[] result = new BTerm[pool.size()];
        pool.copyInto(result);
        return result;

    }

    private BTerm[] stepBehavioralDedudction(BTerm pair,
                                             Vector<Equation> assume,
                                             Operation op,
                                             Vector<Operation> validOps,
                                             boolean trace,
                                             CaseModule cm)

        throws IOException {

        Vector<BTerm> pool = new Vector<>();
        for (int i = 0; i < op.argumentSorts.length; i++ ) {
            if (this.isSubsort(pair.left.sort, op.argumentSorts[i])
                && this.isSubsort(pair.right.sort, op.argumentSorts[i])) {

                if (trace) {
                    //String msg = "target is: "+pair.left+" == "+pair.right;
                    String msg = "target is: " + pair.oldLeft + " == " + pair.oldRight;

                    if (pair.cond != null) {
                        msg += " if " + pair.cond;
                    }
                    writer.write(format(msg, 0) + "\n");
                    writer.write("expand by: " + toString(op) + "\n");
                    writer.flush();
                }

                Module mod = this.clone();
                Hashtable<VarOrCode, Term> v2t = new Hashtable<>();
                if (pair.cond != null) {
                    Variable[] vars = pair.cond.getVariables();
                    for (Variable var : vars) {
                        try {
                            Operation opt = new Operation(var.name.toLowerCase(), var.sort);
                            mod.addOperation(opt);
                            Term tmp = new Term(opt);
                            v2t.put(var, tmp);
                        } catch (Exception e) {
                        }
                    }

                    Term cond = pair.cond.subst(v2t, mod);

                    RewriteEngine re = new RewriteEngine(mod);
                    re.cleanCache();
                    re.turnoff2Eq = true;
                    re.turnoff3Eq = true;
                    cond = mod.getNormalForm(cond);
                    re.turnoff2Eq = false;
                    re.turnoff2Eq = false;

                    try {
                        mod = mod.toRules(cond);
                    } catch (Exception e) {
                    }
                }

                Hashtable<String, Integer> vars = new Hashtable<>(pair.varlist);
                Term term = createTerm(op, vars);

                // test: 10/10/2002
                if (!(op.resultSort instanceof HiddenSort)) {
                    Hashtable<VarOrCode, Term> gst = new Hashtable<>();
                    for (int j = 0; j < op.argumentSorts.length; j++ ) {
                        if (j != i) {
                            Sort sort = op.argumentSorts[j];
                            String sortName = sort.getName();
                            try {
                                Operation c =
                                    new Operation("~sysconst~" + sortName + "-" + j, sort);
                                gst.put(term.subterms[j].var, new Term(c));
                                mod.addOperation(c);
                            } catch (Exception e) {
                            }
                        }
                    }

                    term = term.subst(gst, mod);

                }
                // end test

                /* for fixing a serious mistake in the algorithm
                 *
                 * Term oldLeft = term.subst(this, term.subterms[i].var, pair.left);
                 *
                 * Term oldRight = term.subst(this, term.subterms[i].var, pair.right); */

                Term oldLeft = term.subst(this, term.subterms[i].var, pair.oldLeft);

                Term oldRight = term.subst(this, term.subterms[i].var, pair.oldRight);

                Term l = oldLeft.copy(this);
                Term r = oldRight.copy(this);

                if (pair.cond != null) {
                    l = mod.getNormalForm(l.subst(v2t, mod));
                    r = mod.getNormalForm(r.subst(v2t, mod));
                } else {
                    l = getNormalForm(l);
                    r = getNormalForm(r);
                }

                if (op.resultSort.isHidden() && l.equals(this, r)) {
                    if (trace) {
                        writer.write("reduced to: true\n");
                        if (l.toString()
                             .length() < r.toString()
                                          .length()) {
                            writer.write("     nf: " + format(l.toString(), 7) + "\n");
                        } else {
                            writer.write("     nf: " + format(r.toString(), 7) + "\n");
                        }
                        writer.write("----------------------" + "-------------------\n");
                        writer.flush();
                    }
                    continue;
                }

                if (pair.cond == null) {
                    l = getCoindNormalForm(l, assume, validOps);
                    r = getCoindNormalForm(r, assume, validOps);
                } else {
                    l = mod.getCoindNormalForm(l, assume, validOps);
                    r = mod.getCoindNormalForm(r, assume, validOps);
                }

                @SuppressWarnings("unchecked")
                Vector<String> usedeq = (Vector<String>) l.helper.get("usedeq");
                if (usedeq == null)
                    usedeq = new Vector<>();
                @SuppressWarnings("unchecked")
                Vector<String> vt = (Vector<String>) r.helper.get("usedeq");
                if (vt != null) {
                    for (int k = 0; k < vt.size(); k++ ) {
                        String st = vt.elementAt(k);
                        if (!usedeq.contains(st)) {
                            usedeq.addElement(st);
                        }
                    }
                }

                String eqseq = "";
                for (int k = 0; k < usedeq.size(); k++ ) {
                    String st = usedeq.elementAt(k);
                    if (k == 0) {
                        eqseq += st;
                    } else {
                        eqseq += ", " + st;
                    }
                }

                boolean assumeUsed = (l.helper.get("coind-assume") != null)
                                     || (r.helper.get("coind-assume") != null);
                engine.cleanCache();

                String msg;
                if (assumeUsed) {
                    msg = "deduced using (" + eqseq + ") : " + l + " == " + r;
                } else {
                    msg = "reduced to: " + l + " == " + r;
                }

                if (op.resultSort.isHidden() && !l.equals(this, r)) {

                    if (trace) {
                        writer.write(format(msg, 0) + "\n");
                        writer.flush();
                    }

                    // apply case analysis here
                    if (cm != null) {

                        String string = mod.caseAnalyse(l, r, cm, assume, trace);
                        if (string != null) {
                            if (trace) {
                                //writer.write(string);
                                writer.flush();
                            }
                        } else {

                            if (CaseModule.errMsg != null) {
                                if (trace) {
                                    //writer.write(cm.errMsg);
                                    writer.flush();
                                    writer.write("case analysis failed\n");
                                }
                                CaseModule.errMsg = null;
                            }

                            // add at 10/18/2002
                            if (pair.cond != null) {

                                l = oldLeft.copy(this);
                                r = oldRight.copy(this);

                                l = getNormalForm(l);
                                r = getNormalForm(r);

                                l = getCoindNormalForm(l, assume, validOps);
                                r = getCoindNormalForm(r, assume, validOps);

                            }

                            BTerm bt = new BTerm(pair.sort, l, r, oldLeft, oldRight, vars);
                            if (pair.cond != null) {
                                bt.cond = pair.cond;
                            }
                            pool.addElement(bt);

                            //pool.addElement(new BTerm(pair.sort, l, r,vars));
                            //end change
                        }

                    } else if (pair.cond == null) {
                        pool.addElement(new BTerm(pair.sort, l, r, oldLeft, oldRight, vars));
                        BTerm bt = pool.elementAt(0);
                    } else {

                        Map<Term, VarOrCode> t2v = new Hashtable<>();
                        for (VarOrCode key : v2t.keySet()) {
                            t2v.put(v2t.get(key), key);
                        }

                        l = reverseSubst(l, t2v);
                        r = reverseSubst(r, t2v);

                        BTerm bt = new BTerm(pair.sort, l, r, oldLeft, oldRight, vars);
                        bt.cond = pair.cond;
                        pool.addElement(bt);
                    }

                } else if (!l.sort.isHidden() && !l.equals(this, r)) {

                    if (trace) {
                        writer.write(format(msg, 0) + "\n");
                        writer.flush();
                    }

                    // apply case analysis here

                    if (cm != null) {
                        //String string = caseAnalyse(l, r, cm);
                        String string;

                        if (pair.cond == null) {
                            string = caseAnalyse(l, r, cm, assume, trace);
                        } else {
                            //cm.cond = pair.cond;
                            string = mod.caseAnalyse(l, r, cm, assume, trace);
                        }

                        if (string != null && trace) {
                            //writer.write(string);
                            writer.flush();
                        } else if (string == null) {
                            if (trace) {
                                if (CaseModule.errMsg != null) {
                                    //writer.write(cm.errMsg);

                                    writer.write("case analysis failed\n");
                                    writer.flush();
                                    CaseModule.errMsg = null;
                                } else {
                                    writer.write("--------------------"
                                                 + "---------------------\n");
                                    writer.flush();
                                }

                            }
                            return null;
                        }
                    } else {
                        if (trace) {
                            writer.write("--------------------" + "---------------------\n");
                            writer.flush();
                        }

                        return null;
                    }
                } else if (trace) {
                    if (assumeUsed) {
                        writer.write("deduced using (" + eqseq + ") : true\n");
                        writer.flush();
                    } else {
                        writer.write("reduced to: true\n");
                        writer.flush();
                    }

                    if (l.toString()
                         .length() < r.toString()
                                      .length()) {
                        writer.write("     nf: " + format(l.toString(), 7) + "\n");
                        writer.flush();
                    } else {
                        writer.write("     nf: " + format(r.toString(), 7) + "\n");
                        writer.flush();
                    }
                }
                if (trace) {
                    writer.write("---------------------" + "--------------------\n");
                }

            }
        }

        BTerm[] result = new BTerm[pool.size()];
        pool.copyInto(result);

        return result;
    }

    public Term getCoindNormalForm(Term term,
                                   Vector<Equation> assume,
                                   Vector<Operation> validOps) {

        term.helper.remove("changed");

        boolean assumeUsed = false;
        boolean changed = false;
        Vector<String> usedeq = new Vector<>();

        if (term.helper.get("usedeq") != null) {
            usedeq = (Vector<String>) term.helper.get("usedeq");
        }

        Term result = this.getNormalForm(term);

        Term target = null;
        for (int i = 0; i < assume.size() && target == null; i++ ) {
            Equation eq = assume.elementAt(i);

            Term right = eq.right;
            Term cond = eq.condition;
            Map<VarOrCode, Term> var2term = result.getMatch(eq.left, this);

            if (var2term != null) {
                if (cond != null) {

                    Term tmp = cond.subst(var2term, this);
                    tmp = getNormalForm(tmp);
                    int res = RewriteEngine.boolValue(tmp);
                    if (res != 1)
                        continue;

                }

                target = right.subst(var2term, this);

                assumeUsed = true;
                if (!usedeq.contains(i + "")) {
                    usedeq.addElement("C" + (i + 1) + "");
                }

                if (target.operation != null) {
                    try {
                        Term tmp = target;
                        target = Term.getMinimumTerm(this, target.operation, target.subterms);
                        if (target == null) {
                            target = new Term(this, tmp.operation, tmp.subterms);
                        }
                    } catch (Exception ex) {
                        //ex.printStackTrace();
                    }
                }
            }
        }

        if (target != null) {
            target.helper.put("usedeq", usedeq);
            result = getCoindNormalForm(target, assume, validOps);
            result.helper.put("changed", "*");
        } else if (result.var == null) {

            boolean valid = false;
            for (int i = 0; i < validOps.size(); i++ ) {
                if (result.operation.equals(validOps.elementAt(i))) {
                    valid = true;
                    break;
                }
            }

            if (valid) {

                Term[] args = new Term[result.subterms.length];
                for (int i = 0; i < result.subterms.length; i++ ) {

                    args[i] = getCoindNormalForm(result.subterms[i], assume, validOps);

                    if (!assumeUsed) {

                        Object obj = args[i].helper.get("coind-assume");
                        @SuppressWarnings("unchecked")
                        Vector<String> vt = (Vector<String>) args[i].helper.get("usedeq");
                        if (obj != null) {
                            assumeUsed = true;

                            for (int j = 0; j < vt.size(); j++ ) {
                                String st = vt.elementAt(j);
                                if (st != null && !usedeq.contains(st)) {
                                    usedeq.addElement(st);
                                }
                            }

                        }
                    }

                    if (!changed) {
                        Object obj = args[i].helper.get("changed");
                        if (obj != null) {
                            changed = true;
                        }
                    }
                }
                try {
                    result = new Term(this, result.operation, args);
                    if (changed) {
                        result = getCoindNormalForm(result, assume, validOps);
                    }

                } catch (Exception e) {
                    e.printStackTrace();
                }
            }

        }

        if (assumeUsed) {
            result.helper.put("coind-assume", "*");
            result.helper.put("usedeq", usedeq);
        }

        return result;

    }

    protected static String format(String txt,
                                   int prefix) {

        String result = "";

        int size = prefix;
        StringTokenizer ster = new StringTokenizer(txt, " \n");
        while (ster.hasMoreTokens()) {
            String tmp = ster.nextToken();
            if (size + tmp.length() < 70) {
                result += tmp + " ";
                size += tmp.length() + 1;
            } else {
                result += "\n    " + tmp + " ";
                size = 5 + tmp.length();
            }
        }

        return result;
    }

    protected static String format(String txt,
                                   int prefix,
                                   int inv) {

        String result = "";

        String leading = "";
        for (int i = 0; i < inv; i++ ) {
            leading += " ";
        }

        int size = prefix;
        StringTokenizer ster = new StringTokenizer(txt, " \n");
        while (ster.hasMoreTokens()) {
            String tmp = ster.nextToken();
            if (size + tmp.length() < 70) {
                result += tmp + " ";
                size += tmp.length() + 1;
            } else {
                result += "\n" + leading + tmp + " ";
                size = 5 + tmp.length();
            }
        }

        return result;
    }

    protected void setWriter(Writer writer) {
        Module.writer = writer;
    }

    class BTerm {

        Sort sort;

        Term left;

        Term right;

        Term cond;

        Term oldLeft;

        Term oldRight;

        Map<String, Integer> varlist;

        protected BTerm(Sort sort,
                        Term left,
                        Term right,
                        Term oldLeft,
                        Term oldRight,
                        Map<String, Integer> varlist) {
            this.sort = sort;
            this.left = left;
            this.right = right;
            this.oldLeft = oldLeft;
            this.oldRight = oldRight;
            this.varlist = varlist;
        }

        @Override
        public String toString() {
            return left + "  ==  " + right;
        }

    }

    public Equation getEquation(String name) {

        for (Equation eq : equations) {
            if (eq.name != null && eq.name.equals(name)) {
                return eq;
            }
        }

        return null;

    }

    public Equation getGeneralEquation(String name) {
        for (Equation eq : generalEquations) {
            if (eq.name != null && eq.name.equals(name)) {
                return eq;
            }
        }

        return null;
    }

    public Equation[] getEquations() {
        Equation[] result = new Equation[equations.size()];
        for (int i = 0; i < equations.size(); i++ ) {
            result[i] = equations.get(i);
        }

        return result;
    }

    public Equation getRule(int number) {

        if (isBuiltIn()) {

            int index = 0;
            for (Equation eq : equations) {
                if (number - 1 == index) {
                    return eq;
                }
                index++ ;
            }

            for (Equation eq : generalEquations) {
                if (number - 1 == index) {
                    return eq;
                }
                index++ ;
            }

        } else {

            int index = 0;
            for (Equation eq : equations) {
                if (!eq.info.equals("system-default")) {
                    if (number - 1 == index) {
                        return eq;
                    }
                    index++ ;
                }
            }

            for (Equation eq : generalEquations) {
                if (!eq.info.equals("system-default")) {
                    if (number - 1 == index) {
                        return eq;
                    }
                    index++ ;
                }
            }

            for (Equation eq : equations) {
                if (eq.info.equals("system-default")) {
                    if (number - 1 == index) {
                        return eq;
                    }
                    index++ ;
                }
            }

        }

        return null;
    }

    public String showRules(boolean all) {
        boolean mask = isBuiltIn();
        String result = "";
        int count = 1;

        for (Equation eq : equations) {
            if (mask || !eq.info.equals("system-default")) {
                if (eq.name != null) {
                    result += "   " + eq + "\n";
                } else {
                    result += "   [" + count + "] " + eq + "\n";
                }
                count++ ;
            }
        }

        for (Equation eq : generalEquations) {
            if (!eq.info.equals("system-default")) {
                if (eq.name != null) {
                    result += "   " + eq + "\n";
                } else {
                    result += "   [" + count + "] " + eq + "\n";
                }
                count++ ;
            }
        }

        if (all) {
            for (Equation eq : equations) {
                if (eq.info.equals("system-default")) {
                    if (eq.name != null) {
                        result += "   " + eq + "\n";
                    } else {
                        result += "   [" + count + "] " + eq + "\n";
                    }
                    count++ ;
                }
            }
        }

        return result;
    }

    public String getLocalDefinitionForDynamic() {

        String result = "";

        result += modName;
        result += " is \n";

        if (!protectImportList.isEmpty()) {
            result += "   protecting";
            for (ModuleName element : protectImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        if (!extendImportList.isEmpty()) {
            result += "   extending";
            for (ModuleName element : extendImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        if (!useImportList.isEmpty()) {
            result += "   including";
            for (ModuleName element : useImportList) {
                result += " " + element;
            }
            result += " .\n";
        }

        // handle sorts
        String s = "";
        int count = 0;
        for (Sort tmp : sorts) {
            if (tmp.getInfo()
                   .equals("system-default")) {
                continue;
            }
            s += toString(tmp) + " ";
            count++ ;
        }
        if (count == 1) {
            result += "   sort " + s + " .\n";
        } else if (count > 1) {
            result += "   sorts " + s + " .\n";
        }

        // handle subsorts
        String stmp = toStringWithoutBuiltIn(subsorts);
        StringTokenizer st = new StringTokenizer(stmp, "\n");
        while (st.hasMoreTokens()) {
            result += "   " + st.nextToken()
                                .trim()
                      + "\n";
        }

        // handle variables
        for (Sort tmp : sorts) {
            if (tmp.getInfo()
                   .equals("system-default")) {
                continue;
            }
            Variable[] vars = getVariablesOnSort(tmp);
            if (vars.length == 1) {
                result += "   var ";
            } else if (vars.length > 1) {
                result += "   vars ";
            }

            for (Variable var : vars) {
                result += var.name + " ";
            }

            if (vars.length > 0) {
                result += ": " + toString(tmp) + " .\n";
            }
        }

        // handle constants
        Operation[] cs = getConstants();
        Map<Operation, List<Operation>> map = sort(cs);
        for (Operation c : map.keySet()) {
            List<Operation> list = map.get(c);

            if (list.size() == 1) {
                result += "   op ";
            } else {
                result += "   ops ";
            }

            for (Operation op : list) {
                if (op.name.indexOf(" ") != -1) {
                    result += "(" + op.name + ") ";
                } else {
                    result += op.name + " ";
                }
            }

            String tmp = toString(c);
            result += tmp.substring(4 + c.name.length()) + ".\n";

        }

        // handle non-constants
        for (Operation tmp : operations) {
            if (tmp.info.equals("system-default") || tmp.isConstant()) {
                continue;
            }
            result += "   " + toString(tmp) + ".\n";
        }

        // handle equations
        for (Equation tmp : equations) {
            if (tmp.info.equals("system-default") || tmp.info.equals("system-introduced")) {
                continue;
            }
            result += "   " + tmp + " .\n";
        }

        for (Equation tmp : generalEquations) {
            if (tmp.info.equals("system-default") || tmp.info.equals("system-introduced")) {
                continue;
            }
            result += "   " + tmp + " .\n";
        }

        result += "end\n";

        return result;
    }

    public String getLocalDefinitionWithoutHead() {
        return getLocalDefinitionForDynamic();
    }

    public void mask(Equation eq) {
        mask.add(eq);
    }

    public void maskAll() {
        mask.addAll(equations);
    }

    public void umask(Equation eq) {
        mask.remove(eq);
    }

    public void umaskAll() {
        mask.clear();
    }

    private String caseAnalyse(Term left,
                               Term right,
                               CaseModule cm,
                               Vector<Equation> assume,
                               boolean trace) {
        try {

            cm.failedCases = 0;
            cm.handledCases = 0;

            String name = null;
            if (this.isParameterized()) {
                for (int i = 0; i < paraModules.size(); i++ ) {
                    Module tmp = paraModules.get(i);
                    if (tmp.modName.equals(cm.base)) {
                        name = paraNames.get(i);
                        break;
                    }
                }
            }

            Term context = cm.context;
            if (name != null) {
                context = context.addAnnotation(name, this, new HashMap<ModuleName, Integer>());
            }

            Map<VarOrCode, Term> table = getMatch(left, context);

            if (table == null) {
                table = getMatch(right, context);
            }

            if (table != null) {

                String msg = "-------------------------------------------\n" + "case analysis by "
                             + cm.name + "\n" + "-------------------------------------------\n";
                if (trace) {
                    writer.write("-------------------------------------------\n"
                                 + "case analysis by " + cm.name + "\n"
                                 + "-------------------------------------------\n");
                    writer.flush();
                }

                Map<VarOrCode, Term> v2g = groundize(table);

                boolean inc = false;
                if (v2g.size() > 0) {
                    //msg += "introduce constant(s): \n";

                    if (trace) {
                        writer.write("introduce constant(s): \n");
                        writer.flush();
                    }

                    inc = true;
                }

                for (VarOrCode var : v2g.keySet()) {
                    Term term = v2g.get(var);
                    //msg += "    "+term+" for the variable "+var.name+"\n";

                    if (trace) {
                        writer.write("    " + term + " for the variable " + var.name + "\n");
                        writer.flush();
                    }

                    inc = true;
                }

                for (int i = 0; i < cm.cases.size(); i++ ) {

                    cm.handledCases++ ;

                    if (!inc && i == 0) {

                    } else if (trace) {
                        writer.write("-------------------------------\n");
                        writer.flush();
                    }

                    if (cm.labels.size() == 0) {

                        if (trace) {
                            writer.write("case " + (i + 1) + " : \n");
                            writer.flush();
                        }

                    } else if (trace) {
                        writer.write("case (" + cm.labels.get(i) + ") : \n");
                        writer.flush();
                    }

                    Module mod = this.clone();

                    List<Object> list = cm.cases.get(i);

                    for (int j = 0; j < list.size(); j++ ) {

                        Object obj = list.get(j);
                        Operation op = null;
                        Equation eq = null;

                        if (obj instanceof Operation)
                            op = (Operation) obj;
                        else if (obj instanceof Equation)
                            eq = (Equation) obj;
                        else throw new ModuleException("whoops");

                        if (op != null) {
                            if (trace) {
                                writer.write(format("add: " + cm.toString(op), 0, 10) + "\n");
                                writer.flush();
                            }

                        } else {

                            if (name != null) {
                                eq = eq.addAnnotation(name, this,
                                                      new HashMap<ModuleName, Integer>());
                            }

                            eq = new Equation(eq.left.subst(table, this),
                                              eq.right.subst(table, this));

                            mod.equations.add(eq);

                            if (j == 0) {

                                if (trace) {
                                    writer.write(format("assume: " + eq.left + " = " + eq.right, 0,
                                                        10)
                                                 + "\n");
                                    writer.flush();
                                }

                            } else if (trace) {
                                writer.write("        " + format(eq.left + " = " + eq.right, 0, 10)
                                             + "\n");
                                writer.flush();
                            }
                        }
                    }

                    // bug fix: 10/18/2002

                    if (cm.cond != null) {

                        Term cterm = cm.cond;
                        cterm = cterm.subst(v2g, this);

                        engine.cleanCache();
                        RewriteEngine re = new RewriteEngine(this);
                        engine.turnoff2Eq = true;
                        cterm.parent = null;
                        cterm = re.reduce(cterm);
                        engine.turnoff2Eq = false;

                        Variable[] vars = cterm.getVariables();
                        for (Variable var : vars) {
                            try {
                                Operation op = new Operation(var.name.toLowerCase(), var.sort);
                                mod.addOperation(op);
                                Term tmp = new Term(op);
                                v2g.put(var, tmp);
                            } catch (Exception e) {
                            }
                        }

                        cterm.subst(v2g, mod);
                        try {
                            int k = mod.equations.size();

                            // need to check condition is not false
                            engine.cleanCache();
                            //Term condTerm = mod.getNormalForm(cond.copy(this));
                            Term condTerm = cm.cond.copy(this);
                            condTerm.cleanFlag();
                            condTerm = condTerm.subst(v2g, this);
                            condTerm = mod.getNormalForm(condTerm);

                            //System.out.println("------------------");
                            //System.out.println("PRE = "+cm.cond);
                            //System.out.println("COND = "+cond);
                            //System.out.println("MN = "+condTerm);

                            if (condTerm.operation.equals(BoolModule.falseOp)) {
                                //msg += "the condition is false: "+cond+"\n";

                                if (trace) {
                                    writer.write(format("the condition is false: "
                                                        + cm.cond.subst(v2g, this), 8)
                                                 + "\n");
                                    writer.flush();
                                }

                                cm.failedCases++ ;

                                continue;
                            }

                            engine.cleanCache();

                            mod = mod.toRules(condTerm);
                            for (; k < mod.equations.size(); k++ ) {
                                Equation aEq = mod.equations.get(k);
                                //msg += "        "+
                                //       aEq.toString().substring(3)+"\n";

                                if (trace) {
                                    writer.write("        " + aEq.toString()
                                                                 .substring(3)
                                                 + "\n");
                                    writer.flush();
                                }
                            }

                        } catch (ModuleException e) {
                            return null;
                        }
                    }
                    // end fix

                    RewriteEngine engine = new RewriteEngine(mod);
                    engine.cleanCache();
                    engine.turnoff2Eq = false;

                    String line = "reduce: ";
                    Term l = left.copy(this);
                    l.cleanFlag();
                    l = l.subst(v2g, this);
                    line += l + " == ";
                    l = engine.reduce(l);
                    engine.cleanCache();

                    Term r = right.copy(this);
                    r.cleanFlag();
                    r = r.subst(v2g, this);
                    line += r + " \n";
                    r = engine.reduce(r);
                    engine.cleanCache();

                    if (l.equals(this, r)) {
                        //msg += format(line, 0)+"\n";
                        //msg += "    nf: true\n";

                        if (trace) {
                            writer.write(format(line, 0) + "\n");
                            writer.write("    nf: true\n");
                            writer.flush();
                        }

                    } else {

                        //msg += format(line, 0)+"\n";
                        //msg += "    "+format("nf: "+l+" == "+r, 8, 8)+"\n";
                        //msg += "-------------------------------\n";

                        if (trace) {
                            writer.write(format(line, 0, 8) + "\n");
                            writer.write("    " + format("nf: " + l + " == " + r, 8, 8) + "\n");
                            writer.write("-------------------------------\n");
                            writer.flush();
                        }

                        // try circular coinductive hypotheses here 10/13/2002
                        boolean changed = false;

                        for (int k = 0; k < assume.size(); k++ ) {
                            Equation assumeEq = assume.elementAt(k);
                            if (!assumeEq.isConditional()) {
                                Map<VarOrCode, Term> subst = engine.getMatch(l, assumeEq.left);
                                if (subst != null) {
                                    l = assumeEq.right.subst(subst, mod);
                                    changed = true;
                                }

                                subst = engine.getMatch(r, assumeEq.left);
                                if (subst != null) {
                                    r = assumeEq.right.subst(subst, mod);
                                    changed = true;
                                }
                            } else {

                                Map<VarOrCode, Term> subst = engine.getMatch(l, assumeEq.left);
                                if (subst != null) {

                                    Term cd = assumeEq.condition.subst(subst, mod);
                                    cd = engine.reduce(cd);

                                    if (cd.operation.equals(BoolModule.trueOp)) {
                                        l = assumeEq.right.subst(subst, mod);
                                        changed = true;
                                    }

                                }

                                /* subst = engine.getMatch(r, assumeEq.left); if (subst != null) { r
                                 * = assumeEq.right.subst(subst, mod); changed = true; } */

                            }

                        }

                        if (changed) {
                            //msg += format("deduce to : "+l+" == "+r, 0)+"\n";

                            if (trace) {
                                writer.write(format("deduce to : " + l + " == " + r, 0) + "\n");
                                writer.flush();
                            }

                            l = engine.reduce(l);
                            r = engine.reduce(r);

                            if (l.equals(this, r)) {
                                //msg += format(line, 0)+"\n";
                                //msg += "    nf: true\n";

                                if (trace) {
                                    writer.write(format(line, 0) + "\n");
                                    writer.write("    nf: true\n");
                                    writer.flush();
                                }

                            } else {
                                //msg += format(line, 0)+"\n";
                                //msg += format("nf: "+l+" == "+r, 0)+"\n";
                                //msg += "-------------------------------\n";

                                if (trace) {
                                    writer.write(format(line, 0) + "\n");
                                    writer.write(format("nf: " + l + " == " + r, 0) + "\n");
                                    writer.write("----------------" + "---------------\n");
                                    writer.flush();
                                }

                                // end test

                                CaseModule.errMsg = msg;
                                return null;
                            }
                        } else {
                            CaseModule.errMsg = msg;
                            return null;
                        }
                    }
                }

                if (trace) {
                    writer.write("-----------------------------------------\n");
                    writer.write("analyzed " + cm.handledCases + " cases, all cases succeeded\n");
                    if (cm.cond != null) {
                        writer.write("condition failed in " + cm.failedCases + " cases\n");
                    }
                    writer.flush();
                }

                return msg;
            }

            return null;

        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }

    }

    private Map<VarOrCode, Term> getMatch(Term term,
                                          Term pattern) {

        Map<VarOrCode, Term> table = term.getMatch(pattern, this);

        if (table != null) {
            return table;
        }

        if (term.operation != null) {
            for (Term subterm : term.subterms) {
                table = getMatch(subterm, pattern);
                if (table != null)
                    return table;
            }
        }

        return null;

    }

    private Map<VarOrCode, Term> groundize(Map<VarOrCode, Term> table) {

        ArrayList<Variable> vars = new ArrayList<>();
        for (VarOrCode var : table.keySet()) {
            Term term = table.get(var);
            Variable[] vs = term.getVariables();
            for (Variable element : vs) {
                if (!vars.contains(element)) {
                    vars.add(element);
                }
            }
        }

        Hashtable<VarOrCode, Term> result = new Hashtable<>();
        HashSet<String> set = new HashSet<>();
        for (Variable var : vars) {
            String cname = var.sort.getName()
                                   .substring(0, 1)
                                   .toLowerCase();

            if (cname.equals("0") || cname.equals("1") || cname.equals("2") || cname.equals("3")
                || cname.equals("4") || cname.equals("5") || cname.equals("6") || cname.equals("7")
                || cname.equals("8") || cname.equals("9")) {
                cname = "%" + cname;
            }

            int index = 1;
            String old = cname;
            while (getConstants(cname).length > 0 || set.contains(cname)) {
                cname = old + index;
                index++ ;
            }

            try {
                Operation cop = new Operation(cname, var.sort);
                Term term = new Term(cop);
                result.put(var, term);
                set.add(cname);
            } catch (Exception e) {
            }
        }

        for (VarOrCode var : table.keySet()) {
            Term term = table.get(var);
            term = term.subst(result, this);
            table.put(var, term);
        }

        return result;
    }

    public Module sum(Module module) throws SignatureException {
        int type = this.getType();
        if (module.getType() > type) {
            type = module.getType();
        }

        ModuleName resName = this.getModuleName()
                                 .sum(module.getModuleName());
        Module result = new Module(type, resName);
        result.protectedImport(this);
        result.protectedImport(module);

        return result;

    }

    public void setParametersLevel(int[] levels) {
        this.levels = levels;
    }

    private Module toRules(Term term) throws ModuleException {

        Module result = this.clone();

        if (term.sort.equals(BoolModule.boolSort) && term.sort.getInfo()
                                                              .equals("system-default")) {

            if (term.operation.equals(BoolModule.metaEq)) {
                Equation eq = new Equation(term.subterms[0], term.subterms[1]);
                result.addEquation(eq);
            } else if (term.operation.equals(BoolModule.and)) {

                result = result.toRules(term.subterms[0]);
                result = result.toRules(term.subterms[1]);

            } else {
                try {
                    Equation eq = new Equation(term, new Term(BoolModule.trueOp));
                    result.addEquation(eq);
                } catch (Exception e) {
                }
            }

        } else {
            throw new ModuleException("could not change " + term + " to equations");
        }

        return result;
    }

    private Term reverseSubst(Term term,
                              Map<Term, VarOrCode> t2v) {
        try {

            if (term.var != null) {
                return term;
            } else {

                Operation op = term.operation;
                if (op.isConstant()) {

                    VarOrCode var = null;
                    for (Term tm : t2v.keySet()) {
                        Operation tmp = tm.operation;
                        if (tmp.name.equals(op.name)) {
                            var = t2v.get(tm);
                            break;
                        }
                    }

                    if (var == null) {
                        return term;
                    } else {
                        return new Term((Variable) var);
                    }
                } else {

                    Term[] terms = new Term[term.subterms.length];
                    for (int i = 0; i < terms.length; i++ ) {
                        terms[i] = reverseSubst(term.subterms[i], t2v);
                    }

                    return new Term(this, op, terms);

                }

            }

        } catch (Exception e) {
            return null;
        }

    }

    public boolean containsTokenForModuleName(String string) {
        if (this.modName.containsToken(string)) {
            return true;
        }

        for (ModuleName mname : protectImportList) {
            if (mname.containsToken(string)) {
                return true;
            }
        }

        return false;

    }

    public Term setPerference(Term term) throws TermException {

        if (term.var == null) {

            Operation op = term.operation;
            Operation res = null;

            if (!op.modName.equals(this.modName)) {

                Operation[] ops = this.getOperationsWithName(op.getName());
                for (Operation op2 : ops) {
                    if (op2.modName.equals(this.modName)) {
                        if ((res == null) || op2.less(this, res)) {
                            res = op2;
                        }
                    }
                }

            }

            if (res == null) {
                res = op;
            }

            Term[] terms = new Term[term.subterms.length];
            for (int i = 0; i < term.subterms.length; i++ ) {
                terms[i] = setPerference(term.subterms[i]);
            }

            //System.out.println("res = "+res+"   "+term);
            return new Term(this, res, terms);

        }

        return term;
    }

    public boolean behavioralMultipleReduce(Term[] lefts,
                                            Term[] rights,
                                            Term[] cterms,
                                            boolean trace,
                                            CaseModule cm)
        throws BReduceException, IOException {

        Module module = this;
        Vector<Operation> validOps = new Vector<>();
        Operation[] cobasis = module.getCobasis(); //validOps);

        Operation[] mths = module.getMethods();
        for (Operation mth : mths) {
            boolean found = false;
            for (Operation element : cobasis) {
                if (mth.equals(element)) {
                    found = true;
                }
            }
            if (!found) {
                validOps.addElement(mth);
            }
        }

        Vector<Equation> assume = new Vector<>();
        Vector<BTerm> bterms = new Vector<>();

        for (int k = 0; k < lefts.length; k++ ) {

            Module mod = this.clone();
            Map<VarOrCode, Term> v2t = new HashMap<>();

            if (cterms[k] != null) {

                engine.cleanCache();
                engine.turnoff2Eq = true;

                cterms[k].parent = null;
                cterms[k].copy(this);
                cterms[k] = getNormalForm(cterms[k]);

                Variable[] vars = cterms[k].getVariables();
                for (Variable var : vars) {
                    try {
                        Operation op = new Operation(var.name.toLowerCase(), var.sort);
                        mod.addOperation(op);
                        Term tmp = new Term(op);
                        v2t.put(var, tmp);
                    } catch (Exception e) {
                    }
                }

                Term cond = cterms[k].subst(v2t, mod);
                try {
                    mod = mod.toRules(cond);
                } catch (ModuleException e) {
                    throw new BReduceException(e.getMessage());
                }
            }

            Term oldLeft, oldRight;
            if (cterms[k] == null) {

                lefts[k].parent = null;
                oldLeft = lefts[k].copy(this);
                lefts[k] = getNormalForm(lefts[k]);

                rights[k].parent = null;
                oldRight = rights[k].copy(this);
                rights[k] = getNormalForm(rights[k]);

                engine.cleanCache();
                engine.turnoff2Eq = false;

            } else {

                lefts[k].parent = null;
                oldLeft = lefts[k].copy(this);
                lefts[k] = mod.getNormalForm(lefts[k].subst(v2t, mod));

                rights[k].parent = null;
                oldRight = rights[k].copy(this);
                rights[k] = mod.getNormalForm(rights[k].subst(v2t, mod));

                engine.cleanCache();
                engine.turnoff2Eq = false;

            }

            if (lefts[k].equals(this, rights[k])) {

                String msg = "handled: " + oldLeft + " == " + oldRight;
                if (cterms[k] != null) {
                    msg += "if " + cterms[k];
                }
                writer.write(format(msg, 0) + "\n");
                writer.write("reduced to: true \n");

                msg = "nf: " + lefts[k];
                writer.write("    " + format(msg, 0, 8) + "\n");
                writer.write("-----------------------------------------\n");
                writer.flush();
                continue;

            } else if (lefts[k].sort.equals(rights[k].sort) && lefts[k].sort.isHidden()) {

                if (cterms[k] != null) {
                    lefts[k] = getNormalForm(oldLeft);
                    rights[k] = getNormalForm(oldRight);
                }

                BTerm bt = new BTerm(lefts[k].sort, lefts[k], rights[k], oldLeft, oldRight,
                                     new Hashtable<String, Integer>());
                if (cterms[k] != null) {
                    bt.cond = cterms[k];
                }

                bterms.addElement(bt);

                Equation eq = new Equation(lefts[k], rights[k]);

                if (cterms[k] != null) {
                    eq.condition = cterms[k];
                }

                assume.addElement(eq);

                if (trace) {
                    String msg = "handled: " + oldLeft + " == " + oldRight;
                    if (cterms[k] != null) {
                        msg += "if " + cterms[k];
                    }
                    writer.write(format(msg, 0) + "\n");

                    msg = "reduced to: " + lefts[k] + " == " + rights[k];
                    writer.write(format(msg, 0) + "\n");

                    msg = "add rule (C" + assume.size() + ") : " + eq.toString()
                                                                     .substring(3);
                    writer.write(format(msg, 0) + "\n");
                    writer.write("-----------------------------------------\n");
                    writer.flush();
                }

            } else // try case analyis here
                if (cm != null) {
                    cm.cond = cterms[k];
                    String string =
                        caseAnalyse(oldLeft, oldRight, cm, new Vector<Equation>(), trace);
                    cm.cond = null;

                    if (string != null) {
                        if (trace) {
                            writer.write("-------------------------------\n");
                            writer.flush();
                        }
                        continue;

                    } else if (CaseModule.errMsg != null) {
                        if (trace) {
                            writer.flush();
                        }
                        CaseModule.errMsg = null;
                    }
                } else {
                    return false;
                }

        }

        boolean result = module.behavioralReduce(bterms, assume, cobasis, validOps, trace, cm);
        return result;

    }

    @SuppressWarnings("unused")
    private Vector<Operation> getValidOperation(Operation[] cobasis,
                                                Vector<Operation> validOps) {

        return validOps;

//	/*
//	Vector result = new Vector();
//
//	for (int i=0; i<validOps.size(); i++) {
//	    boolean okay = true;
//            Operation op = (Operation)validOps.elementAt(i);
//
//	    for (int j=0; j<cobasis.length; j++) {
//
//		Hashtable varlist = new Hashtable();
//		Term inner = createTerm(op, varlist);
//		Term outer = createTerm(cobasis[j], (Hashtable)varlist.clone());
//
//                boolean succ = true;
//		for (int k=0; k<cobasis[j].argumentSorts.length; k++) {
//		    if (this.isSubsort(inner.sort,
//				       cobasis[j].argumentSorts[k])) {
//
//			Term tmp = outer.subst(this,
//					       outer.subterms[k].var,
//					       inner);
//			tmp = getNormalForm(tmp);
//
//			if (tmp.var == null) {
//			    if (tmp.sort.isHidden()) {
//				// three cases
//				// case1 : cobasis opeartion f
//
//				Operation f = tmp.operation;
//				boolean found = false;  // in cobasis
//				for (int p=0; p<cobasis.length; p++) {
//				    if (f.equals(cobasis[p])) {
//					found = true;
//					break;
//				    }
//				}
//
//				boolean yes = true;    // all variables
//				if (found) {
//				    for (int p=0; p<tmp.subterms.length; p++) {
//					if (tmp.subterms[p].var == null) {
//					    yes = false;
//					    break;
//					}
//				    }
//
//				    if (!yes) {
//					succ = false;
//					break;
//				    }
//
//				} else {
//
//				    // case2 : an opeartion g in result
//				    if (f.equals(op)) {
//					found = true;
//				    } else {
//					for (int p=0; p<result.size(); p++) {
//					    if (f.equals((Operation)result.elementAt(p))) {
//						found = true;
//						break;
//					    }
//					}
//				    }
//
//				    if (found) {
//					yes = true;
//					for (int p=0; p<tmp.subterms.length; p++) {
//					    if (tmp.subterms[p].var == null) {
//						Operation g = tmp.subterms[p].operation;
//						boolean inco = false;
//                                                for (int q=0; q<cobasis.length; q++) {
//						    inco = true;
//						    break;
//						}
//
//						if (inco) {
//						    boolean allvar = true;
//						    for (int q=0;
//							 q<tmp.subterms[p].subterms.length;
//							 q++) {
//							if (tmp.subterms[p].subterms[q].var ==
//							    null) {
//							    allvar = false;
//							    break;
//							}
//						    }
//
//						    if (!allvar) {
//							yes = false;
//							break;
//						    }
//						} else {
//						    yes = false;
//						    break;
//						}
//					    } //if
//					} //for
//
//					if (!yes) {
//					    succ = false;
//					    break;
//					}
//
//				    } else {
//					succ = false;
//					break;
//				    }
//
//				} // else
//
//
//			    } else {
//				// all opeartions are visible
//				succ = isAllVisible(tmp);
//			    }
//			} // if tmp.var
//		    }
//		}
//
//		if (!succ) {
//		    okay = false;
//		    break;
//		}
//
//	    }
//
//
//	    if (okay) {
//		result.addElement(op);
//	    }
//
//        }
//
//	return result;
//	*/
    }

    private boolean isAllVisible(Term term) {
        if (term.var != null) {
            return true;
        } else if (term.sort.isHidden()) {
            return false;
        } else {
            for (Term subterm : term.subterms) {
                if (!isAllVisible(subterm)) {
                    return false;
                }
            }
            return true;
        }
    }

}
