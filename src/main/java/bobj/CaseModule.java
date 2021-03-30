
package bobj;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;
import java.util.Vector;

public class CaseModule
                        extends
                        Module {
    /**
     *
     */
    private static final long serialVersionUID = 1L;

    ModuleName name, base;

    Term context, cond;

    List<List<Object>> cases;

    List<String> labels;

    static String errMsg;

    int handledCases, failedCases;

    public CaseModule(ModuleName name,
                      List<? extends Module> list)
        throws CaseModuleException {

        this(name, list.get(0));

        CaseModule mod = (CaseModule) list.get(0);
        this.base = mod.base;
        this.context = mod.context;

        // check and input variables
        List<List<List<Object>>> tmpCases = new ArrayList<>();
        tmpCases.add(mod.cases);

        List<List<String>> tmpLabels = new ArrayList<>();
        if (mod.labels.size() == 0) {
            ArrayList<String> tmp = new ArrayList<>();
            for (int i = 0; i < mod.cases.size(); i++ ) {
                tmp.add(String.valueOf(i + 1));
            }
            tmpLabels.add(tmp);
        } else {
            tmpLabels.add(mod.labels);
        }

        for (int j = 0; j < mod.vars.size(); j++ ) {
            Variable var = mod.vars.elementAt(j);
            if (!this.containsVariable(var)) {
                try {
                    this.addVariable(var);
                } catch (SignatureException e) {
                    throw new CaseModuleException(e.getMessage());
                }
            }
        }

        for (int i = 1; i < list.size(); i++ ) {
            mod = (CaseModule) list.get(i);

            if (!mod.base.equals(this.base)) {
                throw new CaseModuleException(mod.name + " is not on the base " + this.base);
            }

            if (!mod.context.equals(this.context) && !mod.context.isSubterm(this.context)) {
                throw new CaseModuleException(mod.context + " is not coherent to " + this.context);
            }

            for (int j = 0; j < mod.vars.size(); j++ ) {
                Variable var = mod.vars.elementAt(j);
                if (!this.containsVariable(var)) {
                    try {
                        this.addVariable(var);
                    } catch (SignatureException e) {
                        throw new CaseModuleException(e.getMessage());
                    }
                }
            }

            tmpCases.add(mod.cases);
            if (mod.labels.size() == 0) {
                ArrayList<String> tmp = new ArrayList<>();
                for (int j = 0; j < mod.cases.size(); j++ ) {
                    tmp.add(String.valueOf(j + 1));
                }
                tmpLabels.add(tmp);
            } else {
                tmpLabels.add(mod.labels);
            }
        }

        List<String> resLabels = new ArrayList<>();
        this.cases = makeCases(tmpCases, tmpLabels, resLabels);
        this.labels = resLabels;

    }

    public CaseModule(ModuleName name,
                      Module module) {
        super(Module.INITIAL, name);

        this.name = name;
        this.base = module.modName;
        this.cases = new ArrayList<>();
        this.labels = new ArrayList<>();

        Module tmp = module.clone();

        // clone signature part
        this.sorts = new Vector<>(tmp.sorts);
        this.subsorts = (Subsort) tmp.subsorts.clone();
        this.operations = new Vector<>(tmp.operations);
        this.tokens = new Vector<>(tmp.tokens);
        this.compatible = new HashMap<>();
        this.alias = new HashMap<>(tmp.alias);
        this.parameters = tmp.parameters;
        this.firsts = new ArrayList<>(tmp.firsts);
        this.lasts = new ArrayList<>(tmp.lasts);
        this.balancedBrackets = tmp.balancedBrackets;
        this.explicitRetract = tmp.explicitRetract;

        // clone module parts
        this.paraModules = new ArrayList<>(tmp.paraModules);
        this.paraNames = new ArrayList<>(tmp.paraNames);
        this.protectImportList = new ArrayList<>(tmp.protectImportList);
        this.extendImportList = new ArrayList<>(tmp.extendImportList);
        this.useImportList = new ArrayList<>(tmp.useImportList);

        this.equations = new ArrayList<>();
        Iterator<Equation> itor = tmp.equations.iterator();
        while (itor.hasNext()) {
            Equation eq = itor.next();
            this.equations.add(eq);
        }

        this.generalEquations = new ArrayList<>();
        itor = tmp.generalEquations.iterator();
        while (itor.hasNext()) {
            Equation eq = itor.next();
            this.generalEquations.add(eq);
        }

        this.props = new HashMap<>(tmp.props);

    }

    public void setContext(Term term) {
        this.context = term;
    }

    @Override
    public String toString() {
        String result = "";
        result = "cases " + this.name + " for " + this.base + " is \n";

        // handle variables
        for (Sort tmp : this.sorts) {
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

        // context
        result += "   context " + this.context + " .\n";

        // cases
        for (int i = 0; i < this.cases.size(); i++ ) {
            if (this.labels.size() > 0) {
                result += "   case (" + this.labels.get(i) + ") :\n";
            } else {
                result += "   case \n";
            }

            List<Object> list = this.cases.get(i);
            for (Object obj : list) {
                if (obj instanceof Operation) {
                    result += "     " + this.toString((Operation) obj) + " .\n";

                } else {
                    result += "     " + obj + " .\n";
                }
            }
        }

        result += "end\n";

        return result;
    }

    private List<List<Object>> makeCases(List<List<List<Object>>> tmpCases,
                                         List<List<String>> llist,
                                         List<String> res) {

        List<List<Object>> result = new ArrayList<>();

        if (tmpCases.size() == 1) {
            List<List<Object>> tmp = tmpCases.get(0);
            result = new ArrayList<>(tmp);

            List<String> ltmp = llist.get(0);
            res.addAll(ltmp);

            return result;
        }

        List<List<List<Object>>> copy = new ArrayList<>(tmpCases);
        List<List<Object>> first = copy.get(0);
        copy.remove(0);

        List<List<String>> lcopy = new ArrayList<>(llist);
        List<String> lfirst = lcopy.get(0);
        lcopy.remove(0);

        List<String> ltmp = new ArrayList<>();
        List<List<Object>> tmp = makeCases(copy, lcopy, ltmp);
        for (int i = 0; i < first.size(); i++ ) {
            for (int j = 0; j < tmp.size(); j++ ) {
                List<Object> element = first.get(i);
                List<Object> aCase = tmp.get(j);
                List<Object> mid = new ArrayList<>();
                mid.addAll(element);
                mid.addAll(aCase);
                result.add(mid);
            }
        }

        for (int i = 0; i < lfirst.size(); i++ ) {
            for (int j = 0; j < ltmp.size(); j++ ) {
                String aStr = lfirst.get(i);
                String bStr = ltmp.get(j);
                res.add(aStr + "," + bStr);
            }
        }

        return result;

    }

    public void remove(String label) throws CaseModuleException {

        if (this.labels.isEmpty()) {
            try {
                int i = Integer.parseInt(label);
                this.cases.remove(i - 1);
            } catch (Exception e) {
                throw new CaseModuleException("no case in " + this.name + " with name " + label);
            }
        } else if (this.labels.contains(label)) {

            int i = this.labels.indexOf(label);
            this.cases.remove(i);
            this.labels.remove(i);

        } else if (label.indexOf("*") != -1) {

            for (int k = this.labels.size() - 1; k >= 0; k-- ) {
                String tmp = this.labels.get(k);
                if (match(label, tmp)) {
                    this.cases.remove(k);
                    this.labels.remove(k);
                }
            }

        } else {
            throw new CaseModuleException("no case in " + this.name + " with name " + label);
        }

    }

    static private boolean match(String pattern,
                                 String string) {

        boolean result = true;

        StringTokenizer st1 = new StringTokenizer(pattern, ",");
        StringTokenizer st2 = new StringTokenizer(string, ",");

        while (st1.hasMoreTokens()) {
            String s1 = st1.nextToken();
            String s2 = st2.nextToken();
            if (s1.equals("*")) {
                continue;
            } else if (!s1.equals(s2)) {
                return false;
            }
        }

        return result;

    }

}
