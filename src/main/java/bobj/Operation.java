
package bobj;

import java.io.Serializable;
import java.util.Map;
import java.util.Stack;
import java.util.StringTokenizer;
import java.util.Vector;

/**
 *
 * a class representing the operation in the first order signature.
 *
 * @author Kai Lin
 * @version %I% %G%
 * @see Sort
 * @see Variable
 * @see Signature
 */
public class Operation
                       implements Serializable, ModNameSubexp, ViewRenamable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    String name;

    ModuleName modName;

    Sort[] argumentSorts;

    String[] argumentNames;

    Sort resultSort;

    String resultName;

    int priority;

    boolean isAssociative;

    boolean isCommutative;

    boolean isIdempotent;

    Operation id;

    Operation implicitId;

    boolean behavorial;

    String[] gather;

    int[] strategy;

    String info;

    Vector<Object> prod;

    static boolean debug = false;

    /**
     * create an operaion by the specified name and the sorts of arguments and the sort of result.
     *
     * @param na
     *            the string of the name of this operation, where "_" is used as the declaration of
     *            argument position
     * @param args
     *            the sort array of arguments
     * @param res
     *            the sort of result
     * @return an operaion with the specified name and the sorts of arguments and the sort of
     *         result. Its priority is minimum, has no defined properties and information.
     * @exception SignatureException
     *                if na is in mix notation and has different arguments as args, or na is empty
     *                string.
     */
    public Operation(String name,
                     Sort[] args,
                     Sort res,
                     ModuleName modName)
        throws SignatureException {

        if (name.trim()
                .equals("")) {
            throw new SignatureException("Empty string can't be" + " operation name");
        }

        //inputname = na.trim();
        this.name = normalize(name.trim());
        this.modName = modName;
        this.info = "";
        this.argumentSorts = args;
        this.resultSort = res;

        //check the consistence of arguments.
        if (name.indexOf("_") != -1) {
            int count = 0;
            String s = name;
            int k = s.indexOf("_");
            while (k != -1) {
                count++ ;
                s = s.substring(k + 1);
                k = s.indexOf("_");
            }
            if (count != args.length) {
                throw new SignatureException("Expect " + count + " argument(s) for operation "
                                             + name);
            }
        }

        //set priority.
        //priority = Integer.valueOf(Integer.MAX_VALUE).intValue();

        if ((name.trim()
                 .indexOf("_") == -1)
            || (!name.trim()
                     .startsWith("_")
                && !name.trim()
                        .endsWith("_"))) {
            this.priority = 0;
        } else if (!name.trim()
                        .startsWith("_")
                   && name.trim()
                          .endsWith("_")
                   && this.argumentSorts.length == 1) {
                       this.priority = 15;
                   } else {
                       this.priority = 41;
                   }

        //set properties.
        this.isAssociative = false;
        this.isCommutative = false;
        this.isIdempotent = false;
        this.behavorial = true;

        //set information
        this.info = "";

        //set prod
        this.prod = new Vector<>();
        if (args.length == 0) {
            StringTokenizer ster = new StringTokenizer(name, " ");
            while (ster.hasMoreTokens()) {
                this.prod.addElement(ster.nextToken());
            }

        } else if (name.indexOf("_") != -1) {
            String stmp = name;
            int index = stmp.indexOf("_");
            int count = 0;
            while (index != -1) {
                String st = stmp.substring(0, index)
                                .trim();
                if (!st.equals("")) {
                    //prod.addElement(st);
                    StringTokenizer ster = new StringTokenizer(st, " ");
                    while (ster.hasMoreTokens()) {
                        this.prod.addElement(ster.nextToken());
                    }
                }
                this.prod.addElement(args[count]);
                count++ ;
                stmp = stmp.substring(index + 1);
                index = stmp.indexOf("_");
            }
            if (!stmp.equals("")) {
                StringTokenizer ster = new StringTokenizer(stmp, " ");
                while (ster.hasMoreTokens()) {
                    this.prod.addElement(ster.nextToken());
                }
            }
        } else {
            this.prod.addElement(name);
            this.prod.addElement("(");
            for (int i = 0; i < args.length; i++ ) {
                this.prod.addElement(args[i]);
                if (i < args.length - 1) {
                    this.prod.addElement(",");
                }
            }
            this.prod.addElement(")");
        }
    }

    public Operation(String name,
                     Sort[] args,
                     Sort res)
        throws SignatureException {
        this(name, args, res, null);
    }

    public Operation(String name,
                     Sort res)
        throws SignatureException {
        this(name, new Sort[0], res, null);
    }

    public ModuleName getModuleName() {
        return this.modName;
    }

    protected static String normalize(String name) {

        String result = "";

        String tmp = name;
        int i = tmp.indexOf("_");
        while (i != -1) {
            if (result.endsWith("_")) {
                result += " " + tmp.substring(0, i)
                                   .trim();
            } else {
                result += tmp.substring(0, i)
                             .trim();
            }
            if (!result.endsWith("_") && !result.endsWith(" ")) {
                result += " _";
            } else {
                result += "_";
            }
            tmp = tmp.substring(i + 1)
                     .trim();
            i = tmp.indexOf("_");
        }

        if (result.endsWith("_")) {
            result += " " + tmp.trim();
        } else {
            result += tmp.trim();
        }

        return result.trim();
    }

    /* create a constant with the specified name and sort.
     *
     * @param na the string of the name of this operation, which doesn't contain "_" .
     *
     * @param res the sort of result .
     *
     * @exception SignatureException if na contains "_" or na is empty string. */
    public Operation(String name,
                     Sort res,
                     ModuleName modName)
        throws SignatureException {
        this(name, new Sort[0], res, modName);
    }

    /**
     * set associativity for this operation.
     *
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setAssociativity() throws SignatureException {
        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];
            if (firstSort.equals(this.resultSort) && secondSort.equals(this.resultSort)) {
                this.isAssociative = true;
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "associativity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }

    }

    /**
     * set associativity for this operation.
     *
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setAssociativity(Signature sig) throws SignatureException {

        if (this.argumentSorts.length == 2) {

            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];

            boolean lcanset = sig.isSubsort(this.resultSort, firstSort)
                              || sig.isSubsort(firstSort, this.resultSort);

            if (!lcanset) {
                lcanset = sig.hasCommonSubsort(this.resultSort, firstSort);
            }

            boolean rcanset = sig.isSubsort(this.resultSort, secondSort)
                              || sig.isSubsort(secondSort, this.resultSort);

            if (!rcanset) {
                rcanset = sig.hasCommonSubsort(this.resultSort, secondSort);
            }

            if (lcanset && rcanset) {
                this.isAssociative = true;
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "associativity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }

    }

    /**
     * set communtativity for this operation.
     *
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setCommutativity() throws SignatureException {
        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];
            if (firstSort.equals(secondSort)) {
                this.isCommutative = true;
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "communtativity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    /**
     * set communtativity for this operation.
     *
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setCommutativity(Signature sig) throws SignatureException {
        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];

            boolean canset = sig.getSuperSort(firstSort, secondSort) != null;

            if (canset) {
                this.isCommutative = true;
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "communtativity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    /**
     * set idempotence for this operation.
     *
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setIdempotence() throws SignatureException {
        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];
            if (firstSort.equals(secondSort)) {
                this.isIdempotent = true;
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "idempotence");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    /**
     * set identity for this operation.
     *
     * @param op
     *            a constant which is the identity of this opertaion.
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setIdentity(Operation op) throws SignatureException {

        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];
            Sort resultSort = op.getResultSort();

            if (resultSort.equals(firstSort) && resultSort.equals(secondSort)) {
                if (op.argumentSorts.length == 0) {
                    this.id = op;
                } else {
                    throw new SignatureException("Inconsistent argument sorts for " + "identity");
                }
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "identity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    public void setIdentity(Signature sig,
                            Operation op)
        throws SignatureException {

        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];

            if (sig.isSubsort(op.resultSort, firstSort)
                || sig.isSubsort(op.resultSort, secondSort)) {
                if (op.argumentSorts.length == 0) {
                    this.id = op;
                } else {
                    throw new SignatureException("Inconsistent argument sorts for " + "identity");
                }
            } else {
                throw new SignatureException("Inconsistent argument sorts for " + "identity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    /**
     * set identity for this operation.
     *
     * @param op
     *            a constant which is the identity of this opertaion.
     * @exception SignatureException
     *                if this operation is not binary operation or has not consistent arguments
     *                sort.
     */

    public void setIdentity(Operation op,
                            Signature sig)
        throws SignatureException {

        if (this.argumentSorts.length == 2) {
            Sort firstSort = this.argumentSorts[0];
            Sort secondSort = this.argumentSorts[1];
            Sort resultSort = op.getResultSort();

            if (sig.isSubsort(resultSort, firstSort) || sig.isSubsort(resultSort, secondSort)) {
                if (op.argumentSorts.length == 0) {
                    this.id = op;

                } else {
                    throw new SignatureException("Inconsistent argument" + " sorts for identity");
                }
            } else {
                throw new SignatureException("Inconsistent argument sorts " + "for identity");
            }
        } else {
            throw new SignatureException("Expect two arguments for " + this.name);
        }
    }

    /**
     * set information as the specified string.
     *
     * @param s
     *            string
     */
    public void setInfo(String s) {
        this.info = s;
    }

    /**
     * return a string representing this operation. Example:
     * <P>
     * op if_then_else : Bool Nat Nat -> Nat [prec 100] .
     *
     */
    @Override
    public String toString() {
        String result = "op ";

        result += this.name + " :";

        for (Sort tmp : this.argumentSorts) {
            result += " " + tmp.getName() + "." + tmp.getModuleName();
        }

        result += " -> " + this.resultSort.getName() + "." + this.resultSort.getModuleName() + "  ";
        result += "[";

        if (this.isAssociative)
            result += " assoc";
        if (this.isCommutative)
            result += " comm";
        if (this.isIdempotent)
            result += " idem";
        if (this.id != null)
            result += " idr: " + this.id.getName();
        if (!this.behavorial)
            result += "ncong";

        if (this.priority != Integer.MAX_VALUE) {
            result += " prec " + this.priority;
        }

        if (this.gather != null) {
            result += " gather(";
            for (int i = 0; i < this.gather.length; i++ ) {
                if (i != 0) {
                    result += ", ";
                }
                result += this.gather[i];
            }
            result += ")";
        }

        if (this.strategy != null) {
            result += " strategy(";
            for (int i = 0; i < this.strategy.length; i++ ) {
                if (i != 0) {
                    result += ", ";
                }
                result += this.strategy[i];
            }
            result += ")";
        }

        if (result.endsWith("[")) {
            result = result.substring(0, result.length() - 1);
        } else {
            result += " ] ";
        }

        //result += modName;

        return result;
    }

    /**
     * return the name of this operation.
     */
    public String getName() {
        return this.name;
    }

    public String getCleanName() {
        String result = this.name.trim();
        if (result.startsWith("_")) {
            result = result.substring(1)
                           .trim();
        }

        if (result.endsWith("_")) {
            result = result.substring(0, result.length() - 1)
                           .trim();
        }

        if (result.indexOf("_") != -1) {
            result = this.name;
        }

        return result;

    }

    /**
     * return the vector of the argument sorts. This vector can be modified without any side effect.
     */
    public Sort[] getArgumentSorts() {
        return this.argumentSorts;
    }

    /**
     * return the i_th argument sort.
     *
     * @exception SignatureException
     *                if i is less then 0 or greater than the number of arguments.
     */
    public Sort getArgumentSortAt(int i) throws SignatureException {
        Sort result = null;
        if (i < this.argumentSorts.length) {
            result = this.argumentSorts[i];
        } else {
            throw new SignatureException("The number of arguments out of bound " + i);
        }
        return result;
    }

    /**
     * return the result sort.
     *
     */
    public Sort getResultSort() {
        return this.resultSort;
    }

    /**
     * return the priority of this operation.
     *
     */
    public int getPriority() {
        return this.priority;
    }

    /**
     * return the arity of this operation.
     */
    public int getArity() {
        return this.argumentSorts.length;
    }

    /**
     * return the information of this operation.
     *
     */
    public String getInfo() {
        return this.info;
    }

    /**
     * return the identity of this operation.
     *
     */
    public Operation getIdentity() {
        if (this.id != null) {
            return this.id;
        } else if (this.implicitId != null) {
            return this.implicitId;
        } else {
            return null;
        }
    }

    /**
     *
     * test if this operation is a constant.
     *
     */
    public boolean isConstant() {
        return this.argumentSorts.length == 0;
    }

    /**
     *
     * test if this operation is associative.
     *
     */
    public boolean isAssociative() {
        return this.isAssociative;
    }

    /**
     *
     * test if this operation is commutative.
     *
     */
    public boolean isCommutative() {
        return this.isCommutative;
    }

    /**
     *
     * test if this operation is idempotent.
     *
     */
    public boolean isIdempotent() {
        return this.isIdempotent;
    }

    /**
     *
     * test if this operation is in mix notation.
     *
     */
    public boolean isMixNotation() {
        return this.name.indexOf("_") != -1;
    }

    /**
     *
     * test if this operation is equal to the specified operation.
     *
     * @param op
     *            operation
     * @return true if this operation is equals to op.
     */

    @Override
    public boolean equals(Object obj) {

        if (obj instanceof Operation) {

            Operation op = (Operation) obj;
            if (this.name.equals(op.name) && this.resultSort.equals(op.resultSort)
                && this.argumentSorts.length == op.argumentSorts.length) {

                for (int i = 0; i < this.argumentSorts.length; i++ ) {
                    if (!this.argumentSorts[i].equals(op.argumentSorts[i])) {
                        return false;
                    }
                }

                if (this.modName != null && op.modName != null) {
                    return this.modName.equals(op.modName);
                } else if (this.modName == null && op.modName == null) {
                    return true;
                }

            }

        }

        return false;
    }

    @Override
    public int hashCode() {
        return this.name.hashCode() * 31 + this.resultSort.hashCode()
               + this.argumentSorts.hashCode() + ((this.modName != null) ? this.modName.hashCode()
                                                                         : 0);
    }

    public boolean hasSameSignature(Operation op) {

        if (this.resultSort.equals(op.resultSort)
            && this.argumentSorts.length == op.argumentSorts.length) {

            for (int i = 0; i < this.argumentSorts.length; i++ ) {
                if (!this.argumentSorts[i].equals(op.argumentSorts[i])) {
                    return false;
                }
            }

            return true;

        }

        return false;
    }

    /* set the priority of this operation .
     *
     * @param pri an positive integer */
    public void setPriority(int pri) {
        if (pri > 0) {
            this.priority = pri;
        } else {
            pri = Integer.MAX_VALUE;
        }
    }

    protected Vector<Object> getTokens() {
        return new Vector<>(this.prod);
    }

    public void setBehavorial(boolean flag) {
        this.behavorial = flag;
    }

    public boolean isBehavorial() {
        return this.behavorial;
    }

    /* check whether this operation is less than another operation op under the specified
     * signature. */
    public boolean less(Signature sig,
                        Operation op) {

        boolean result = false;
        boolean samename = true;
        if (this.prod.size() == op.prod.size()) {

            for (int i = 0; i < this.prod.size() && samename; i++ ) {
                Object prodItem = this.prod.elementAt(i);
                Object opProdItem = op.prod.elementAt(i);

                if (prodItem instanceof String) {
                    if (opProdItem instanceof String) {

                        samename = ((String) prodItem).trim()
                                                      .equals(((String) opProdItem).trim());

                    } else {
                        samename = false;
                    }
                }

                if (prodItem instanceof Sort) {
                    if (opProdItem instanceof Sort) {
                        samename = true;
                    } else {
                        samename = false;
                    }
                }
            }

        } else if (op.getArity() == 1 && getArity() == 1) {
            samename = this.name.trim()
                                .equals(op.name.trim() + " _")
                       || op.name.trim()
                                 .startsWith(this.name.trim() + " _");
        } else {
            samename = false;
        }

        if (samename && this.getArity() == op.getArity()) {

            if (getArity() != 0) {
                boolean less = false;
                boolean comparable = true;

                for (int i = 0; i < this.argumentSorts.length && comparable; i++ ) {
                    Sort s1 = this.argumentSorts[i];
                    Sort s2 = op.argumentSorts[i];

                    if (sig.isSubsort(s1, s2)) {
                        less = less || sig.less(s1, s2);
                    } else {
                        comparable = false;
                    }
                }

                if (comparable && less) {
                    result = sig.isSubsort(this.resultSort, op.resultSort);
                } else if (comparable) {
                    //result = sig.isSubsort(resultSort, op.resultSort);
                    result = sig.less(this.resultSort, op.resultSort);
                }

            } else //result = sig.isSubsort(resultSort, op.resultSort);
                if (sig.less(this.resultSort, op.resultSort)) {
                    result = true;
                }
        }

        return result;

    }

    public boolean isAttribute() {
        return !this.resultSort.isHidden() && this.behavorial;
    }

    public boolean isMethod() {
        return this.resultSort.isHidden() && this.behavorial;
    }

    public boolean isNonBehavorial() {
        if (!this.behavorial) {
            for (Sort argumentSort : this.argumentSorts) {
                if (argumentSort.isHidden()) {
                    return true;
                }
            }
            if (this.resultSort.isHidden()) {
                return true;
            }
        }
        return false;
    }

    public Operation changeModuleName(ModuleName olds,
                                      ModuleName news) {

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.changeModuleName(olds, news);

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].changeModuleName(olds, news);
        }

        try {

            if (this.modName.equals(olds)) {
                result = new Operation(this.name, args, res, news);
            } else {
                result =
                    new Operation(this.name, args, res, this.modName.changeModuleName(olds, news));
            }

            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;

            if (this.id != null) {
                result.id = this.id.changeModuleName(olds, news);
            }

            if (this.implicitId != null) {
                result.implicitId = this.implicitId.changeModuleName(olds, news);
            }

            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Operation changeAbsoluteModuleName(ModuleName olds,
                                              ModuleName news) {

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.changeAbsoluteModuleName(olds, news);

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].changeAbsoluteModuleName(olds, news);
        }

        try {

            if (this.modName.equals(olds)) {
                result = new Operation(this.name, args, res, news);
            } else {
                result = new Operation(this.name, args, res, this.modName);
            }
            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;

            if (this.id != null) {
                result.id = this.id.changeAbsoluteModuleName(olds, news);
            }

            if (this.implicitId != null) {
                result.implicitId = this.implicitId.changeAbsoluteModuleName(olds, news);
            }

            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Operation changeParameterName(String olds,
                                         String news) {

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.changeParameterName(olds, news);

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].changeParameterName(olds, news);
        }

        try {

            result =
                new Operation(this.name, args, res, this.modName.changeParameterName(olds, news));

            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;

            if (this.id != null) {
                result.id = this.id.changeParameterName(olds, news);
            }

            if (this.implicitId != null) {
                result.implicitId = this.implicitId.changeParameterName(olds, news);
            }

            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Operation addAnnotation(String name,
                                   Map<ModuleName, Integer> env) {

        if (this.info.equals("system-default")) {
            return this;
        }

        Integer aInt = env.get(this.modName);
        if (aInt != null && aInt.intValue() == 0) {
            return this;
        }

        if (this.modName.hasNotation()) {
            return this;
        }

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.addAnnotation(name, env);

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].addAnnotation(name, env);
        }

        try {

            result = new Operation(this.name, args, res, this.modName.addAnnotation(name));
            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;
            result.id = this.id;
            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        } catch (Exception e) {
            System.out.println(this);
            e.printStackTrace();
            System.out.println("Fatal Error of some kinds Operation.java");
            System.exit(0);
        }

        return result;
    }

    public Operation removeAnnotation(String name) {

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.removeAnnotation(name);

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].removeAnnotation(name);
        }

        try {

            result = new Operation(this.name, args, res, this.modName.getOriginModuleName());
            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;
            result.id = this.id;
            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Operation changeSort(Sort olds,
                                Sort news) {

        Operation result = null;
        Sort[] args = new Sort[this.argumentSorts.length];
        Sort res = this.resultSort.equals(olds) ? news
                                                : this.resultSort;

        for (int j = 0; j < this.argumentSorts.length; j++ ) {
            args[j] = this.argumentSorts[j].equals(olds) ? news
                                                         : this.argumentSorts[j];
        }

        try {
            result = new Operation(this.name, args, res, this.modName);
            result.priority = this.priority;
            result.info = this.info;
            result.isAssociative = this.isAssociative;
            result.isCommutative = this.isCommutative;
            result.isIdempotent = this.isIdempotent;
            if (this.id != null)
                result.id = this.id.changeSort(olds, news);
            if (this.implicitId != null)
                result.implicitId = this.implicitId.changeSort(olds, news);
            result.behavorial = this.behavorial;
            result.gather = this.gather;
            result.strategy = this.strategy;

        } catch (SignatureException e) {
        }

        return result;
    }

    public Operation replaceOperationName(String to) {
        return this.replaceOperationName(this.name, to);
    }

    public Operation replaceOperationName(String from,
                                          String to) {

        Operation result = this;

        boolean same = true;
        StringTokenizer st1 = new StringTokenizer(from, "_ ");
        StringTokenizer st2 = new StringTokenizer(this.name, "_ ");
        while (st1.hasMoreTokens() && same) {
            String tmp1 = st1.nextToken();
            if (st2.hasMoreTokens()) {
                String tmp2 = st2.nextToken();
                if (!tmp1.equals(tmp2)) {
                    same = false;
                    break;
                }
            } else {
                same = false;
                break;
            }
        }

        if (st2.hasMoreTokens()) {
            same = false;
        }

        if (same) {

            try {
                result = new Operation(to, this.argumentSorts, this.resultSort, this.modName);

                result.isAssociative = this.isAssociative;
                result.isCommutative = this.isCommutative;
                result.isIdempotent = this.isIdempotent;
                result.behavorial = this.behavorial;

                if (this.id != null) {
                    result.id = this.id.replaceOperationName(from, to);
                }

                if (this.implicitId != null) {
                    result.implicitId = this.implicitId;
                }

                result.gather = this.gather;
                result.strategy = this.strategy;

            } catch (SignatureException e) {
            }

        }

        return result;

    }

    public boolean uses(Sort sort) {
        for (Sort argumentSort : this.argumentSorts) {
            if (argumentSort.equals(sort)) {
                return true;
            }
        }

        if (this.resultSort.equals(sort)) {
            return true;
        }

        return false;

    }

    public boolean isDefinedOnInitial() {
        boolean result = true;
        for (int i = 0; i < this.argumentSorts.length && result; i++ ) {
            result = this.argumentSorts[i].isInitial();
        }

        if (result)
            result = this.resultSort.isInitial();
        return result;
    }

    public Operation copy() {

        Operation result = null;

        try {
            result = new Operation(this.name, this.argumentSorts, this.resultSort, this.modName);
        } catch (Exception e) {
        }

        result.argumentNames = this.argumentNames;
        result.resultName = this.resultName;
        result.priority = this.priority;
        result.isAssociative = this.isAssociative;
        result.isCommutative = this.isCommutative;
        result.isIdempotent = this.isIdempotent;
        result.id = this.id;
        result.implicitId = this.implicitId;
        result.behavorial = this.behavorial;
        result.gather = this.gather;
        result.strategy = this.strategy;

        result.info = this.info;
        result.prod = new Vector<>(this.prod);

        return result;

    }

    public void setGather(String[] gather) throws SignatureException {
        if (gather.length != this.argumentSorts.length) {
            throw new SignatureException("expect " + this.argumentSorts.length
                                         + " in gather definition");
        }

        this.gather = gather;

    }

    public void setStrategy(int[] strategy) {
        this.strategy = strategy;
    }

    protected boolean hasBalancedBrackets() {

        Stack<String> stack = new Stack<>();

        Vector<Object> tokens = getTokens();
        for (int i = 0; i < tokens.size(); i++ ) {
            Object obj = tokens.elementAt(i);
            if (obj instanceof String) {
                String str = (String) obj;
                if (str.equals("(") || str.equals("{") || str.equals("[")) {
                    stack.push(str);
                    continue;
                }

                if (str.equals(")") || str.equals("}") || str.equals("]")) {
                    if (stack.isEmpty()) {
                        return false;
                    } else {
                        String top = stack.pop();
                        if ((top.equals("(") && str.equals(")"))
                            || (top.equals("[") && str.equals("]"))
                            || (top.equals("{") && str.equals("}"))) {
                        } else {
                            return false;
                        }
                    }
                }
            }
        }

        if (!stack.isEmpty()) {
            return false;
        }

        return true;

    }

}
