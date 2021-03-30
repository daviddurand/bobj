
package bobj;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class Subsort
                     implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    protected Map<Sort, Vector<Sort>> subsorts = new HashMap<>();

    public void addSubsort(Sort parent,
                           Sort child)
        throws SubsortException {

        // first get all subsorts for parent and child

        Vector<Sort> pv = new Vector<>();
        Vector<Sort> cv = new Vector<>();

        if (this.subsorts.containsKey(child)) {
            cv = this.subsorts.get(child);
            this.subsorts.remove(child);
        }
        if (this.subsorts.containsKey(parent)) {
            pv = this.subsorts.get(parent);
            this.subsorts.remove(parent);
        }

        // insert child into pv
        if (!pv.contains(child))
            pv.addElement(child);

        // insert all the elements of cv into pv
        for (Sort aChild : cv) {
            if (aChild.equals(parent))
                throw new SubsortException("contradiction subsort: " + child + " and "
                                           + parent.getName());
            if (!pv.contains(aChild))
                pv.addElement(aChild);
        }
        this.subsorts.put(parent, pv);
        this.subsorts.put(child, cv);

        // insert child and all the elements in cv to all possible places
        for (Sort sort : this.subsorts.keySet()) {
            Vector<Sort> sv = this.subsorts.get(sort);

            // if sv contains parent, then insert
            if (sv.contains(parent)) {
                insert(sv, child);
                for (Sort tmp : cv) {
                    insert(sv, tmp);
                }
            }
        }

    }

    private static void insert(Vector<Sort> set,
                               Sort sort) {
        if (!set.contains(sort))
            set.addElement(sort);
    }

    public boolean isSubsort(Sort parent,
                             Sort child) {

        boolean result = false;

        if (parent.getName()
                  .equals("Universal")
            && parent.getInfo()
                     .equals("system-default")) {
            result = true;
        } else {

            result = this.subsorts.keySet()
                                  .contains(parent);
            if (result) {
                Vector<Sort> v = this.subsorts.get(parent);
                result = false;
                if (v.contains(child)) {
                    result = true;
                }
            }

        }

        return result;

    }

    @Override
    public String toString() {

        String result = "";
        for (Sort parent : this.subsorts.keySet()) {
            Vector<Sort> v = this.subsorts.get(parent);

            if (v != null && v.size() != 0) {
                result += "  subsorts ";
                for (int i = 0; i < v.size(); i++ ) {
                    Sort kid = v.elementAt(i);
                    result += kid.getName() + "." + kid.getModuleName() + " ";
                }
                result += "< " + parent.getName() + " .\n";
            }
        }

        return result;
    }

    public Sort[] getChildren(Sort parent) {

        Vector<Sort> kids = new Vector<>();
        for (Sort sort : this.subsorts.keySet()) {
            if (sort.equals(parent)) {
                kids = this.subsorts.get(sort);
            }
        }

        Sort[] result = new Sort[kids.size()];
        kids.copyInto(result);
        return result;
    }

    protected Subsort changeModuleName(ModuleName olds,
                                       ModuleName news) {

        Subsort result = new Subsort();

        for (Sort ps : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(ps);

            ps = ps.changeModuleName(olds, news);

            Vector<Sort> res = new Vector<>();
            if (vec != null) {
                for (int i = 0; i < vec.size(); i++ ) {
                    Sort tmp = vec.elementAt(i);
                    tmp = tmp.changeModuleName(olds, news);
                    res.addElement(tmp);
                }
            }

            result.subsorts.put(ps, res);

        }

        return result;

    }

    protected Subsort changeAbsoluteModuleName(ModuleName olds,
                                               ModuleName news) {

        Subsort result = new Subsort();

        for (Sort ps : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(ps);

            ps = ps.changeAbsoluteModuleName(olds, news);

            Vector<Sort> res = new Vector<>();
            if (vec != null) {
                for (int i = 0; i < vec.size(); i++ ) {
                    Sort tmp = vec.elementAt(i);
                    tmp = tmp.changeAbsoluteModuleName(olds, news);
                    res.addElement(tmp);
                }
            }

            result.subsorts.put(ps, res);

        }

        return result;

    }

    protected Subsort changeParameterName(String olds,
                                          String news) {

        Subsort result = new Subsort();

        for (Sort ps : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(ps);

            ps = ps.changeParameterName(olds, news);

            Vector<Sort> res = new Vector<>();
            if (vec != null) {
                for (int i = 0; i < vec.size(); i++ ) {
                    Sort tmp = vec.elementAt(i);
                    tmp = tmp.changeParameterName(olds, news);
                    res.addElement(tmp);
                }
            }

            result.subsorts.put(ps, res);

        }

        return result;

    }

    protected Subsort changeSort(Sort olds,
                                 Sort news) {

        Subsort tmp = new Subsort();
        for (Sort parent : this.subsorts.keySet()) {
            Vector<Sort> cv = this.subsorts.get(parent);

            if (parent.equals(olds)) {
                parent = news;
            }

            for (int i = 0; i < cv.size(); i++ ) {
                Sort child = cv.elementAt(i);
                if (child.equals(olds)) {
                    child = news;
                }
                try {
                    tmp.addSubsort(parent, child);
                } catch (Exception ex) {
                }
            }

        }

        return tmp;

    }

    protected Subsort addAnnotation(String name,
                                    Map<ModuleName, Integer> env) {

        Subsort result = new Subsort();

        for (Sort ps : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(ps);
            Sort sort = ps.addAnnotation(name, env);

            for (int i = 0; i < vec.size(); i++ ) {
                Sort tmp = vec.elementAt(i);
                tmp = tmp.addAnnotation(name, env);
                try {
                    result.addSubsort(sort, tmp);
                } catch (Exception ex) {
                }
            }

        }

        return result;

    }

    protected Subsort removeAnnotation(String name) {

        Subsort result = new Subsort();

        for (Sort ps : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(ps);
            Vector<Sort> res = new Vector<>();

            for (int i = 0; i < vec.size(); i++ ) {
                Sort tmp = vec.elementAt(i);
                tmp = tmp.removeAnnotation(name);
                res.addElement(tmp);

            }
            ps = ps.removeAnnotation(name);
            result.subsorts.put(ps, res);

        }

        return result;

    }

    public boolean contains(Subsort ss) {
        boolean result = true;

        for (Sort parent : ss.subsorts.keySet()) {
            Vector<Sort> v = ss.subsorts.get(parent);
            for (int i = 0; i < v.size(); i++ ) {
                Sort kid = v.elementAt(i);
                result = isSubsort(parent, kid);
                if (!result)
                    return false;
            }
        }

        return result;
    }

    public Sort canApply(Sort s1,
                         Sort s2) {

        Sort result = null;

        Vector<Sort> kids = null;
        for (Sort tmp : this.subsorts.keySet()) {
            if (s2.equals(tmp)) {
                kids = this.subsorts.get(tmp);
                break;
            }
        }

        if (kids != null) {
            for (int i = 0; i < kids.size(); i++ ) {
                Sort tmp = kids.elementAt(i);
                if (isSubsort(s1, tmp)) {
                    return tmp;
                }
            }
        }

        return result;
    }

    @Override
    public Object clone() {
        Subsort result = new Subsort();
        for (Sort sort : this.subsorts.keySet()) {
            Vector<Sort> vec = this.subsorts.get(sort);
            vec = new Vector<>(vec);
            result.subsorts.put(sort, vec);
        }

        //result.subsorts = (HashMap)subsorts.clone();
        return result;
    }

}
