package bobj;

import java.util.HashMap;
import java.util.Map;

public class RenamingMap
                         extends
                         HashMap<ViewRenamable, ViewRenamable>
                         implements ViewRenamable {
    @Override
    public int hashCode() {
        return keySet().hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof RenamingMap)
            return super.equals(o);
        else if (o instanceof Map) {
            System.err.println("comparison failed " + this + " compared to" + o);
            return false;
        } else return false;
    }

}
