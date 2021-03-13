
package bobj;

public class TermException
                           extends
                           RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    int count;

    public TermException() {
        super();
    }

    public TermException(String msg) {
        super(msg);
    }

    public TermException(String msg,
                         int count) {
        super(msg);
        this.count = count;
    }

    public int getCount() {
        return this.count;
    }

}
