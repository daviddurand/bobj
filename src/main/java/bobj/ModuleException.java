
package bobj;

/**
 *
 * @author: Kai Lin
 * @version: %I% %G%
 * @see java.lang.Exception
 */
public class ModuleException
                             extends
                             RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    /**
     * create a signature exception with the specified string.
     */
    public ModuleException(String msg) {
        super(msg);
    }

}
