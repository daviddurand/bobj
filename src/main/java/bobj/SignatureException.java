
package bobj;

/**
 *
 * @author: Kai Lin
 * @version: %I% %G%
 * @see java.lang.Exception
 */
public class SignatureException
                                extends
                                RuntimeException {
    /**
     *
     */
    private static final long serialVersionUID = 1L;

    /**
     * create a signature exception with the specified string.
     */
    public SignatureException(String str) {
        super(str);
    }

}
