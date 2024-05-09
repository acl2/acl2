/*
 * Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

// This file is handwritten (not generated)
// for the reason given in the file hard-error.lisp.

import edu.kestrel.acl2.aij.*;

public class HardErrorShallowGuardedTests {

    private static void testNoError() {
        System.out.print("Testing no error...");
        try {
            Acl2Value functionResult =
                HardErrorShallowGuarded.ACL2.
                error_if_nil(Acl2Integer.make(0));
            if (functionResult.equals(Acl2Symbol.makeKeyword("OKAY")))
                System.out.println(" PASS");
            else
                System.out.println(" FAIL (wrong result)");
        } catch (Acl2HardError e) {
            System.out.println(" FAIL (hard error thrown)");
        } catch (Exception e) {
            System.out.println(" FAIL (other exception thrown)");
        }
    }

    private static void testError() {
        System.out.print("Testing error...");
        try {
            Acl2Value functionResult =
                HardErrorShallowGuarded.ACL2.error_if_nil(Acl2Symbol.NIL);
            System.out.println(" FAIL (no exception thrown)");
        } catch (Acl2HardError e) {
            System.out.println(" PASS");
        } catch (Exception e) {
            System.out.println(" FAIL (other exception thrown)");
        }
    }

    public static void main(String[] args) {
        HardErrorShallowGuarded.initialize();
        testNoError();
        testError();
    }
}
