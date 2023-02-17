/*
 * Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

// This file is handwritten (not generated)
// for the reason given in the file hard-error.lisp.

import edu.kestrel.acl2.aij.*;

public class HardErrorDeepGuardedTests {

    private static void testNoError() {
        System.out.print("Testing no error...");
        Acl2Value functionArgument = Acl2Integer.make(0);
        Acl2Value[] functionArguments = new Acl2Value[]{functionArgument};
        Acl2Symbol functionName = Acl2Symbol.make("ACL2", "ERROR-IF-NIL");
        try {
            Acl2Value functionResult =
                HardErrorDeepGuarded.call(functionName, functionArguments);
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
        Acl2Value functionArgument = Acl2Symbol.NIL;
        Acl2Value[] functionArguments = new Acl2Value[]{functionArgument};
        Acl2Symbol functionName = Acl2Symbol.make("ACL2", "ERROR-IF-NIL");
        try {
            Acl2Value functionResult =
                HardErrorDeepGuarded.call(functionName, functionArguments);
            System.out.println(" FAIL (no exception thrown)");
        } catch (Acl2HardError e) {
            System.out.println(" PASS");
        } catch (Exception e) {
            System.out.println(" FAIL (other exception thrown)");
        }
    }

    public static void main(String[] args) {
        HardErrorDeepGuarded.initialize();
        testNoError();
        testError();
    }
}
