/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

// This file is handwritten (not generated)
// because there is no support yet in ATJ
// for generating tests involving Java primitive types.

import edu.kestrel.acl2.aij.*;

public class PrimitivesShallowGuardedTests {

    private static void runTest(int x, int y) throws Acl2EvaluationException {
        int z = PrimitivesShallowGuarded.ACL2.f_int(x, y);
        System.out.println("f-int(" + x + "," + y + ") = " + z);
    }

    public static void main(String[] args) throws Acl2EvaluationException {
        PrimitivesShallowGuarded.initialize();
        runTest(8, 15);
        runTest(-280, 3971);
        runTest(1000000, 1000000);
    }

}
