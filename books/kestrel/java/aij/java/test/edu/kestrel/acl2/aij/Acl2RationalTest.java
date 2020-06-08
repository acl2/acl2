/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2RationalTest {

    @Test
    void makeIntInt() {
        assertDoesNotThrow(() -> Acl2Rational.make(0, 1));
        assertDoesNotThrow(() -> Acl2Rational.make(1, 1));
        assertDoesNotThrow(() -> Acl2Rational.make(1, 2));
        assertDoesNotThrow(() -> Acl2Rational.make(-33, 17));
        assertDoesNotThrow(() -> Acl2Rational.make(22929, -1292927));
    }

}
