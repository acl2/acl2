/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2IntegerTest {

    @Test
    void makeInt() {
        assertDoesNotThrow(() -> Acl2Integer.make(0));
        assertDoesNotThrow(() -> Acl2Integer.make(1));
        assertDoesNotThrow(() -> Acl2Integer.make(-1));
        assertDoesNotThrow(() -> Acl2Integer.make(32792));
        assertDoesNotThrow(() -> Acl2Integer.make(984022928));
        assertDoesNotThrow(() -> Acl2Integer.make(-26999));
    }

}
