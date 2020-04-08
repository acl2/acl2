/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2StringTest {

    @Test
    void makeNull() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2String.make(null));
    }

    @Test
    void makeWrong() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2String.make("\uffff"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2String.make("ABC\u0100abc"));
    }

}
