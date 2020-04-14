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

    @Test
    void makeRight() {
        assertDoesNotThrow(() -> Acl2String.make(""));
        assertDoesNotThrow(() -> Acl2String.make("string"));
        assertDoesNotThrow(() -> Acl2String.make("TWO WORDS"));
        assertDoesNotThrow(() -> Acl2String.make("\0\1\2"));
        assertDoesNotThrow(() -> Acl2String.make("\u00ff\u00a8"));
        assertDoesNotThrow(() -> Acl2String.make(".ab#$\n"));
    }

    @Test
    void getJavaStringFromConstant() {
        assertEquals(Acl2String.EMPTY.getJavaString(), "");
        assertEquals(Acl2String.ACL2.getJavaString(), "ACL2");
    }

    @Test
    void getJavaStringFromMake() {
        assertEquals(Acl2String.make("xyz").getJavaString(), "xyz");
        assertEquals(Acl2String.make("").getJavaString(), "");
        assertEquals(Acl2String.make("\0A?").getJavaString(), "\0A?");
        assertEquals(Acl2String.make("@").getJavaString(), "@");
    }

}
