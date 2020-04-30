/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

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

    @Test
    void makeLong() {
        assertDoesNotThrow(() -> Acl2Integer.make(0L));
        assertDoesNotThrow(() -> Acl2Integer.make(1L));
        assertDoesNotThrow(() -> Acl2Integer.make(-28282822967648723L));
        assertDoesNotThrow(() -> Acl2Integer.make(1000000000000000000L));
    }

    @Test
    void makeNull() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Integer.make(null));
    }

    @Test
    void makeBigInteger() {
        assertDoesNotThrow(() -> Acl2Integer.make(BigInteger.ZERO));
        assertDoesNotThrow(() -> Acl2Integer.make(BigInteger.ONE));
        assertDoesNotThrow(() -> Acl2Integer.make(BigInteger.TWO));
        assertDoesNotThrow(() -> Acl2Integer.make(BigInteger.TEN));
        assertDoesNotThrow
                (() -> Acl2Integer.make(new BigInteger
                        ("1892739481723785127364812376426476238746189273641")));
        assertDoesNotThrow
                (() -> Acl2Integer.make(new BigInteger
                        (new byte[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10})));
        assertDoesNotThrow
                (() -> Acl2Integer.make
                        (new BigInteger("aaaabbbbccccddddeeeeffff", 16)));
    }

}
