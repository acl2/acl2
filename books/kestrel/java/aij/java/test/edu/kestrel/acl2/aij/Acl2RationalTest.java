/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.*;

class Acl2RationalTest {

    @Test
    void makeIntInt() {
        assertDoesNotThrow(() -> Acl2Rational.make(0, 1));
        assertDoesNotThrow(() -> Acl2Rational.make(1, 1));
        assertDoesNotThrow(() -> Acl2Rational.make(1, 2));
        assertDoesNotThrow(() -> Acl2Rational.make(21, 21));
        assertDoesNotThrow(() -> Acl2Rational.make(-33, 17));
        assertDoesNotThrow(() -> Acl2Rational.make(22929, -1292927));
    }

    @Test
    void makeLongLong() {
        assertDoesNotThrow(() -> Acl2Rational.make(0L, 1L));
        assertDoesNotThrow(() -> Acl2Rational.make(1L, 1L));
        assertDoesNotThrow(() -> Acl2Rational.make(1L, 2L));
        assertDoesNotThrow(() -> Acl2Rational.make(21L, 21L));
        assertDoesNotThrow(() -> Acl2Rational.make(-33L, 17L));
        assertDoesNotThrow(() ->
                Acl2Rational.make(2292983408573429857L, -1292927723987238472L));
    }

    @Test
    void makeBigIntegerBigInteger() {
        assertDoesNotThrow(() ->
                Acl2Rational.make(BigInteger.ONE, BigInteger.TWO));
        assertDoesNotThrow(() ->
                Acl2Rational.make(new BigInteger("3737389299292929292"),
                        new BigInteger("-3283482738974827394728397492873492")));
    }

    @Test
    void makeAcl2IntegerAcl2Integer() {
        assertDoesNotThrow(() ->
                Acl2Rational.make(Acl2Integer.ONE, Acl2Integer.make(50)));
        assertDoesNotThrow(() ->
                Acl2Rational.make(Acl2Integer.ONE.make(BigInteger.TEN),
                        Acl2Integer.make(new BigInteger("-11"))));
    }

}
