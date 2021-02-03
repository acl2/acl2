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

    @Test
    void makeIntIntIsAcl2Integer() {
        assertTrue(Acl2Rational.make(1, 1) instanceof Acl2Integer);
        assertTrue(Acl2Rational.make(-50, 5) instanceof Acl2Integer);
        assertTrue(Acl2Rational.make(0, -17) instanceof Acl2Integer);
    }

    @Test
    void makeLongLongIsAcl2Integer() {
        assertTrue(Acl2Rational.make(2000000000000L, 1000000000000L)
                instanceof Acl2Integer);
        assertTrue(Acl2Rational.make(3L, 1) instanceof Acl2Integer);
    }

    @Test
    void makeBigIntegerBigIntegerIsAcl2Integer() {
        assertTrue(Acl2Rational.make(BigInteger.TEN, BigInteger.TWO)
                instanceof Acl2Integer);
        assertTrue(Acl2Rational.make
                (new BigInteger("-55"), new BigInteger("11"))
                instanceof Acl2Integer);
    }

    @Test
    void makeAcl2IntegerAcl2IntegerIsAcl2Integer() {
        assertTrue(Acl2Rational.make(Acl2Integer.ZERO, Acl2Integer.make(-1))
                instanceof Acl2Integer);
        assertTrue(Acl2Rational.make(Acl2Integer.make(-20),
                Acl2Integer.make(10))
                instanceof Acl2Integer);
    }

    @Test
    void getNumeratorFromMakeIntInt() {
        assertEquals(Acl2Rational.make(3, 4).getNumerator(),
                Acl2Integer.make(3));
        assertEquals(Acl2Rational.make(20, 30).getNumerator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Rational.make(-647, 121).getNumerator(),
                Acl2Integer.make(-647));
    }

    @Test
    void getNumeratorFromMakeLongLong() {
        assertEquals(Acl2Rational.make(37L, 22L).getNumerator(),
                Acl2Integer.make(37));
        assertEquals(Acl2Rational.make(3333333333L, 2222222222L).getNumerator(),
                Acl2Integer.make(3));
        assertEquals(Acl2Rational.make(10000000000L, -3).getNumerator(),
                Acl2Integer.make(-10000000000L));
    }

    @Test
    void getNumeratorFromMakeBigIntegerBigInteger() {
        assertEquals(Acl2Rational.make(BigInteger.ONE, BigInteger.TWO)
                        .getNumerator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Rational.make(BigInteger.TWO, BigInteger.TEN)
                        .getNumerator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Rational.make(new BigInteger("20"),
                new BigInteger("-30"))
                        .getNumerator(),
                Acl2Integer.make(-2));
    }

    @Test
    void getNumeratorFromMakeAcl2IntegerAcl2Integer() {
        assertEquals(Acl2Rational.make(Acl2Integer.ONE, Acl2Integer.make(4))
                        .getNumerator(),
                Acl2Integer.ONE);
        assertEquals
                (Acl2Rational.make(Acl2Integer.make(-55), Acl2Integer.make(-54))
                                .getNumerator(),
                        Acl2Integer.make(55));
    }

    @Test
    void getDenominatorFromMakeIntInt() {
        assertEquals(Acl2Rational.make(3, 4).getDenominator(),
                Acl2Integer.make(4));
        assertEquals(Acl2Rational.make(20, 30).getDenominator(),
                Acl2Integer.make(3));
        assertEquals(Acl2Rational.make(-647, 121).getDenominator(),
                Acl2Integer.make(121));
    }

    @Test
    void getDenominatorFromMakeLongLong() {
        assertEquals(Acl2Rational.make(37L, 22L).getDenominator(),
                Acl2Integer.make(22));
        assertEquals(Acl2Rational.make(3333333333L, 2222222222L)
                        .getDenominator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Rational.make(10000000000L, -3).getDenominator(),
                Acl2Integer.make(3));
        assertEquals(Acl2Rational.make(3, 10000000000L).getDenominator(),
                Acl2Integer.make(10000000000L));
    }

    @Test
    void getDenominatorFromMakeBigIntegerBigInteger() {
        assertEquals(Acl2Rational.make(BigInteger.ONE, BigInteger.TWO)
                        .getDenominator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Rational.make(BigInteger.TWO, BigInteger.TEN)
                        .getDenominator(),
                Acl2Integer.make(5));
        assertEquals(Acl2Rational.make(new BigInteger("20"),
                new BigInteger("-30"))
                        .getDenominator(),
                Acl2Integer.make(3));
    }

    @Test
    void getDenominatorFromMakeAcl2IntegerAcl2Integer() {
        assertEquals(Acl2Rational.make(Acl2Integer.ONE, Acl2Integer.make(4))
                        .getDenominator(),
                Acl2Integer.make(4));
        assertEquals
                (Acl2Rational.make(Acl2Integer.make(-55), Acl2Integer.make(-54))
                                .getDenominator(),
                        Acl2Integer.make(54));
    }

    @Test
    void compareToIntegers() { // compare arithmetically -- see ACL2's alphorder
        assertTrue(Acl2Rational.make(1, 2).compareTo(Acl2Integer.ONE) < 0);
        assertTrue(Acl2Rational.make(-5, 4).
                compareTo(Acl2Integer.make(-10)) > 0);
        assertTrue(Acl2Rational.make(45, -9).
                compareTo(Acl2Integer.make(-5)) == 0);
    }

    @Test
    void compareToRatios() { // compare arithmetically -- see ACL2's alphorder
        assertTrue(Acl2Rational.make(11, 17).
                compareTo(Acl2Rational.make(12, 17)) < 0);
        assertTrue(Acl2Rational.make(11, 17).
                compareTo(Acl2Rational.make(1, 16)) > 0);
        assertTrue(Acl2Rational.make(11, 17).
                compareTo(Acl2Rational.make(-22, -34)) == 0);
        assertTrue(Acl2Rational.make(30, 10).
                compareTo(Acl2Rational.make(8, 9)) > 0);
    }

    @Test
    void compareToComplexRational() {
        // compare lexicographically -- see ACL2's alphorder
        assertTrue(Acl2Rational.make(2, 3).
                compareTo(Acl2Number.make(1, 1)) < 0);
        assertTrue(Acl2Rational.make(7, -2).
                compareTo(Acl2Number.make(-50, 2)) > 0);
        assertTrue(Acl2Rational.make(8, 3).
                compareTo(Acl2Number.make
                        (Acl2Rational.make(8, 3), Acl2Integer.make(1))) < 0);
        assertTrue(Acl2Rational.make(8, 3).
                compareTo(Acl2Number.make
                        (Acl2Rational.make(8, 3), Acl2Integer.make(-1))) > 0);
    }

}
