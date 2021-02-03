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

    @Test
    void getJavaIntFromConstant() {
        assertEquals(Acl2Integer.ZERO.getJavaInt(), 0);
        assertEquals(Acl2Integer.ONE.getJavaInt(), 1);
    }

    @Test
    void getJavaIntFromMakeInt() {
        assertEquals(Acl2Integer.make(0).getJavaInt(), 0);
        assertEquals(Acl2Integer.make(1).getJavaInt(), 1);
        assertEquals(Acl2Integer.make(-1).getJavaInt(), -1);
        assertEquals(Acl2Integer.make(2678).getJavaInt(), 2678);
        assertEquals(Acl2Integer.make(-1000000000).getJavaInt(), -1000000000);
    }

    @Test
    void getJavaIntFromMakeLong() {
        assertEquals(Acl2Integer.make(0L).getJavaInt(), 0);
        assertEquals(Acl2Integer.make(1L).getJavaInt(), 1);
        assertEquals(Acl2Integer.make(-1000000000L).getJavaInt(), -1000000000);
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make(44444444444444L).getJavaInt());
    }

    @Test
    void getJavaIntFromMakeBigInteger() {
        assertEquals(Acl2Integer.make(BigInteger.ZERO).getJavaInt(), 0);
        assertEquals(Acl2Integer.make(BigInteger.ONE).getJavaInt(), 1);
        assertEquals(Acl2Integer.make(BigInteger.TWO).getJavaInt(), 2);
        assertEquals(Acl2Integer.make(BigInteger.TEN).getJavaInt(), 10);
        assertEquals(Acl2Integer.make
                (new BigInteger("1234567890")).getJavaInt(), 1234567890);
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("72983728478274982748282710100"))
                        .getJavaInt());
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("-72983728478274982748282710100"))
                        .getJavaInt());
    }

    @Test
    void getJavaLongFromConstant() {
        assertEquals(Acl2Integer.ZERO.getJavaLong(), 0L);
        assertEquals(Acl2Integer.ONE.getJavaLong(), 1L);
    }

    @Test
    void getJavaLongFromMakeInt() {
        assertEquals(Acl2Integer.make(0).getJavaLong(), 0L);
        assertEquals(Acl2Integer.make(1).getJavaLong(), 1L);
        assertEquals(Acl2Integer.make(-1).getJavaLong(), -1L);
        assertEquals(Acl2Integer.make(2678).getJavaLong(), 2678L);
        assertEquals(Acl2Integer.make(-1000000000).getJavaLong(), -1000000000L);
    }

    @Test
    void getJavaLongFromMakeLong() {
        assertEquals(Acl2Integer.make(0L).getJavaLong(), 0L);
        assertEquals(Acl2Integer.make(1L).getJavaLong(), 1L);
        assertEquals(Acl2Integer.make(-1000000000L).getJavaLong(),
                -1000000000L);
        assertEquals(Acl2Integer.make(-1000000000000000000L).getJavaLong(),
                -1000000000000000000L);
    }

    @Test
    void getJavaLongFromMakeBigInteger() {
        assertEquals(Acl2Integer.make(BigInteger.ZERO).getJavaLong(), 0L);
        assertEquals(Acl2Integer.make(BigInteger.ONE).getJavaLong(), 1L);
        assertEquals(Acl2Integer.make(BigInteger.TWO).getJavaLong(), 2L);
        assertEquals(Acl2Integer.make(BigInteger.TEN).getJavaLong(), 10L);
        assertEquals(Acl2Integer.make
                (new BigInteger("1234567890")).getJavaLong(), 1234567890L);
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("72983728478274982748282710100"))
                        .getJavaInt());
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("-72983728478274982748282710100"))
                        .getJavaLong());
    }

    @Test
    void getJavaBigIntegerFromConstant() {
        assertEquals(Acl2Integer.ZERO.getJavaBigInteger(), BigInteger.ZERO);
        assertEquals(Acl2Integer.ONE.getJavaBigInteger(), BigInteger.ONE);
    }

    @Test
    void getJavaBigIntegerFromMakeInt() {
        assertEquals(Acl2Integer.make(0).getJavaBigInteger(), BigInteger.ZERO);
        assertEquals(Acl2Integer.make(1).getJavaBigInteger(), BigInteger.ONE);
        assertEquals(Acl2Integer.make(2).getJavaBigInteger(), BigInteger.TWO);
        assertEquals(Acl2Integer.make(10).getJavaBigInteger(), BigInteger.TEN);
        assertEquals(Acl2Integer.make(-1).getJavaBigInteger(),
                new BigInteger("-1"));
        assertEquals(Acl2Integer.make(2678).getJavaBigInteger(),
                new BigInteger("2678"));
        assertEquals(Acl2Integer.make(-1000000000).getJavaBigInteger(),
                new BigInteger("-1000000000"));
    }

    @Test
    void getJavaBigIntegerFromMakeLong() {
        assertEquals(Acl2Integer.make(0L).getJavaBigInteger(), BigInteger.ZERO);
        assertEquals(Acl2Integer.make(1L).getJavaBigInteger(), BigInteger.ONE);
        assertEquals(Acl2Integer.make(2L).getJavaBigInteger(), BigInteger.TWO);
        assertEquals(Acl2Integer.make(10L).getJavaBigInteger(), BigInteger.TEN);
        assertEquals(Acl2Integer.make(-1L).getJavaBigInteger(),
                new BigInteger("-1"));
        assertEquals(Acl2Integer.make(2678L).getJavaBigInteger(),
                new BigInteger("2678"));
        assertEquals(Acl2Integer.make(-1000000000L).getJavaBigInteger(),
                new BigInteger("-1000000000"));
        assertEquals(Acl2Integer.make(-1000000000000000000L).
                        getJavaBigInteger(),
                new BigInteger("-1000000000000000000"));
    }

    @Test
    void getJavaBigIntegerFromMakeBigInteger() {
        assertEquals(Acl2Integer.make(BigInteger.ZERO).getJavaBigInteger(),
                BigInteger.ZERO);
        assertEquals(Acl2Integer.make(BigInteger.ONE).getJavaBigInteger(),
                BigInteger.ONE);
        assertEquals(Acl2Integer.make(BigInteger.TWO).getJavaBigInteger(),
                BigInteger.TWO);
        assertEquals(Acl2Integer.make(BigInteger.TEN).getJavaBigInteger(),
                BigInteger.TEN);
        assertEquals(Acl2Integer.make(new BigInteger("124")).
                        getJavaBigInteger(),
                new BigInteger("124"));
        assertEquals(Acl2Integer.make
                        (new BigInteger("58748592475802735872046572345892645")).
                        getJavaBigInteger(),
                new BigInteger("58748592475802735872046572345892645"));
    }

    @Test
    void getNumeratorFromConstant() {
        assertEquals(Acl2Integer.ZERO.getNumerator(), Acl2Integer.ZERO);
        assertEquals(Acl2Integer.ONE.getNumerator(), Acl2Integer.ONE);
    }

    @Test
    void getNumeratorFromMakeInt() {
        assertEquals(Acl2Integer.make(0).getNumerator(),
                Acl2Integer.ZERO);
        assertEquals(Acl2Integer.make(1).getNumerator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2).getNumerator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Integer.make(10).getNumerator(),
                Acl2Integer.make(10));
        assertEquals(Acl2Integer.make(-1).getNumerator(),
                Acl2Integer.make(-1));
        assertEquals(Acl2Integer.make(2678).getNumerator(),
                Acl2Integer.make(2678));
        assertEquals(Acl2Integer.make(-1000000000).getNumerator(),
                Acl2Integer.make(-1000000000));
    }

    @Test
    void getNumeratorFromMakeLong() {
        assertEquals(Acl2Integer.make(0L).getNumerator(),
                Acl2Integer.ZERO);
        assertEquals(Acl2Integer.make(1L).getNumerator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2L).getNumerator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Integer.make(10L).getNumerator(),
                Acl2Integer.make(10));
        assertEquals(Acl2Integer.make(-1L).getNumerator(),
                Acl2Integer.make(-1));
        assertEquals(Acl2Integer.make(2678L).getNumerator(),
                Acl2Integer.make(2678));
        assertEquals(Acl2Integer.make(-1000000000L).getNumerator(),
                Acl2Integer.make(-1000000000));
        assertEquals(Acl2Integer.make(-1000000000000000000L).
                        getNumerator(),
                Acl2Integer.make(-1000000000000000000L));
    }

    @Test
    void genNumeratorFromMakeBigInteger() {
        assertEquals(Acl2Integer.make(BigInteger.ZERO).getNumerator(),
                Acl2Integer.ZERO);
        assertEquals(Acl2Integer.make(BigInteger.ONE).getNumerator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(BigInteger.TWO).getNumerator(),
                Acl2Integer.make(2));
        assertEquals(Acl2Integer.make(BigInteger.TEN).getNumerator(),
                Acl2Integer.make(10));
        assertEquals(Acl2Integer.make(new BigInteger("124")).getNumerator(),
                Acl2Integer.make(124));
        assertEquals(Acl2Integer.make
                        (new BigInteger("58748592475802735872046572345892645")).
                        getNumerator(),
                Acl2Integer.make
                        (new BigInteger
                                ("58748592475802735872046572345892645")));
    }

    @Test
    void getDenominatorFromConstant() {
        assertEquals(Acl2Integer.ZERO.getDenominator(), Acl2Integer.ONE);
        assertEquals(Acl2Integer.ONE.getDenominator(), Acl2Integer.ONE);
    }

    @Test
    void getDenominatorFromMakeInt() {
        assertEquals(Acl2Integer.make(0).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(1).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(10).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(-1).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2678).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(-1000000000).getDenominator(),
                Acl2Integer.ONE);
    }

    @Test
    void getDenominatorFromMakeLong() {
        assertEquals(Acl2Integer.make(0L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(1L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(10L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(-1L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(2678L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(-1000000000L).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(-1000000000000000000L).
                        getDenominator(),
                Acl2Integer.ONE);
    }

    @Test
    void getDenominatorFromMakeBigInteger() {
        assertEquals(Acl2Integer.make(BigInteger.ZERO).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(BigInteger.ONE).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(BigInteger.TWO).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(BigInteger.TEN).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make(new BigInteger("124")).getDenominator(),
                Acl2Integer.ONE);
        assertEquals(Acl2Integer.make
                        (new BigInteger("58748592475802735872046572345892645")).
                        getDenominator(),
                Acl2Integer.ONE);
    }

    @Test
    void compareToIntegers() { // compare arithmetically -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Integer.ZERO) == 0);
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Integer.ONE) < 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Integer.ZERO) > 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Integer.ONE) == 0);
        assertTrue(Acl2Integer.make(2728L).
                compareTo(Acl2Integer.make(10000)) < 0);
        assertTrue(Acl2Integer.make(BigInteger.TEN).
                compareTo(Acl2Integer.make(-11)) > 0);
        assertTrue(Acl2Integer.make(189).compareTo(Acl2Integer.make(189)) == 0);
    }

    @Test
    void compareToRatios() { // compare arithmetically -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Rational.make(2, 3)) < 0);
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Rational.make(-2, 3)) > 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Rational.make(5, 3)) < 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Rational.make(-5, 3)) > 0);
        assertTrue(Acl2Integer.make(7383).compareTo
                (Acl2Rational.make(1000000, 999)) > 0);
        assertTrue(Acl2Integer.make(-7383).compareTo
                (Acl2Rational.make(-1000000, 999)) < 0);
    }

    @Test
    void compareToComplexRationals() {
        // compare lexicographically -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Number.make(1, 100)) < 0);
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Number.make(-1, 100)) > 0);
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Number.make(0, 100)) < 0);
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Number.make(0, -100)) > 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Number.make(5, 100)) < 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Number.make(0, 100)) > 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Number.make(1, 100)) < 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Number.make(1, -100)) > 0);
        assertTrue(Acl2Integer.make(13579).
                compareTo(Acl2Number.make(13580, 0)) < 0);
        assertTrue(Acl2Integer.make(13579).
                compareTo(Acl2Number.make(13578, 0)) > 0);
        assertTrue(Acl2Integer.make(13579).
                compareTo(Acl2Number.make(13579, 1000)) < 0);
        assertTrue(Acl2Integer.make(13579).
                compareTo(Acl2Number.make(13579, -15)) > 0);
    }

    @Test
    void compareToCharacters() { // integers come before -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Character.make('a')) < 0);
        assertTrue(Acl2Integer.make(1).compareTo(Acl2Character.make('1')) < 0);
        assertTrue(Acl2Integer.make(12345).
                compareTo(Acl2Character.make('#')) < 0);
    }

    @Test
    void compareToStrings() { // integers come before -- see ACL2's alphorder
        assertTrue(Acl2Integer.ONE.compareTo(Acl2String.ACL2) < 0);
        assertTrue(Acl2Integer.make(10).compareTo(Acl2String.make("10")) < 0);
        assertTrue(Acl2Integer.make(-2).compareTo(Acl2String.make("abc")) < 0);
    }

    @Test
    void compareToSymbols() { // integers come before -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.compareTo(Acl2Symbol.T) < 0);
        assertTrue(Acl2Integer.ONE.compareTo(Acl2Symbol.NIL) < 0);
    }

    @Test
    void compareToConsPairs() { // integers come before -- see ACL2's alphorder
        assertTrue(Acl2Integer.ZERO.
                compareTo(Acl2ConsPair.make(Acl2String.EMPTY,
                        Acl2Integer.ZERO)) < 0);
        assertTrue(Acl2Integer.make(-800).
                compareTo(Acl2ConsPair.make(Acl2Symbol.CAR,
                        Acl2Rational.make(1, 3))) < 0);
    }

    @Test
    void equalsToIntegers() { // equality of numeric values
        assertTrue(Acl2Integer.ZERO.equals(Acl2Integer.ZERO));
        assertTrue(Acl2Integer.ZERO.equals(Acl2Integer.make(0)));
        assertTrue(Acl2Integer.ZERO.equals(Acl2Integer.make(0L)));
        assertTrue(Acl2Integer.ZERO.equals(Acl2Integer.make(BigInteger.ZERO)));
        assertTrue(Acl2Integer.make(0).equals(Acl2Integer.ZERO));
        assertTrue(Acl2Integer.make(0L).equals(Acl2Integer.ZERO));
        assertTrue(Acl2Integer.make(BigInteger.ZERO).equals(Acl2Integer.ZERO));
        assertTrue(Acl2Integer.ONE.equals(Acl2Integer.ONE));
        assertTrue(Acl2Integer.make(33).equals(Acl2Integer.make(33L)));
    }

    @Test
    void equalsToNonIntegers() { // not equal
        // ratios:
        assertFalse(Acl2Integer.ZERO.equals(Acl2Rational.make(1, 3)));
        assertFalse(Acl2Integer.ZERO.equals(Acl2Rational.make(-121, 3333)));
        // complex rationals:
        assertFalse(Acl2Integer.ZERO.equals(Acl2Number.make(0, 3)));
        assertFalse(Acl2Integer.ZERO.equals(Acl2Number.make(-10, -10)));
        // characters:
        assertFalse(Acl2Integer.make(5).equals(Acl2Character.make('5')));
        assertFalse(Acl2Integer.make(0).equals(Acl2Character.make('Q')));
        // strings:
        assertFalse(Acl2Integer.ONE.equals(Acl2String.make("ONE")));
        assertFalse(Acl2Integer.make(12).equals(Acl2String.make("")));
        // symbols:
        assertFalse(Acl2Integer.make(-77).equals(Acl2Symbol.CAR));
        assertFalse(Acl2Integer.ONE.equals(Acl2Symbol.CDR));
        // cons pairs:
        assertFalse(Acl2Integer.make(-19).
                equals(Acl2ConsPair.make(Acl2Integer.ZERO,
                        Acl2Number.make(1, 0))));
    }

}
