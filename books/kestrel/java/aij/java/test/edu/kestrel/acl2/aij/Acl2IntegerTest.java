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
    void getJavaIntFromMake() {
        assertEquals(Acl2Integer.make(0).getJavaInt(), 0);
        assertEquals(Acl2Integer.make(1).getJavaInt(), 1);
        assertEquals(Acl2Integer.make(-1).getJavaInt(), -1);
        assertEquals(Acl2Integer.make(2678).getJavaInt(), 2678);
        assertEquals(Acl2Integer.make(-1000000000).getJavaInt(), -1000000000);
    }

    @Test
    void getJavaIntFromMakeFail() {
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make(44444444444444L).getJavaInt());
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("72983728478274982748282710100"))
                        .getJavaInt());
    }

    @Test
    void getJavaLongFromConstant() {
        assertEquals(Acl2Integer.ZERO.getJavaLong(), 0L);
        assertEquals(Acl2Integer.ONE.getJavaLong(), 1L);
    }

    @Test
    void getJavaLongFromMake() {
        assertEquals(Acl2Integer.make(0).getJavaLong(), 0L);
        assertEquals(Acl2Integer.make(1).getJavaLong(), 1L);
        assertEquals(Acl2Integer.make(-1).getJavaLong(), -1L);
        assertEquals(Acl2Integer.make(2678).getJavaLong(), 2678L);
        assertEquals(Acl2Integer.make(-1000000000).getJavaLong(), -1000000000L);
        assertEquals(Acl2Integer.make(-1000000000000000000L).getJavaLong(),
                -1000000000000000000L);
    }

    @Test
    void getJavaLongFromMakeFail() {
        assertThrows(ArithmeticException.class,
                () -> Acl2Integer.make
                        (new BigInteger("72983728478274982748282710100"))
                        .getJavaLong());
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
    void getJavaBigIntegerFromMake() {
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

}
