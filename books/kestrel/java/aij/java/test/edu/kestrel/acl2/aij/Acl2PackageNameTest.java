/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2PackageNameTest {

    @Test
    void makeNull() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make(null));
    }

    @Test
    void makeEmpty() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make(""));
    }

    @Test
    void makeLowercase() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("p"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("abc"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("MYpkg"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("myPKG"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("aBc"));
    }

    @Test
    void makeNonASCII() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\200"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\200\240\300"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("PKG\200"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\200PKG"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("MY\200PKG"));
    }

    @Test
    void makeControlASCII() { // i.e. ASCII characters below 32 (except 10)
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\b"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\b\t\f\r"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\bPKG"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("PKG\b"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("MY\bPKG"));
    }

    @Test
    void makeDelete() { // i.e. ASCII character 127
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\377"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\377\377"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("\377PKG"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("PKG\377"));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2PackageName.make("MY\377PKG"));
    }

    @Test
    void makeLetters() {
        assertDoesNotThrow(() -> Acl2PackageName.make("KEYWORD"));
        assertDoesNotThrow(() -> Acl2PackageName.make("JAVA"));
        assertDoesNotThrow(() -> Acl2PackageName.make("STD"));
        assertDoesNotThrow(() -> Acl2PackageName.make("MYPKG"));
        assertDoesNotThrow(() -> Acl2PackageName.make("P"));
        assertDoesNotThrow
                (() -> Acl2PackageName.make("ABCDEFGHIJKLMNOPQRSTUVWXYZ"));
    }

    @Test
    void makeLettersDashes() {
        assertDoesNotThrow(() -> Acl2PackageName.make("COMMON-LISP"));
        assertDoesNotThrow(() -> Acl2PackageName.make("MY-PKG"));
        assertDoesNotThrow(() -> Acl2PackageName.make("P-Q"));
        assertDoesNotThrow(() -> Acl2PackageName.make("-PKG"));
        assertDoesNotThrow(() -> Acl2PackageName.make("PKG-"));
        assertDoesNotThrow(() -> Acl2PackageName.make("---P-K-G---"));
    }

    @Test
    void makeDigits() {
        assertDoesNotThrow(() -> Acl2PackageName.make("0"));
        assertDoesNotThrow(() -> Acl2PackageName.make("1"));
        assertDoesNotThrow(() -> Acl2PackageName.make("123"));
        assertDoesNotThrow(() -> Acl2PackageName.make("0123456789"));
        assertDoesNotThrow(() -> Acl2PackageName.make("8888"));
    }

    @Test
    void makeLettersDigits() {
        assertDoesNotThrow(() -> Acl2PackageName.make("ACL2"));
        assertDoesNotThrow(() -> Acl2PackageName.make("PKG1"));
        assertDoesNotThrow(() -> Acl2PackageName.make("PKG2"));
        assertDoesNotThrow(() -> Acl2PackageName.make("PKG3"));
        assertDoesNotThrow(() -> Acl2PackageName.make("123P"));
    }

    @Test
    void makeLettersDigitsDashes() {
        assertDoesNotThrow(() -> Acl2PackageName.make("ACL2-USER"));
        assertDoesNotThrow(() -> Acl2PackageName.make("CATCH-22"));
        assertDoesNotThrow(() -> Acl2PackageName.make("-0-A---"));
    }

    @Test
    void makeStrange() {
        assertDoesNotThrow(() -> Acl2PackageName.make(" "));
        assertDoesNotThrow(() -> Acl2PackageName.make("-"));
        assertDoesNotThrow(() -> Acl2PackageName.make("_"));
        assertDoesNotThrow(() -> Acl2PackageName.make("%%%"));
        assertDoesNotThrow(() -> Acl2PackageName.make(".,:;!?"));
        assertDoesNotThrow(() -> Acl2PackageName.make("A --> B"));
    }

    @Test
    void getJavaStringFromConstants() {
        assertEquals(Acl2PackageName.KEYWORD.getJavaString(), "KEYWORD");
        assertEquals(Acl2PackageName.LISP.getJavaString(), "COMMON-LISP");
        assertEquals(Acl2PackageName.ACL2.getJavaString(), "ACL2");
        assertEquals(Acl2PackageName.ACL2_OUTPUT.getJavaString(),
                "ACL2-OUTPUT-CHANNEL");
        assertEquals(Acl2PackageName.ACL2_INPUT.getJavaString(),
                "ACL2-INPUT-CHANNEL");
        assertEquals(Acl2PackageName.ACL2_PC.getJavaString(), "ACL2-PC");
        assertEquals(Acl2PackageName.ACL2_USER.getJavaString(), "ACL2-USER");
    }

    @Test
    void getJavaStringFromMake() {
        assertEquals(Acl2PackageName.make("PKG").getJavaString(), "PKG");
        assertEquals(Acl2PackageName.make("188").getJavaString(), "188");
        assertEquals(Acl2PackageName.make("A2-U").getJavaString(), "A2-U");
        assertEquals(Acl2PackageName.make("+ *").getJavaString(), "+ *");
    }

    @Test
    void toStringFromConstants() {
        assertEquals(Acl2PackageName.KEYWORD.toString(), "KEYWORD");
        assertEquals(Acl2PackageName.LISP.toString(), "COMMON-LISP");
        assertEquals(Acl2PackageName.ACL2.toString(), "ACL2");
        assertEquals(Acl2PackageName.ACL2_OUTPUT.toString(),
                "ACL2-OUTPUT-CHANNEL");
        assertEquals(Acl2PackageName.ACL2_INPUT.toString(),
                "ACL2-INPUT-CHANNEL");
        assertEquals(Acl2PackageName.ACL2_PC.toString(), "ACL2-PC");
        assertEquals(Acl2PackageName.ACL2_USER.toString(), "ACL2-USER");
    }

    @Test
    void toStringFromMakeNoBars() {
        assertEquals(Acl2PackageName.make("ABC").toString(), "ABC");
        assertEquals(Acl2PackageName.make("X123").toString(), "X123");
        assertEquals(Acl2PackageName.make("H2O").toString(), "H2O");
        assertEquals(Acl2PackageName.make("H2-O").toString(), "H2-O");
        assertEquals(Acl2PackageName.make("--").toString(), "--");
    }

    @Test
    void toStringFromMakeBars() {
        assertEquals(Acl2PackageName.make("MY_PKG").toString(), "|MY_PKG|");
        assertEquals(Acl2PackageName.make("8080").toString(), "|8080|");
        assertEquals(Acl2PackageName.make("$").toString(), "|$|");
        assertEquals(Acl2PackageName.make("|").toString(), "|\\||");
        assertEquals(Acl2PackageName.make("\\").toString(), "|\\\\|");
    }

    @Test
    void compareToConstants() {
        assertTrue(Acl2PackageName.KEYWORD.
                compareTo(Acl2PackageName.ACL2) > 0);
        assertTrue(Acl2PackageName.ACL2_USER.
                compareTo(Acl2PackageName.LISP) < 0);
        assertTrue(Acl2PackageName.ACL2_PC.
                compareTo(Acl2PackageName.ACL2_PC) == 0);
    }

    @Test
    void compareToMake() {
        assertTrue(Acl2PackageName.make("PKG").
                compareTo(Acl2PackageName.make("X")) < 0);
        assertTrue(Acl2PackageName.make("PKG").
                compareTo(Acl2PackageName.make("PKGPKG")) < 0);
        assertTrue(Acl2PackageName.make("ZZZ").
                compareTo(Acl2PackageName.make("PKG")) > 0);
        assertTrue(Acl2PackageName.make("ZZZZZZ").
                compareTo(Acl2PackageName.make("ZZZ")) > 0);
        assertTrue(Acl2PackageName.make("SAME-0").
                compareTo(Acl2PackageName.make("SAME-0")) == 0);
    }

}
