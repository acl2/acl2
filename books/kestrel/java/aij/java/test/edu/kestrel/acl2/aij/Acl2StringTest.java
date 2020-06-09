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

    @Test
    void toStringFromConstant() {
        assertEquals(Acl2String.EMPTY.toString(), "\"\"");
        assertEquals(Acl2String.ACL2.toString(), "\"ACL2\"");
    }

    @Test
    void toStringFromMakeNormal() {
        assertEquals(Acl2String.make("Normal.").toString(), "\"Normal.\"");
        assertEquals(Acl2String.make("$_()").toString(), "\"$_()\"");
    }

    @Test
    void toStringFromMakeHex() {
        assertEquals(Acl2String.make("  ").toString(), "\"\\20\\20\"");
        assertEquals(Acl2String.make("O\234o").toString(), "\"O\\9co\"");
        assertEquals(Acl2String.make("O\ro").toString(), "\"O\\0do\"");
        assertEquals(Acl2String.make("C:\\dir").toString(), "\"C:\\\\dir\"");
    }

    @Test
    void compareToStrings() { // compare alphabetically -- see ACL2's alphorder
        assertTrue(Acl2String.EMPTY.compareTo(Acl2String.EMPTY) == 0);
        assertTrue(Acl2String.ACL2.compareTo(Acl2String.ACL2) == 0);
        assertTrue(Acl2String.make("ab&1 Op").
                compareTo(Acl2String.make("ab&1 Op")) == 0);
        assertTrue(Acl2String.make("abb").
                compareTo(Acl2String.make("zuu")) < 0);
        assertTrue(Acl2String.make("LONG").
                compareTo(Acl2String.make("LONGer")) < 0);
        assertTrue(Acl2String.EMPTY.compareTo(Acl2String.ACL2) < 0);
        assertTrue(Acl2String.make("Later.").
                compareTo(Acl2String.make("Earlier.")) > 0);
        assertTrue(Acl2String.make("longER").
                compareTo(Acl2String.make("long")) > 0);
        assertTrue(Acl2String.ACL2.compareTo(Acl2String.EMPTY) > 0);
    }

    @Test
    void compareToCharacters() { // strings come after -- see ACL2's alphorder
        assertTrue(Acl2String.EMPTY.compareTo(Acl2Character.CODE_0) > 0);
        assertTrue(Acl2String.ACL2.compareTo(Acl2Character.CODE_0) > 0);
        assertTrue(Acl2String.make("theorem").
                compareTo(Acl2Character.make('q')) > 0);
        assertTrue(Acl2String.make("PROVER").
                compareTo(Acl2Character.make('e')) > 0);
        assertTrue(Acl2String.make("").
                compareTo(Acl2Character.make('d')) > 0);
    }

    @Test
    void compareToNumbers() { // strings come after -- see ACL2's alphorder
        assertTrue(Acl2String.EMPTY.compareTo(Acl2Integer.ZERO) > 0);
        assertTrue(Acl2String.make("any string").
                compareTo(Acl2Integer.make(335)) > 0);
        assertTrue(Acl2String.make("ABO").
                compareTo(Acl2Rational.make(-2, 3)) > 0);
        assertTrue(Acl2String.make("_-_-_").
                compareTo(Acl2Number.make(0, 1)) > 0);
    }

    @Test
    void compareToSymbols() { // strings come before -- see ACL2's alphorder
        assertTrue(Acl2String.EMPTY.compareTo(Acl2Symbol.T) < 0);
        assertTrue(Acl2String.ACL2.compareTo(Acl2Symbol.CONSP) < 0);
        assertTrue(Acl2String.make("one two three").
                compareTo(Acl2Symbol.IF) < 0);
    }

    @Test
    void compareToConsPairs() { // strings come before -- see ACL2's lexorder
        assertTrue(Acl2String.EMPTY.
                compareTo(Acl2ConsPair.make(Acl2String.EMPTY,
                        Acl2String.EMPTY)) < 0);
        assertTrue(Acl2String.ACL2.
                compareTo(Acl2ConsPair.make(Acl2Integer.make(33),
                        Acl2ConsPair.make(Acl2Character.make('a'),
                                Acl2Character.make('b')))) < 0);
        assertTrue(Acl2String.make("a STRing").
                compareTo(Acl2ConsPair.make(Acl2Symbol.T, Acl2Symbol.NIL)) < 0);
    }

    @Test
    void equalsToStrings() { // equality of underlying character sequences
        assertTrue(Acl2String.EMPTY.equals(Acl2String.EMPTY));
        assertTrue(Acl2String.ACL2.equals(Acl2String.ACL2));
        assertTrue(Acl2String.make("same").equals(Acl2String.make("same")));
        assertFalse(Acl2String.EMPTY.equals(Acl2String.ACL2));
        assertFalse(Acl2String.make("acl2").equals(Acl2String.ACL2));
        assertFalse(Acl2String.make("!@#").equals(Acl2String.make("{}")));
    }

    @Test
    void equalsToNonStrings() { // not equal
        // characters:
        assertFalse(Acl2String.EMPTY.equals(Acl2Character.CODE_0));
        assertFalse(Acl2String.ACL2.equals(Acl2Character.make('c')));
        assertFalse(Acl2String.make("a").equals(Acl2Character.make('a')));
        // symbols:
        assertFalse(Acl2String.EMPTY.equals(Acl2Symbol.T));
        assertFalse(Acl2String.ACL2.equals(Acl2Symbol.BINARY_STAR));
        assertFalse(Acl2String.make("NIL").equals(Acl2Symbol.NIL));
        // numbers:
        assertFalse(Acl2String.EMPTY.equals(Acl2Integer.ONE));
        assertFalse(Acl2String.ACL2.equals(Acl2Integer.make(11)));
        assertFalse(Acl2String.make("STR").equals(Acl2Rational.make(1, 2)));
        assertFalse(Acl2String.make("x").equals(Acl2Number.make(-1, -2)));
        // cons pairs:
        assertFalse(Acl2String.make("something").
                equals(Acl2ConsPair.make(Acl2Integer.make(34),
                        Acl2String.make("something"))));
    }

}
