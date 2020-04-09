/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2CharacterTest {

    @Test
    void makeWrong() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\u0100'));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\ua802'));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\uffff'));
    }

    @Test
    void makeRight() {
        assertDoesNotThrow(() -> Acl2Character.make('\0'));
        assertDoesNotThrow(() -> Acl2Character.make('A'));
        assertDoesNotThrow(() -> Acl2Character.make('x'));
        assertDoesNotThrow(() -> Acl2Character.make('5'));
        assertDoesNotThrow(() -> Acl2Character.make('?'));
        assertDoesNotThrow(() -> Acl2Character.make(' '));
        assertDoesNotThrow(() -> Acl2Character.make('*'));
        assertDoesNotThrow(() -> Acl2Character.make('\n'));
        assertDoesNotThrow(() -> Acl2Character.make('\200'));
        assertDoesNotThrow(() -> Acl2Character.make('\300'));
        assertDoesNotThrow(() -> Acl2Character.make('\u00ff'));
    }

    @Test
    void getJavaCharFromConstant() {
        assertEquals(Acl2Character.CODE_0.getJavaChar(), '\0');
    }

    @Test
    void getJavaCharFromMake() {
        assertEquals(Acl2Character.make('a').getJavaChar(), 'a');
        assertEquals(Acl2Character.make('\7').getJavaChar(), '\7');
        assertEquals(Acl2Character.make('|').getJavaChar(), '|');
        assertEquals(Acl2Character.make('\u00f0').getJavaChar(), '\u00f0');
    }

    @Test
    void toStringFromConstant() {
        assertEquals(Acl2Character.CODE_0.toString(), "#\\00");
    }

    @Test
    void toStringFromMakeNormal() {
        assertEquals(Acl2Character.make('c').toString(), "#\\c");
        assertEquals(Acl2Character.make('F').toString(), "#\\F");
        assertEquals(Acl2Character.make('*').toString(), "#\\*");
        assertEquals(Acl2Character.make('%').toString(), "#\\%");
    }

    @Test
    void toStringFromMakeSpecial() {
        assertEquals(Acl2Character.make(' ').toString(), "#\\Space");
        assertEquals(Acl2Character.make('\t').toString(), "#\\Tab");
        assertEquals(Acl2Character.make('\n').toString(), "#\\Newline");
        assertEquals(Acl2Character.make('\f').toString(), "#\\Page");
        assertEquals(Acl2Character.make('\r').toString(), "#\\Return");
        assertEquals(Acl2Character.make('\177').toString(), "#\\Rubout");
    }

    @Test
    void toStringFromMakeHex() {
        assertEquals(Acl2Character.make('\u0000').toString(), "#\\00");
        assertEquals(Acl2Character.make('\u00ff').toString(), "#\\ff");
        assertEquals(Acl2Character.make('\u00b2').toString(), "#\\b2");
        assertEquals(Acl2Character.make('\u0014').toString(), "#\\14");
    }

    @Test
    void compareToCharacters() { // compare codes -- see ACL2's alphorder
        assertTrue(Acl2Character.CODE_0.compareTo(Acl2Character.CODE_0) == 0);
        assertTrue(Acl2Character.CODE_0.
                compareTo(Acl2Character.make('Y')) < 0);
        assertTrue(Acl2Character.make('i').
                compareTo(Acl2Character.CODE_0) > 0);
        assertTrue(Acl2Character.make('8').
                compareTo(Acl2Character.make('\377')) < 0);
        assertTrue(Acl2Character.make('Z').
                compareTo(Acl2Character.make('A')) > 0);
        assertTrue(Acl2Character.make('@').
                compareTo(Acl2Character.make('@')) == 0);
    }

    @Test
    void compareToNumbers() { // characters come after -- see ACL2's alphorder
        assertTrue(Acl2Character.make('a').
                compareTo(Acl2Integer.make(-45)) > 0);
        assertTrue(Acl2Character.make('^').
                compareTo(Acl2Rational.make(-45,4)) > 0);
        assertTrue(Acl2Character.make('{').
                compareTo(Acl2Number.make(1, 1)) > 0);
    }

    @Test
    void compareToStrings() { // characters come before -- see ACL2's alphorder
        assertTrue(Acl2Character.make('H').
                compareTo(Acl2String.make("some string")) < 0);
        assertTrue(Acl2Character.make('\u00ee').
                compareTo(Acl2String.make("")) < 0);
        assertTrue(Acl2Character.make('H').
                compareTo(Acl2String.make("ABCDEFGHIJKLMNOPQRSTUVWXYZ")) < 0);
        assertTrue(Acl2Character.make('H').compareTo(Acl2String.EMPTY) < 0);
        assertTrue(Acl2Character.make('H').compareTo(Acl2String.ACL2) < 0);
    }

    @Test
    void compareToSymbols() { // characters come before -- see ACL2's alphorder
        assertTrue(Acl2Character.make('T').compareTo(Acl2Symbol.T) < 0);
        assertTrue(Acl2Character.make('t').compareTo(Acl2Symbol.NIL) < 0);
    }

    @Test
    void compareToConsPairs() { // characters come before -- see ACL2's lexorder
        assertTrue(Acl2Character.CODE_0.
                compareTo(Acl2ConsPair.make(Acl2Character.make('w'),
                        Acl2String.EMPTY)) < 0);
        assertTrue(Acl2Character.make('C').
                compareTo(Acl2ConsPair.make(Acl2Character.make('C'),
                        Acl2Character.make('C'))) < 0);
        assertTrue(Acl2Character.make('\177').
                compareTo(Acl2ConsPair.make(Acl2Integer.make(0),
                        Acl2Symbol.LEN)) < 0);
    }

    @Test
    void equalsToCharacters() { // equality of codes
        assertTrue(Acl2Character.make('o').equals(Acl2Character.make('o')));
        assertTrue(Acl2Character.make('\22').equals(Acl2Character.make('\22')));
        assertTrue(Acl2Character.CODE_0.equals(Acl2Character.CODE_0));
        assertFalse(Acl2Character.CODE_0.equals(Acl2Character.make('4')));
        assertFalse(Acl2Character.make('0').equals(Acl2Character.make('4')));
        assertFalse(Acl2Character.make('\2').equals(Acl2Character.make('2')));
    }

    @Test
    void equalsToNonCharacters() {
        // strings:
        assertFalse(Acl2Character.CODE_0.equals(Acl2String.make("str")));
        assertFalse(Acl2Character.make('a').equals(Acl2String.make("a")));
        // symbols:
        assertFalse(Acl2Character.CODE_0.equals(Acl2Symbol.T));
        assertFalse(Acl2Character.make('~').equals(Acl2Symbol.IF));
        // numbers:
        assertFalse(Acl2Character.make('-').equals(Acl2Integer.make(473)));
        assertFalse(Acl2Character.make('-').equals(Acl2Rational.make(3,4)));
        assertFalse(Acl2Character.make('-').equals(Acl2Number.make(3,4)));
        // cons pairs:
        assertFalse(Acl2Character.CODE_0.
                equals(Acl2ConsPair.make(Acl2Character.make('a'),
                        Acl2Number.make(Acl2Rational.make(2,3),
                                Acl2Rational.make(-3,4)))));
    }

}
