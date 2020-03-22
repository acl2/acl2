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

}
