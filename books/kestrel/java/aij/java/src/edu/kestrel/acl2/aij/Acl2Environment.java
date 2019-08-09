/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Representation of (part of) the ACL2 execution environment.
 */
public final class Acl2Environment {

    //////////////////////////////////////// private members:

    /**
     * Prevents the creation of instances of this class
     * by code outside this class.
     * Code in this class does not create instances of this class either.
     * This class is used only for its static members.
     */
    private Acl2Environment() {
    }

    /**
     * Content of the {@code *pkg-witness-name*} ACL2 constant.
     * This constant describes
     * the exact semantics of the ACL2 function {@code pkg-witness}.
     * The value of this ACL2 constant is an ACL2 string,
     * but we use the corresponding Java string here.
     */
    private static String packageWitnessName;

    //////////////////////////////////////// package-private members:

    /**
     * Returns the content of the {@code *pkg-witness-name*} ACL2 constant.
     */
    static String getPackageWitnessName() {
        return packageWitnessName;
    }

    //////////////////////////////////////// public members:

    /**
     * Sets the content of the {@code *pkg-witness-name*} ACL2 constant.
     *
     * @throws IllegalArgumentException if content is null
     * @throws IllegalStateException    if the content is already set
     */
    public static void setPackageWitnessName(String content) {
        if (content == null)
            throw new IllegalArgumentException("Null witness.");
        if (packageWitnessName == null)
            packageWitnessName = content;
        else
            throw new IllegalStateException
                    ("Witness already defined: \""
                            + packageWitnessName
                            + "\".");
    }
}
