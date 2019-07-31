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
     * Information about the defined ACL2 packages.
     * This maps the name of each defined package
     * to a Java list of its imported symbols,
     * consistently with the {@code pkg-imports} ACL2 function.
     * This field is never {@code null}.
     * For each defined package,
     * its list of symbols never has two symbols with the same name.
     * The order of the imported symbols is
     * as returned by the {@cod pkg-imports} ACL2 function.
     */
    private static final Map<Acl2PackageName, List<Acl2Symbol>>
            packageDefs = new HashMap<>();

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
     * Checks if an ACL2 package with the given name is defined.
     */
    static boolean hasPackage(Acl2PackageName packageName) {
        return packageDefs.containsKey(packageName);
    }

    /**
     * Returns a Java list of the imported symbols of the named ACL2 package.
     * The returned list is created anew, so it can be freely modified.
     * This method should be called only if the package is defined,
     * i.e. if {@link #hasPackage(Acl2PackageName)} returns {@code true}.
     */
    static List<Acl2Symbol> getImportedList(Acl2PackageName packageName) {
        List<Acl2Symbol> list = packageDefs.get(packageName);
        List<Acl2Symbol> result = new ArrayList<>(list.size());
        result.addAll(list);
        return result;
    }

    /**
     * Returns the content of the {@code *pkg-witness-name*} ACL2 constant.
     */
    static String getPackageWitnessName() {
        return packageWitnessName;
    }

    //////////////////////////////////////// public members:

    /**
     * Adds an ACL2 package definition,
     * consisting of a package name and a Java list of imported symbols.
     * A package with the same name must not have been already defined.
     * The imported symbols must have all different names.
     * This method makes an internal copy of the argument list,
     * which can be thus freely modified after this method returns.
     *
     * @throws IllegalArgumentException if packageName or imported is null,
     *                                  or two imported symbols
     *                                  have the same name
     * @throws IllegalStateException    if a package with the given name
     *                                  is already defined
     */
    public static void addPackageDef(Acl2PackageName packageName,
                                     List<Acl2Symbol> imported) {
        if (packageName == null)
            throw new IllegalArgumentException("Null package name.");
        if (imported == null)
            throw new IllegalArgumentException("Null import list.");
        if (packageDefs.containsKey(packageName))
            throw new IllegalStateException
                    ("Package already defined: \"" + packageName + "\".");
        List<Acl2Symbol> importedCopy = new ArrayList<>(imported.size());
        for (Acl2Symbol symbol : imported) {
            Acl2String symbolName = symbol.getName();
            if (importedCopy.contains(symbol))
                throw new IllegalArgumentException
                        ("Symbol with name "
                                + symbolName
                                + " already imported by package "
                                + packageName + ".");
            importedCopy.add(symbol);
        }
        packageDefs.put(packageName, importedCopy);
        Acl2Symbol.addPackageImports(packageName, importedCopy);
    }

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
