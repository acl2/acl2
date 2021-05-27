/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Representation of ACL2 symbols.
 * These are the values that satisfy {@code symbolp}.
 */
public final class Acl2Symbol extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Package name of the symbol.
     * Invariant: not null.
     */
    private final Acl2PackageName packageName;

    /**
     * Name of the symbol.
     * Invariant: not null.
     */
    private final Acl2String name;

    /**
     * Constructs a symbol with the given package name and name.
     *
     * @param packageName The package name of the symbol.
     *                    Invariant: not null.
     * @param name        The name of the symbol.
     *                    Invariant: not null.
     */
    private Acl2Symbol(Acl2PackageName packageName, Acl2String name) {
        this.packageName = packageName;
        this.name = name;
    }

    /**
     * All the symbols created so far.
     * These are stored as a map from package names
     * to maps from strings to symbols:
     * this structure is isomorphic to a map
     * from (i) package names paired with string to (ii) symbols.
     * <p>
     * For all of these associations,
     * the string is the {@link #name} field of the symbol.
     * For some of these associations,
     * the package name is the {@link #packageName} field of the symbol.
     * For others, it differs, based on packages' import lists,
     * e.g. the package name {@code "ACL2"} and the symbol name {@code "CONS"}
     * are associated with the symbol
     * whose {@link #packageName} is {@link Acl2PackageName#LISP},
     * not {@link Acl2PackageName#ACL2},
     * because the {@code "ACL2"} package
     * imports the symbol {@code cons} from the {@code "COMMON-LISP"} package.
     * Some inner maps share values,
     * e.g. the inner map associated with {@code "ACL2"} in the outer map
     * maps {@code "CONS"} to the same {@link Acl2Symbol} object
     * that the inner map assocaited with {@code "COMMON-LISP"} in the outer map
     * maps {@code "CONS"}.
     * <p>
     * This nested map structure is extended in three circumstances:
     * <ol>
     * <li>
     * When {@link Acl2Package#define(Acl2PackageName, List)} is called,
     * i.e. when a new package is defined.
     * In this case, the nested map structure is extended
     * according to the package's import list
     * (see {@link #addPackageImports(Acl2PackageName, List)}).
     * The new associations have all symbols whose package names
     * match the corresponding keys in the outer map.
     * <li>
     * When {@link #imake(Acl2PackageName, Acl2String)} is called.
     * In this case, this nested map structure is consulted
     * to see if the symbol already exists.
     * If it does, it is reused.
     * Otherwise, the map structure is extended with the new symbol,
     * whose package name matches the key in the outer map in this case.
     * <li>
     * When this {@link Acl2Symbol} class is initialized.
     * The static initializer creates
     * the values of the constant fields {@link #T} and the like.
     * This starts populating the nested map structure,
     * which is initially empty.
     * Having constants for these ACL2 symbols maximizes their access speed.
     * </ol>
     * <p>
     * All the symbols are thus interned.
     * <p>
     * Invariant: not null, no null keys, no null values,
     * no null keys or values in inner maps.
     */
    private static final Map<Acl2PackageName, Map<Acl2String, Acl2Symbol>>
            symbols = new HashMap<>();

    //////////////////////////////////////// package-private members:

    /**
     * Adds information about all the symbols imported by a package.
     * This is called by {@link Acl2Package#define(Acl2PackageName, List)}
     * when a new package is defined.
     *
     * @param packageName The name of the package being defined.
     *                    Invariant: not null.
     * @param imported    The import list of the package.
     *                    Invariants: not null, no null elements.
     */
    static void addPackageImports(Acl2PackageName packageName,
                                  List<Acl2Symbol> imported) {
        Map<Acl2String, Acl2Symbol> innerMap = symbols.get(packageName);
        if (innerMap == null)
            innerMap = new HashMap<>();
        for (Acl2Symbol symbol : imported)
            innerMap.put(symbol.getName(), symbol);
        symbols.put(packageName, innerMap);
    }

    /**
     * Checks if this symbol is a symbol, which is always true.
     * This is consistent with the {@code symbolp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol symbolp() {
        return Acl2Symbol.T;
    }

    /**
     * Checks if this symbol is a symbol, which is always true,
     * returning a Java boolean instead of an ACL2 symbol.
     * This is consistent with the {@code symbolp} ACL2 function.
     *
     * @return {@code true}.
     */
    @Override
    boolean symbolpBoolean() {
        return true;
    }

    /**
     * Returns the package name of this symbol,
     * consistently with the {@code symbol-package-name} ACL2 function.
     *
     * @return The package name of this symbol.
     */
    @Override
    Acl2String symbolPackageName() {
        return Acl2String.imake(packageName.getJavaString());
    }

    /**
     * Returns the package name of this symbol,
     * consistently with the {@code symbol-package-name} ACL2 function,
     * returning a Java string instead of an ACL2 string.
     *
     * @return The package name of this symbol.
     */
    @Override
    String symbolPackageNameString() {
        return packageName.getJavaString();
    }

    /**
     * Returns the name of this symbol,
     * consistently with the {@code symbol-name} ACL2 function.
     *
     * @return The name of this symbol.
     */
    @Override
    Acl2String symbolName() {
        return name;
    }

    /**
     * Returns the name of this symbol,
     * consistently with the {@code symbol-name} ACL2 function,
     * returning a Java string instead of an ACL2 string.
     *
     * @return The name of this symbol.
     */
    @Override
    String symbolNameString() {
        return name.getJavaString();
    }

    /**
     * Interns the argument string in the package of this symbol,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this symbol is the second argument of that function
     * and the argument string is the first argument of that function.
     *
     * @param str The string to intern in the package.
     *            Invariant: not null.
     * @return The interned symbol.
     */
    @Override
    Acl2Symbol internInPackageOfThis(Acl2String str) {
        Acl2PackageName packageName = this.packageName;
        return imake(packageName, str);
    }

    /**
     * Compares this symbol with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // symbols are greater than characters:
        return 1;
    }

    /**
     * Compares this symbol with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // symbols are greater than strings:
        return 1;
    }

    /**
     * Compares this symbol with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // compare name and package names lexicographically:
        int nameCmp = this.name.compareTo(o.name);
        if (nameCmp != 0)
            return nameCmp;
        else
            return this.packageName.compareTo(o.packageName);
    }

    /**
     * Compares this symbol with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // symbols are greater than numbers:
        return 1;
    }

    /**
     * Compares this symbol with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // symbols are greater than rationals:
        return 1;
    }

    /**
     * Compares this symbol with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // symbols are greater than integers:
        return 1;
    }

    /**
     * Compares this symbol with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this symbol with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // symbols are less than cons pairs:
        return -1;
    }

    /**
     * Returns a symbol denoted by the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol.
     *                    Invariant: not null, package defined.
     * @param name        The name denoting the symbol.
     *                    Invariant: not null.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If the package is not defined.
     */
    static Acl2Symbol imake(Acl2PackageName packageName, Acl2String name) {
        Map<Acl2String, Acl2Symbol> innerMap = symbols.get(packageName);
        Acl2Symbol symbol = innerMap.get(name);
        if (symbol == null) {
            symbol = new Acl2Symbol(packageName, name);
            innerMap.put(name, symbol);
        }
        return symbol;
    }

    /**
     * Returns a symbol denoted by the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol.
     *                    Invariant: not null, package defined.
     * @param name        The name denoting the symbol.
     *                    Invariant: not null, no elements above 255.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If the package is not defined.
     */
    static Acl2Symbol imake(Acl2PackageName packageName, String name) {
        return imake(packageName, Acl2String.imake(name));
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this symbol with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this string with.
     * @return {@code true} if the object is equal to this symbol,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since symbols are interned,
           a symbol is equal to an object if
           they are the same object. */
        return this == o;
    }

    /**
     * Compares this symbol with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this symbol with.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return -o.compareToSymbol(this);
    }

    /**
     * Returns a printable representation of this symbol.
     * We always include the package prefix,
     * since there is no notion of "current package" here;
     * the package name is represented
     * as explained in {@link Acl2PackageName#toString()}.
     * The symbol name comes after two colons.
     * If the symbol name is not empty,
     * consists of only of uppercase letters, digits, and dashes,
     * and does not start with a digit,
     * then the symbol name is used as is;
     * otherwise, it is preceded and followed by vertical bars,
     * and any backslash or vertical bar in the symbol name
     * is preceded by a backslash.
     * The conditions here under which
     * the symbol name is surrounded by vertical bars
     * are more stringent than in ACL2;
     * future versions of this method may relax those conditions
     * and match ACL2's conditions more closely.
     * This scheme should ensure that symbols are always printed clearly.
     *
     * @return A printable representation of this symbol.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        boolean noBars = true;
        String jstring = this.name.getJavaString();
        noBars = noBars && !jstring.isEmpty();
        for (int i = 0; i < jstring.length(); ++i) {
            char jchar = jstring.charAt(i);
            noBars = noBars &&
                    (('A' <= jchar && jchar <= 'Z') ||
                            ('0' <= jchar && jchar <= '9' && i != 0) ||
                            (jchar == '-'));
            if (jchar == '|')
                result.append("\\|");
            else if (jchar == '\\')
                result.append("\\\\");
            else result.append(jchar);
        }
        if (!noBars) {
            result.insert(0, '|');
            result.append('|');
        }
        return this.packageName + "::" + result;
    }

    /**
     * Returns a symbol denoted by the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol.
     * @param name        The name denoting the symbol.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code packageName} or {@code name}
     *                                  is null,
     *                                  or the package is not defined.
     */
    public static Acl2Symbol make(Acl2PackageName packageName,
                                  Acl2String name) {
        if (packageName == null)
            throw new IllegalArgumentException("Null package name.");
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        if (Acl2Package.getDefined(packageName) == null)
            throw new IllegalArgumentException
                    ("Undefined package: \"" + packageName + "\".");
        return imake(packageName, name);
    }

    /**
     * Returns a symbol denoted by the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol.
     * @param name        The name denoting the symbol, as a Java string.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code packageName} or {@code name}
     *                                  is null,
     *                                  or the package is not defined,
     *                                  or {@code name} contains
     *                                  characters above 255.
     */
    public static Acl2Symbol make(Acl2PackageName packageName, String name) {
        return make(packageName, Acl2String.make(name));
    }

    /**
     * Returns a symbol denoted by the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol,
     *                    as a Java string.
     * @param name        The name denoting the symbol.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code packageName} or {@code name}
     *                                  is null,
     *                                  or the package is not defined,
     *                                  or {@code packageName} contains
     *                                  characters above 255.
     */
    public static Acl2Symbol make(String packageName, Acl2String name) {
        return make(Acl2PackageName.make(packageName), name);
    }

    /**
     * Returns an symbol with the given package name and name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @param packageName The package name denoting the symbol,
     *                    as a Java string.
     * @param name        The name denoting the symbol,
     *                    as a Java string.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code packageName} or {@code name}
     *                                  is null,
     *                                  or the package is not defined,
     *                                  or {@code packageName} contains
     *                                  characters above 255,
     *                                  or {@code name} contains
     *                                  characters above 255.
     */
    public static Acl2Symbol make(String packageName, String name) {
        return Acl2Symbol.make(Acl2PackageName.make(packageName), name);
    }

    /**
     * Returns a symbol denoted by
     * the {@code "KEYWORD"} package name and the given name.
     *
     * @param name The name denoting the symbol, as a Java string.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code name} is null
     *                                  or contains characters above 255.
     * @throws IllegalStateException    If the {@code "KEYWORD"} package
     *                                  is not defined yet.
     */
    public static Acl2Symbol makeKeyword(String name) {
        return Acl2Symbol.make(Acl2PackageName.KEYWORD, name);
    }

    /**
     * Returns an symbol denoted by
     * the {@code "COMMON-LISP"} package name and the given name.
     *
     * @param name The name denoting the symbol, as a Java string.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code name} is null
     *                                  or contains characters above 255.
     * @throws IllegalStateException    If the {@code "COMMON-LISP"} package
     *                                  is not defined yet.
     */
    public static Acl2Symbol makeLisp(String name) {
        return Acl2Symbol.make(Acl2PackageName.LISP, name);
    }

    /**
     * Returns a symbol denoted by
     * the {@code "ACL2"} package name and the given name.
     *
     * @param name The name denoting the symbol, as a Java string.
     * @return The denoted symbol.
     * @throws IllegalArgumentException If {@code name} is null
     *                                  or contains characters above 255.
     * @throws IllegalStateException    If the {@code "ACL2"} package
     *                                  is not defined yet.
     */
    public static Acl2Symbol makeAcl2(String name) {
        return Acl2Symbol.make(Acl2PackageName.ACL2, name);
    }

    /**
     * The symbol denoted by {@code acl2::t}.
     */
    public static final Acl2Symbol T;

    /**
     * The symbol denoted by {@code acl2::nil}.
     */
    public static final Acl2Symbol NIL;

    /**
     * The symbol denoted by {@code acl2::list}.
     */
    public static final Acl2Symbol LIST;

    /**
     * The symbol denoted by {@code acl2::if}.
     */
    public static final Acl2Symbol IF;

    /**
     * The symbol denoted by {@code acl2::characterp}.
     */
    public static final Acl2Symbol CHARACTERP;

    /**
     * The symbol denoted by {@code acl2::stringp}.
     */
    public static final Acl2Symbol STRINGP;

    /**
     * The symbol denoted by {@code acl2::symbolp}.
     */
    public static final Acl2Symbol SYMBOLP;

    /**
     * The symbol denoted by {@code acl2::integerp}.
     */
    public static final Acl2Symbol INTEGERP;

    /**
     * The symbol denoted by {@code acl2::rationalp}.
     */
    public static final Acl2Symbol RATIONALP;

    /**
     * The symbol denoted by {@code acl2::complex-rationalp}.
     */
    public static final Acl2Symbol COMPLEX_RATIONALP;

    /**
     * The symbol denoted by {@code acl2::acl2-numberp}.
     */
    public static final Acl2Symbol ACL2_NUMBERP;

    /**
     * The symbol denoted by {@code acl2::consp}.
     */
    public static final Acl2Symbol CONSP;

    /**
     * The symbol denoted by {@code acl2::char-code}.
     */
    public static final Acl2Symbol CHAR_CODE;

    /**
     * The symbol denoted by {@code acl2::code-char}.
     */
    public static final Acl2Symbol CODE_CHAR;

    /**
     * The symbol denoted by {@code acl2::coerce}.
     */
    public static final Acl2Symbol COERCE;

    /**
     * The symbol denoted by {@code acl2::intern-in-package-of-symbol}.
     */
    public static final Acl2Symbol INTERN_IN_PACKAGE_OF_SYMBOL;

    /**
     * The symbol denoted by {@code acl2::symbol-package-name}.
     */
    public static final Acl2Symbol SYMBOL_PACKAGE_NAME;

    /**
     * The symbol denoted by {@code acl2::symbol-name}.
     */
    public static final Acl2Symbol SYMBOL_NAME;

    /**
     * The symbol denoted by {@code acl2::pkg-imports}.
     */
    public static final Acl2Symbol PKG_IMPORTS;

    /**
     * The symbol denoted by {@code acl2::pkg-witness}.
     */
    public static final Acl2Symbol PKG_WITNESS;

    /**
     * The symbol denoted by {@code acl2::unary--}.
     */
    public static final Acl2Symbol UNARY_MINUS;

    /**
     * The symbol denoted by {@code acl2::unary-/}.
     */
    public static final Acl2Symbol UNARY_SLASH;

    /**
     * The symbol denoted by {@code acl2::binary-+}.
     */
    public static final Acl2Symbol BINARY_PLUS;

    /**
     * The symbol denoted by {@code acl2::binary-*}.
     */
    public static final Acl2Symbol BINARY_STAR;

    /**
     * The symbol denoted by {@code acl2::<}.
     */
    public static final Acl2Symbol LESS_THAN;

    /**
     * The symbol denoted by {@code acl2::complex}.
     */
    public static final Acl2Symbol COMPLEX;

    /**
     * The symbol denoted by {@code acl2::realpart}.
     */
    public static final Acl2Symbol REALPART;

    /**
     * The symbol denoted by {@code acl2::imagpart}.
     */
    public static final Acl2Symbol IMAGPART;

    /**
     * The symbol denoted by {@code acl2::numerator}.
     */
    public static final Acl2Symbol NUMERATOR;

    /**
     * The symbol denoted by {@code acl2::denominator}.
     */
    public static final Acl2Symbol DENOMINATOR;

    /**
     * The symbol denoted by {@code acl2::cons}.
     */
    public static final Acl2Symbol CONS;

    /**
     * The symbol denoted by {@code acl2::car}.
     */
    public static final Acl2Symbol CAR;

    /**
     * The symbol denoted by {@code acl2::cdr}.
     */
    public static final Acl2Symbol CDR;

    /**
     * The symbol denoted by {@code acl2::equal}.
     */
    public static final Acl2Symbol EQUAL;

    /**
     * The symbol denoted by {@code acl2::bad-atom<=}.
     */
    public static final Acl2Symbol BAD_ATOM_LESS_THAN_OR_EQUAL_TO;

    /**
     * The symbol denoted by {@code acl2::or}.
     */
    public static final Acl2Symbol OR;

    /**
     * The symbol denoted by {@code acl2::nonnegative-integer-quotient}.
     */
    public static final Acl2Symbol NONNEGATIVE_INTEGER_QUOTIENT;

    /**
     * The symbol denoted by {@code acl2::string-append}.
     */
    public static final Acl2Symbol STRING_APPEND;

    /**
     * The symbol denoted by {@code acl2::len}.
     */
    public static final Acl2Symbol LEN;

    /**
     * The symbol denoted by {@code common-lisp::char}.
     */
    public static final Acl2Symbol CHAR;

    static { // builds the pre-created symbols
        // names of the symbols:
        Acl2String stringT = Acl2String.imake("T");
        Acl2String stringNil = Acl2String.imake("NIL");
        Acl2String stringList = Acl2String.imake("LIST");
        Acl2String stringIf = Acl2String.imake("IF");
        Acl2String stringCharacterp = Acl2String.imake("CHARACTERP");
        Acl2String stringStringp = Acl2String.imake("STRINGP");
        Acl2String stringSymbolp = Acl2String.imake("SYMBOLP");
        Acl2String stringIntegerp = Acl2String.imake("INTEGERP");
        Acl2String stringRationalp = Acl2String.imake("RATIONALP");
        Acl2String stringComplexRationalp =
                Acl2String.imake("COMPLEX-RATIONALP");
        Acl2String stringAcl2Numberp = Acl2String.imake("ACL2-NUMBERP");
        Acl2String stringConsp = Acl2String.imake("CONSP");
        Acl2String stringCharCode = Acl2String.imake("CHAR-CODE");
        Acl2String stringCodeChar = Acl2String.imake("CODE-CHAR");
        Acl2String stringCoerce = Acl2String.imake("COERCE");
        Acl2String stringInternInPackageOfSymbol =
                Acl2String.imake("INTERN-IN-PACKAGE-OF-SYMBOL");
        Acl2String stringSymbolPackageName =
                Acl2String.imake("SYMBOL-PACKAGE-NAME");
        Acl2String stringSymbolName = Acl2String.imake("SYMBOL-NAME");
        Acl2String stringPkgImports = Acl2String.imake("PKG-IMPORTS");
        Acl2String stringPkgWitness = Acl2String.imake("PKG-WITNESS");
        Acl2String stringUnaryMinus = Acl2String.imake("UNARY--");
        Acl2String stringUnarySlash = Acl2String.imake("UNARY-/");
        Acl2String stringBinaryPlus = Acl2String.imake("BINARY-+");
        Acl2String stringBinaryTimes = Acl2String.imake("BINARY-*");
        Acl2String stringLessThan = Acl2String.imake("<");
        Acl2String stringComplex = Acl2String.imake("COMPLEX");
        Acl2String stringRealpart = Acl2String.imake("REALPART");
        Acl2String stringImagpart = Acl2String.imake("IMAGPART");
        Acl2String stringNumerator = Acl2String.imake("NUMERATOR");
        Acl2String stringDenominator = Acl2String.imake("DENOMINATOR");
        Acl2String stringCons = Acl2String.imake("CONS");
        Acl2String stringCar = Acl2String.imake("CAR");
        Acl2String stringCdr = Acl2String.imake("CDR");
        Acl2String stringEqual = Acl2String.imake("EQUAL");
        Acl2String stringBadAtomLessThanOrEqualTo =
                Acl2String.imake("BAD-ATOM<=");
        Acl2String stringOr = Acl2String.imake("OR");
        Acl2String stringNonnegativeIntegerQuotient =
                Acl2String.imake("NONNEGATIVE-INTEGER-QUOTIENT");
        Acl2String stringStringAppend = Acl2String.make("STRING-APPEND");
        Acl2String stringLen = Acl2String.make("LEN");
        Acl2String stringChar = Acl2String.make("CHAR");
        // symbols:
        T = new Acl2Symbol(Acl2PackageName.LISP, stringT);
        NIL = new Acl2Symbol(Acl2PackageName.LISP, stringNil);
        LIST = new Acl2Symbol(Acl2PackageName.LISP, stringList);
        IF = new Acl2Symbol(Acl2PackageName.LISP, stringIf);
        CHARACTERP = new Acl2Symbol(Acl2PackageName.LISP, stringCharacterp);
        STRINGP = new Acl2Symbol(Acl2PackageName.LISP, stringStringp);
        SYMBOLP = new Acl2Symbol(Acl2PackageName.LISP, stringSymbolp);
        INTEGERP = new Acl2Symbol(Acl2PackageName.LISP, stringIntegerp);
        RATIONALP = new Acl2Symbol(Acl2PackageName.LISP, stringRationalp);
        COMPLEX_RATIONALP =
                new Acl2Symbol(Acl2PackageName.ACL2, stringComplexRationalp);
        ACL2_NUMBERP = new Acl2Symbol(Acl2PackageName.ACL2, stringAcl2Numberp);
        CONSP = new Acl2Symbol(Acl2PackageName.LISP, stringConsp);
        CHAR_CODE = new Acl2Symbol(Acl2PackageName.LISP, stringCharCode);
        CODE_CHAR = new Acl2Symbol(Acl2PackageName.LISP, stringCodeChar);
        COERCE = new Acl2Symbol(Acl2PackageName.LISP, stringCoerce);
        INTERN_IN_PACKAGE_OF_SYMBOL =
                new Acl2Symbol(Acl2PackageName.ACL2,
                        stringInternInPackageOfSymbol);
        SYMBOL_PACKAGE_NAME =
                new Acl2Symbol(Acl2PackageName.ACL2, stringSymbolPackageName);
        SYMBOL_NAME = new Acl2Symbol(Acl2PackageName.LISP, stringSymbolName);
        PKG_IMPORTS = new Acl2Symbol(Acl2PackageName.ACL2, stringPkgImports);
        PKG_WITNESS = new Acl2Symbol(Acl2PackageName.ACL2, stringPkgWitness);
        UNARY_MINUS = new Acl2Symbol(Acl2PackageName.ACL2, stringUnaryMinus);
        UNARY_SLASH = new Acl2Symbol(Acl2PackageName.ACL2, stringUnarySlash);
        BINARY_PLUS = new Acl2Symbol(Acl2PackageName.ACL2, stringBinaryPlus);
        BINARY_STAR = new Acl2Symbol(Acl2PackageName.ACL2, stringBinaryTimes);
        LESS_THAN = new Acl2Symbol(Acl2PackageName.LISP, stringLessThan);
        COMPLEX = new Acl2Symbol(Acl2PackageName.LISP, stringComplex);
        REALPART = new Acl2Symbol(Acl2PackageName.LISP, stringRealpart);
        IMAGPART = new Acl2Symbol(Acl2PackageName.LISP, stringImagpart);
        NUMERATOR = new Acl2Symbol(Acl2PackageName.LISP, stringNumerator);
        DENOMINATOR = new Acl2Symbol(Acl2PackageName.LISP, stringDenominator);
        CONS = new Acl2Symbol(Acl2PackageName.LISP, stringCons);
        CAR = new Acl2Symbol(Acl2PackageName.LISP, stringCar);
        CDR = new Acl2Symbol(Acl2PackageName.LISP, stringCdr);
        EQUAL = new Acl2Symbol(Acl2PackageName.LISP, stringEqual);
        BAD_ATOM_LESS_THAN_OR_EQUAL_TO =
                new Acl2Symbol(Acl2PackageName.ACL2,
                        stringBadAtomLessThanOrEqualTo);
        OR = new Acl2Symbol(Acl2PackageName.LISP, stringOr);
        NONNEGATIVE_INTEGER_QUOTIENT =
                new Acl2Symbol(Acl2PackageName.ACL2,
                        stringNonnegativeIntegerQuotient);
        STRING_APPEND =
                new Acl2Symbol(Acl2PackageName.ACL2, stringStringAppend);
        LEN = new Acl2Symbol(Acl2PackageName.ACL2, stringLen);
        CHAR = new Acl2Symbol(Acl2PackageName.LISP, stringChar);
        // initial inner map for the "COMMON-LISP" package:
        Map<Acl2String, Acl2Symbol> initialLispMap = new HashMap<>();
        initialLispMap.put(stringT, T);
        initialLispMap.put(stringNil, NIL);
        initialLispMap.put(stringList, LIST);
        initialLispMap.put(stringIf, IF);
        initialLispMap.put(stringCharacterp, CHARACTERP);
        initialLispMap.put(stringStringp, STRINGP);
        initialLispMap.put(stringSymbolp, SYMBOLP);
        initialLispMap.put(stringIntegerp, INTEGERP);
        initialLispMap.put(stringRationalp, RATIONALP);
        initialLispMap.put(stringConsp, CONSP);
        initialLispMap.put(stringCharCode, CHAR_CODE);
        initialLispMap.put(stringCodeChar, CODE_CHAR);
        initialLispMap.put(stringCoerce, COERCE);
        initialLispMap.put(stringSymbolName, SYMBOL_NAME);
        initialLispMap.put(stringLessThan, LESS_THAN);
        initialLispMap.put(stringComplex, COMPLEX);
        initialLispMap.put(stringRealpart, REALPART);
        initialLispMap.put(stringImagpart, IMAGPART);
        initialLispMap.put(stringNumerator, NUMERATOR);
        initialLispMap.put(stringDenominator, DENOMINATOR);
        initialLispMap.put(stringCons, CONS);
        initialLispMap.put(stringCar, CAR);
        initialLispMap.put(stringCdr, CDR);
        initialLispMap.put(stringEqual, EQUAL);
        initialLispMap.put(stringOr, OR);
        initialLispMap.put(stringChar, CHAR);
        // initial inner map for the "ACL2" package:
        Map<Acl2String, Acl2Symbol> initialAcl2Map = new HashMap<>();
        initialAcl2Map.put(stringComplexRationalp, COMPLEX_RATIONALP);
        initialAcl2Map.put(stringAcl2Numberp, ACL2_NUMBERP);
        initialAcl2Map.put(stringInternInPackageOfSymbol,
                INTERN_IN_PACKAGE_OF_SYMBOL);
        initialAcl2Map.put(stringSymbolPackageName, SYMBOL_PACKAGE_NAME);
        initialAcl2Map.put(stringPkgImports, PKG_IMPORTS);
        initialAcl2Map.put(stringPkgWitness, PKG_WITNESS);
        initialAcl2Map.put(stringUnaryMinus, UNARY_MINUS);
        initialAcl2Map.put(stringUnarySlash, UNARY_SLASH);
        initialAcl2Map.put(stringBinaryPlus, BINARY_PLUS);
        initialAcl2Map.put(stringBinaryTimes, BINARY_STAR);
        initialAcl2Map.put(stringBadAtomLessThanOrEqualTo,
                BAD_ATOM_LESS_THAN_OR_EQUAL_TO);
        initialAcl2Map.put(stringNonnegativeIntegerQuotient,
                NONNEGATIVE_INTEGER_QUOTIENT);
        initialAcl2Map.put(stringStringAppend, STRING_APPEND);
        initialAcl2Map.put(stringLen, LEN);
        // initial outer map:
        symbols.put(Acl2PackageName.LISP, initialLispMap);
        symbols.put(Acl2PackageName.ACL2, initialAcl2Map);
    }

    /**
     * Returns the package name of this symbol.
     *
     * @return The package name of this symbol.
     */
    public Acl2PackageName getPackageName() {
        return this.packageName;
    }

    /**
     * Returns the name of this symbol.
     *
     * @return The name of this symbol.
     */
    public Acl2String getName() {
        return this.name;
    }

}
