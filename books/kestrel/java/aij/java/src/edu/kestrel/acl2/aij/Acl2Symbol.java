/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Representation of ACL2 symbols.
 * These are the ACL2 values that satisfy {@code symbolp}.
 */
public final class Acl2Symbol extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Package name of the ACL2 symbol.
     * This is never {@code null}.
     */
    private final Acl2PackageName packageName;

    /**
     * Name of the ACL2 symbol.
     * This is never {@code null}.
     */
    private final Acl2String name;

    /**
     * Constructs an ACL2 symbol from its package name and name.
     */
    private Acl2Symbol(Acl2PackageName packageName, Acl2String name) {
        this.packageName = packageName;
        this.name = name;
    }

    /**
     * All the ACL2 symbols created so far.
     * These are stored as a map from ACL2 package names
     * to maps from ACL2 strings to ACL2 symbols:
     * this structure is isomorphic to a map
     * from package names paired with string to symbols.
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
     * <p>
     * This nested map structure is extended in three circumstances:
     * <ol>
     * <li>
     * When {@link Acl2Package#define(Acl2PackageName, List)} is called,
     * i.e. when a package definition is added to the ACL2 environment.
     * In this case, the nested map structure is extended
     * according to the package's import list
     * (see {@link #addPackageImports(Acl2PackageName, List)}).
     * The new associations have all symbols whose package names
     * match the corresponding keys in the outer map.
     * <li>
     * When {@link #make(Acl2PackageName, Acl2String)} is called.
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
     * Thus, all the ACL2 symbols are interned.
     * <p>
     * This field is never {@code null},
     * its keys are never {@code null},
     * and its values are never {@code null};
     * the keys and values of the inner maps are never {@code null}.
     */
    private static final Map<Acl2PackageName, Map<Acl2String, Acl2Symbol>>
            symbols = new HashMap<>();

    //////////////////////////////////////// package-private members:

    /**
     * Adds information about all the ACL2 symbols imported by an ACL2 package.
     * This is called by {@link Acl2Package#define(Acl2PackageName, List)}
     * when a new package definition is added to the environment.
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
     * Returns {@code true},
     * consistently with the {@code symbolp} ACL2 function.
     */
    @Override
    Acl2Symbol symbolp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the symbol package name of this ACL2 symbol,
     * consistently with the {@code symbol-package-name} ACL2 function.
     */
    @Override
    Acl2String symbolPackageName() {
        return Acl2String.make(packageName.getJavaString());
    }

    /**
     * Returns the symbol name of this ACL2 symbol,
     * consistently with the {@code symbol-name} ACL2 function.
     */
    @Override
    Acl2String symbolName() {
        return name;
    }

    /**
     * Interns the argument ACL2 string in the package of this ACL2 value,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this ACL2 value is the second argument of that function
     * and the argument ACL2 value is the first argument of that function.
     */
    @Override
    Acl2Symbol internInPackageOfThis(Acl2String str) {
        Acl2PackageName packageName = this.packageName;
        return Acl2Symbol.make(packageName, str);
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // symbols are greater than characters:
        return 1;
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToString(Acl2String o) {
        // symbols are greater than strings:
        return 1;
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
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
     * Compares this ACL2 symbol with the argument ACL2 number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // symbols are greater than numbers:
        return 1;
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // symbols are greater than rationals:
        return 1;
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // symbols are greater than integers:
        return 1;
    }

    /**
     * Compares this ACL2 symbol with
     * the argument ACL2 {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this symbol is less than, equal to, or greater than the argument
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // symbols are less than cons pairs:
        return -1;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 symbol is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this ACL2 symbol with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return - o.compareToSymbol(this);
    }

    /**
     * Returns a printable representation of this ACL2 symbol.
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
     * This scheme should ensure that ACL2 symbols are always printed clearly.
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
     * Returns an ACL2 symbol denoted by the given package name and given name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @throws IllegalArgumentException if packageName or name is null,
     *                                  or the package is not defined
     */
    public static Acl2Symbol make(Acl2PackageName packageName,
                                  Acl2String name) {
        if (packageName == null)
            throw new IllegalArgumentException("Null package name.");
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        Map<Acl2String, Acl2Symbol> innerMap = symbols.get(packageName);
        if (innerMap == null)
            throw new IllegalArgumentException
                    ("Undefined package: \"" + packageName + "\".");
        Acl2Symbol symbol = innerMap.get(name);
        if (symbol == null) {
            symbol = new Acl2Symbol(packageName, name);
            innerMap.put(name, symbol);
        }
        return symbol;
    }

    /**
     * Returns an ACL2 symbol denoted by the given package name and given name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @throws IllegalArgumentException if packageName or name is null,
     *                                  or the package is not defined
     *                                  or name contains characters above 255
     */
    public static Acl2Symbol make(Acl2PackageName packageName, String name) {
        return make(packageName, Acl2String.make(name));
    }

    /**
     * Returns an ACL2 symbol denoted by the given package name and given name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @throws IllegalArgumentException if packageName or name is null,
     *                                  or the package is not defined
     *                                  or name contains characters above 255
     */
    public static Acl2Symbol make(String packageName, Acl2String name) {
        return make(Acl2PackageName.make(packageName), name);
    }

    /**
     * Returns an ACL2 symbol with the given package name and given name.
     * The resulting symbol's package may differ from the given package,
     * if the given package imports a symbol with that name.
     *
     * @throws IllegalArgumentException if packageName or name is null,
     *                                  or packageName is not valid,
     *                                  or the package is not defined
     *                                  or name contains characters above 255
     */
    public static Acl2Symbol make(String packageName, String name) {
        return Acl2Symbol.make(Acl2PackageName.make(packageName), name);
    }

    /**
     * Returns an ACL2 symbol denoted by
     * the {@code "KEYWORD"} package name and the given name.
     *
     * @throws IllegalArgumentException if name is null
     *                                  or contains characters above 255
     * @throws IllegalStateException    if the "KEYWORD" package
     *                                  is not defined yet
     */
    public static Acl2Symbol makeKeyword(String name) {
        return Acl2Symbol.make(Acl2PackageName.KEYWORD, name);
    }

    /**
     * Returns an ACL2 symbol denoted by
     * the {@code "COMMON-LISP"} package name and the given name.
     *
     * @throws IllegalArgumentException if name is null
     *                                  or contains characters above 255
     * @throws IllegalStateException    if the "COMMON-LISP" package
     *                                  is not defined yet
     */
    public static Acl2Symbol makeLisp(String name) {
        return Acl2Symbol.make(Acl2PackageName.LISP, name);
    }

    /**
     * Returns an ACL2 symbol denoted by
     * the {@code "ACL2"} package name and the given name.
     *
     * @throws IllegalArgumentException if name is null
     *                                  or contains characters above 255
     * @throws IllegalStateException    if the "ACL2" package is not defined yet
     */
    public static Acl2Symbol makeAcl2(String name) {
        return Acl2Symbol.make(Acl2PackageName.ACL2, name);
    }

    /**
     * The ACL2 symbol denoted by {@code acl2::t}.
     */
    public static final Acl2Symbol T;

    /**
     * The ACL2 symbol denoted by {@code acl2::nil}.
     */
    public static final Acl2Symbol NIL;

    /**
     * The ACL2 symbol denoted by {@code acl2::list}.
     */
    public static final Acl2Symbol LIST;

    /**
     * The ACL2 symbol denoted by {@code acl2::if}.
     */
    public static final Acl2Symbol IF;

    /**
     * The ACL2 symbol denoted by {@code acl2::characterp}.
     */
    public static final Acl2Symbol CHARACTERP;

    /**
     * The ACL2 symbol denoted by {@code acl2::stringp}.
     */
    public static final Acl2Symbol STRINGP;

    /**
     * The ACL2 symbol denoted by {@code acl2::symbolp}.
     */
    public static final Acl2Symbol SYMBOLP;

    /**
     * The ACL2 symbol denoted by {@code acl2::integerp}.
     */
    public static final Acl2Symbol INTEGERP;

    /**
     * The ACL2 symbol denoted by {@code acl2::rationalp}.
     */
    public static final Acl2Symbol RATIONALP;

    /**
     * The ACL2 symbol denoted by {@code acl2::complex-rationalp}.
     */
    public static final Acl2Symbol COMPLEX_RATIONALP;

    /**
     * The ACL2 symbol denoted by {@code acl2::acl2-numberp}.
     */
    public static final Acl2Symbol ACL2_NUMBERP;

    /**
     * The ACL2 symbol denoted by {@code acl2::consp}.
     */
    public static final Acl2Symbol CONSP;

    /**
     * The ACL2 symbol denoted by {@code acl2::char-code}.
     */
    public static final Acl2Symbol CHAR_CODE;

    /**
     * The ACL2 symbol denoted by {@code acl2::code-char}.
     */
    public static final Acl2Symbol CODE_CHAR;

    /**
     * The ACL2 symbol denoted by {@code acl2::coerce}.
     */
    public static final Acl2Symbol COERCE;

    /**
     * The ACL2 symbol denoted by {@code acl2::intern-in-package-of-symbol}.
     */
    public static final Acl2Symbol INTERN_IN_PACKAGE_OF_SYMBOL;

    /**
     * The ACL2 symbol denoted by {@code acl2::symbol-package-name}.
     */
    public static final Acl2Symbol SYMBOL_PACKAGE_NAME;

    /**
     * The ACL2 symbol denoted by {@code acl2::symbol-name}.
     */
    public static final Acl2Symbol SYMBOL_NAME;

    /**
     * The ACL2 symbol denoted by {@code acl2::pkg-imports}.
     */
    public static final Acl2Symbol PKG_IMPORTS;

    /**
     * The ACL2 symbol denoted by {@code acl2::pkg-witness}.
     */
    public static final Acl2Symbol PKG_WITNESS;

    /**
     * The ACL2 symbol denoted by {@code acl2::unary--}.
     */
    public static final Acl2Symbol UNARY_MINUS;

    /**
     * The ACL2 symbol denoted by {@code acl2::unary-/}.
     */
    public static final Acl2Symbol UNARY_SLASH;

    /**
     * The ACL2 symbol denoted by {@code acl2::binary-+}.
     */
    public static final Acl2Symbol BINARY_PLUS;

    /**
     * The ACL2 symbol denoted by {@code acl2::binary-*}.
     */
    public static final Acl2Symbol BINARY_STAR;

    /**
     * The ACL2 symbol denoted by {@code acl2::<}.
     */
    public static final Acl2Symbol LESS_THAN;

    /**
     * The ACL2 symbol denoted by {@code acl2::complex}.
     */
    public static final Acl2Symbol COMPLEX;

    /**
     * The ACL2 symbol denoted by {@code acl2::realpart}.
     */
    public static final Acl2Symbol REALPART;

    /**
     * The ACL2 symbol denoted by {@code acl2::imagpart}.
     */
    public static final Acl2Symbol IMAGPART;

    /**
     * The ACL2 symbol denoted by {@code acl2::numerator}.
     */
    public static final Acl2Symbol NUMERATOR;

    /**
     * The ACL2 symbol denoted by {@code acl2::denominator}.
     */
    public static final Acl2Symbol DENOMINATOR;

    /**
     * The ACL2 symbol denoted by {@code acl2::cons}.
     */
    public static final Acl2Symbol CONS;

    /**
     * The ACL2 symbol denoted by {@code acl2::car}.
     */
    public static final Acl2Symbol CAR;

    /**
     * The ACL2 symbol denoted by {@code acl2::cdr}.
     */
    public static final Acl2Symbol CDR;

    /**
     * The ACL2 symbol denoted by {@code acl2::equal}.
     */
    public static final Acl2Symbol EQUAL;

    /**
     * The ACL2 symbol denoted by {@code acl2::bad-atom<=}.
     */
    public static final Acl2Symbol BAD_ATOM_LESS_THAN_OR_EQUAL_TO;

    /**
     * The ACL2 symbol denoted by {@code acl2::or}.
     */
    public static final Acl2Symbol OR;

    static { // builds the pre-created symbols
        // names of the symbols:
        Acl2String stringT = Acl2String.make("T");
        Acl2String stringNil = Acl2String.make("NIL");
        Acl2String stringList = Acl2String.make("LIST");
        Acl2String stringIf = Acl2String.make("IF");
        Acl2String stringCharacterp = Acl2String.make("CHARACTERP");
        Acl2String stringStringp = Acl2String.make("STRINGP");
        Acl2String stringSymbolp = Acl2String.make("SYMBOLP");
        Acl2String stringIntegerp = Acl2String.make("INTEGERP");
        Acl2String stringRationalp = Acl2String.make("RATIONALP");
        Acl2String stringComplexRationalp =
                Acl2String.make("COMPLEX-RATIONALP");
        Acl2String stringAcl2Numberp = Acl2String.make("ACL2-NUMBERP");
        Acl2String stringConsp = Acl2String.make("CONSP");
        Acl2String stringCharCode = Acl2String.make("CHAR-CODE");
        Acl2String stringCodeChar = Acl2String.make("CODE-CHAR");
        Acl2String stringCoerce = Acl2String.make("COERCE");
        Acl2String stringInternInPackageOfSymbol =
                Acl2String.make("INTERN-IN-PACKAGE-OF-SYMBOL");
        Acl2String stringSymbolPackageName =
                Acl2String.make("SYMBOL-PACKAGE-NAME");
        Acl2String stringSymbolName = Acl2String.make("SYMBOL-NAME");
        Acl2String stringPkgImports = Acl2String.make("PKG-IMPORTS");
        Acl2String stringPkgWitness = Acl2String.make("PKG-WITNESS");
        Acl2String stringUnaryMinus = Acl2String.make("UNARY--");
        Acl2String stringUnarySlash = Acl2String.make("UNARY-/");
        Acl2String stringBinaryPlus = Acl2String.make("BINARY-+");
        Acl2String stringBinaryTimes = Acl2String.make("BINARY-*");
        Acl2String stringLessThan = Acl2String.make("<");
        Acl2String stringComplex = Acl2String.make("COMPLEX");
        Acl2String stringRealpart = Acl2String.make("REALPART");
        Acl2String stringImagpart = Acl2String.make("IMAGPART");
        Acl2String stringNumerator = Acl2String.make("NUMERATOR");
        Acl2String stringDenominator = Acl2String.make("DENOMINATOR");
        Acl2String stringCons = Acl2String.make("CONS");
        Acl2String stringCar = Acl2String.make("CAR");
        Acl2String stringCdr = Acl2String.make("CDR");
        Acl2String stringEqual = Acl2String.make("EQUAL");
        Acl2String stringBadAtomLessThanOrEqualTo =
                Acl2String.make("BAD-ATOM<=");
        Acl2String stringOr = Acl2String.make("OR");
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
        COMPLEX = new Acl2Symbol(Acl2PackageName.ACL2, stringComplex);
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
        initialLispMap.put(stringRealpart, REALPART);
        initialLispMap.put(stringImagpart, IMAGPART);
        initialLispMap.put(stringNumerator, NUMERATOR);
        initialLispMap.put(stringDenominator, DENOMINATOR);
        initialLispMap.put(stringCons, CONS);
        initialLispMap.put(stringCar, CAR);
        initialLispMap.put(stringCdr, CDR);
        initialLispMap.put(stringEqual, EQUAL);
        initialLispMap.put(stringOr, OR);
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
        initialAcl2Map.put(stringComplex, COMPLEX);
        initialAcl2Map.put(stringBadAtomLessThanOrEqualTo,
                BAD_ATOM_LESS_THAN_OR_EQUAL_TO);
        // initial outer map:
        symbols.put(Acl2PackageName.LISP, initialLispMap);
        symbols.put(Acl2PackageName.ACL2, initialAcl2Map);
    }

    /**
     * Returns the package name of this ACL2 symbol.
     */
    public Acl2PackageName getPackageName() {
        return this.packageName;
    }

    /**
     * Returns the name of this ACL2 symbol.
     */
    public Acl2String getName() {
        return this.name;
    }

}
