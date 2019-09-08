/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 named functions in ACL2 terms.
 * These are native functions (subclass {@link Acl2NativeFunction})
 * and defined functions (subclass {@link Acl2DefinedFunction}).
 * This abstract superclass contains their common
 * state (i.e. the name of the function) and
 * behavior (i.e. equality, hashing, comparison, and string representation).
 * ACL2 named functions are interned:
 * there is exactly one instance for each function name;
 * see the subclasses for details.
 */
public abstract class Acl2NamedFunction extends Acl2Function {

    //////////////////////////////////////// package-private members:

    /**
     * Name of this ACL2 function.
     * This is never {@code null}.
     */
    private final Acl2Symbol name;

    /**
     * Constructs an ACL2 named function from its name.
     * Accessed only by the subclasses.
     */
    Acl2NamedFunction(Acl2Symbol name) {
        this.name = name;
    }

    /**
     * Returns the name of this function.
     * Accessed only by the subclasses.
     */
    Acl2Symbol getName() {
        return this.name;
    }

    /**
     * Flag saying whether all the defined functions created so far
     * have valid definitions.
     * This is initially true because there are no defined functions initially.
     * This is reset to false whenever a new defined function is created,
     * because that one has not been validated yet.
     * This is set to true by {@link #validateAll()}.
     */
    private static boolean validatedAll = true;

    /**
     * Sets to true the flag that says whether
     * all the defined functions created so far have valid definitions.
     * This is called only by the subclass {@link Acl2DefinedFunction}.
     */
    static void setValidatedAll(boolean value) {
        validatedAll = value;
    }

    /**
     * Validates all the function calls in this named function.
     * Since a named function contains no function calls,
     * this method does nothing.
     */
    @Override
    void validateFunctionCalls() {
    }

    /**
     * Sets the indices of all the variables in this function.
     * Since a named function has no variables, this method does nothing.
     */
    @Override
    void setVariableIndices() {
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 named function is equal to the argument object.
     * The only way in which code external to AIJ can create named functions
     * is through the {@link #make(Acl2Symbol)} method:
     * since both defined and native functions are interned
     * (see {@link Acl2DefinedFunction} and {@link Acl2NativeFunction}),
     * two named functions are equal iff they are the same object.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this ACL2 named function with the argument ACL2 function
     * for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.).
     *
     * @return a negative integer, zero, or a positive integer as
     * this function is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Function o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2NamedFunction) {
            Acl2NamedFunction that = (Acl2NamedFunction) o;
            return this.name.compareTo(that.name);
        }
        // named functions are less than lambda expressions:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 named function.
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns an ACL2 named function with the given name.
     *
     * @throws IllegalArgumentException if name is null
     */
    public static Acl2NamedFunction make(Acl2Symbol name) {
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        Acl2NativeFunction function = Acl2NativeFunction.getInstance(name);
        if (function != null)
            return function;
        return Acl2DefinedFunction.getInstance(name);
    }

    /**
     * Validate all the existing function definitions.
     * This ensures that
     *
     * @throws IllegalStateException if validation fails
     */
    public static void validateAll() {
        Acl2DefinedFunction.validateAllDefinitions();
    }

    /**
     * Defines this ACL2 named function.
     *
     * @throws IllegalArgumentException if parameters or body is null
     *                                  or the function definition is malformed
     *                                  in a way that
     *                                  some valid variable index cannot be set
     * @throws IllegalStateException    if the function is
     *                                  already defined or native,
     *                                  or some variable index is already set
     */
    public abstract void define(Acl2Symbol[] parameters, Acl2Term body);

    /**
     * Call this ACL2 named function on the given values.
     *
     * @throws IllegalArgumentException if values is null,
     *                                  or any value is null
     * @throws IllegalStateException    if not all the defined functions
     *                                  have been validated
     * @throws Acl2EvaluationException  if the function is
     *                                  neither defined nor native,
     *                                  or values.length differs from
     *                                  the function's arity,
     *                                  or the function call fails
     */
    public Acl2Value call(Acl2Value[] values) throws Acl2EvaluationException {
        if (!validatedAll)
            throw new IllegalStateException
                    ("Not all function definitions have been validated.");
        if (values == null)
            throw new IllegalArgumentException("Null value array.");
        for (int i = 0; i < values.length; ++i)
            if (values[i] == null)
                throw new IllegalArgumentException
                        ("Null value at index " + i + ".");
        return this.apply(values);
    }

}
