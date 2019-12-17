/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 named functions in terms.
 * These are native functions (subclass {@link Acl2NativeFunction})
 * and defined functions (subclass {@link Acl2DefinedFunction}).
 * This abstract superclass contains their common
 * state (i.e. the name of the function) and
 * behavior (i.e. equality, hashing, comparison, and string representation).
 * Named functions are interned:
 * there is exactly one instance for each function name;
 * see the subclasses for details.
 */
public abstract class Acl2NamedFunction extends Acl2Function {

    //////////////////////////////////////// private members:

    /**
     * Name of this named function.
     * Invariant: not null.
     */
    private final Acl2Symbol name;

    /**
     * Flag saying whether all the function calls
     * in all the defined functions created so far
     * are valid.
     * This is initially true because there are no defined functions initially.
     * This is set to false whenever a new defined function is created,
     * because that one has not been validated yet.
     * This is set to true by {@link #validateAllFunctionCalls()}.
     */
    private static boolean validatedAllFunctionCalls = true;

    //////////////////////////////////////// package-private members:

    /**
     * Constructs a named function with the given name
     * This is accessed only by the subclasses.
     *
     * @param name The name of the function.
     *             Invariant: not null.
     */
    Acl2NamedFunction(Acl2Symbol name) {
        this.name = name;
    }

    /**
     * Returns the name of this named function.
     * This is accessed only by the subclasses.
     *
     * @return The name of this function.
     */
    Acl2Symbol getName() {
        return this.name;
    }

    /**
     * Sets the flag that says whether all the function calls
     * in all the defined functions created so far
     * are valid.
     * This is called only by the subclass {@link Acl2DefinedFunction}.
     *
     * @param value The value for the @{link #validatedAllFunctionCalls} flag.
     */
    static void setValidatedAllFunctionCalls(boolean value) {
        validatedAllFunctionCalls = value;
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
     * Sets the indices of all the variables in this named function.
     * Since a named function has no variables, this method does nothing.
     */
    @Override
    void setVariableIndices() {
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this named function with the argument object for equality.
     * The only way in which code external to AIJ can create named functions
     * is through the {@link #make(Acl2Symbol)} method:
     * since both defined and native functions are interned
     * (see {@link Acl2DefinedFunction} and {@link Acl2NativeFunction}),
     * two named functions are equal iff they are the same object.
     *
     * @param o The object to compare this named function with.
     * @return {@code true} if the object is equal to this named function,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this named function with the argument function for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.).
     *
     * @param o The function to compare this named function to.
     * @return A negative integer, zero, or a positive integer as this
     * named function is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
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
     * Returns a printable representation of this named function.
     *
     * @return A printable representation of this named function.
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns a named function with the given name.
     *
     * @param name The name of the named function.
     * @return The named function.
     * @throws IllegalArgumentException If {@code name} is null.
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
     * Ensure that all the function calls
     * in all the defined functions created so far
     * are valid.
     * That is, each call references an existing function
     * and has a number of actual arguments that matches the arity.
     *
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    public static void validateAllFunctionCalls() {
        Acl2DefinedFunction.validateFunctionCallsInAllDefinitions();
    }

    /**
     * Defines this named function.
     * This also sets the indices of all the variables in the defining body;
     * see {@link Acl2Variable} for more information about variable indices.
     * The {@link Acl2Variable}s in the body term must not be shared,
     * directly or indirectly,
     * within the body term
     * or with body terms passed to other calls of this method:
     * this way, variable indices can be set appropriately,
     * based on where the variables occur in terms,
     * and not on the variables themselves alone;
     * otherwise, the variable index setting process may stop with an error
     * due to some index being already set.
     *
     * @param parameters The formal parameters of the function definition.
     * @param body       The body of the function definition.
     * @throws IllegalArgumentException If {@code parameters} is null,
     *                                  or any of its elements is null,
     *                                  or {@code body} is null,
     *                                  or the function is native,
     *                                  or the function definition
     *                                  (viewed as a lambda expression)
     *                                  contains some variable
     *                                  that is not bound in the formals of
     *                                  its smallest enclosing
     *                                  lambda expression
     *                                  or that has an index already set.
     */
    public abstract void define(Acl2Symbol[] parameters, Acl2Term body);

    /**
     * Calls this named function on the given values.
     *
     * @param values The arguments of the call.
     * @return The result of calling this named function on the arguments.
     * @throws IllegalArgumentException      If {@code values} is null,
     *                                       or any of its elements is null,
     *                                       or {@code values.length} differs
     *                                       from the function's arity.
     * @throws IllegalStateException         If not all the defined functions
     *                                       have been validated.
     * @throws Acl2UndefinedPackageException If a call of {@code pkg-imports}
     *                                       or {@code pkg-witness} fails.
     */
    public Acl2Value call(Acl2Value[] values)
            throws Acl2UndefinedPackageException {
        if (!validatedAllFunctionCalls)
            throw new IllegalStateException
                    ("Not all function definitions have been validated.");
        if (values == null)
            throw new IllegalArgumentException("Null value array.");
        if (values.length != getArity())
            throw new IllegalArgumentException
                    ("Wrong number of actual arguments " + values.length +
                            " for function with arity " + getArity() + ".");
        for (int i = 0; i < values.length; ++i)
            if (values[i] == null)
                throw new IllegalArgumentException
                        ("Null value at index " + i + ".");
        return this.apply(values);
    }

}
