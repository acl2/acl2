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

    //////////////////////////////////////// package-private members:

    /**
     * Name of this named function.
     * This is never {@code null}.
     */
    private final Acl2Symbol name;

    /**
     * Constructs a named function with the given name
     * This is accessed only by the subclasses.
     *
     * @param name The name of the function.
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
     * Flag saying whether all the defined functions created so far
     * (which are all named functions) have valid definitions.
     * This is initially true because there are no defined functions initially.
     * This is set to false whenever a new defined function is created,
     * because that one has not been validated yet.
     * This is set to true by {@link #validateAll()}.
     */
    private static boolean validatedAll = true;

    /**
     * Sets the flag that says whether
     * all the defined functions created so far have valid definitions.
     * This is called only by the subclass {@link Acl2DefinedFunction}.
     *
     * @param value The value to set the @{link #validatedAll} flag to.
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
     * @throws NullPointerException If the argument is {@code null}.
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
     * Ensure that all the defined functions created so far
     * have valid definitions.
     *
     * @throws IllegalStateException If validation fails.
     */
    public static void validateAll() {
        Acl2DefinedFunction.validateAllDefinitions();
    }

    /**
     * Defines this named function.
     * This also sets the indices of all the variables in the defining body;
     * see {@link Acl2Variable} for more information about variable indices.
     *
     * @param parameters The formal parameters of the function definition.
     * @param body       The body of the function definition.
     * @throws IllegalArgumentException If {@code parameters} or {@code body}
     *                                  is {@code null},
     *                                  or the function definition is malformed
     *                                  in a way that
     *                                  some variable index cannot be set.
     * @throws IllegalStateException    If the function is
     *                                  already defined or native,
     *                                  or some variable index is already set.
     */
    public abstract void define(Acl2Symbol[] parameters, Acl2Term body);

    /**
     * Calls this named function on the given values.
     *
     * @param values The arguments of the call.
     * @return The result of calling this named function on the arguments.
     * @throws IllegalArgumentException If {@code values} is {@code null},
     *                                  or any of its elements is {@code null}.
     * @throws IllegalStateException    If not all the defined functions
     *                                  have been validated.
     * @throws Acl2EvaluationException  If this named function is
     *                                  neither defined nor native,
     *                                  or {@code values.length} differs from
     *                                  the function's arity,
     *                                  or a call of {@code pkg-imports}
     *                                  or {@code pkg-witness} fails.
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
