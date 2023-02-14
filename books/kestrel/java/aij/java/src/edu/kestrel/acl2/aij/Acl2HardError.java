/*
 * Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 hard errors.
 * Since a hard error in ACL2 stops execution, we model it as an exception.
 * This exception is unchecked for now
 * (by extending {@link RuntimeException} instead of {@link Exception}),
 * but we may want to make it checked in the future.
 */
public final class Acl2HardError extends RuntimeException {

    /**
     * Context of the hard error.
     * This is the argument {@code ctx} passed to ACL2's {@code hard-error}.
     * Invariant: not null.
     */
    private final Acl2Value ctx;

    /**
     * String of the hard error.
     * This is the argument {@code str} passed to ACL2's {@code hard-error}.
     * Invariant: not null.
     */
    private final Acl2Value str;

    /**
     * Context of the hard error.
     * This is the argument {@code alist} passed to ACL2's {@code hard-error}.
     * Invariant: not null.
     */
    private final Acl2Value alist;

    /**
     * Constructs a hard error with the given context, string, and alist.
     * These may be any ACL2 values,
     * also because the guard of {@code hard-error} is {@code t} in ACL2.
     * For now we just store the context, string, and alist,
     * without looking at them;
     * in the future, we may want to construct a human-oriented message,
     * obtained by processing the string and alist,
     * according to the semantics of ACL2 format directives.
     *
     * @param ctx   The context of the hard error.
     *              Invariant: not null.
     * @param str   The string of the hard error.
     *              Invariant: not null.
     * @param alist The alist of the hard error.
     *              Invariant: not null.
     */
    Acl2HardError(Acl2Value ctx, Acl2Value str, Acl2Value alist) {
        this.ctx = ctx;
        this.str = str;
        this.alist = alist;
    }
}
