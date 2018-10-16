/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Exceptions thrown when ACL2 term evaluation fails.
 */
public final class Acl2EvaluationException extends Exception {

    /**
     * Constructs an evaluation exception
     * with {@code null} as its detail message.
     */
    public Acl2EvaluationException() {
        super();
    }

    /**
     * Constructs an evaluation exception
     * with the given detail message.
     */
    public Acl2EvaluationException(String message) {
        super(message);
    }

    /**
     * Constructs an evaluation exception
     * with the given detail message and cause.
     */
    public Acl2EvaluationException(String message, Throwable cause) {
        super(message, cause);
    }
}
