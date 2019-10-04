; System Utilities -- World Queries
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "system/pseudo-good-worldp" :dir :system)
(include-book "term-function-recognizers")

(include-book "kestrel/std/system/function-name-listp" :dir :system)
(include-book "kestrel/std/system/function-namep" :dir :system)
(include-book "kestrel/std/system/function-symbol-listp" :dir :system)
(include-book "kestrel/std/system/logic-function-namep" :dir :system)
(include-book "kestrel/std/system/logical-name-listp" :dir :system)
(include-book "kestrel/std/system/macro-keyword-args" :dir :system)
(include-book "kestrel/std/system/macro-required-args" :dir :system)
(include-book "kestrel/std/system/macro-name-listp" :dir :system)
(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "kestrel/std/system/macro-symbol-listp" :dir :system)
(include-book "kestrel/std/system/macro-symbolp" :dir :system)
(include-book "kestrel/std/system/primitivep" :dir :system)
(include-book "kestrel/std/system/theorem-name-listp" :dir :system)
(include-book "kestrel/std/system/theorem-namep" :dir :system)
(include-book "kestrel/std/system/theorem-symbol-listp" :dir :system)
(include-book "kestrel/std/system/theorem-symbolp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "arglistp-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (system-utilities-non-built-in)
  :short "Utilities to query @(see world)s."
  :long
  "<p>
   These complement the world query utilities
   in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
   </p>
   <p>
   Many of these world query utilities come in two variants:
   a ``fast'' one and a ``logic-friendly'' one.
   The former has relatively weak and no (strong) return type theorems;
   the latter has stronger guards and some run-time checks
   that are believed to never fail
   and that enable the proof of (stronger) return type theorems
   without having to assume stronger properties in the guard
   of the @(see world) arguments.
   The logic-friendly variants are helpful
   to prove properties (including verifying guards)
   of logic-mode code that calls them,
   but the fast variants avoid the performance penalty
   of the always-satisfied run-time checks,
   when proving properties of the code that calls them is not a focus
   (e.g. in program-mode code).
   </p>
   <p>
   The built-in world query utilities
   have the characteristics of the fast variants.
   Below we provide logic-friendly variants of
   some built-in world query utilities.
   </p>
   <p>
   The fast variants provided below are named in a way
   that is ``consistent'' with the built-in world query utilities.
   The logic-friendly world query utilities are named by adding @('+')
   after the name of the corresponding fast world query utilities
   (both built-in and provided below).
   </p>
   <p>
   These utilities are being moved to @(csee std/system).
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define formals+ ((fn (or (function-namep fn wrld)
                          (pseudo-lambdap fn)))
                  (wrld plist-worldp-with-formals))
  :returns (formals symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee formals)."
  :long
  "<p>
   This returns the same result as @(tsee formals) on named functions,
   but it has a stronger guard for named functions
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>
   <p>
   This utility also operates on lambda expressions, unlike @(tsee formals).
   </p>"
  (b* ((result (cond ((symbolp fn) (formals fn wrld))
                     (t (lambda-formals fn)))))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the formals ~x0 of ~x1 are not a true list of symbols."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define arity+ ((fn (or (function-namep fn wrld)
                        (pseudo-lambdap fn)))
                (wrld plist-worldp-with-formals))
  :returns (result natp
                   :hyp (or (function-namep fn wrld) (pseudo-lambdap fn))
                   :hints (("Goal" :in-theory (enable arity pseudo-lambdap))))
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee arity)."
  :long
  "<p>
   This returns the same result as @(tsee arity),
   but it has a stronger guard.
   </p>"
  (arity fn wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stobjs-in+ ((fn (function-namep fn wrld))
                    (wrld plist-worldp))
  :returns (result symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee stobjs-in)."
  :long
  "<p>
   This returns the same result as @(tsee stobjs-in),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (stobjs-in fn wrld)))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the STOBJS-IN property ~x0 of ~x1 is not a true list of symbols."
             result fn))))

(define stobjs-out+ ((fn (function-namep fn wrld))
                     (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (result symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee stobjs-out)."
  :long
  "<p>
   This returns the same result as @(tsee stobjs-out),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>
   <p>
   The function must not be in @('*stobjs-out-invalid*'),
   because in that case its output stobjs depend on how it is called.
   </p>"
  (b* ((result (stobjs-out fn wrld)))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the STOBJS-OUT property ~x0 of ~x1 is not a true list of symbols."
             result fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-args+ ((mac (macro-namep mac wrld))
                     (wrld plist-worldp))
  :returns (result true-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee macro-args)."
  :long
  "<p>
   This returns the same result as the built-in system utility @('macro-args')
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (macro-args mac wrld)))
    (if (true-listp result)
        result
      (raise "Internal error: ~
              the MACRO-ARGS property ~x0 of ~x1 is not a true list."
             result mac))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definedp ((fn symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a named logic-mode function is defined."
  :long
  "<p>
   We check if the function symbol has an @('unnormalized-body') property.
   </p>
   <p>
   Note that some program-mode functions may be defined
   but not have an @('unnormalized-body') property.
   </p>
   <p>
   See @(tsee definedp+) for a logic-friendly variant of this utility.
   </p>"
  (if (getpropc fn 'unnormalized-body nil wrld) t nil))

(define definedp+ ((fn (logic-function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee definedp)."
  :long
  "<p>
   This returns the same result as @(tsee definedp),
   but it has a stronger guard.
   </p>"
  (definedp fn wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitivep+ ((fn (function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee primitivep)."
  :long
  "<p>
   This returns the same result as @(tsee guard-verified-p),
   but it has a stronger guard.
   The guard requires an extra @(see world) argument,
   which is usually available when doing system programming.
   </p>"
  (declare (ignore wrld))
  (primitivep fn))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-verified-p ((fn/thm symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a named function or theorem is @(tsee guard)-verified."
  :long
  "<p>
   See @(tsee guard-verified-p+) for a logic-friendly variant of this utility.
   </p>"
  (eq (symbol-class fn/thm wrld) :common-lisp-compliant))

(define guard-verified-p+ ((fn/thm (or (function-namep fn/thm wrld)
                                       (theorem-namep fn/thm wrld)))
                           (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee guard-verified-p)."
  :long
  "<p>
   This returns the same result as @(tsee guard-verified-p),
   but it has a stronger guard.
   </p>"
  (guard-verified-p fn/thm wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubody+ ((fn (or (and (logic-function-namep fn wrld)
                             (definedp fn wrld))
                        (pseudo-lambdap fn)))
                (wrld plist-worldp))
  :returns (body pseudo-termp
                 :hyp (or (symbolp fn) (pseudo-lambdap fn))
                 :hints (("Goal" :in-theory (enable pseudo-lambdap))))
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee ubody)."
  :long
  "<p>
   This returns the same result as @(tsee ubody),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (ubody fn wrld)))
    (if (pseudo-termp result)
        result
      (raise "Internal error: ~
              the unnormalized body ~x0 of ~x1 is not a pseudo-term."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uguard ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (guard "A @(tsee pseudo-termp).")
  :parents (world-queries)
  :short "Unoptimized guard of a named function or of a lambda expression."
  :long
  "<p>
   This is a specialization of
   <see topic='@(url system-utilities)'>@('guard')</see>
   with @('nil') as the second argument.
   Since @(tsee body) is in program mode only because of
   the code that handles the case in which the second argument is non-@('nil'),
   we avoid calling @(tsee guard) and instead replicate
   the code that handles the case in which the second argument is @('nil');
   thus, this utility is in logic mode and guard-verified.
   </p>
   <p>
   See @(tsee uguard+) for a logic-friendly variant of this utility.
   </p>"
  (cond ((symbolp fn) (getpropc fn 'guard *t* wrld))
        (t *t*)))

(define uguard+ ((fn (or (function-namep fn wrld)
                         (pseudo-lambdap fn)))
                 (wrld plist-worldp))
  :returns (guard pseudo-termp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee uguard)."
  :long
  "<p>
   This returns the same result as @(tsee uguard),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (uguard fn wrld)))
    (if (pseudo-termp result)
        result
      (raise "Internal error: ~
              the guard ~x0 of ~x1 is not a pseudo-term."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define non-executablep ((fn symbolp) (wrld plist-worldp))
  :returns (status "@('t'), @('nil'), or @(':program').")
  :parents (world-queries)
  :short "@(see Non-executable) status of a named logic-mode defined function."
  :long
  "<p>
   See @(tsee non-executablep+) for a logic-friendly variant of this utility.
   </p>"
  (getpropc fn 'non-executablep nil wrld))

(define non-executablep+ ((fn (function-namep fn wrld))
                          (wrld plist-worldp))
  :returns (nonexec (or (booleanp nonexec) (eq nonexec :program)))
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee non-executablep)."
  :long
  "<p>
   This returns the same result as @(tsee non-executablep),
   but it has a stronger guard
   and includes run-time checks (which should always succeed) on the result
   that allow us to prove the return type theorems
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (non-executablep fn wrld))
       ((unless (or (booleanp result)
                    (eq result :program)))
        (raise "Internal error: ~
                the non-executable status ~x0 of ~x1 is not ~
                T, NIL, or :PROGRAM."
               result fn))
       ((when (and (logicp fn wrld)
                   (eq result :program)))
        (raise "Internal error: ~
                the non-executable status of the logic-mode function ~x0 ~
                is :PROGRAM instead of T or NIL."
               fn)))
    result)
  ///

  (more-returns
   (nonexec booleanp
            :hyp (logicp fn wrld)
            :name booleanp-of-non-executablep+-when-logicp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unwrapped-nonexec-body ((fn symbolp) (wrld plist-worldp))
  :returns (unwrapped-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (world-queries)
  :short "Body of a named logic-mode defined non-executable function,
          without the ``non-executable wrapper''."
  :long
  "<p>
   @(tsee defun-nx) generates
   a logic-mode function whose body is wrapped as follows:
   </p>
   @({
     (return-last 'progn
                  (throw-nonexec-error 'fn
                                       (cons arg1 ... (cons argN 'nil)...))
                  body)
   })
   <p>
   If @(tsee defun) is used for a logic-mode function with
   <see topic='@(url non-executable)'>@(':non-executable')</see> set to @('t'),
   the submitted body (once translated) must be wrapped as above.
   </p>
   <p>
   This utility returns
   the unwrapped body of a logic-mode non-executable function @('fn'),
   by removing the wrapper shown above.
   </p>
   <p>
   See @(tsee unwrapped-nonexec-body+) for
   a logic-friendly variant of this utility.
   </p>"
  (fourth (ubody fn wrld)))

(define unwrapped-nonexec-body+ ((fn (and (logic-function-namep fn wrld)
                                          (definedp fn wrld)
                                          (non-executablep fn wrld)))
                                 (wrld plist-worldp-with-formals))
  :returns (unwrapped-body pseudo-termp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee unwrapped-nonexec-body)."
  :long
  "<p>
   This returns the same result as @(tsee unwrapped-nonexec-body),
   but it has a stronger guard,
   is guard-verified,
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   This utility also includes a run-time check (which should always succeed)
   that the wrapper around the body has the expected form,
   via the built-in function @('throw-nonexec-error-p');
   this allows us to verify the guards
   without strengthening the guard of @('wrld').
   </p>"
  (b* ((body (ubody+ fn wrld))
       ((unless (and (throw-nonexec-error-p body fn (formals+ fn wrld))
                     (consp (cdddr body))))
        (raise "Internal error: ~
                the body ~x0 of the non-executable function ~x1 ~
                does not have the expected wrapper."
               body fn))
       (unwrapped-body (fourth body))
       ((unless (pseudo-termp unwrapped-body))
        (raise "Internal error: ~
                the unwrapped body ~x0 of the non-executable function ~x1 ~
                is not a pseudo-term."
               unwrapped-body fn)))
    unwrapped-body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-of-results ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n natp "Actually a @(tsee posp).")
  :parents (world-queries)
  :short "Number of values returned by a named function."
  :long
  "<p>
   This is 1, unless the function uses @(tsee mv)
   (directly, or indirectly by calling another function that does)
   to return multiple values.
   </p>
   <p>
   The number of results of the function
   is the length of its @(tsee stobjs-out) list.
   </p>
   <p>
   The function must not be in @('*stobjs-out-invalid*'),
   because in that case the number of its results depends on how it is called.
   </p>
   <p>
   See @(tsee number-of-results+) for a logic-friendly variant of this utility.
   </p>"
  (len (stobjs-out fn wrld)))

(define number-of-results+ ((fn (function-namep fn wrld))
                            (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n posp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee number-of-results)."
  :long
  "<p>
   This returns the same result as @(tsee number-of-results),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (number-of-results fn wrld)))
    (if (posp result)
        result
      (prog2$
       (raise "Internal error: ~
              the STOBJS-OUT property of ~x0 is empty."
              fn)
       1)))) ; any POSP could be used here

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define no-stobjs-p ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (world-queries)
  :short "Check if a named function has no input or output @(see stobj)s."
  :long
  "<p>
   The function must not be in @('*stobjs-out-invalid*'),
   because in that case its (output) stobjs depend on how it is called.
   </p>
   <p>
   See @(tsee no-stobjs-p+) for a logic-friendly variant of this utility.
   </p>"
  (and (all-nils (stobjs-in fn wrld))
       (all-nils (stobjs-out fn wrld))))

(define no-stobjs-p+ ((fn (function-namep fn wrld))
                      (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee no-stobjs-p)."
  :long
  "<p>
   This returns the same result as @(tsee no-stobjs-p),
   but it has a stronger guard and is guard-verified.
   </p>"
  (and (all-nils (stobjs-in+ fn wrld))
       (all-nils (stobjs-out+ fn wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irecursivep ((fn symbolp) (wrld plist-worldp))
  :returns (clique "A @(tsee symbol-listp).")
  :parents (world-queries)
  :short "List of mutually recursive functions of which
          the specified named function is a member,
          based on the @(tsee defun) form that introduced this function,
          or @('nil') if the specified function is not recursive."
  :long
  "<p>
   This is a specialization of @(tsee recursivep)
   with @('nil') as the second argument:
   the @('i') that starts the name of @('irecursivep') conveys that
   the result is based on the @(tsee defun) form that <i>introduced</i> @('fn').
   </p>
   <p>
   See @(tsee irecursivep+) for a logic-friendly variant of this utility.
   </p>"
  (recursivep fn nil wrld))

(define irecursivep+ ((fn (logic-function-namep fn wrld))
                      (wrld plist-worldp))
  :returns (clique symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee irecursivep)."
  :long
  "<p>
   This returns the same result as @(tsee irecursivep),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (irecursivep fn wrld)))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the RECURSIVEP property ~x0 of ~x1 is not a true list of symbols."
             result fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define measure ((fn symbolp) (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (world-queries)
  :short "Measure expression of a named logic-mode recursive function."
  :long
  "<p>
   See @(see xargs) for a discussion of the @(':measure') keyword.
   </p>
   <p>
   See @(tsee measure+) for a logic-friendly variant of this utility.
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :measure)))

(define measure+ ((fn (and (logic-function-namep fn wrld)
                           (recursivep fn nil wrld)))
                  (wrld plist-worldp))
  :returns (measure pseudo-termp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee measure)."
  :long
  "<p>
   This returns the same result as @(tsee measure),
   but it has a stronger guard,
   is guard-verified,
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   This utility also includes a run-time check (which should always succeed)
   on the form of the @('justification') property of the function
   that allows us to verify the guards
   without strengthening the guard of @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the JUSTIFICATION property ~x0 of ~x1 is not well-formed."
               justification fn))
       (measure (access justification justification :measure))
       ((unless (pseudo-termp measure))
        (raise "Internal error: ~
                the measure ~x0 of ~x1 is not a pseudo-term."
               measure fn)))
    measure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define measured-subset ((fn symbolp) (wrld plist-worldp))
  :returns (measured-subset "A @(tsee symbol-listp).")
  :verify-guards nil
  :parents (world-queries)
  :short "Subset of the formal arguments
          of a named logic-mode recursive function
          that occur in its @(see measure) expression."
  :long
  "<p>
   See @(tsee measured-subset+) for a logic-friendly variant of this utility.
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :subset)))

(define measured-subset+ ((fn (and (logic-function-namep fn wrld)
                                   (recursivep fn nil wrld)))
                          (wrld plist-worldp))
  :returns (measured-subset symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee measured-subset)."
  :long
  "<p>
   This returns the same result as @(tsee measured-subset),
   but it has a stronger guard,
   is guard-verified,
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   This utility also includes a run-time check (which should always succeed)
   on the form of the @('justification') property of the function
   that allows us to verify the guards
   without strengthening the guard of @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the JUSTIFICATION property ~x0 of ~x1 is not well-formed."
               justification fn))
       (measured-subset (access justification justification :subset))
       ((unless (symbol-listp measured-subset))
        (raise "Internal error: ~
                the measured subset ~x0 of ~x1 is not a true list of symbols."
               measured-subset fn)))
    measured-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define well-founded-relation ((fn symbolp) (wrld plist-worldp))
  :returns (well-founded-relation "A @(tsee symbolp).")
  :verify-guards nil
  :parents (world-queries)
  :short "Well-founded relation of a named logic-mode recursive function."
  :long
  "<p>
   See @(see well-founded-relation-rule)
   for a discussion of well-founded relations in ACL2,
   including the @(':well-founded-relation') rule class.
   </p>
   <p>
   See @(tsee well-founded-relation+) for
   a logic-friendly variant of this utility.
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :rel)))

(define well-founded-relation+ ((fn (and (logic-function-namep fn wrld)
                                         (recursivep fn nil wrld)))
                                (wrld plist-worldp))
  :returns (well-founded-relation symbolp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee well-founded-relation)."
  :long
  "<p>
   This returns the same result as @(tsee well-founded-relation),
   but it has a stronger guard,
   is guard-verified,
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   This utility also includes a run-time check (which should always succeed)
   on the form of the @('justification') property of the function
   that allows us to verify the guards
   without strengthening the guard of @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the justification ~x0 of ~x1 is not well-formed."
               justification fn))
       (well-founded-relation (access justification justification :rel))
       ((unless (symbolp well-founded-relation))
        (raise "Internal error: ~
                the well-founded relation ~x0 of ~x1 is not a symbol."
               well-founded-relation fn)))
    well-founded-relation))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ruler-extenders ((fn symbolp) (wrld plist-worldp))
  :returns (ruler-extenders "A @(tsee symbol-listp) of @(':all').")
  :verify-guards nil
  :parents (world-queries)
  :short "Ruler-extenders of a named logic-mode recursive function."
  :long
  "<p>
   See @(see rulers) for background.
   </p>
   <p>
   See @(tsee ruler-extenders+) for a logic-friendly variant of this utility.
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :ruler-extenders)))

(define ruler-extenders+ ((fn (and (logic-function-namep fn wrld)
                                   (recursivep fn nil wrld)))
                          (wrld plist-worldp))
  :returns (ruler-extenders (or (symbol-listp ruler-extenders)
                                (equal ruler-extenders :all)))
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee ruler-extenders)."
  :long
  "<p>
   This returns the same result as @(tsee ruler-extenders),
   but it has a stronger guard,
   is guard-verified,
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   This utility also includes a run-time check (which should always succeed)
   on the form of the @('justification') property of the function
   that allows us to verify the guards
   without strengthening the guard of @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the 'JUSTIFICATION property ~x0 of ~x1 is not well-formed."
               justification fn))
       (ruler-extenders (access justification justification :ruler-extenders))
       ((unless (or (symbol-listp ruler-extenders)
                    (eq ruler-extenders :all)))
        (raise "Internal error: ~
                the well-founded relation ~x0 of ~x1 ~
                is neither a true list of symbols nor :ALL."
               ruler-extenders fn)))
    ruler-extenders))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MACRO-REQUIRED-ARGS moved to [books]/kestrel/std/system/

(define macro-required-args+ ((mac (macro-namep mac wrld))
                              (wrld plist-worldp))
  :returns (required-args symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee macro-required-args)."
  :long
  "<p>
   This returns the same result as @(tsee macro-required-args),
   but it has a stronger guard,
   is guard-verified,
   and includes run-time checks (which should always succeed)
   that allows us to prove the return type theorem and to verify guards
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((all-args (macro-args+ mac wrld)))
    (if (null all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args+-aux mac (cddr all-args) nil)
        (macro-required-args+-aux mac all-args nil))))

  :prepwork
  ((define macro-required-args+-aux ((mac symbolp)
                                     (args true-listp)
                                     (rev-result symbol-listp))
     :returns (final-result symbol-listp
                            :hyp (symbol-listp rev-result))
     (if (endp args)
         (reverse rev-result)
       (b* ((arg (car args)))
         (if (lambda-keywordp arg)
             (reverse rev-result)
           (if (symbolp arg)
               (macro-required-args+-aux mac
                                         (cdr args)
                                         (cons arg rev-result))
             (raise "Internal error: ~
                     the required macro argument ~x0 of ~x1 is not a symbol."
                    arg mac))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MACRO-KEYWORD-ARGS moved to [books]/kestrel/std/system/

(define macro-keyword-args+ ((mac (macro-namep mac wrld))
                             (wrld plist-worldp))
  :returns (keyword-args symbol-alistp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee macro-keyword-args)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee macro-keyword-args),
    but it has a stronger guard,
    is guard-verified,
    and includes run-time checks (which should always succeed)
    that allow us to prove the return type theorem and to verify the guards
    without strengthening the guard on @('wrld').")
  (b* ((all-args (macro-args+ mac wrld))
       (args-after-&key (cdr (member-eq '&key all-args)))
       (keyword-args (macro-keyword-args+-aux mac args-after-&key)))
    keyword-args)

  :prepwork
  ((define macro-keyword-args+-aux ((mac symbolp) args)
     :returns (keyword-args symbol-alistp)
     :verify-guards :after-returns
     :parents nil ; override default
     (b* (((when (atom args)) nil)
          (arg (car args))
          ((when (lambda-keywordp arg)) nil)
          ((when (symbolp arg))
           (acons arg nil (macro-keyword-args+-aux mac (cdr args))))
          ((unless (and (consp arg)
                        (symbolp (first arg))
                        (consp (cdr arg))
                        (consp (second arg))
                        (eq (car (second arg)) 'quote)
                        (consp (cdr (second arg)))))
           (raise "Internal error: ~
                   the keyword macro argument ~x0 of ~x1 ~
                   does not have the expected form."
                  arg mac)))
       (acons (first arg)
              (unquote (second arg))
              (macro-keyword-args+-aux mac (cdr args)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define thm-formula ((thm symbolp) (wrld plist-worldp))
  :returns (formula "A @(tsee pseudo-termp).")
  :parents (world-queries)
  :short "Formula of a named theorem."
  :long
  "<p>
   This is a specialization of @(tsee formula) to named theorems,
   for which the second argument of @(tsee formula) is immaterial.
   Since @(tsee formula) is in program mode only because of
   the code that handles the cases in which the first argument
   is not the name of a theorem,
   we avoid calling @(tsee formula) and instead replicate
   the code that handles the case in which
   the first argument is the name of a theorem;
   thus, this utility is in logic mode and guard-verified.
   </p>
   <p>
   See @(tsee thm-formula+) for a logic-friendly variant of this utility.
   </p>"
  (getpropc thm 'theorem nil wrld))

(define thm-formula+ ((thm (theorem-namep thm wrld))
                      (wrld plist-worldp))
  :returns (formula pseudo-termp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee thm-formula)."
  :long
  "<p>
   This returns the same result as @(tsee thm-formula),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (thm-formula thm wrld)))
    (if (pseudo-termp result)
        result
      (raise "Internal error: ~
              the FORMULA property ~x0 of ~x1 is not a pseudo-term."
             result thm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classes ((thm symbolp) (wrld plist-worldp))
  :returns (classes "An @(tsee alistp)
                     from @(tsee keywordp) to @(tsee keyword-value-listp).")
  :parents (world-queries)
  :short "Rule classes of a theorem."
  :long
  "<p>
   These form a value of type @('keyword-to-keyword-value-list-alistp'),
   which is defined in @('[books]/system/pseudo-good-worldp.lisp').
   </p>
   <p>
   See @(tsee classes+) for a logic-friendly variant of this utility.
   </p>"
  (getpropc thm 'classes nil wrld))

(define classes+ ((thm (theorem-namep thm wrld))
                  (wrld plist-worldp))
  :returns (classes keyword-to-keyword-value-list-alistp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee classes)."
  :long
  "<p>
   This returns the same result as @(tsee classes),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (classes thm wrld)))
    (if (keyword-to-keyword-value-list-alistp result)
        result
      (raise "Internal error: ~
              the rule classes ~x0 of ~x1 are not an alist
              from keywords to keyword-value lists."
             result thm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define induction-machine ((fn symbolp) (wrld plist-worldp))
  :returns (result "A @('pseudo-induction-machinep').")
  :parents (world-queries)
  :short "Induction machine of a named logic-mode (singly) recursive function."
  :long
  "<p>
   This is a list of @('tests-and-calls') records
   (see the ACL2 source code for information on these records),
   each of which contains zero or more recursive calls
   along with the tests that lead to them.
   The induction machine is a value of type @('pseudo-induction-machinep'),
   which is defined in @('[books]/system/pseudo-good-worldp.lisp').
   </p>
   <p>
   Note that
   induction is not directly supported for mutually recursive functions.
   </p>
   <p>
   See @(tsee induction-machine+) for a logic-friendly variant of this utility.
   </p>"
  (getpropc fn 'induction-machine nil wrld))

(define induction-machine+ ((fn (and (logic-function-namep fn wrld)
                                     (= 1 (len (irecursivep+ fn wrld)))))
                            (wrld plist-worldp))
  :returns (result (pseudo-induction-machinep fn result))
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee induction-machine)."
  :long
  "<p>
   This returns the same result as @(tsee induction-machine),
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((result (induction-machine fn wrld)))
    (if (pseudo-induction-machinep fn result)
        result
      (raise "Internal error: ~
              the INDUCTION-MACHINE property ~x0 of ~x1 ~
              does not have the expected form."
             result fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-tests-and-callp (x)
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Recognize well-formed @('tests-and-call') records."
  :long
  "<p>
   A @('tests-and-call') record is defined as
   </p>
   @({
     (defrec tests-and-call (tests call) nil)
   })
   <p>
   (see the ACL2 source code).
   </p>
   <p>
   In a well-formed @('tests-and-call') record,
   @('tests') must be a list of terms and
   @('call') must be a term.
   </p>
   <p>
   This recognizer is analogous to @('pseudo-tests-and-callsp')
   in @('[books]/system/pseudo-good-worldp.lisp')
   for @('tests-and-calls') records.
   </p>"
  (case-match x
    (('tests-and-call tests call)
     (and (pseudo-term-listp tests)
          (pseudo-termp call)))
    (& nil))
  ///

  (defrule weak-tests-and-call-p-when-pseudo-tests-and-callp
    (implies (pseudo-tests-and-callp x)
             (weak-tests-and-call-p x))))

(std::deflist pseudo-tests-and-call-listp (x)
  (pseudo-tests-and-callp x)
  :parents (world-queries)
  :short "Recognize true lists of well-formed @('tests-and-call') records."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define recursive-calls ((fn symbolp) (wrld plist-worldp))
  :returns (calls-with-tests "A @(tsee pseudo-tests-and-call-listp).")
  :mode :program
  :parents (world-queries)
  :short "Recursive calls of a named non-mutually-recursive function,
          along with the controlling tests."
  :long
  "<p>
   For singly recursive logic-mode functions,
   this is similar to the result of @(tsee induction-machine),
   but each record has one recursive call (instead of zero or more),
   and there is exactly one record for each recursive call.
   </p>
   <p>
   This utility works on both logic-mode and program-mode functions
   (if the program-mode functions have an @('unnormalized-body') property).
   This utility should not be called on a function that is
   mutually recursive with other functions;
   it must be called only on singly recursive functions,
   or on non-recursive functions (the result is @('nil') in this case).
   </p>
   <p>
   This utility may be extended to handle also mutually recursive functions.
   </p>
   <p>
   If the function is in logic mode and recursive,
   we obtain its ruler extenders and pass them to
   the built-in function @('termination-machine').
   Otherwise, we pass the default ruler extenders.
   </p>"
  (b* ((ruler-extenders (if (and (logicp fn wrld)
                                 (irecursivep fn wrld))
                            (ruler-extenders fn wrld)
                          (default-ruler-extenders wrld))))
    (termination-machine
     (list fn) (ubody fn wrld) nil nil ruler-extenders)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-disabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if the definition of a named function is disabled."
  (if (member-equal `(:definition ,fn) (disabledp fn)) t nil))

(define fundef-enabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if the definition of a named function is enabled."
  (not (fundef-disabledp fn state)))

(define rune-disabledp ((rune (runep rune (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if a @(see rune) is disabled."
  (if (member-equal rune (disabledp (cadr rune))) t nil))

(define rune-enabledp ((rune (runep rune (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if a @(see rune) is enabled."
  (not (rune-disabledp rune state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define known-packages (state)
  :returns (pkg-names "A @(tsee string-listp).")
  :parents (world-queries)
  :short "List of names of the known packages, in chronological order."
  :long
  "<p>
   See @(tsee known-packages+) for a logic-friendly variant of this utility.
   </p>"
  (reverse (strip-cars (known-package-alist state))))

(define known-packages+ (state)
  :returns (pkg-names string-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee known-packages)."
  :long
  "<p>
   This returns the same result as @(tsee known-packages),
   but it includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('state').
   </p>"
  (b* ((result (known-packages state)))
    (if (string-listp result)
        result
      (raise "Internal error: ~
              the list of keys ~x0 of the alist of known packages ~
              is not a true list of strings."
             result))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define included-books ((wrld plist-worldp))
  :returns (result "A @(tsee string-listp).")
  :verify-guards nil
  :parents (world-queries)
  :short "List of full pathnames of all books currently included
          (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-event-landmark-listp (x)
  (pseudo-event-landmarkp x)
  :parents (world-queries)
  :short "Recognize true lists of event landmarks."
  :long
  "<p>
   See @('pseudo-event-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp').
   </p>"
  :true-listp t
  :elementp-of-nil nil)

(std::deflist pseudo-command-landmark-listp (x)
  (pseudo-command-landmarkp x)
  :parents (world-queries)
  :short "Recognize true lists of command landmarks."
  :long
  "<p>
   See @('pseudo-command-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp').
   </p>"
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define event-landmark-names ((event pseudo-event-landmarkp))
  :returns (names "A @('string-or-symbol-listp').")
  :verify-guards nil
  :parents (world-queries)
  :short "Names introduced by an event landmark."
  :long
  "<p>
   Each event landmark introduces zero or more names into the @(see world).
   See @('pseudo-event-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp'),
   and the description of event tuples in the ACL2 source code.
   </p>"
  (let ((namex (access-event-tuple-namex event)))
    (cond ((equal namex 0) nil) ; no names
          ((consp namex) namex) ; list of names
          (t (list namex))))) ; single name

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-namep-msg-weak ((name symbolp) type (wrld plist-worldp))
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (msg/nil "A message (see @(tsee msg)) or @('nil').")
  :mode :program
  :parents (world-queries)
  :short "Return either @('nil') or a message indicating why the name is not
          a legal new name."
  :long
  "<p>
   This helper function for @(tsee fresh-namep-msg) avoids the ``virginity''
   check ensuring that the name is not already defined in raw Lisp.  See @(tsee
   fresh-namep-msg).
   </p>"
  (flet ((not-new-namep-msg (name wrld)
                            ;; It is tempting to report that the properties
                            ;; 'global-value, 'table-alist, 'table-guard are
                            ;; not relevant for this check.  But that would
                            ;; probably make the message confusing.
                            (let ((old-type (logical-name-type name wrld t)))
                              (cond
                               (old-type
                                (msg "~x0 is already the name for a ~s1."
                                     name
                                     (case old-type
                                       (function "function")
                                       (macro "macro")
                                       (const "constant")
                                       (stobj "stobj")
                                       (constrained-function
                                        "constrained function"))))
                               (t
                                (msg "~x0 has properties in the world; it is ~
                                      not a new name."
                                     name))))))
    (cond
     ((mv-let (ctx msg)
        (chk-all-but-new-name-cmp name 'fresh-namep-msg type wrld)
        (and ctx ; it's an error
             msg)))
     ((not (new-namep name wrld))
      (not-new-namep-msg name wrld))
     (t (case type
          (const
           (and (not (legal-constantp name))
                ;; A somewhat more informative error message is produced by
                ;; chk-legal-defconst-name, but I think the following suffices.
                (msg "~x0 is not a legal constant name."
                     name)))
          (stobj
           (and (not (new-namep (the-live-var name) wrld))
                (not-new-namep-msg (the-live-var name) wrld)))
          (t nil))))))

(define fresh-namep-msg ((name symbolp) type (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv (erp "Always @('nil').")
               (msg/nil "A message (see @(tsee msg)) or @('nil').")
               state)
  :mode :program
  :parents (world-queries)
  :short "Return either @('nil') or a message indicating why the name is not
          a legal new name."
  :long
  "<p>
   Returns an <see topic='@(url error-triple)'>error triple</see>
   @('(mv nil msg/nil state)'), where @('msg/nil')
   is either @('nil') or a message (see @(tsee msg)) indicating why the given
   name is not legal for a definition of the given type: @('function') for
   @(tsee defun), @('macro') for @(tsee defmacro), @('const') for @(tsee
   defconst), @('stobj') for @(tsee defstobj), @('constrained-function') for
   @(tsee defchoose), and otherwise @('nil') (for other kinds of @(see events),
   for example @(tsee defthm) and @(tsee deflabel)).  See @(see name).
   </p>
   <p>
   WARNING: This is an incomplete check in the case of a stobj name, because
   the field names required for a more complete check are not supplied as
   inputs.
   </p>
   <p>
   Implementation Note.  This function modifies @(see state), because the check
   for legality of new definitions (carried out by ACL2 source function
   @('chk-virgin-msg')) modifies state.  That modification is necessary because
   for all we know, raw Lisp is adding or removing function definitions that we
   don't know about without our having modified state; so logically, we pop the
   oracle when making this check.  End of Implementation Note.
   </p>"
  (let ((msg (fresh-namep-msg-weak name type wrld)))
    (cond (msg (value msg))
          (t (mv-let (msg state)
               (chk-virgin-msg name type wrld state)
               (value msg))))))

(define chk-fresh-namep ((name symbolp) type ctx (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv erp val state)
  :mode :program
  :parents (world-queries)
  :short "Check whether name is a legal new name."
  :long
  "<p>
   Returns an <see topic='@(url error-triple)'>error triple</see>
   @('(mv erp val state)') where @('erp') is
   @('nil') if and only if name is a legal new name, and @('val') is
   irrelevant.  If @('erp') is not nil, then an explanatory error message is
   printed.
   </p>
   <p>
   For more information about legality of new names see @(tsee fresh-namep-msg),
   which returns an <see topic='@(url error-triple)'>error triple</see>,
   @('(mv nil msg/nil state)').  When
   non-@('nil'), the value @('msg/nil') provides the message printed by
   @('chk-fresh-namep').
   </p>"
  (er-let* ((msg (fresh-namep-msg name type wrld state))) ; never an error
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))
