; World Queries
;
; Copyright (C) 2015-2017
;   Kestrel Institute (http://www.kestrel.edu)
;   Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "system/pseudo-good-worldp" :dir :system)
(include-book "term-applicand-recognizers")

(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "arglistp-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (kestrel-utilities system-utilities)
  :short "Utilities to query @(see world)s."
  :long
  "<p>
   These complement the world query utilities
   in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
   </p>")

(define theorem-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a symbol names a theorem,
          i.e. it has a @('theorem') property."
  :long
  "<p>
   This function is named in analogy to
   the @(tsee function-symbolp) built-in system utility.
   </p>"
  (not (eq t (getpropc sym 'theorem t wrld))))

(define macro-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a symbol names a macro,
          i.e. it has a @('macro-args') property."
  :long
  "<p>
   This function is named in analogy to
   the @(tsee function-symbolp) built-in system utility.
   </p>"
  (not (eq t (getpropc sym 'macro-args t wrld))))

(std::deflist function-symbol-listp (x wrld)
  (function-symbolp x wrld)
  :guard (and (symbol-listp x)
              (plist-worldp wrld))
  :parents (world-queries)
  :short "Check if all the symbols in a list name functions."
  :true-listp t)

(std::deflist theorem-symbol-listp (x wrld)
  (theorem-symbolp x wrld)
  :guard (and (symbol-listp x)
              (plist-worldp wrld))
  :parents (world-queries)
  :short "Check if all the symbols in a list name theorems."
  :true-listp t)

(std::deflist macro-symbol-listp (x wrld)
  (macro-symbolp x wrld)
  :guard (and (symbol-listp x)
              (plist-worldp wrld))
  :parents (world-queries)
  :short "Check if all the symbols in a list name macros."
  :true-listp t)

(define function-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Recognize symbols that name functions."
  (and (symbolp x)
       (function-symbolp x wrld))
  :enabled t)

(define theorem-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Recognize symbols that name theorems."
  (and (symbolp x)
       (theorem-symbolp x wrld)))

(define macro-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Recognize symbols that name macros."
  (and (symbolp x)
       (macro-symbolp x wrld)))

(std::deflist function-name-listp (x wrld)
  (function-namep x wrld)
  :guard (plist-worldp wrld)
  :parents (world-queries)
  :short "Recognize @('nil')-terminated of symbols that name functions."
  :true-listp t)

(std::deflist theorem-name-listp (x wrld)
  (theorem-namep x wrld)
  :guard (plist-worldp wrld)
  :parents (world-queries)
  :short "Recognize @('nil')-terminated of symbols that name theorems."
  :true-listp t)

(std::deflist macro-name-listp (x wrld)
  (macro-namep x wrld)
  :guard (plist-worldp wrld)
  :parents (world-queries)
  :short "Recognize @('nil')-terminated of symbols that name macros."
  :true-listp t)

(define logical-name-listp (names (wrld plist-worldp))
  ;; we cannot use STD::DEFLIST to define LOGICAL-NAME-LISTP
  ;; because STD::DEFLIST attempts to prove that LOGICAL-NAMEP is boolean,
  ;; which it is not
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (world-queries)
  :short "Recognize @('nil')-terminated lists of logical names."
  :long
  "<p>
   See @('logical-namep') in the ACL2 source code.
   </p>"
  (cond ((atom names) (null names))
        (t (and (logical-namep (car names) wrld)
                (logical-name-listp (cdr names) wrld)))))

(define logic-function-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Recognize symbols that name logic-mode functions."
  (and (function-namep x wrld)
       (logicp x wrld))
  :enabled t)

(define formals+ ((fn (or (function-namep fn wrld)
                          (pseudo-lambdap fn)))
                  (wrld plist-worldp-with-formals))
  :returns (formals symbol-listp)
  :parents (world-queries)
  :short "Logic-friendly variant of @(tsee formals)."
  :long
  "<p>
   This returns the same result of @(tsee formals) on functions,
   but it has a stronger guard
   and includes a run-time check (which should always succeed) on the result
   that allows us to prove the return type theorem
   without strengthening the guard on @('wrld').
   </p>
   <p>
   This utility also works on lambda expressions.
   </p>"
  (b* ((formals (cond ((symbolp fn) (formals fn wrld))
                      (t (lambda-formals fn)))))
    (if (symbol-listp formals)
        formals
      (raise "Internal error: ~
              the formals ~x0 of ~x1 are not ~
              a NIL-terminated list of symbols."
             formals fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

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
   This returns the same result of @(tsee arity) on functions,
   but it has a stronger guard.
   </p>
   <p>
   This utility also works on lambda expressions.
   </p>"
  (arity fn wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(define definedp ((fn (logic-function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a logic-mode function is defined,
          i.e. it has an @('unnormalized-body') property."
  (not (eq t (getpropc fn 'unnormalized-body t wrld)))
  :guard-hints (("Goal" :in-theory (enable function-namep))))

(define guard-verified-p ((fn/thm (or (function-namep fn/thm wrld)
                                      (theorem-namep fn/thm wrld)))
                          (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "Check if a function or theorem is @(tsee guard)-verified."
  (eq (symbol-class fn/thm wrld) :common-lisp-compliant)
  :guard-hints (("Goal" :in-theory (enable function-namep theorem-namep))))

(define non-executablep ((fn (and (logic-function-namep fn wrld)
                                  (definedp fn wrld)))
                         (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (world-queries)
  :short "The @(tsee non-executable) status of a logic-mode defined function."
  :long
  "<p>
   The check that the non-executable status is a boolean should always succeed,
   but it allows us to prove the return type theorem for this function
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((non-executablep (getpropc fn 'non-executablep nil wrld)))
    (if (booleanp non-executablep)
        non-executablep
      (raise "Internal error: ~
              the non-executable status ~x0 of ~x1 is not a boolean."
             non-executablep fn)))
  :guard-hints (("Goal" :in-theory (enable function-namep))))

(define ubody ((fn (or (and (logic-function-namep fn wrld)
                            (definedp fn wrld))
                       (pseudo-lambdap fn)))
               (wrld plist-worldp))
  :returns (body pseudo-termp
                 :hyp (or (symbolp fn) (pseudo-lambdap fn))
                 :hints (("Goal" :in-theory (enable pseudo-lambdap))))
  :parents (world-queries)
  :short "Unnormalized body of a logic-mode defined named function,
          or body of a lambda expression."
  :long
  "<p>
   The check that the unnormalized body of a named function is a pseudo-term,
   should always succeed,
   but it allows us to prove the return type theorem for this function
   without strengthening the guard on @('wrld').
   </p>"
  (cond ((symbolp fn)
         (b* ((body (getpropc fn 'unnormalized-body nil wrld)))
           (if (pseudo-termp body)
               body
             (raise "Internal error: ~
                     the unnormalized body ~x0 of ~x1 is not a pseudo-term."
                    body fn))))
        (t (lambda-body fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(define unwrapped-nonexec-body ((fn (and (logic-function-namep fn wrld)
                                         (definedp fn wrld)
                                         (non-executablep fn wrld)))
                                (wrld plist-worldp))
  :returns (unwrapped-body pseudo-termp)
  :verify-guards nil
  :parents (world-queries)
  :short "Body of a logic-mode defined non-executable function,
          without the &ldquo;non-executable wrapper&rdquo;."
  :long
  "<p>
   @(tsee defun-nx) wraps the body of the function @('fn') being defined
   in a wrapper that has
   the following <see topic='@(url term)'>translated</see> form:
   </p>
   @({
     (return-last 'progn
                  (throw-nonexec-error 'fn
                                       (cons arg1 ... (cons argN 'nil)...))
                  body)
   })
   <p>
   If @(tsee defun) is used with
   <see topic='@(url non-executable)'>@(':non-executable')</see> set to @('t'),
   the submitted body (once translated) must be wrapped like that.
   </p>
   <p>
   @(tsee unwrapped-nonexec-body) returns
   the unwrapped body of the non-executable function @('fn').
   </p>
   <p>
   The code of this system utility defensively ensures that
   the body of @('fn') has the form above.
   </p>
   <p>
   The check that the unwrapped body is a pseudo-term should always succeed,
   but it allows us to prove the return type theorem for this function
   without strengthening the guard on @('wrld').
   </p>"
  (let ((body (ubody fn wrld)))
    (if (throw-nonexec-error-p body fn (formals fn wrld))
        (let ((unwrapped-body (fourth body)))
          (if (pseudo-termp unwrapped-body)
              unwrapped-body
            (raise "Internal error: ~
                    the unwrapped body ~x0 of the non-executable function ~x1 ~
                    is not a pseudo-term."
                   unwrapped-body fn)))
      (raise "Internal error: ~
              the body ~x0 of the non-executable function ~x1 ~
              does not have the expected wrapper."
             body fn))))

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
              the input stobjs ~x0 of ~x1 do not form ~
              a NIL-terminated list of symbols."
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
   </p>"
  (b* ((result (stobjs-out fn wrld)))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the output stobjs ~x0 of ~x1 do not form ~
              a NIL-terminated list of symbols."
             result fn))))

(define number-of-results ((fn (function-namep fn wrld))
                           (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n natp "Actually a @(tsee posp).")
  :parents (world-queries)
  :short "Number of values returned by a function."
  :long
  "<p>
   This is 1, unless the function uses @(tsee mv)
   (directly, or indirectly by calling another function that does)
   to return multiple values.
   </p>
   <p>
   The number of results of the function
   is the length of its @(tsee stobjs-out) list.
   But the function must not be in @('*stobjs-out-invalid*'),
   because in that case the number of its results depends on how it is called.
   </p>"
  (len (stobjs-out fn wrld))
  :guard-hints (("Goal" :in-theory (enable function-namep))))

(define no-stobjs-p ((fn (function-namep fn wrld)) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (world-queries)
  :short "Check if a function has no input or output @(see stobj)s."
  :long
  "<p>
   The guard condition that @('fn') is not in @('*stobjs-out-invalid*')
   is copied from @('stobjs-out').
   </p>"
  (and (all-nils (stobjs-in fn wrld))
       (all-nils (stobjs-out fn wrld))))

(define irecursivep ((fn symbolp) (wrld plist-worldp))
  :returns (clique "A @(tsee symbol-listp).")
  :parents (world-queries)
  :short "List of mutually recursive functions of which
          this function is a member,
          based on the @(tsee defun) form that introduced this function,
          or @('nil') if this function is not recursive."
  :long
  "<p>
   This is a specialization of @(tsee recursivep)
   with @('nil') as the second argument:
   the @('i') that starts the name of @('irecursivep') conveys that
   the result is based on the @(tsee defun) form that introduced @('fn').
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
  (b* ((clique (irecursivep fn wrld)))
    (if (symbol-listp clique)
        clique
      (raise "Internal error: ~
              the 'RECURSIVEP property ~x0 of ~x1 is not ~
              a NIL-terminated list of symbols."
             clique fn))))

(define measure ((fn (and (logic-function-namep fn wrld)
                          (recursivep fn nil wrld)))
                 (wrld plist-worldp))
  :returns (measure pseudo-termp)
  :parents (world-queries)
  :short "Measure expression of a logic-mode recursive function."
  :long
  "<p>
   See @(see xargs) for a discussion of the @(':measure') keyword.
   </p>
   <p>
   The checks that the justification property is well-formed
   and that the measure is a pseudo-term
   should always succeed,
   but they allow us to verify the guards of this function
   and to prove the return type theorem for this function,
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the justification ~x0 of ~x1 is not well-formed."
               justification fn))
       (measure (access justification justification :measure))
       ((unless (pseudo-termp measure))
        (raise "Internal error: ~
                the measure ~x0 of ~x1 is not a pseudo-term."
               measure fn)))
    measure))

(define measured-subset ((fn (and (logic-function-namep fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  :returns (measured-subset symbol-listp)
  :parents (world-queries)
  :short "Subset of the formal arguments of a logic-mode recursive function
          that occur in its @(see measure) expression."
  :long
  "<p>
   The checks that the justification property is well-formed
   and that the measured subset is a @('nil')-terminated list of symbols
   should always succeed,
   but they allow us to verify the guards of this function
   and to prove the return type theorem for this function,
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the justification ~x0 of ~x1 is not well-formed."
               justification fn))
       (measured-subset (access justification justification :subset))
       ((unless (symbol-listp measured-subset))
        (raise "Internal error: ~
                the measured subset ~x0 of ~x1 is not ~
                a NIL-terminated list of symbols."
               measured-subset fn)))
    measured-subset))

(define well-founded-relation ((fn (and (logic-function-namep fn wrld)
                                        (recursivep fn nil wrld)))
                               (wrld plist-worldp))
  :returns (well-founded-relation symbolp)
  :parents (world-queries)
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>
   See @(see well-founded-relation-rule)
   for a discussion of well-founded relations in ACL2,
   including the @(':well-founded-relation') rule class.
   </p>
   <p>
   The checks that the justification property is well-formed
   and that the well-founded relation is a symbol
   should always succeed,
   but they allow us to verify the guards of this function
   and to prove the return type theorem for this function,
   without strengthening the guard on @('wrld').
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

(define ruler-extenders ((fn (and (logic-function-namep fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  :returns (ruler-extenders (or (symbol-listp ruler-extenders)
                                (equal ruler-extenders :all)))
  :parents (world-queries)
  :short "Ruler-extenders of a logic-mode recursive function
          (see @(see rulers) for background)."
  :long
  "<p>
   The checks that the justification property is well-formed
   and that the ruler-extenders are
   a @('nil')-terminated list of symbols or @(':all')
   should always succeed,
   but they allow us to verify the guards of this function
   and to prove the return type theorem for this function,
   without strengthening the guard on @('wrld').
   </p>"
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the justification ~x0 of ~x1 is not well-formed."
               justification fn))
       (ruler-extenders (access justification justification :ruler-extenders))
       ((unless (or (symbol-listp ruler-extenders)
                    (eq ruler-extenders :all)))
        (raise "Internal error: ~
                the well-founded relation ~x0 of ~x1 is not ~
                a NIL-terminated list of symbols or :ALL."
               ruler-extenders fn)))
    ruler-extenders))

(define macro-required-args ((mac (macro-namep mac wrld)) (wrld plist-worldp))
  :returns (required-args "A @(tsee symbol-listp).")
  :verify-guards nil
  :parents (world-queries)
  :short "Required arguments of a macro, in order."
  :long
  "<p>
   The arguments of a macro form a list that
   optionally starts with @('&whole') followed by another symbol,
   continues with zero or more symbols that do not start with @('&')
   which are the required arguments,
   and possibly ends with
   a symbol starting with @('&') followed by more things.
   </p>
   <p>
   After removing @('&whole') and the symbol following it
   (if the list of arguments starts with @('&whole')),
   we collect all the arguments until
   either the end of the list is reached
   or a symbol starting with @('&') is encountered.
   </p>"
  (let ((all-args (macro-args mac wrld)))
    (if (null all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args-aux (cddr all-args) nil)
        (macro-required-args-aux all-args nil))))

  :prepwork
  ((define macro-required-args-aux ((args true-listp)
                                    (rev-result symbol-listp))
     :returns (final-result "A @(tsee symbol-listp).")
     :verify-guards nil
     (if (endp args)
         (reverse rev-result)
       (let ((arg (car args)))
         (if (lambda-keywordp arg)
             (reverse rev-result)
           (macro-required-args-aux (cdr args)
                                    (cons arg rev-result))))))))

(define fundef-disabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if the definition of a function is disabled."
  (if (member-equal `(:definition ,fn) (disabledp fn)) t nil))

(define fundef-enabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (world-queries)
  :short "Check if the definition of a function is enabled."
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

(define included-books ((wrld plist-worldp))
  :returns (result "A @(tsee string-listp).")
  :verify-guards nil
  :parents (world-queries)
  :short "List of full pathnames of all books currently included
          (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist wrld)))

(define induction-machine ((fn (and (logic-function-namep fn wrld)
                                    (= 1 (len (recursivep fn nil wrld)))))
                           (wrld plist-worldp))
  :returns (machine "A @('pseudo-induction-machinep') for @('fn').")
  :parents (world-queries)
  :short "Induction machine of a (singly) recursive logic-mode function."
  :long
  "<p>
   This is a list of @('tests-and-calls') records
   (see the ACL2 source code for information on these records),
   each of which contains zero or more recursive calls
   along with the tests that lead to them.
   </p>
   <p>
   This function only applies to singly recursive functions,
   because induction is not directly supported for mutually recursive functions.
   </p>"
  (getpropc fn 'induction-machine nil wrld))

(define thm-formula ((thm symbolp) (wrld plist-worldp))
  :returns (formula "A @(tsee pseudo-termp).")
  :parents (world-queries)
  :short "Formula of a theorem."
  :long
  "<p>
   This is a specialization of @(tsee formula) to theorems.
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
  (b* ((formula (thm-formula thm wrld)))
    (if (pseudo-termp formula)
        formula
      (raise "Internal error: ~
              the 'FORMULA property ~x0 of ~x1 is not a pseudo-term."
             formula thm)))
  :guard-hints (("Goal" :in-theory (enable theorem-namep))))

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
             (weak-tests-and-call-p x))
    :rule-classes nil))

(std::deflist pseudo-tests-and-call-listp (x)
  (pseudo-tests-and-callp x)
  :parents (world-queries)
  :short "Recognize @('nil')-terminated lists of
          well-formed @('tests-and-call') records."
  :true-listp t
  :elementp-of-nil nil)

(define recursive-calls ((fn (and (logic-function-namep fn wrld)
                                  (= 1 (len (recursivep fn nil wrld)))))
                         (wrld plist-worldp))
  :returns (calls-with-tests "A @(tsee pseudo-tests-and-call-listp).")
  :mode :program
  :parents (world-queries)
  :short "Recursive calls of a (singly) recursive logic-mode function,
          along with the controlling tests."
  :long
  "<p>
   This is similar to the result of @(tsee induction-machine),
   but each record has one recursive call (instead of zero or more),
   and there is exactly one record for each recursive call.
   </p>"
  (termination-machine
   (list fn) (ubody fn wrld) nil nil (ruler-extenders fn wrld)))

(std::deflist pseudo-event-landmark-listp (x)
  (pseudo-event-landmarkp x)
  :parents (world-queries)
  :short "Recognize @('nil')-terminated lists of event landmarks."
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
  :short "Recognize @('nil')-terminated lists of command landmarks."
  :long
  "<p>
   See @('pseudo-command-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp').
   </p>"
  :true-listp t
  :elementp-of-nil nil)

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

(define fresh-namep-msg-weak (name type (wrld plist-worldp))
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (msg/nil "A message (see @(tsee msg)) or @('nil').")
  :mode :program
  :parents (world-queries)
  :short "Returns either @('nil') or a message indicating why the name is not ~
          a legal new name."
  :long
  "<p>
   This helper function for @(tsee fresh-namep-msg) avoids the ``virginity''
   check ensuring that the name is not already defined in raw Lisp.  See @(tsee
   fresh-namep-msg).
   </p>"

  (flet ((not-new-namep-msg (name wrld)

; It is tempting to report that the properties 'global-value, 'table-alist,
; 'table-guard are not relevant for this check.  But that would probably make
; the message confusing.

                            (let ((old-type (logical-name-type name wrld t)))
                              (cond
                               (old-type
                                (msg "~x0 is already the name for a ~s1."
                                     name
                                     (string-downcase
                                      (symbol-name old-type))))
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

; A somewhat more informative error message is produced by
; chk-legal-defconst-name, but I think the following suffices.

                (msg "~x0 is not a legal constant name."
                     name)))
          (stobj
           (and (not (new-namep (the-live-var name) wrld))
                (not-new-namep-msg (the-live-var name) wrld)))
          (t nil))))))

(define fresh-namep-msg (name type (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv (erp "Always @('nil')")
               (msg/nil "A message (see @(tsee msg)) or @('nil').")
               state)
  :mode :program
  :parents (world-queries)
  :short "Returns either @('nil') or a message indicating why the name is not ~
          a legal new name."
  :long
  "<p>
   Returns an @('error-triple') @('(mv nil msg/nil state)'), where @('msg/nil')
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

(define chk-fresh-namep (name type ctx (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv erp val state)
  :mode :program
  :parents (world-queries)
  :short "Checks whether name is a legal new name."
  :long
  "<p>
   Returns an @(see error-triple) @('(mv erp val state)') where @('erp') is
   @('nil') if and only if name is a legal new name, and @('val') is
   irrelevant.  If @('erp') is not nil, then an explanatory error message is
   printed.
   </p>

   <p>
   For more information about legality of new names see @(tsee fresh-namep-msg),
   which returns an @(see error-triple), @('(mv nil msg/nil state)').  When
   non-@('nil'), the value @('msg/nil') provides the message printed by
   @('chk-fresh-namep').
   </p>"
  (er-let* ((msg (fresh-namep-msg name type wrld state))) ; never an error
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))
