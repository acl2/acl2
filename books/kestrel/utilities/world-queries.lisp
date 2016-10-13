; World Queries
;
; Copyright (C) 2015-2016
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

; This file contains utilities for querying ACL2 worlds
; that complement the world query utilities in the ACL2 source code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "system/pseudo-good-worldp" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (set-default-parents world-queries))

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
  :short "True iff the symbol @('sym') names a theorem,
          i.e. it has a @('theorem') property."
  (not (eq t (getpropc sym 'theorem t wrld))))

(define macro-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff the symbol @('sym') names a macro."
  (not (eq t (getpropc sym 'macro-args t wrld))))

(define function-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a function."
  (and (symbolp x)
       (function-symbolp x wrld))
  :enabled t)

(define theorem-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a theorem."
  (and (symbolp x)
       (theorem-symbolp x wrld)))

(define macro-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a macro."
  (and (symbolp x)
       (macro-symbolp x wrld)))

(define logical-name-listp (names (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
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
  :short "True iff @('x') is a symbol that names a logic-mode function."
  (and (function-namep x wrld)
       (logicp x wrld))
  :enabled t)

(define definedp ((fn (logic-function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short "True iff the logic-mode function @('fn') is defined,
          i.e. it has an @('unnormalized-body') property."
  (not (eq t (getpropc fn 'unnormalized-body t wrld))))

(define guard-verified-p ((fn/thm (or (function-namep fn/thm wrld)
                                      (theorem-namep fn/thm wrld)))
                          (wrld plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep theorem-namep)))
  :short "True iff the function or theorem @('fn/thm')
          is @(tsee guard)-verified."
  (eq (symbol-class fn/thm wrld) :common-lisp-compliant))

(define non-executablep ((fn (and (logic-function-namep fn wrld)
                                  (definedp fn wrld)))
                         (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short "The @(tsee non-executable) status
          of the logic-mode, defined function @('fn')."
  (getpropc fn 'non-executablep nil wrld))

(define unwrapped-nonexec-body ((fn (and (function-namep fn wrld)
                                         (non-executablep fn wrld)))
                                (wrld plist-worldp))
  :returns (unwrapped-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Body of a non-executable function,
          without the &ldquo;non-executable wrapper&rdquo;."
  :long
  "<p>
   @(tsee Defun-nx) wraps the body of the function @('fn') being defined
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
   @(tsee Unwrapped-nonexec-body) returns
   the unwrapped body of the non-executable function @('fn').
   </p>
   <p>
   The code of this system utility defensively ensures that
   the body of @('fn') has the form above.
   </p>"
  (let ((body (body fn nil wrld)))
    (if (throw-nonexec-error-p body fn (formals fn wrld))
        (fourth (body fn nil wrld))
      (raise "The body ~x0 of the non-executable function ~x1 ~
             does not have the expected wrapper." body fn))))

(define number-of-results ((fn (function-namep fn wrld))
                           (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n "A @(tsee posp).")
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
  :short "True iff the function @('fn') has no input or output @(see stobj)s."
  :long
  "<p>
   The guard condition that @('fn') is not in @('*stobjs-out-invalid*')
   is copied from @('stobjs-out').
   </p>"
  (and (all-nils (stobjs-in fn wrld))
       (all-nils (stobjs-out fn wrld))))

(define measure ((fn (and (logic-function-namep fn wrld)
                          (recursivep fn nil wrld)))
                 (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Measure expression of a logic-mode recursive function."
  :long
  "<p>
   See @(see xargs) for a discussion of the @(':measure') keyword.
   </p>"
  (access justification (getpropc fn 'justification nil wrld) :measure))

(define measured-subset ((fn (and (logic-function-namep fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  :returns (measured-subset "A @(tsee symbol-listp).")
  :verify-guards nil
  :short "Subset of the formal arguments of the recursive function @('fn')
          that occur in its @(see measure) expression."
  (access justification (getpropc fn 'justification nil wrld) :subset))

(define well-founded-relation ((fn (and (logic-function-namep fn wrld)
                                        (recursivep fn nil wrld)))
                               (wrld plist-worldp))
  :returns (well-founded-relation "A @(tsee symbolp).")
  :verify-guards nil
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>See @(see well-founded-relation-rule)
   for a discussion of well-founded relations in ACL2,
   including the @(':well-founded-relation') rule class.</p>"
  (access justification (getpropc fn 'justification nil wrld) :rel))

(define ruler-extenders ((fn (and (logic-function-namep fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  :returns (ruler-extenders "A @(tsee symbol-listp) or @(':all').")
  :verify-guards nil
  :short "Ruler-extenders of a logic-mode recursive function
          (see @(see rulers) for background)."
  (access justification (getpropc fn 'justification nil wrld) :ruler-extenders))

(define macro-required-args ((mac (macro-namep mac wrld)) (wrld plist-worldp))
  :returns (required-args symbol-listp)
  :verify-guards nil
  :short "Required arguments of the macro @('mac'), in order."
  :long
  "<p>
   The arguments of a macro form a list that
   optionally starts with @('&whole') followed by another symbol,
   continues with zero or more symbols that do not start with @('&')
   which are the required arguments,
   and possibly ends with a symbol starting with @('&') followed by more symbols.
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
          (reverse (macro-required-args-aux (cddr all-args) nil))
        (reverse (macro-required-args-aux all-args nil)))))

  :prepwork
  ((define macro-required-args-aux ((args symbol-listp)
                                    (rev-result symbol-listp))
     :returns (final-rev-result symbol-listp :hyp (symbol-listp rev-result))
     (if (endp args)
         rev-result
       (let ((arg (mbe :logic (if (symbolp (car args)) (car args) nil)
                       :exec (car args))))
         (if (lambda-keywordp arg)
             rev-result
           (macro-required-args-aux (cdr args)
                                    (cons arg rev-result))))))))

(define fundef-disabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "True iff the definition of the function @('fn') is disabled."
  (member-equal `(:definition ,fn) (disabledp fn)))

(define fundef-enabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "True iff the definition of the function @('fn') is enabled."
  (not (fundef-disabledp fn state)))

(define rune-disabledp ((rune (runep rune (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "True iff the @(see rune) @('rune') is disabled."
  (member-equal rune (disabledp (cadr rune))))

(define rune-enabledp ((rune (runep rune (w state))) state)
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "True iff the @(see rune) @('rune') is enabled."
  (not (rune-disabledp rune state)))

(define included-books ((wrld plist-worldp))
  :returns (result "A @(tsee string-listp).")
  :verify-guards nil
  :short "List of full pathnames of all books currently included
          (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist wrld)))

(define induction-machine ((fn (and (logic-function-namep fn wrld)
                                    (= 1 (len (recursivep fn nil wrld)))))
                           (wrld plist-worldp))
  :returns (machine "A @('pseudo-induction-machinep') for @('fn').")
  :verify-guards nil
  :short "Induction machine of a (singly) recursive function."
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

(define pseudo-tests-and-callp (x)
  :returns (yes/no booleanp)
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
  :short "Recognize @('nil')-terminated lists of
          well-formed @('tests-and-call') records."
  :true-listp t
  :elementp-of-nil nil)

(define recursive-calls ((fn (and (logic-function-namep fn wrld)
                                  (= 1 (len (recursivep fn nil wrld)))))
                         (wrld plist-worldp))
  :returns (calls-with-tests "A @(tsee pseudo-tests-and-call-listp).")
  :mode :program
  :short "Recursive calls of a (singly) recursive function,
          along with the controlling tests."
  :long
  "<p>
   This is similar to the result of @(tsee induction-machine),
   but each record has one recursive calls (instead of zero or more),
   and there is exactly one record for each recursive call.
   </p>"
  (termination-machine
   (list fn) (body fn nil wrld) nil nil (ruler-extenders fn wrld)))

(std::deflist pseudo-event-landmark-listp (x)
  (pseudo-event-landmarkp x)
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
