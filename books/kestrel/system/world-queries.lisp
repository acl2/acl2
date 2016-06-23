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

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist-base" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/pseudo-good-worldp" :dir :system)
(include-book "system/kestrel" :dir :system)

(local (set-default-parents world-queries))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities to query <see topic='@(url world)'>worlds</see>."
  :long
  "<p>
  These complement the world query utilities
  in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
  </p>")

(define theorem-symbolp ((sym symbolp) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the symbol @('sym') names a theorem,
  i.e. it has a @('theorem') property."
  (not (eq t (getpropc sym 'theorem t w))))

(define macro-symbolp ((sym symbolp) (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff the symbol @('sym') names a macro."
  (not (eq t (getpropc sym 'macro-args t w))))

(define function-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a function."
  (and (symbolp x) (function-symbolp x w)))

(define theorem-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a theorem."
  (and (symbolp x) (theorem-symbolp x w)))

(define macro-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a macro."
  (and (symbolp x) (macro-symbolp x w)))

(define logical-name-listp (names (w plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize @('nil')-terminated lists of logical names."
  :long
  "<p>
  See @('logical-namep') in the ACL2 source code.
  </p>"
  (cond ((atom names) (null names))
        (t (and (logical-namep (car names) w)
                (logical-name-listp (cdr names) w)))))

(define definedp ((fun (function-namep fun w)) (w plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short
  "True iff the function @('fun') is defined,
  i.e. it has an @('unnormalized-body') property."
  :long
  "<p>
  Note that built-in @(see program)-mode functions
  do not have an @('unnormalized-body') property,
  even though they have definitions.
  Since their translated bodies are not stored,
  they are not considered to be &ldquo;defined&rdquo;
  from the perspective of the @(tsee definedp) system utility.
   </p>"
  (not (eq t (getpropc fun 'unnormalized-body t w))))

(define guard-verified-p ((fun/thm (or (function-namep fun/thm w)
                                       (theorem-namep fun/thm w)))
                          (w plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep theorem-namep)))
  :short
  "True iff the function or theorem @('fun/thm') is @(tsee guard)-verified."
  (eq (symbol-class fun/thm w) :common-lisp-compliant))

(define non-executablep ((fun (and (function-namep fun w)
                                   (definedp fun w)))
                         (w plist-worldp))
  ;; :returns (result (member result '(t nil :program)))
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short "The @(tsee non-executable) status of the defined function @('fun')."
  (getpropc fun 'non-executablep nil w))

(define unwrapped-nonexec-body ((fun (and (function-namep fun w)
                                          (non-executablep fun w)))
                                (w plist-worldp))
  ;; :returns (unwrapped-body pseudo-termp)
  :verify-guards nil
  :short
  "Body of a non-executable function,
  without the &ldquo;non-executable wrapper&rdquo;."
  :long
  "<p>
  @(tsee Defun-nx) wraps the body of the function @('fun') being defined
  in a wrapper that has
  the following <see topic='@(url term)'>translated</see> form:
  </p>
  @({
    (return-last 'progn
                 (throw-nonexec-error 'fun
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
  the unwrapped body of the non-executable function @('fun').
  </p>
  <p>
  The code of this system utility defensively ensures that
  the body of @('fun') has the form above.
  </p>"
  (let ((body (body fun nil w)))
    (if (throw-nonexec-error-p body fun (formals fun w))
        (fourth (body fun nil w))
      (raise "The body ~x0 of the non-executable function ~x1 ~
             does not have the expected wrapper." body fun))))

(define no-stobjs-p ((fun (function-namep fun w)) (w plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short
  "True iff the function @('fun') has no
  input or output <see topic='@(url stobj)'>stobjs</see>."
  (and (all-nils (stobjs-in fun w))
       (all-nils (stobjs-out fun w))))

(define measure ((fun (and (function-namep fun w)
                           (logicp fun w)
                           (recursivep fun w)))
                 (w plist-worldp))
  ;; :returns (measure pseudo-termp)
  :verify-guards nil
  :short "Measure expression of a logic-mode recursive function."
  :long "<p>See @(see xargs) for a discussion of the @(':measure') keyword.</p>"
  (access justification (getpropc fun 'justification nil w) :measure))

(define measured-subset ((fun (and (function-namep fun w)
                                   (logicp fun w)
                                   (recursivep fun w)))
                         (w plist-worldp))
  ;; :returns (measured-subset symbol-listp)
  :verify-guards nil
  :short
  "Subset of the formal arguments of the recursive function @('fun')
  that occur in its @(see measure) expression."
  (access justification (getpropc fun 'justification nil w) :subset))

(define well-founded-relation ((fun (and (function-namep fun w)
                                         (logicp fun w)
                                         (recursivep fun w)))
                               (w plist-worldp))
  ;; :returns (well-founded-relation symbolp)
  :verify-guards nil
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>See @(see well-founded-relation-rule)
  for a discussion of well-founded relations in ACL2,
  including the @(':well-founded-relation') rule class.</p>"
  (access justification (getpropc fun 'justification nil w) :rel))

(define ruler-extenders ((fun (and (function-namep fun w)
                                   (logicp fun w)
                                   (recursivep fun w)))
                         (w plist-worldp))
  ;; :returns (ruler-extenders (or (symbol-listp ruler-extenders)
  ;;                               (equal ruler-extenders :all)))
  :verify-guards nil
  :short
  "Ruler-extenders of a logic-mode recursive function
  (see @(see rulers) for background)."
  (access justification (getpropc fun 'justification nil w) :ruler-extenders))

(define macro-required-args ((mac (macro-namep mac w)) (w plist-worldp))
  ;; :returns (required-args symbol-listp)
  :verify-guards nil
  :short "Required arguments of the macro @('mac'), in order."
  :long
  "<p>
  The arguments of a macro form a list that
  optionally starts with @('&whole') followed by another symbol,
  continues with zero or more symbols that do not start with @('&')
  which are the required arguments,
  and possibly ends with a symbol starting with @('&') followed by more symbols.
  </p>"
  (let ((all-args (macro-args mac w)))
    (if (null all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args-aux (cddr all-args))
        (macro-required-args-aux all-args))))

  :prepwork
  ((define macro-required-args-aux ((args symbol-listp))
     ;; :returns (required-args symbol-listp)
     :parents (macro-required-args)
     :short "Auxiliary function of @(tsee macro-required-args)."
     :long
     "<p>
     After removing @('&whole') and the symbol following it
     (if the list of arguments starts with @('&whole')),
     collect all the arguments until
     either the end of the list is reached
     or a symbol starting with @('&') is encountered.
     </p>"
     (if (endp args)
         nil
       (let ((arg (car args)))
         (if (lambda-keywordp arg)
             nil
           (cons arg (macro-required-args-aux (cdr args)))))))))

(define fundef-disabledp ((fun (function-namep fun (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the definition of the function @('fun') is disabled."
  (member-equal `(:definition ,fun) (disabledp fun)))

(define fundef-enabledp ((fun (function-namep fun (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the definition of the function @('fun') is enabled."
  (not (fundef-disabledp fun state)))

(define rune-disabledp ((rune (runep rune (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the @(see rune) @('rune') is disabled."
  (member-equal rune (disabledp (cadr rune))))

(define rune-enabledp ((rune (runep rune (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the @(see rune) @('rune') is enabled."
  (not (rune-disabledp rune state)))

(define included-books ((w plist-worldp))
  ;; :returns (result string-listp)
  :verify-guards nil
  :short
  "List of full pathnames of all books currently included
  (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist w)))

(define induction-machine ((fun (and (function-namep fun w)
                                     (logicp fun w)
                                     (eql 1 (len (recursivep fun w)))))
                           (w plist-worldp))
  ;; :returns (machine (pseudo-induction-machinep fun machine))
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
  (getpropc fun 'induction-machine nil w))

(std::deflist weak-tests-and-call-listp (x)
  (weak-tests-and-call-p x)
  :short "List of @('tests-and-call') records."
  :long
  "<p>
  See the ACL2 source code for information on these records.
  </p>"
  :true-listp t
  :elementp-of-nil nil)

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
  :short
  "Recognize @('nil')-terminated lists of
  well-formed @('tests-and-call') records."
  :true-listp t
  :elementp-of-nil nil)

(define recursive-calls ((fun (and (function-namep fun w)
                                   (logicp fun w)
                                   (eql 1 (len (recursivep fun w)))))
                         (w plist-worldp))
  ;; :returns (calls-with-tests pseudo-tests-and-call-listp)
  :verify-guards nil
  :short
  "Recursive calls of a (singly) recursive function,
  along with the controlling tests."
  :long
  "<p>
  This is similar to the result of @(tsee induction-machine),
  but each record has one recursive calls (instead of zero or more),
  and there is exactly one record for each recursive call.
  </p>"
  (recursive-calls-aux2 (induction-machine fun w))

  :prepwork

  ((define recursive-calls-aux1 ((tests pseudo-term-listp)
                                 (calls pseudo-term-listp))
     ;; :returns (calls-with-tests pseudo-tests-and-call-listp)
     :parents (recursive-calls)
     :short "First auxiliary function of @(tsee recursive-calls)."
     :long
     "<p>
     Pair each call in @('calls') with the tests @('tests').
     </p>"
     (if (endp calls)
         nil
       (cons (make tests-and-call
                   :tests tests
                   :call (car calls))
             (recursive-calls-aux1 tests (cdr calls)))))

   (define recursive-calls-aux2
     ((tests-and-calls-list pseudo-tests-and-calls-listp))
     ;; :returns (calls-with-tests pseudo-tests-and-call-listp)
     :verify-guards nil
     :parents (recursive-calls)
     :short "Second auxiliary function of @(tsee recursive-calls)."
     :long
     "<p>
     Collect all the calls, with tests, from the induction machine.
     </p>"
     (if (endp tests-and-calls-list)
         nil
       (let* ((tests-and-calls (car tests-and-calls-list))
              (tests (access tests-and-calls tests-and-calls :tests))
              (calls (access tests-and-calls tests-and-calls :calls)))
         (append (recursive-calls-aux1 tests calls)
                 (recursive-calls-aux2 (cdr tests-and-calls-list))))))))

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
  ;; :returns (names string-or-symbol-listp)
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
