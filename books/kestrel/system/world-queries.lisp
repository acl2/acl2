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

(local (set-default-parents world-queries))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities to query @(see world)s."
  :long
  "<p>
  These complement the world query utilities
  in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
  </p>")

(define theorem-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the symbol @('sym') names a theorem,
  i.e. it has a @('theorem') property."
  (not (eq t (getpropc sym 'theorem t wrld))))

(define macro-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff the symbol @('sym') names a macro."
  (not (eq t (getpropc sym 'macro-args t wrld))))

(define function-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a function."
  (and (symbolp x) (function-symbolp x wrld)))

(define theorem-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a theorem."
  (and (symbolp x) (theorem-symbolp x wrld)))

(define macro-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a macro."
  (and (symbolp x) (macro-symbolp x wrld)))

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

(define definedp ((fn (function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short
  "True iff the function @('fn') is defined,
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
  (not (eq t (getpropc fn 'unnormalized-body t wrld))))

(define guard-verified-p ((fn/thm (or (function-namep fn/thm wrld)
                                      (theorem-namep fn/thm wrld)))
                          (wrld plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable function-namep theorem-namep)))
  :short
  "True iff the function or theorem @('fn/thm') is @(tsee guard)-verified."
  (eq (symbol-class fn/thm wrld) :common-lisp-compliant))

(define non-executablep ((fn (and (function-namep fn wrld)
                                  (definedp fn wrld)))
                         (wrld plist-worldp))
  ;; :returns (result (member result '(t nil :program)))
  :guard-hints (("Goal" :in-theory (enable function-namep)))
  :short "The @(tsee non-executable) status of the defined function @('fn')."
  (getpropc fn 'non-executablep nil wrld))

(define unwrapped-nonexec-body ((fn (and (function-namep fn wrld)
                                         (non-executablep fn wrld)))
                                (wrld plist-worldp))
  ;; :returns (unwrapped-body pseudo-termp)
  :verify-guards nil
  :short
  "Body of a non-executable function,
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

(define no-stobjs-p ((fn (function-namep fn wrld)) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short
  "True iff the function @('fn') has no input or output @(see stobj)s."
  :long
  "<p>
  The guard condition that @('fn') is not in @('*stobjs-out-invalid*')
  is copied from @('stobjs-out').
  </p>"
  (and (all-nils (stobjs-in fn wrld))
       (all-nils (stobjs-out fn wrld))))

(define measure ((fn (and (function-namep fn wrld)
                          (logicp fn wrld)
                          (recursivep fn nil wrld)))
                 (wrld plist-worldp))
  ;; :returns (measure pseudo-termp)
  :verify-guards nil
  :short "Measure expression of a logic-mode recursive function."
  :long "<p>See @(see xargs) for a discussion of the @(':measure') keyword.</p>"
  (access justification (getpropc fn 'justification nil wrld) :measure))

(define measured-subset ((fn (and (function-namep fn wrld)
                                  (logicp fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  ;; :returns (measured-subset symbol-listp)
  :verify-guards nil
  :short
  "Subset of the formal arguments of the recursive function @('fn')
  that occur in its @(see measure) expression."
  (access justification (getpropc fn 'justification nil wrld) :subset))

(define well-founded-relation ((fn (and (function-namep fn wrld)
                                        (logicp fn wrld)
                                        (recursivep fn nil wrld)))
                               (wrld plist-worldp))
  ;; :returns (well-founded-relation symbolp)
  :verify-guards nil
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>See @(see well-founded-relation-rule)
  for a discussion of well-founded relations in ACL2,
  including the @(':well-founded-relation') rule class.</p>"
  (access justification (getpropc fn 'justification nil wrld) :rel))

(define ruler-extenders ((fn (and (function-namep fn wrld)
                                  (logicp fn wrld)
                                  (recursivep fn nil wrld)))
                         (wrld plist-worldp))
  ;; :returns (ruler-extenders (or (symbol-listp ruler-extenders)
  ;;                               (equal ruler-extenders :all)))
  :verify-guards nil
  :short
  "Ruler-extenders of a logic-mode recursive function
  (see @(see rulers) for background)."
  (access justification (getpropc fn 'justification nil wrld) :ruler-extenders))

(define macro-required-args ((mac (macro-namep mac wrld)) (wrld plist-worldp))
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
  (let ((all-args (macro-args mac wrld)))
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

(define fundef-disabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the definition of the function @('fn') is disabled."
  (member-equal `(:definition ,fn) (disabledp fn)))

(define fundef-enabledp ((fn (function-namep fn (w state))) state)
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short "True iff the definition of the function @('fn') is enabled."
  (not (fundef-disabledp fn state)))

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

(define included-books ((wrld plist-worldp))
  ;; :returns (result string-listp)
  :verify-guards nil
  :short
  "List of full pathnames of all books currently included
  (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist wrld)))

(define induction-machine ((fn (and (function-namep fn wrld)
                                    (logicp fn wrld)
                                    (eql 1 (len (recursivep fn nil wrld)))))
                           (wrld plist-worldp))
  ;; :returns (machine (pseudo-induction-machinep fn machine))
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
  :short
  "Recognize @('nil')-terminated lists of
  well-formed @('tests-and-call') records."
  :true-listp t
  :elementp-of-nil nil)

(define recursive-calls ((fn (and (function-namep fn wrld)
                                  (logicp fn wrld)
                                  (eql 1 (len (recursivep fn nil wrld)))))
                         (wrld plist-worldp))
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
  (recursive-calls-aux2 (induction-machine fn wrld))

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

(define defchoosep ((fn (function-namep fn wrld)) (wrld plist-worldp))
  ;; :returns (axiom pseudo-termp)
  :short
  "Check if the function @('fn') was introduced via @(tsee defchoose),
  returning the function's constraining axiom if the check succeeds."
  :long
  "<p>
  A function introduced via @(tsee defchoose) is recognizable
  by the presence of the @('defchoose-axiom') property,
  which is the axiom that constrains the function.
  </p>"
  (getpropc fn 'defchoose-axiom nil wrld)
  :guard-hints (("Goal" :in-theory (enable function-namep))))

(define defchoose-bound-vars ((fn (and (function-namep fn wrld)
                                       (defchoosep fn wrld)))
                              (wrld plist-worldp))
  :returns (bound-vars symbol-listp)
  :prepwork ((program))
  :short
  "Bound variables of the function @('fn') introduced via @(tsee defchoose)."
  :long
  "<p>
  The bound variables are in the third element of the @(tsee defchoose) event,
  which is either a single bound variable
  or a non-empty list of bound variables.
  </p>"
  (let* ((event (get-event fn wrld))
         (bound-var/bound-vars (third event)))
    (if (symbolp bound-var/bound-vars)
        (list bound-var/bound-vars)
      bound-var/bound-vars)))

(define defchoose-strengthen ((fn (and (function-namep fn wrld)
                                       (defchoosep fn wrld)))
                              (wrld plist-worldp))
  :returns (t/nil booleanp)
  :prepwork ((program))
  :short
  "Value of the @(':strengthen') option
  of the function @('fn') introduced via @(tsee defchoose)."
  :long
  "<p>
  If explicitly supplied, the value of the @(':strengthen') option
  is the last element of the @(tsee defchoose) event,
  which consists of seven element in this case.
  If not explicitly supplied,
  the value of the @(':strengthen') option is @('nil'),
  and the @(tsee defchoose) event consists of five elements only.
  </p>"
  (let ((event (get-event fn wrld)))
    (if (eql (len event) 5)
        nil
      (car (last event)))))

(define defchoose-untrans-body ((fn (and (function-namep fn wrld)
                                         (defchoosep fn wrld)))
                                (wrld plist-worldp))
  :prepwork ((program))
  :short
  "Body of the function @('fn') introduced via @(tsee defchoose),
  in <see topic='@(url term)'>untranslated form</see>."
  :long
  "<p>
  The untranslated body, as supplied by the user,
  is the fifth element of the @(tsee defchoose) event.
  </p>"
  (fifth (get-event fn wrld)))

(define defchoose-body ((fn (and (function-namep fn wrld)
                                 (defchoosep fn wrld)))
                        (wrld plist-worldp))
  :returns (body pseudo-termp)
  :prepwork ((program))
  :short
  "Body of the function @('fn') introduced via @(tsee defchoose),
  in <see topic='@(url term)'>translated form</see>."
  :long
  "<p>
  The body @('body') is extracted from the constraining axiom of @('fn'),
  which has one of the following forms
  (see @('defchoose-constraint') in the ACL2 source code):
  </p>
  <ul>
    <li>
    @('(implies body ...)'),
    if @(':strengthen') is @('nil')
    and @('fn') has one bound variable.
    </li>
    <li>
    @('(if ... (implies body ...) nil)'),
    if @('strengthen') is @('nil')
    and @('fn') has more than one bound variable.
    </li>
    <li>
    @('(if (implies body ...) ... nil)'),
    if @(':strengthen') is @('t')
    and @('fn') has one bound variable.
    </li>
    <li>
    @('(if (if ... (implies body ...) nil) ... nil)'),
    if @('strengthen') is @('t')
    and @('fn') has more than one bound variable.
    </li>
  </ul>"
  (b* ((axiom (defchoosep fn wrld))
       (strengthen (defchoose-strengthen fn wrld))
       (bound-vars (defchoose-bound-vars fn wrld))
       (one-bound-var (eql (len bound-vars) 1)))
    (if strengthen
        (if one-bound-var
            (second (second axiom))
          (second (third (second axiom))))
      (if one-bound-var
          (second axiom)
        (second (third axiom))))))
