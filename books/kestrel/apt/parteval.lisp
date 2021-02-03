; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-list-has-no-duplicates" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-untranslated-term" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/ibody" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)
(include-book "kestrel/utilities/directed-untranslate" :dir :system)
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "std/alists/remove-assocs" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")
(include-book "utilities/untranslate-specifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 parteval

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old'),
   @('static'),
   @('new-name'),
   @('new-enable'),
   @('thm-name'),
   @('thm-enable'),
   @('verify-guards'),
   @('untranslate'),
   @('print'), and
   @('show-only')
   are the homonymous inputs to @(tsee parteval),
   before being processed.
   These parameters have no types because they may be any values."

  "@('old$'),
   @('static$'),
   @('new-name$'),
   @('new-enable$'),
   @('thm-name$'),
   @('thm-enable$'),
   @('verify-guards$'),
   @('untranslate$'),
   @('print$'), and
   @('show-only$')
   are the results of processing
   the homonymous inputs (without the @('$')) to @(tsee parteval).
   Some are identical to the corresponding inputs,
   but they have types implied by their successful validation,
   performed when they are processed."

  "@('y1...ym') is the list of static formals @('(y1 ... ym)')."

  "@('yj...ym') is a suffix of @('y1...ym')."

  "@('new-formals') are the formal parameters of the new function."

  "@('case') is 1, 2, or 3, corresponding to the three forms of @('old')
   described in the reference documentation."

  "@('call') is the call to @(tsee restrict) supplied by the user."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing parteval)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-process-old (old verify-guards ctx state)
  :returns (mv erp
               (old$ symbolp "The name of the target function
                              of the transformation,
                              denoted by the @('old') input.")
               state)
  :verify-guards nil
  :short "Process the @('old') input."
  (b* (((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-is-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-is-defined$ old$ description t nil))
       ((er &) (ensure-function-number-of-results$ old$ 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-is-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value :this-is-irrelevant))))
    (value old$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-process-static-terms
  ((cj...cm true-listp "List @('(c1 ... cm)') initially,
                        then a tail of that in the recursive calls.")
   (yj...ym symbol-listp)
   (old$ symbolp)
   (verify-guards$ booleanp)
   ctx
   state)
  :guard (equal (len cj...cm) (len yj...ym))
  :mode :program
  :returns (mv erp
               (cj...cm$ "The @(tsee pseudo-term-listp) list
                          of terms @('cj...cm'), in translated form.")
               state)
  :short "Process the @('c1'), ..., @('cm') parts of the @('static') input."
  (b* (((when (endp cj...cm)) (value nil))
       (yj (car yj...ym))
       (cj (car cj...cm))
       (description
        (msg "The term ~x0 assigned to the static parameter ~x1" cj yj))
       ((er (list cj$ stobjs-out))
        (ensure-value-is-untranslated-term$ cj description t nil))
       ((er &) (ensure-term-ground$ cj$ description t nil))
       ((er &) (ensure-term-logic-mode$ cj$ description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if verify-guards$
                   (ensure-term-guard-verified-exec-fns$
                    cj$
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old$ (msg-downcase-first description))
                    t nil)
                 (value :this-is-irrelevant)))
       ((er &) (ensure-term-does-not-call$ cj$ old$ description t nil))
       (cj+1...cm (cdr cj...cm))
       (yj+1...ym (cdr yj...ym))
       ((er cj+1...cm$) (parteval-process-static-terms
                         cj+1...cm yj+1...ym old$ verify-guards$ ctx state)))
    (value (cons cj$ cj+1...cm$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-process-static (static
                                 (old$ symbolp)
                                 (verify-guards$ booleanp)
                                 ctx
                                 state)
  :returns (mv erp
               (static$ "A @(tsee symbol-alistp)
                         from @('y1'), ..., @('ym')
                         to the translated @('c1'), ..., @('cm').")
               state)
  :mode :program
  :short "Process the @('static') input."
  (b* (((er &) (ensure-doublet-list$ static "The second input" t nil))
       (alist (doublets-to-alist static))
       (y1...ym (strip-cars alist))
       (description
        (msg "The list ~x0 of static parameters" y1...ym))
       ((when (null y1...ym))
        (er-soft+ ctx t nil "~@0 must not be empty." description))
       ((er &) (ensure-list-has-no-duplicates$ y1...ym description t nil))
       ((er &) (ensure-value-is-symbol-list$ y1...ym description t nil))
       ((er &) (ensure-list-subset$ y1...ym (formals old$ (w state))
                                    description t nil))
       (c1...cm (strip-cdrs alist))
       ((er c1...cm$) (parteval-process-static-terms c1...cm y1...ym
                                                     old$ verify-guards$
                                                     ctx state))
       (static$ (pairlis$ y1...ym c1...cm$)))
    (value static$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-process-thm-name (thm-name
                                   (old$ symbolp)
                                   (new-name$ symbolp)
                                   ctx
                                   state)
  :returns (mv erp
               (thm-name$ "A @(tsee symbolp)
                           to use for the theorem
                           that relates the old and new functions.")
               state)
  :mode :program
  :short "Process the @(':thm-name') input."
  (b* (((er &) (ensure-value-is-symbol$ thm-name "The :THM-NAME input" t nil))
       (name (if (eq thm-name :auto)
                 (make-paired-name old$ new-name$ 2 (w state))
               thm-name))
       (description (msg "The name ~x0 of the theorem ~
                          that relates the target function ~x1 ~
                          to the new function ~x2, ~
                          ~@3,"
                         name old$ new-name$
                         (if (eq thm-name :auto)
                             "automatically generated ~
                              since the :THM-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :THM-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil))
       ((er &) (ensure-symbol-different$
                name new-name$
                (msg "the name ~x0 of the new function ~
                      (determined by the :NEW-NAME input)." new-name$)
                description
                t nil)))
    (value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-unchanging-static-in-rec-args-p
  ((rec-args pseudo-term-listp "Arguments of a recursive call of @('old').")
   (old$ symbolp)
   (yj...ym symbol-listp)
   (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Check if the static parameters do not change
          in the arguments of a recursive call of @('old')."
  :long
  (xdoc::topstring-p
   "This is used to check if a recursive @('old') has
    the case 2 form described in the reference documentation.")
  (or (endp yj...ym)
      (b* ((yj (car yj...ym))
           (pos (position-eq yj (formals old$ wrld))))
        (and (eq yj (nth pos rec-args))
             (parteval-unchanging-static-in-rec-args-p rec-args
                                                       old$
                                                       (cdr yj...ym)
                                                       wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-unchanging-static-in-rec-calls-p
  ((rec-calls-with-tests pseudo-tests-and-call-listp
                         "Recursive calls of @('old').")
   (old$ symbolp)
   (y1...ym symbol-listp)
   (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Check if the static parameters do not change
          in the arguments of the recursive calls of @('old')."
  :long
  (xdoc::topstring-p
   "This is used to check if a recursive @('old') has
    the case 2 form described in the reference documentation.")
  (or (endp rec-calls-with-tests)
      (b* ((rec-call-with-tests (car rec-calls-with-tests))
           (rec-call (access tests-and-call rec-call-with-tests :call))
           (rec-args (fargs rec-call)))
        (and (parteval-unchanging-static-in-rec-args-p
              rec-args old$ y1...ym wrld)
             (parteval-unchanging-static-in-rec-calls-p
              (cdr rec-calls-with-tests) old$ y1...ym wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-case-of-old ((old$ symbolp)
                              (static$ symbol-alistp)
                              (wrld plist-worldp))
  :returns (case "1, 2, or 3.")
  :mode :program
  :short "Classify @('old') into one of the three cases
          described in the reference documentation."
  (b* (((when (not (irecursivep old$ wrld))) 1)
       ((when (member-eq old$ (all-ffn-symbs
                               (termination-theorem old$ wrld) nil))) 3)
       ((when (parteval-unchanging-static-in-rec-calls-p
               (recursive-calls old$ wrld) old$ (strip-cars static$) wrld)) 2))
    3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-process-inputs (old
                                 static
                                 new-name
                                 new-enable
                                 thm-name
                                 thm-enable
                                 verify-guards
                                 untranslate
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    static$
                                    new-name$
                                    new-enable$
                                    thm-name$
                                    verify-guards$
                                    case
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         symbol-alistp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         natp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  :long
  (xdoc::topstring-p
   "The inputs are processed
    in the order in which they appear in the documentation,
    except that @(':verify-guards') is processed just before @('static')
    because the result of processing @(':verify-guards')
    is used to process @('static').
    @('old') is processed before @(':verify-guards')
    because the result of processing @('old')
    is used to process @(':verify-guards').
    @(':verify-guards') is also used to process @('old'),
    but it is only tested for equality with @('t')
    (see @(tsee parteval-process-old)).")
  (b* ((wrld (w state))
       ((er old$) (parteval-process-old old verify-guards ctx state))
       ((er verify-guards$) (process-input-verify-guards verify-guards
                                                         old$
                                                         ctx
                                                         state))
       ((er static$) (parteval-process-static
                      static old$ verify-guards$ ctx state))
       (case (parteval-case-of-old old$ static$ wrld))
       ((er (list new-name$ names-to-avoid))
        (process-input-new-name new-name old$ nil ctx state))
       ((er new-enable$) (process-input-new-enable new-enable old$ ctx state))
       ((er thm-name$) (parteval-process-thm-name
                        thm-name old$ new-name$ ctx state))
       (names-to-avoid (cons thm-name$ names-to-avoid))
       ((er &) (ensure-value-is-boolean$ thm-enable
                                         "The :THM-ENABLE input" t nil))
       ((when (and (= case 3)
                   new-enable$
                   thm-enable))
        (er-soft+ ctx t nil
                  "Since (i) the target function ~x0 ~
                   has the form of case 3 in :DOC PARTEVAL, ~
                   (ii) either the :NEW-ENABLE input is T, ~
                   or it is (perhaps by default) :AUTO ~
                   and (iii) the target function is enabled, ~
                   the :THM-ENABLE input cannot be T."
                  old$))
       ((er &) (ensure-is-untranslate-specifier$ untranslate
                                                 "The :UNTRANSLATE input"
                                                 t nil))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 static$
                 new-name$
                 new-enable$
                 thm-name$
                 verify-guards$
                 case
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation parteval
                                    :some-local-nonlocal-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-transform-rec-args
  ((rec-args pseudo-term-listp "Arguments of a recursive call of @('old').")
   (old$ symbolp)
   (yj...ym symbol-listp)
   (wrld plist-worldp))
  :returns (new-rec-args "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :short "Transform the arguments of a recursive call of @('old')."
  :long
  (xdoc::topstring-p
   "This applies to case 2 in the reference documentation.
    Each call of @('old') is replaced with
    a call of @('new') with the static arguments removed.
    This code performs the removal of these arguments.")
  (cond ((endp yj...ym) rec-args)
        (t (b* ((yj (car yj...ym))
                (pos (position-eq yj (formals old$ wrld)))
                (rec-args (append (take pos rec-args)
                                  (nthcdr (1+ pos) rec-args))))
             (parteval-transform-rec-args rec-args old$ (cdr yj...ym) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parteval-transform-rec-calls-in-term
  :short "Transform the recursive calls in the body of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to case 2 in the reference documentation.
     Each call of @('old') is replaced with
     a call of @('new') with the static arguments removed.
     This code recursively processes the terms in the body of @('old')."))
  :verify-guards nil

  (define parteval-transform-rec-calls-in-term ((body-term pseudo-termp)
                                                (old$ symbolp)
                                                (new-name$ symbolp)
                                                (y1...ym symbol-listp)
                                                (wrld plist-worldp))
    :returns new-body-term ; PSEUDO-TERMP
    (cond ((variablep body-term) body-term)
          ((fquotep body-term) body-term)
          (t (b* ((fn/lambda (ffn-symb body-term))
                  (args (fargs body-term))
                  (new-args (parteval-transform-rec-calls-in-terms args
                                                                   old$
                                                                   new-name$
                                                                   y1...ym
                                                                   wrld)))
               (cond ((eq fn/lambda old$)
                      (fcons-term new-name$
                                  (parteval-transform-rec-args
                                   new-args old$ y1...ym wrld)))
                     ((symbolp fn/lambda) (fcons-term fn/lambda new-args))
                     (t (make-lambda (lambda-formals fn/lambda)
                                     (parteval-transform-rec-calls-in-term
                                      (lambda-body fn/lambda)
                                      old$ new-name$ y1...ym wrld))))))))

  (define parteval-transform-rec-calls-in-terms ((body-terms pseudo-term-listp)
                                                 (old$ symbolp)
                                                 (new-name$ symbolp)
                                                 (y1...ym symbol-listp)
                                                 (wrld plist-worldp))
    :returns new-body-term ; PSEUDO-TERM-LISTP
    (cond ((endp body-terms) nil)
          (t (cons (parteval-transform-rec-calls-in-term
                    (car body-terms) old$ new-name$ y1...ym wrld)
                   (parteval-transform-rec-calls-in-terms
                    (cdr body-terms) old$ new-name$ y1...ym wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-new-fn-body ((old$ symbolp)
                                  (static$ symbol-alistp)
                                  (new-name$ symbolp)
                                  (case (member case '(1 2 3)))
                                  (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the body of the new function."
  :long
  (xdoc::topstring
   (xdoc::p
    "In case 1, we replace each @('yj') with @('cj') in the body of @('old').")
   (xdoc::p
    "In case 2, we replace each recursive call of @('old')
     with a call of @('new') with the static arguments removed,
     and then we replace each @('yj') with @('cj').")
   (xdoc::p
    "In case 3, we call @('old') with each @('yj') replaced with @('cj')."))
  (case case
    (1 (fsublis-var static$ (ubody old$ wrld)))
    (2 (b* ((body (ubody old$ wrld))
            (body (parteval-transform-rec-calls-in-term body
                                                        old$
                                                        new-name$
                                                        (strip-cars static$)
                                                        wrld))
            (body (fsublis-var static$ body)))
         body))
    (3 (fsublis-var static$ `(,old$ ,@(formals old$ wrld))))
    (t (impossible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-new-fn ((old$ symbolp)
                             (static$ symbol-alistp)
                             (new-name$ symbolp)
                             (new-enable$ booleanp)
                             (verify-guards$ booleanp)
                             (untranslate$ untranslate-specifier-p)
                             (case (member case '(1 2 3)))
                             (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp).")
               (new-formals "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the new function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the new function is determined by
     whether the new function must be enabled or not.")
   (xdoc::p
    "The parameters of the new function are
     the dynamic parameters of the old function,
     obtained by removing the static parameters from the old function.
     The parameters of the new function are returned as one of the results.")
   (xdoc::p
    "The new function is recursive only in case 2.
     The generated termination hints are
     as in the design notes and @('parteval-template.lisp').")
   (xdoc::p
    "The guard of the new function is obtained
     by replacing each @('yj') with @('cj')
     in the guard of the old function.")
   (xdoc::p
    "Guard verification is deferred, because in case 2
     its proof depends on the @('old-to-new') theorem.
     It is deferred also for cases 1 and 3, even if that is not necessary,
     for greater simplicity."))
  (b* ((macro (function-intro-macro new-enable$ nil))
       (formals (set-difference-eq (formals old$ wrld) (strip-cars static$)))
       (body (parteval-gen-new-fn-body old$ static$ new-name$ case wrld))
       (body (case untranslate$
               (:nice
                (directed-untranslate
                 (ibody old$ wrld) (ubody old$ wrld) body nil nil wrld))
               (:nice-expanded
                (directed-untranslate-no-lets
                 (ibody old$ wrld) (ubody old$ wrld) body nil nil wrld))
               (nil body)
               (t (untranslate body nil wrld))))
       (wfrel? (and (= case 2)
                    (well-founded-relation old$ wrld)))
       (measure? (and (= case 2)
                      (untranslate (measure old$ wrld) nil wrld)))
       (termination-hints? (and (= case 2)
                                `(("Goal"
                                   :in-theory nil
                                   :use (:instance
                                         (:termination-theorem ,old$)
                                         :extra-bindings-ok
                                         ,@(alist-to-doublets static$))))))
       (guard (fsublis-var static$ (uguard old$ wrld)))
       (guard (untranslate guard nil wrld))
       (local-event
        `(local
          (,macro ,new-name$ (,@formals)
                  (declare (xargs
                            ,@(and (= case 2)
                                   (list :well-founded-relation wfrel?
                                         :measure measure?
                                         :hints termination-hints?
                                         :ruler-extenders :all))
                            :guard ,guard
                            :verify-guards nil))
                  ,body)))
       (exported-event
        `(,macro ,new-name$ (,@formals)
                 (declare (xargs
                           ,@(and (= case 2)
                                  (list :well-founded-relation wfrel?
                                        :measure measure?
                                        :ruler-extenders :all))
                           :guard ,guard
                           :verify-guards ,verify-guards$))
                 ,body)))
    (mv local-event exported-event formals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-static-equalities ((static$ symbol-alistp))
  :returns (equalities "A @(tsee pseudo-term-listp).")
  :short "Generate the equalities whose conjunction forms
          the antecedent of the theorem relating old and new function."
  :long
  (xdoc::topstring-p
   "Each equality has the form @('(equal yj cj)').")
  (b* (((when (endp static$)) nil)
       ((cons arg$ static$) static$)
       (equality `(equal ,(car arg$) ,(cdr arg$)))
       (equalities (parteval-gen-static-equalities static$)))
    (cons equality equalities)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-old-to-new-thm ((old$ symbolp)
                                     (static$ symbol-alistp)
                                     (new-name$ symbolp)
                                     (thm-name$ symbolp)
                                     (thm-enable$ booleanp)
                                     (case (member case '(1 2 3)))
                                     (new-formals symbol-listp)
                                     (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the old and new function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the theorem is determined by
     whether the theorem must be enabled or not.")
   (xdoc::p
    "The theorem is an implication,
     whose antecedent is @('(and (equal y1 c1) ... (equal ym cm))')
     and whose consequent is (using the notation in the documentation)
     @('(equal (old x1 ... xn y1 ... ym) (new x1 ... xn))').")
   (xdoc::p
    "The hints follow the proof
     in the design notes and in @('parteval-template.lisp')."))
  (b* ((equalities (parteval-gen-static-equalities static$))
       (antecedent (conjoin equalities))
       (consequent `(equal (,old$ ,@(formals old$ wrld))
                           (,new-name$ ,@new-formals)))
       (formula (implicate antecedent consequent))
       (formula (untranslate formula t wrld))
       (hints (case case
                (1 `(("Goal" :in-theory '(,old$ ,new-name$))))
                (2 `(("Goal"
                      :in-theory '(,old$ ,new-name$)
                      :induct (,new-name$ ,@new-formals))))
                (3 `(("Goal" :in-theory '(,new-name$))))
                (t (impossible)))))
    (evmac-generate-defthm thm-name$
                           :formula formula
                           :hints hints
                           :enable thm-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-old-to-new-thm-instances
  ((rec-calls-with-tests pseudo-tests-and-call-listp
                         "Recursive calls of @('old').")
   (old$ symbolp)
   (static$ symbol-alistp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances pseudo-event-form-listp)
  :verify-guards nil
  :short "Generate an instance of the @('old-to-new') theorem
          for each recursive call of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the guard verification proof of @('new') in case 2.
     The design notes and @('parteval-template.lisp') show that, in case 2,
     the @('old-to-new') theorem must be instantiated
     by replacing the dynamic formal arguments
     with the corresponding actual arguments in the recursive call.
     This must be done for all recursive calls.
     In addition, the static parameters @('yj'),
     which in case 2 are unchanged in all the recursive calls,
     must be replaced with the constant terms @('cj').")
   (xdoc::p
    "This code goes through the recursive calls of old
     and generates the lemma instances as just described.
     For each such call,
     first we create an alist from all the formal parameters of @('old')
     to the arguments in the recursive calls
     with each @('yj') replaced with @('cj');
     then we remove the static parameters from that alist
     (which that alist maps all to themselves),
     and we join the result with @('static$'),
     obtaining the whole instantiation, in alist form."))
  (b* (((when (endp rec-calls-with-tests)) nil)
       (rec-call-with-tests (car rec-calls-with-tests))
       (rec-call (access tests-and-call rec-call-with-tests :call))
       (rec-args (fargs rec-call))
       (rec-args (fsublis-var static$ rec-args))
       (all-alist (pairlis$ (formals old$ wrld) rec-args))
       (dynamic-alist (remove-assocs-eq (strip-cars static$) all-alist))
       (final-alist (append dynamic-alist static$))
       (lemma-instance `(:instance ,thm-name$
                         :extra-bindings-ok
                         ,@(alist-to-doublets final-alist)))
       (lemma-instances (parteval-gen-old-to-new-thm-instances
                         (cdr rec-calls-with-tests)
                         old$ static$ thm-name$ wrld)))
    (cons lemma-instance lemma-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-new-fn-verify-guards ((old$ symbolp)
                                           (static$ symbol-alistp)
                                           (new-name$ symbolp)
                                           (thm-name$ symbolp)
                                           (case (member case '(1 2 3)))
                                           (wrld plist-worldp))
  :returns (local-event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the event to verify the guards of the new function."
  :long
  (xdoc::topstring-p
   "We instruct ACL2 not to simplify the guard conjecture,
    and accordingly to use the unsimplified guard theorem of @('old').
    This increases the robustness of the generated proof.")
  (b* ((guard-thm-instance `(:instance
                             (:guard-theorem ,old$ nil)
                             :extra-bindings-ok
                             ,@(alist-to-doublets static$)))
       (old-to-new-instances?
        (and (= case 2)
             (parteval-gen-old-to-new-thm-instances
              (recursive-calls old$ wrld) old$ static$ thm-name$ wrld)))
       (hints `(("Goal"
                 :in-theory nil
                 :use ,(cons guard-thm-instance old-to-new-instances?)))))
    `(local (verify-guards ,new-name$
              :hints ,hints
              :guard-simplify nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-gen-everything ((old$ symbolp)
                                 (static$ symbol-alistp)
                                 (new-name$ symbolp)
                                 (new-enable$ booleanp)
                                 (thm-name$ symbolp)
                                 (thm-enable$ booleanp)
                                 (verify-guards$ booleanp)
                                 (untranslate$ untranslate-specifier-p)
                                 (print$ evmac-input-print-p)
                                 (show-only$ booleanp)
                                 (case (member case '(1 2 3)))
                                 (call pseudo-event-formp)
                                 (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the top-level event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a @(tsee progn) that consists of
     the expansion of @(tsee parteval) (the @(tsee encapsulate)),
     followed by an event to extend the transformation table,
     optionally followed by events to print the exported events
     (if specified by the @(':print') input).
     The @(tsee progn) ends with @(':invisible')
     to avoid printing a return value.")
   (xdoc::p
    "The @(tsee encapsulate) starts with some implicitly local events to
     ensure logic mode and
     avoid errors due to ignored or irrelevant formals
     in the generated function.
     Other implicitly local events remove any default and override hints,
     to prevent such hints from sabotaging the generated proofs.")
   (xdoc::p
    "The @(tsee encapsulate) is stored into the transformation table,
     associated to the call to the transformation.
     Thus, the table event and (if present) the screen output events
     (which are in the @(tsee progn) but not in the @(tsee encapsulate))
     are not stored into the transformation table,
     because they carry no additional information,
     and because otherwise the table event would have to contain itself.")
   (xdoc::p
    "If @(':print') is @(':all'),
     the @(tsee encapsulate) is wrapped to show ACL2's output
     in response to the submitted events.
     If @(':print') is @(':result') or @(':info') or @(':all'),
     the @(tsee progn) includes events to print
     the exported events on the screen without hints;
     these are the same event forms
     that are introduced non-locally and redundantly in the @(tsee encapsulate).
     If @(':print') is @(':info') or @(':all'),
     a blank line is printed just before the result, for visual separation;
     if @(':print') is @(':result'),
     the blank line is not printed.")
   (xdoc::p
    "If @(':show-only') is @('t'),
     the @(tsee encapsulate) is just printed on the screen
     and not returned as part of the event to submit,
     which in this case is just an @(':invisible') form.
     In this case, if @(':print') is @(':info') or @(':all'),
     a blank line is printed just before the @(tsee encapsulate),
     for visual separation."))
  (b* (((mv new-fn-local-event
            new-fn-exported-event
            new-formals) (parteval-gen-new-fn old$
                                              static$
                                              new-name$
                                              new-enable$
                                              verify-guards$
                                              untranslate$
                                              case
                                              wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event) (parteval-gen-old-to-new-thm
                                            old$
                                            static$
                                            new-name$
                                            thm-name$
                                            thm-enable$
                                            case
                                            new-formals
                                            wrld))
       (new-fn-verify-guards-event? (and verify-guards$
                                         (list
                                          (parteval-gen-new-fn-verify-guards
                                           old$
                                           static$
                                           new-name$
                                           thm-name$
                                           case
                                           wrld))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             (evmac-prepare-proofs)
                             ,new-fn-local-event
                             ,old-to-new-thm-local-event
                             ,@new-fn-verify-guards-event?
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print$ '(:result :info :all))
                      `(,@(and (member-eq print$ '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-fn-exported-event)
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-fn (old
                     static
                     new-name
                     new-enable
                     thm-name
                     thm-enable
                     verify-guards
                     untranslate
                     print
                     show-only
                     (call pseudo-event-formp)
                     ctx
                     state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (parteval-implementation)
  :short "Check redundancy,
          process the inputs, and
          generate the event to submit."
  :long
  (xdoc::topstring-p
   "If this call to the transformation is redundant,
    a message to that effect is printed on the screen.
    If the transformation is redundant and @(':show-only') is @('t'),
    the @(tsee encapsulate), retrieved from the table, is shown on the screen.")
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old$
                  static$
                  new-name$
                  new-enable$
                  thm-name$
                  verify-guards$
                  case
                  &)) ; NAMES-TO-AVOID
        (parteval-process-inputs old
                                 static
                                 new-name
                                 new-enable
                                 thm-name
                                 thm-enable
                                 verify-guards
                                 untranslate
                                 print
                                 show-only
                                 ctx
                                 state))
       (event (parteval-gen-everything old$
                                       static$
                                       new-name$
                                       new-enable$
                                       thm-name$
                                       thm-enable
                                       verify-guards$
                                       untranslate
                                       print
                                       show-only
                                       case
                                       call
                                       (w state))))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection parteval-macro-definition
  :parents (parteval-implementation)
  :short "Definition of the @(tsee parteval) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee parteval-fn).")
   (xdoc::@def "parteval"))
  (defmacro parteval (&whole
                      call
                      ;; mandatory inputs:
                      old
                      static
                      ;; optional inputs:
                      &key
                      (new-name ':auto)
                      (new-enable ':auto)
                      (thm-name ':auto)
                      (thm-enable 't)
                      (verify-guards ':auto)
                      (untranslate ':nice)
                      (print ':result)
                      (show-only 'nil))
    `(make-event-terse (parteval-fn ',old
                                    ',static
                                    ',new-name
                                    ',new-enable
                                    ',thm-name
                                    ',thm-enable
                                    ',verify-guards
                                    ',untranslate
                                    ',print
                                    ',show-only
                                    ',call
                                    (cons 'parteval ',old)
                                    state)
                       :suppress-errors ,(not print))))
