; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "defun-sk2")
(include-book "defund-sk2")

(include-book "kestrel/error-checking/ensure-list-has-no-duplicates" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/fresh-namep" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defequal

 :items

 ((xdoc::evmac-topic-implementation-item-input "name")

  (xdoc::evmac-topic-implementation-item-input "left")

  (xdoc::evmac-topic-implementation-item-input "right")

  (xdoc::evmac-topic-implementation-item-input "vars")

  "@('n') is the arity of @('left') and @('right'),
   as described in the user documentation."

  "@('x1...xn') is the list of variable symbols @('x1'), ..., @('xn')
   described in the user documentation."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defequal-table
  :parents (defequal-implementation)
  :short "Table that records successful @(tsee defequal) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used just to handle redundancy fow now.")
   (xdoc::p
    "The table uses @(tsee defequal) calls as keys,
     which it associates to their expansions (@(tsee encapsulate)) as values.
     The calls are stripped of the @(':print') and @(':show-only') options."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table defequal-table nil nil
  :guard (and (pseudo-event-formp acl2::key)
              (pseudo-event-formp acl2::val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-trim-call ((call pseudo-event-formp))
  :returns (trimmed-call pseudo-event-formp :hyp :guard)
  :short "Trim a @(tsee defequal) call
          by removing the @(':print') and @(':show-only') inputs."
  (cons (car call)
        (defequal-trim-call-args (cdr call)))
  :guard-hints (("Goal" :in-theory (enable pseudo-event-formp)))
  :prepwork
  ((define defequal-trim-call-args ((args true-listp))
     :returns (trimmed-args true-listp)
     (cond ((endp args) nil)
           ((member-eq (car args) '(:print :show-only))
            (defequal-trim-call-args (cddr args)))
           (t (cons (car args) (defequal-trim-call-args (cdr args))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-record-call ((call pseudo-event-formp)
                              (expansion pseudo-event-formp))
  :returns (table-event pseudo-event-formp)
  :short "Table event to record a call of @(tsee defequal)."
  (b* ((call (defequal-trim-call call)))
    `(table defequal-table ',call ',expansion)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-redundant? ((call pseudo-event-formp) (wrld plist-worldp))
  :returns (event? maybe-pseudo-event-formp)
  :short "Check if a call of @(tsee defequal) is redundant,
          returning the associated expansion if it is."
  (b* ((table (table-alist+ 'defequal-table wrld))
       (call (defequal-trim-call call))
       (pair? (assoc-equal call table)))
    (if pair?
        (b* ((expansion (cdr pair?)))
          (if (pseudo-event-formp expansion)
              expansion
            (raise "Internal error: ~
                    the DEFEQUAL table associates the call ~x0 ~
                    with a value ~x1 that is not a pseudo event form."
                   call expansion)))
      nil))
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing defequal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-name (name
                               (names-to-avoid symbol-listp)
                               ctx
                               state)
  :returns (mv erp
               (updated-names-to-avoid "Always @(tsee symbol-listp).")
               state)
  :mode :program
  :short "Process the @('name') input."
  (b* (((er &) (ensure-value-is-symbol$ name "The NAME input" t nil))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$ name
                                            (msg "The NAME input ~x0" name)
                                            'function
                                            names-to-avoid
                                            t
                                            nil)))
    (value names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-left-and-right (left
                                         (left-present booleanp)
                                         right
                                         (right-present booleanp)
                                         verify-guards
                                         ctx
                                         state)
  :returns (mv erp (n natp) state)
  :verify-guards nil
  :short "Process the @(':left') and @(':right') inputs."
  (b* ((wrld (w state))
       ((unless left-present)
        (er-soft+ ctx t 0 "The :LEFT input must be present, but it is not."))
       ((unless right-present)
        (er-soft+ ctx t 0 "The :RIGHT input must be present, but it is not."))
       ((er &) (ensure-value-is-function-name$ left "The :LEFT input" t 0))
       ((er &) (ensure-value-is-function-name$ right "The :RIGHT input" t 0))
       (left-guard (uguard left wrld))
       (right-guard (uguard right wrld))
       (left-arity (arity+ left wrld))
       (right-arity (arity+ right wrld))
       ((unless (= left-arity right-arity))
        (er-soft+ ctx t 0
                  "The function ~x0 specified by the :LEFT input ~
                   and the function ~x1 specified by :RIGHT input ~
                   must have the same arity, but they do not: ~
                   the first has arity ~x2 and the second has arity ~x3."
                  left right left-arity right-arity))
       ((unless (> left-arity 0))
        (er-soft+ ctx t 0
                  "The arity of the functions ~x0 and ~x1 ~
                   specified by the :LEFT and :RIGHT inputs ~
                   must not be zero, but it is zero instead."
                  left right))
       ((when (and (not (funvarp left wrld))
                   (not (sofunp left wrld))
                   (not (funvarp right wrld))
                   (not (sofunp right wrld))))
        (er-soft+ ctx t 0
                  "At least one of the two functions ~x0 and ~x1 ~
                   specified by the :LEFT and :RIGHT inputs ~
                   must be a function variable ~
                   or a second-order function, ~
                   but they are not."
                  left right))
       ((er &)
        (if (eq verify-guards t)
            (b* (((unless (equal left-guard *t*))
                  (er-soft+ ctx t 0
                            "Since the :VERIFY-GUARD input ~
                             is (perhaps by default) T, ~
                             the guard of the function ~x0 ~
                             specified by the :LEFT input ~
                             must be T, but it is ~x1 instead."
                            left left-guard))
                 ((unless (equal right-guard *t*))
                  (er-soft+ ctx t 0
                            "Since the :VERIFY-GUARD input ~
                             is (perhaps by default) T, ~
                             the guard of the function ~x0 ~
                             specified by the :RIGHT input ~
                             must be T, but it is ~x1 instead."
                            right right-guard))
                 ((unless (guard-verified-p+ left wrld))
                  (er-soft+ ctx t 0
                            "Since the :VERIFY-GUARD input ~
                             is (perhaps by default) T, ~
                             the function ~x0 ~
                             specified by the :LEFT input ~
                             must be guard-verified, but it is not."
                            left))
                 ((unless (guard-verified-p+ right wrld))
                  (er-soft+ ctx t 0
                            "Since the :VERIFY-GUARD input ~
                             is (perhaps by default) T, ~
                             the function ~x0 ~
                             specified by the :RIGHT input ~
                             must be guard-verified, but it is not."
                            right)))
              (value nil))
          (value nil))))
    (value left-arity)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-vars (vars
                               (name symbolp)
                               (left symbolp)
                               (right symbolp)
                               (n natp)
                               ctx
                               state)
  :returns (mv erp (x1...xn symbol-listp) state)
  :short "Process the @(':vars') input."
  (if (eq vars :auto)
      (value (defequal-process-vars-aux name n))
    (b* (((er &) (ensure-value-is-symbol-list$ vars "The :VARS input" t nil))
         ((er &) (ensure-list-has-no-duplicates$
                  vars
                  (msg "The list ~x0 of variables specified by the :VARS input"
                       vars)
                  t
                  nil))
         ((unless (= (len vars) n))
          (er-soft+ ctx t nil
                    "The number of variables ~x0 specified by the :VARS input ~
                     must be equal to the arity ~x1 ~
                     of the functions ~x2 and ~x3 ~
                     specified by the :LEFT and :RIGHT inputs, ~
                     but it is ~x4 instead."
                    vars n left right (len vars))))
      (value vars)))

  :prepwork

  ((local (in-theory (enable acl2::ensure-value-is-symbol-list
                             acl2::ensure-list-has-no-duplicates)))

   (define defequal-process-vars-aux ((name symbolp) (n natp))
     :returns (x1...xn symbol-listp)
     (cond ((zp n) nil)
           (t (append (defequal-process-vars-aux name (1- n))
                      (list (packn-pos (list "X" n) name)))))
     :prepwork
     ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-left-to-right-name (left-to-right-name
                                             (name symbolp)
                                             (left symbolp)
                                             (right symbolp)
                                             (names-to-avoid symbol-listp)
                                             ctx
                                             state)
  :returns (mv erp
               (result "A tuple @('(left-to-right updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':left-to-right') input."
  (b* (((er &) (ensure-value-is-symbol$ left-to-right-name
                                        "The :LEFT-TO-RIGHT input"
                                        t
                                        nil))
       (left-to-right (if (eq left-to-right-name :auto)
                          (packn-pos (list left '-to- right) name)
                        left-to-right-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         left-to-right
         (msg "The name ~x0 specified by :LEFT-TO-RIGHT-NAME" left-to-right)
         'function
         names-to-avoid
         t
         nil)))
    (value (list left-to-right names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-right-to-left-name (right-to-left-name
                                             (name symbolp)
                                             (left symbolp)
                                             (right symbolp)
                                             (names-to-avoid symbol-listp)
                                             ctx
                                             state)
  :returns (mv erp
               (result "A tuple @('(right-to-left updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':right-to-left') input."
  (b* (((er &) (ensure-value-is-symbol$ right-to-left-name
                                        "The :RIGHT-TO-LEFT input"
                                        t
                                        nil))
       (right-to-left (if (eq right-to-left-name :auto)
                          (packn-pos (list right '-to- left) name)
                        right-to-left-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         right-to-left
         (msg "The name ~x0 specified by :RIGHT-TO-LEFT-NAME" right-to-left)
         'function
         names-to-avoid
         t
         nil)))
    (value (list right-to-left names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-process-inputs (name
                                 left
                                 (left-present booleanp)
                                 right
                                 (right-present booleanp)
                                 vars
                                 enable
                                 verify-guards
                                 left-to-right-name
                                 left-to-right-enable
                                 right-to-left-name
                                 right-to-left-enable
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A tuple @('(x1...xn
                                    left-to-right
                                    right-to-left
                                    updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbol-listp
                                                    symbol-listp
                                                    symbolp
                                                    symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((names-to-avoid nil)
       ((er names-to-avoid) (defequal-process-name
                              name names-to-avoid ctx state))
       ((er n) (defequal-process-left-and-right
                 left left-present right right-present verify-guards ctx state))
       ((er x1...xn) (defequal-process-vars vars name left right n ctx state))
       ((er &) (ensure-value-is-boolean$ enable
                                         "The :ENABLE input"
                                         t
                                         nil))
       ((er &) (ensure-value-is-boolean$ verify-guards
                                         "The :VERIFY-GUARDS input"
                                         t
                                         nil))
       ((er (list left-to-right names-to-avoid))
        (defequal-process-left-to-right-name
          left-to-right-name name left right names-to-avoid ctx state))
       ((er &) (ensure-value-is-boolean$ left-to-right-enable
                                         "The :LEFT-TO-RIGHT-ENABLE input"
                                         t
                                         nil))
       ((er (list right-to-left names-to-avoid))
        (defequal-process-right-to-left-name
          right-to-left-name name left right names-to-avoid ctx state))
       ((er &) (ensure-value-is-boolean$ right-to-left-enable
                                         "The :RIGHT-TO-LEFT-ENABLE input"
                                         t
                                         nil))
       ((when (and left-to-right-enable
                   right-to-left-enable))
        (er-soft+ ctx t nil
                  "The :LEFT-TO-RIGHT-ENABLE and :RIGHT-TO-LEFT-ENABLE inputs ~
                   are both T; this is disallowed."))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list x1...xn left-to-right right-to-left names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defequal
                                    :some-local-nonlocal-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-gen-equality ((name symbolp)
                               (left symbolp)
                               (right symbolp)
                               (x1...xn symbol-listp)
                               (enable booleanp)
                               (verify-guards booleanp)
                               (left-to-right symbolp)
                               (left-to-right-enable))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the equality function."
  (b* ((macro (if enable 'defun-sk2 'defund-sk2))
       (body `(forall (,@x1...xn)
                      (equal (,left ,@x1...xn)
                             (,right ,@x1...xn))))
       (declare `(declare (xargs :guard t :verify-guards ,verify-guards)))
       (options `(:rewrite :direct
                  :thm-name ,left-to-right
                  ,@(and (not enable)
                         left-to-right-enable
                         (list :thm-enable t))))
       (local-event
        `(local
          (,macro ,name ()
                  ,declare
                  ,@(and verify-guards
                         '((declare
                            (xargs :guard-hints (("Goal" :in-theory nil))))))
                  ,body
                  ,@options)))
       (exported-event
        `(,macro ,name ()
                 ,declare
                 ,body
                 ,@options)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-gen-right-to-left ((right-to-left symbolp)
                                    (right-to-left-enable booleanp)
                                    (name symbolp)
                                    (left symbolp)
                                    (right symbolp)
                                    (x1...xn symbol-listp)
                                    (left-to-right symbolp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the right-to-left rewrite rule."
  (b* ((macro (if right-to-left-enable 'defthm 'defthmd))
       (body `(implies (,name)
                       (equal (,right ,@x1...xn)
                              (,left ,@x1...xn))))
       (hints `(:hints (("Goal" :in-theory '(,left-to-right)))))
       (local-event `(local (,macro ,right-to-left ,body ,@hints)))
       (exported-event `(,macro ,right-to-left ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-gen-theory-invariant ((left-to-right symbolp)
                                       (right-to-left symbolp))
  :returns (even pseudo-event-formp)
  :short "Generate the theory invariant."
  `(theory-invariant (incompatible (:rewrite ,left-to-right)
                                   (:rewrite ,right-to-left))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-gen-everything ((name symbolp)
                                 (left symbolp)
                                 (right symbolp)
                                 (x1...xn symbol-listp)
                                 (enable booleanp)
                                 (verify-guards booleanp)
                                 (left-to-right symbolp)
                                 (left-to-right-enable booleanp)
                                 (right-to-left symbolp)
                                 (right-to-left-enable booleanp)
                                 (print evmac-input-print-p)
                                 (show-only booleanp)
                                 (call pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Generate the top-level event."
  (b* (((mv local-equality exported-equality)
        (defequal-gen-equality
          name left right x1...xn enable verify-guards
          left-to-right left-to-right-enable))
       ((mv local-right-to-left exported-right-to-left)
        (defequal-gen-right-to-left
          right-to-left right-to-left-enable
          name left right x1...xn left-to-right))
       (theory-invariant
        (defequal-gen-theory-invariant left-to-right right-to-left))
       (events `((logic)
                 (evmac-prepare-proofs)
                 ,local-equality
                 ,local-right-to-left
                 ,exported-equality
                 ,exported-right-to-left
                 ,theory-invariant))
       (encapsulate `(encapsulate () ,@events))
       ((when show-only)
        (if (member-eq print '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (table-record (defequal-record-call call encapsulate))
       (print-result (and
                      (member-eq print '(:result :info :all))
                      `(,@(and (member-eq print '(:all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',exported-equality)
                        (cw-event "~x0~|" ',exported-right-to-left)
                        (cw-event "~x0~|" ',theory-invariant)))))
    `(progn
       ,encapsulate+
       ,table-record
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defequal-fn (name
                     left
                     (left-present booleanp)
                     right
                     (right-present booleanp)
                     vars
                     enable
                     verify-guards
                     left-to-right-name
                     left-to-right-enable
                     right-to-left-name
                     right-to-left-enable
                     print
                     show-only
                     (call pseudo-event-formp)
                     ctx
                     state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (defequal-implementation)
  :short "Check redundancy, process the inputs, generated the events."
  (b* ((expansion? (defequal-redundant? call (w state)))
       ((when expansion?)
        (b* (((run-when show-only) (cw "~x0~|" expansion?)))
          (cw "~%The call ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list x1...xn left-to-right right-to-left)) (defequal-process-inputs
                                                          name
                                                          left left-present
                                                          right right-present
                                                          vars
                                                          enable
                                                          verify-guards
                                                          left-to-right-name
                                                          left-to-right-enable
                                                          right-to-left-name
                                                          right-to-left-enable
                                                          print
                                                          show-only
                                                          ctx
                                                          state))
       (event (defequal-gen-everything
                name
                left
                right
                x1...xn
                enable
                verify-guards
                left-to-right
                left-to-right-enable
                right-to-left
                right-to-left-enable
                print
                show-only
                call)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defequal-macro-definition
  :parents (defequal-implementation)
  :short "Definition of the @(tsee defequal) macro."
  :long (xdoc::topstring-@def "defequal")
  (defmacro defequal (&whole call
                             name
                             &key
                             (left ':no-default left-present)
                             (right ':no-default right-present)
                             (vars ':auto)
                             (enable 'nil)
                             (verify-guards 't)
                             (left-to-right-name ':auto)
                             (left-to-right-enable 'nil)
                             (right-to-left-name ':auto)
                             (right-to-left-enable 'nil)
                             (print ':result)
                             (show-only 'nil))
    `(make-event-terse (defequal-fn
                         ',name
                         ',left
                         ',left-present
                         ',right
                         ',right-present
                         ',vars
                         ',enable
                         ',verify-guards
                         ',left-to-right-name
                         ',left-to-right-enable
                         ',right-to-left-name
                         ',right-to-left-enable
                         ',print
                         ',show-only
                         ',call
                         (cons 'defequal ',name)
                         state)
                       :suppress-errors ,(not print))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro acl2::defequal (&rest args)
  `(defequal ,@args))
