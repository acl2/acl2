; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "translation")
(include-book "outcomes")
(include-book "language/acl2-to-deep")

(include-book "tools/nld" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::set-numbered-name-index-start "__")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-term-from-hyp ((hyp obligation-hypp))
  (obligation-hyp-case hyp
    :condition (d-->a-expr hyp.get)
    :binding (b* (((binding b) hyp.get)
                  (lhs (case-match b.variables
                         ((v) (intern-syndef (identifier->name (typed-variable->name v))))
                         (& `(mv ,@(variable-names b.variables))))))
               `(equal ,lhs ,(d-->a-expr b.value)))))

(define get-hypothesis-terms ((hyps obligation-hyp-listp))
  (if (endp hyps)
      ()
    (cons (get-term-from-hyp (car hyps))
          (get-hypothesis-terms (cdr hyps)))))

(define get-var-predicate-term ((var typed-variablep))
  (b* (((typed-variable v) var)
       (type-pred (type-name-to-pred (d-->a-type-name v.type))))
    `(,type-pred ,(intern-syndef (identifier->name v.name)))))

(define get-variable-type-predicate-terms ((vars typed-variable-listp))
  (if (endp vars)
      ()
    (cons (get-var-predicate-term (car vars))
          (get-variable-type-predicate-terms (cdr vars)))))

(acl2::program)

(define proof-obligation-to-acl2-theorem ((oblig proof-obligationp) (enabled-list true-listp))
  (b* (((proof-obligation o) oblig)
       (formula `(implies (and ,@(get-variable-type-predicate-terms o.variables)
                               ,@(get-hypothesis-terms o.hypotheses))
                          ,(d-->a-expr o.conclusion)))
       (enabled-list (append enabled-list
                             (relevant-fn-names formula))))
    `(thm ,formula
          ,@(and enabled-list
                 `(:hints (("Goal" :in-theory (enable ,@enabled-list))))))))

(define shallow-types-of-variables ((vars typed-variable-listp))
  (if (endp vars)
      ()
    (cons (d-->s-type (typed-variable->type (car vars)))
          (shallow-types-of-variables (cdr vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define get-transformed-definitions ((transform transformp)
                                     (ctxt contextp)
                                     (w acl2::plist-worldp))
  ;:returns (f toplevel-listp)
  (b* (((transform transfm) transform)
       (fn-def (get-function-definition transfm.old-function-name (context->tops ctxt)))
       (old-fn-symbol (intern-syndef (identifier->name transfm.old-function-name)))
       (new-fn-symbol (intern-syndef (identifier->name transfm.new-function-name)))
       (new-acl2-fn-normalized-def (acl2::fn-body new-fn-symbol nil w))
       (new-acl2-fn-def (acl2::untranslate new-acl2-fn-normalized-def nil w))
       (new-guard-conjuncts (acl2::get-conjuncts (acl2::fn-guard new-fn-symbol w)))
       (new-normalized-guard-conjuncts (acl2::untranslate-lst new-guard-conjuncts nil w))
       (new-formals (acl2::fn-formals new-fn-symbol w))
       (new-fn-def (acl2-to-deep-fn new-fn-symbol new-formals new-acl2-fn-def
                                    new-normalized-guard-conjuncts fn-def ctxt))
       (ctxt (context-add-toplevel (toplevel-function new-fn-def) ctxt))
       (wrapper-name? (lookup-transform-argument transfm.arguments "wrapper_name"))
       (new-wrapper-fn-def (and wrapper-name?
                                (let ((wrapper-fn-symbol (and wrapper-name?
                                                              (intern-syndef (identifier->name wrapper-name?)))))
                                  (acl2-to-deep-fn wrapper-fn-symbol
                                                   (acl2::fn-formals wrapper-fn-symbol w)
                                                   (acl2::untranslate (acl2::fn-body wrapper-fn-symbol nil w) nil w)
                                                   (acl2::get-conjuncts (acl2::fn-guard wrapper-fn-symbol w))
                                                   fn-def ctxt))))
       (ctxt (if new-wrapper-fn-def
                 (context-add-toplevel (toplevel-function new-wrapper-fn-def) ctxt)
               ctxt))
       (old-to-new-theorem-name-1 (acl2::pack$ old-fn-symbol "_becomes_" new-fn-symbol))
       (old-to-new-theorem-name-2 (pack-1 old-fn-symbol "_becomes_" new-fn-symbol))
       (old-to-new-theorem-name (if (acl2::getprop old-to-new-theorem-name-1
                                                   'acl2::theorem nil 'acl2::current-acl2-world w)
                                    old-to-new-theorem-name-1
                                  (if (acl2::getprop old-to-new-theorem-name-2
                                                     'acl2::theorem nil 'acl2::current-acl2-world w)
                                      old-to-new-theorem-name-2
                                    (pack-1 old-fn-symbol "_to_" new-fn-symbol))))
       (- (cw "old-to-new-theorem-name: ~x0~%" old-to-new-theorem-name))
       (old-to-new-thm-body (acl2::getprop old-to-new-theorem-name 'acl2::theorem nil 'acl2::current-acl2-world w))
       (old-to-new-thm-def (and old-to-new-thm-body
                                (acl2-to-deep-thm old-to-new-theorem-name old-to-new-thm-body fn-def ctxt))))
    `(,(toplevel-function new-fn-def)
      ,@(and new-wrapper-fn-def (list (toplevel-function new-wrapper-fn-def)))
      ,@(and old-to-new-thm-def (list (toplevel-theorem old-to-new-thm-def))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define toplevel-failure-outcome ((top toplevelp))
  ;:returns (o outcomep)
  (if (equal (toplevel-kind top)
             :theorem)
      (make-outcome-theorem-failure :message (toplevel-name top))
    (make-outcome-unexpected-failure :message (toplevel-name top))))

(define toplevel-succcess-outcome ((top toplevelp)
                                   (ctxt contextp)
                                   (w acl2::plist-worldp))
  ;:returns (o outcomep)
  (let ((name (toplevel-name top)))
    (toplevel-case top
      :type (make-outcome-type-success :message name)
      :types (make-outcome-type-success :message name)                   
      :function (make-outcome-function-success :message name)
      :functions (make-outcome-function-success :message name)
      :specification (make-outcome-specification-success :message name)
      :theorem (make-outcome-theorem-success :message name)
      :transform (make-outcome-transformation-success
                  :message name
                  :toplevels (get-transformed-definitions (toplevel-transform->get top)
                                                          ctxt w)))))

(define check-obligations ((obligs proof-obligation-listp)
                           (this-top toplevelp)
                           (fn-names-being-defined string-listp)
                           state)
  ;; Only returns outcomes for failed obligations
  ;:returns (mv erp (outcomes outcome-listp) state)
  (if (endp obligs)
      (value ())
    (b* (((cons oblig r-obligs) obligs)
         ((mv - r-outcomes state) (check-obligations r-obligs this-top fn-names-being-defined state))
         (prerequisite-type-defs (defining-forms-for-unnamed-types-in-s-exp
                                   (shallow-types-of-variables (proof-obligation->variables oblig))))
         (state
          (acl2::submit-event-quiet `(progn ,@prerequisite-type-defs) state))
         (thm (proof-obligation-to-acl2-theorem oblig (translate-names fn-names-being-defined)))
         ((mv erp state)
          (acl2::submit-event-helper thm :brief nil state)))
      (if erp
          (value (cons (make-outcome-proof-obligation-failure
                        :message (toplevel-name this-top)  ;"Obligation not proven!"
                        :obligation-expr
                        (make-expression-binary :operator (binary-op-implies)
                                                :left-operand (conjoin-expressions
                                                               (obligation-hyps-to-expressions
                                                                (proof-obligation->hypotheses oblig)))
                                                :right-operand (proof-obligation->conclusion oblig))
                        ;; :source-expr (proof-obligation->source-expression oblig)
                        ;; :toplevel-name (toplevel-name this-top)
                        )
                       r-outcomes))
        (value r-outcomes)))))

(defmacro cw-to-string (str &rest args)
  `(b* (((mv - str)
        (fmt-to-string ,str (pairlis2 acl2::*base-10-chars* (list ,@args)))))
     str))

(define generate-and-process-acl2-events ((tops toplevel-listp) (ctxt contextp) state)
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  ;:returns (mv erp (outcomes outcome-listp) events state)
  (b* (((when (endp tops)) (mv () () state))
       ((cons this-top r-tops) tops)
       (fn-names-being-defined (toplevel-fn-names this-top))
       ((mv err? obligs ctxt) (check-toplevel this-top ctxt))
       ((when err?) (mv ()
                        (list (make-outcome-unexpected-failure
                               :message (cw-to-string "Static semantic failure:~%~x0"
                                                      err?)))
                        state))
       ((mv before-obligs after-obligs)
        (split-obligations-using-functions obligs fn-names-being-defined))
       ((mv - outcomes state)
        (check-obligations before-obligs this-top () state))
       ((when outcomes)                 ; One or more obligations failed to prove
        (mv () outcomes state))
       (this-event (d-->s-toplevel this-top))
       ((mv err state)
        (acl2::submit-event-helper this-event nil nil state))
       ((when err)
        (mv () (list (toplevel-failure-outcome this-top)) state))
       ((mv - outcomes state)
        (check-obligations after-obligs this-top fn-names-being-defined state))
       ((when outcomes)                 ; One or more obligations failed to prove
        (mv () outcomes state))
       (success-outcome (toplevel-succcess-outcome this-top ctxt (w state)))
       ((mv r-events r-outcomes state) (generate-and-process-acl2-events r-tops ctxt state))
       ((when (and r-outcomes (null r-events)))
        (mv () r-outcomes state)))
    (mv (cons this-event r-events)
        (cons success-outcome r-outcomes)
        state)))

(define process-syntheto-toplevel-fn (top/tops state)
  ;:returns (mv erp (outcomes outcome-listp) state)
  :short "Translate a Syntheto top-level construct, or a list of them,
          into corresponding ACL2 events and execute them, returning a list of outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the entry point for the translation from Syntheto to ACL2 and processing in ACL2.")
   (xdoc::p
    "We ensure that the input is a top-level construct or a list of them.")
   (xdoc::p
    "We retrieve the existing (i.e. old) top-level constructs
     from the current translation state.
     We wrap them into a context and we check that
     the input satisfies the static semantics
     (this wrapping is a bit awkward, and we will eliminate it
     after we make some planned improvements to the static semantics).
     If the static semantic checks succeed,
     we generate an event to extend the translation state with the input.")
   (xdoc::p
    "This is just a start: there is, of course, much more to do here.
     In particular, we need to generate ACL2 events
     corresponding to the input Syntheto top-level constructs.
     We are also curently ignoring the type obligations
     generated by the static semantics checks:
     these should be turned into ACL2 theorems,
     and used to generate proofs for the other events
     (e.g. guard proofs for function definitions)."))
  (b* (((mv er tops)
        (cond ((toplevelp top/tops) (mv nil (list top/tops)))
              ((toplevel-listp top/tops) (mv nil top/tops))
              (t (mv t nil))))
       ((when er)
        (value (make-outcome-unexpected-failure
                :message "Expected a toplevel or toplevel-list argument.")))
       (tstate (get-trans-state (w state)))
       (old-tops (trans-state->tops tstate))
       (ctxt (make-context :tops old-tops))
       (tstate (extend-trans-state-list tops tstate))
       (table-event `(set-trans-state ,tstate))
       (state (acl2::submit-event-quiet table-event state))
       ((mv events outcomes state)
        (generate-and-process-acl2-events tops ctxt state))
       (new-tops (tops-from-transform-outcomes outcomes))
       (tstate (extend-trans-state-list new-tops tstate))
       (table-event `(set-trans-state ,tstate))
       (events (if (endp events)
                   events               ; Failure
                 (append events (list table-event))) ; Success. Save context for future defs.
               )
       (final-outcome (if (endp outcomes)
                          (make-outcome-unexpected-failure
                           :message "Shouldn't happen: No actual outcomes!")
                        (car (last outcomes))))
       (make-final-outcome-form (syntheto::outcome--make-myself final-outcome)))
    (value `(progn ,@events (value-triple ',make-final-outcome-form)))))

(defmacro+ process-syntheto-toplevel (top/tops)
  :short "Translate to ACL2 and Syntheto top-level construct or a list of them."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the entry point of the translation from Syntheto to ACL2.
     The argument is evaluated, and it must evaluate to
     a Syntheto top-level construct or to a list of them;
     this is checked by the function called by this macro.
     The function returns events that are submitted to ACL2 by this macro.
     The events update the translation state table
     and generate ACL2 counterparts of the Syntheto construct(s)."))
  `(make-event (process-syntheto-toplevel-fn ,top/tops state)))
