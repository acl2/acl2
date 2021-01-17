; Isar (Intelligible Semi-Automated Reasoning) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ISAR")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defisar

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input "name")

  (xdoc::evmac-topic-implementation-item-input "formula")

  (xdoc::evmac-topic-implementation-item-input "proof")

  "@('hyps') is the list of hypotheses of @('formula')."

  "@('concl') is the conclusion of @('formula')"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-formula-to-hyps+concl (formula)
  :returns (mv (hyps true-listp) concl)
  :short "Decompose the input formula into hypotheses and conclusion."
  (case-match formula
    (('implies hyp/hyps concl)
     (case-match hyp/hyps
       (('and . hyp/hyps)
        (if (true-listp hyp/hyps)
            (mv hyp/hyps concl)
          (prog2$ (raise "Internal error: malformed hypotheses ~x0 in ~x1."
                         hyp/hyps formula)
                  (mv nil nil))))
       (& (mv (list hyp/hyps) concl))))
    (& (mv nil formula))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate fact-info
  :short "Recognize information about facts."
  :long
  (xdoc::topstring
   (xdoc::p
    "Facts are stored in an alist from their names to this information,
     which consists of the name of the theorem generated for the fact
     and the formula of the theorem (i.e. the fact)."))
  ((thm-name symbolp)
   (formula "An untranslated term."))
  :pred fact-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist fact-info-listp (x)
  :short "Recognize lists of information about facts."
  (fact-infop x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fact-info-list->thm-name-list ((infos fact-info-listp))
  :returns (thm-names symbol-listp :hyp :guard)
  :short "Lift @(tsee fact-info->thm-name) to lists."
  (cond ((endp infos) nil)
        (t (cons (fact-info->thm-name (car infos))
                 (fact-info-list->thm-name-list (cdr infos))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist keyword-fact-info-alistp (x)
  :short "Recognize alists from keywords to fact information."
  :long
  (xdoc::topstring
   (xdoc::p
    "An alist of this type stores information about
     all the facts proved so far when running the proof."))
  :key (keywordp x)
  :val (fact-infop x)
  :true-listp t

  ///

  (defrule fact-info-listp-of-strip-cdr-when-keyword-fact-info-alistp
    (implies (keyword-fact-info-alistp x)
             (fact-info-listp (strip-cdrs x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-assume (assume-args
                        (name symbolp)
                        (hyps true-listp)
                        (events pseudo-event-form-listp)
                        (facts keyword-fact-info-alistp)
                        ctx
                        state)
  :returns (mv erp
               (result (tuple (new-events pseudo-event-form-listp)
                              (new-facts keyword-fact-info-alistp)
                              result)
                       :hyp (and (pseudo-event-form-listp events)
                                 (keyword-fact-info-alistp facts)))
               state)
  :short "Execute an @(':assume') command."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @(':assume') command takes exactly one argument,
     which must be a list of a keyword and a formula.
     The keyword must not be already the name of a fact.
     We do not check the formula here;
     we implicitly check it when the generated theorem is submitted."))
  (b* (((unless (tuplep 1 assume-args))
        (er-soft+ ctx t (list nil nil)
                  "Malformed :ASSUME arguments ~x0." assume-args))
       (assume-id+fact (car assume-args))
       ((unless (tuplep 2 assume-id+fact))
        (er-soft+ ctx t (list nil nil)
                  "Malformed :ASSUME argument ~x0." assume-id+fact))
       (assume-id (first assume-id+fact))
       (assume-fact (second assume-id+fact))
       ((unless (keywordp assume-id))
        (er-soft+ ctx t (list nil nil)
                  "The fact name ~x0 must be a keyword." assume-id))
       ((when (consp (assoc-eq assume-id facts)))
        (er-soft+ ctx t (list nil nil) "Duplicate fact name ~x0." assume-id))
       (thm-name (packn-pos (list name "<" assume-id ">") name))
       (thm-formula (if (consp hyps)
                        `(implies (and ,@hyps) ,assume-fact)
                      assume-fact))
       (thm-hints '(("Goal" :in-theory nil)))
       (thm-event `(local (defthm ,thm-name ,thm-formula :hints ,thm-hints)))
       (thm-event (restore-output thm-event))
       (print-event `(cw-event "~%~%~%~s0~%~x1~%~%"
                               "****************************************"
                               '(:assume ,@assume-args)))
       (events (list* thm-event print-event events))
       (fact-info (make-fact-info :thm-name thm-name :formula assume-fact))
       (facts (acons assume-id fact-info facts)))
    (value (list events facts)))
  ///
  (more-returns
   (result true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-derive-thm-hyps ((derive-from keyword-listp)
                                 (facts keyword-fact-info-alistp)
                                 ctx
                                 state)
  :returns (mv erp
               (thm-hyps true-listp)
               state)
  :short "Generate the hypotheses for the theorem generated for
          a @(':derive') command."
  (b* (((when (endp derive-from)) (value nil))
       (id (car derive-from))
       (lookup (assoc-eq id facts))
       ((unless (consp lookup)) (er-soft+ ctx t nil "Fact ~x0 not found." id))
       (info (cdr lookup))
       (thm-hyp (fact-info->formula info))
       ((er thm-hyps)
        (defisar-derive-thm-hyps (cdr derive-from) facts ctx state)))
    (value (cons thm-hyp thm-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-derive (derive-args
                        (name symbolp)
                        (events pseudo-event-form-listp)
                        (facts keyword-fact-info-alistp)
                        ctx
                        state)
  :returns (mv erp
               (result (tuple (new-events pseudo-event-form-listp)
                              (new-facts keyword-fact-info-alistp)
                              result)
                       :hyp (and (pseudo-event-form-listp events)
                                 (keyword-fact-info-alistp facts)))
               state)
  :short "Execute a @(':derive') command."
  (b* (((mv okp derive-id derive-fact derive-from derive-hints)
        (case-match derive-args
          (((id fact)) (mv t id fact nil nil))
          (((id fact) :from from) (mv t id fact from nil))
          (((id fact) :hints hints) (mv t id fact nil hints))
          (((id fact) :from from :hints hints) (mv t id fact from hints))
          (& (mv nil nil nil nil nil))))
       ((when (not okp))
        (er-soft+ ctx t (list nil nil)
                  "Malformed :DERIVE arguments ~x0." derive-args))
       ((unless (keywordp derive-id))
        (er-soft+ ctx t (list nil nil)
                  "The fact name ~x0 must be a keyword." derive-id))
       ((when (consp (assoc-eq derive-id facts)))
        (er-soft+ ctx t (list nil nil) "Duplicate fact name ~x0." derive-id))
       (thm-name (packn-pos (list name "<" derive-id ">") name))
       ((unless (keyword-listp derive-from))
        (er-soft+ ctx t (list nil nil)
                  "The :FROM fact names ~x0 must be keywords." derive-from))
       ((mv erp thm-hyps state)
        (defisar-derive-thm-hyps derive-from facts ctx state))
       ((when erp) (mv erp (list nil nil) state))
       (thm-formula (if (consp thm-hyps)
                        `(implies (and ,@thm-hyps) ,derive-fact)
                      derive-fact))
       (thm-hints derive-hints)
       (thm-event `(local (defthm ,thm-name ,thm-formula :hints ,thm-hints)))
       (thm-event (restore-output thm-event))
       (print-event `(cw-event "~%~%~%~s0~%~x1~%~%"
                               "****************************************"
                               '(:derive ,@derive-args)))
       (events (list* thm-event print-event events))
       (fact-info (make-fact-info :thm-name thm-name :formula derive-fact))
       (facts (acons derive-id fact-info facts)))
    (value (list events facts)))
  ///
  (more-returns
   (result true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-qed ((name symbolp)
                     formula
                     (events pseudo-event-form-listp)
                     (facts keyword-fact-info-alistp))
  :returns (new-events pseudo-event-form-listp
                       :hyp (pseudo-event-form-listp events))
  :short "Execute the @(':qed') command."
  (b* ((fact-infos (strip-cdrs facts))
       (fact-thm-names (fact-info-list->thm-name-list fact-infos))
       (hints `(("Goal" :in-theory nil :use ,fact-thm-names)))
       (local-thm `(local
                    (defthm ,name ,formula :hints ,hints)))
       (local-thm (restore-output local-thm))
       (exported-thm `(defthm ,name ,formula))
       (print-event `(cw-event "~%~%~%~s0~%~x1~%~%"
                               "****************************************"
                               '(:qed)))
       (events (list* exported-thm local-thm print-event events)))
    events))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-commands ((commands true-listp)
                          (name symbolp)
                          formula
                          (hyps true-listp)
                          (events pseudo-event-form-listp)
                          (facts keyword-fact-info-alistp)
                          ctx
                          state)
  :returns (mv erp
               (events pseudo-event-form-listp
                       :hyp (and (pseudo-event-form-listp events)
                                 (keyword-fact-info-alistp facts)))
               state)
  :short "Execute a sequence of commands."
  (b* (((when (endp commands))
        (value
         (cons `(cw-event "~%~%~%~s0~s1~s0~%"
                          "!!!!!!!!!!!!!!!!!!!!"
                          "The proof is partial (no :QED).")
               events)))
       (command (car commands))
       ((unless (and (true-listp command)
                     (consp command)))
        (er-soft+ ctx t nil
                  "Malformed proof command ~x0." command))
       (command-name (car command))
       ((unless (keywordp command-name))
        (er-soft+ ctx t nil
                  "Non-keyword proof command name ~x0." command-name)))
    (case command-name
      (:assume (b* (((mv erp (list events facts) state)
                     (defisar-assume (cdr command)
                       name hyps
                       events facts ctx state))
                    ((when erp) (mv erp nil state)))
                 (defisar-commands (cdr commands)
                   name formula hyps
                   events facts ctx state)))
      (:derive (b* (((mv erp (list events facts) state)
                     (defisar-derive (cdr command)
                       name events facts ctx state))
                    ((when erp) (mv erp nil state)))
                 (defisar-commands (cdr commands)
                   name formula hyps
                   events facts ctx state)))
      (:qed (b* (((run-unless (endp (cdr commands)))
                  (cw "Commands found after :QED." (cdr commands))))
              (value
               (defisar-qed name formula events facts))))
      (t (er-soft+ ctx t nil
                   "Unrecognized command ~x0." command-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-proof ((commands true-listp)
                       (name symbolp)
                       formula
                       ctx
                       state)
  :returns (mv erp (events pseudo-event-form-listp) state)
  :short "Execute a proof."
  (b* (((mv hyps &) (defisar-formula-to-hyps+concl formula))
       ((er events)
        (defisar-commands commands name formula hyps nil nil ctx state)))
    (value (rev events)))
  :prepwork
  ((defrulel rev-of-pseudo-event-form-listp
     (implies (pseudo-event-form-listp x)
              (pseudo-event-form-listp (rev x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-fn (name formula proof ctx state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Generate and submit the @(tsee defisar) events."
  (b* (((unless (symbolp name))
        (er-soft+ ctx t '(_)
                  "The name input must be a symbol, ~
                   but it is ~x0 instead." name))
       ((unless (true-listp proof))
        (er-soft+ ctx t '(_)
                  "The :PROOF input must be a list of commands, ~
                   but it is ~x0 instead." proof))
       ((mv erp events state) (defisar-proof proof name formula ctx state))
       ((when erp) (mv erp '(_) state)))
    (value `(progn
              (encapsulate () ,@events)
              (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defisar-macro-definition
  :short "Definition of the @(tsee defisar) macro."
  (defmacro defisar (name formula &key proof)
    `(make-event-terse (defisar-fn
                         ',name
                         ',formula
                         ',proof
                         (cons 'defisar ',name)
                         state)
                       :suppress-errors nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defisar-macro-definition
  :short "Synonym of @(tsee defisar) in the @('\"ACL2\"') package."
  (defmacro acl2::defisar (&rest args)
    `(defisar ,@args)))
