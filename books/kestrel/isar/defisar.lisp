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

  (xdoc::evmac-topic-implementation-item-input "disable")

  (xdoc::evmac-topic-implementation-item-input "rule-classes")

  "@('hyps') is the list of hypotheses of @('formula')."

  "@('concl') is the conclusion of @('formula')"

  "@('facts') is an alist from keyword that identify facts
   to information about those facts."

  "@('bindings') is an alist from variable symbols to formulas,
   corresponding to the @(':let') bindings.")

 :default-parent t)

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
                        (bindings symbol-alistp)
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
     we implicitly check it when the generated theorem is submitted.")
   (xdoc::p
    "The bindings are reversed before being put into the formula,
     because they are @(tsee cons)ed as go through the @(':let')s."))
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
       (thm-formula (if bindings
                        `(let* ,(rev (alist-to-doublets bindings))
                           ,thm-formula)
                      thm-formula))
       (thm-hints '(("Goal" :in-theory nil)))
       (thm-event `(local
                    (defthm ,thm-name
                      ,thm-formula
                      :hints ,thm-hints
                      :rule-classes nil)))
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

(define defisar-let (let-args
                     (bindings symbol-alistp)
                     ctx
                     state)
  :returns (mv erp
               (new-bindings symbol-alistp :hyp (symbol-alistp bindings))
               state)
  :short "Execute a @(':let') command."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @(':let') command takes exactly one argument,
     which must be a list of a variable symbol and a term.
     The variable symbol must not be already bound.
     We do no check he term here:
     we implicitly check it when the bound variable is used."))
  (b* (((unless (tuplep 1 let-args))
        (er-soft+ ctx t nil
                  "Malformed :LET arguments ~x0." let-args))
       (let-var+term (car let-args))
       ((unless (tuplep 2 let-var+term))
        (er-soft+ ctx t nil
                  "Malformed :LET argument ~x0." let-var+term))
       (let-var (first let-var+term))
       (let-term (second let-var+term))
       ((unless (symbolp let-var))
        (er-soft+ ctx t nil
                  "The variable ~x0 must be a symbol." let-var))
       ((when (consp (assoc-eq let-var bindings)))
        (er-soft+ ctx t nil "Duplicate variable ~x0." let-var)))
    (value (acons let-var let-term bindings))))

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
                        (bindings symbol-alistp)
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
  :long
  (xdoc::topstring
   (xdoc::p
    "The bindings are reversed before being put into the formula,
     because they are @(tsee cons)ed as go through the @(':let')s."))
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
       (thm-formula (if bindings
                        `(let* ,(rev (alist-to-doublets bindings))
                           ,thm-formula)
                      thm-formula))
       (thm-hints derive-hints)
       (thm-event `(local
                    (defthm ,thm-name
                      ,thm-formula
                      :hints ,thm-hints
                      :rule-classes nil)))
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
                     (facts keyword-fact-info-alistp)
                     (disable booleanp)
                     rule-classes)
  :returns (new-events pseudo-event-form-listp
                       :hyp (pseudo-event-form-listp events))
  :short "Execute the @(':qed') command."
  (b* ((fact-infos (strip-cdrs facts))
       (fact-thm-names (fact-info-list->thm-name-list fact-infos))
       (hints `(("Goal" :in-theory nil :use ,fact-thm-names)))
       (defthm/defthmd (if disable 'defthmd 'defthm))
       (local-thm `(local (,defthm/defthmd ,name
                            ,formula
                            :hints ,hints
                            :rule-classes ,rule-classes)))
       (local-thm (restore-output local-thm))
       (exported-thm `(,defthm/defthmd ,name
                        ,formula
                        :rule-classes ,rule-classes))
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
                          (bindings symbol-alistp)
                          (disable booleanp)
                          rule-classes
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
                          " The proof is partial (no :QED). ")
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
                       events facts bindings ctx state))
                    ((when erp) (mv erp nil state)))
                 (defisar-commands (cdr commands)
                   name formula hyps
                   events facts bindings disable rule-classes ctx state)))
      (:let (b* (((mv erp bindings state)
                  (defisar-let (cdr command) bindings ctx state))
                 ((when erp) (mv erp nil state)))
              (defisar-commands (cdr commands)
                name formula hyps
                events facts bindings disable rule-classes ctx state)))
      (:derive (b* (((mv erp (list events facts) state)
                     (defisar-derive (cdr command)
                       name events facts bindings ctx state))
                    ((when erp) (mv erp nil state)))
                 (defisar-commands (cdr commands)
                   name formula hyps
                   events facts bindings disable rule-classes ctx state)))
      (:qed (b* (((run-unless (endp (cdr commands)))
                  (cw "Commands ~x0 found after :QED." (cdr commands))))
              (value
               (defisar-qed name formula events facts disable rule-classes))))
      (t (er-soft+ ctx t nil
                   "Unrecognized command ~x0." command-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-proof ((commands true-listp)
                       (name symbolp)
                       formula
                       (disable booleanp)
                       rule-classes
                       ctx
                       state)
  :returns (mv erp (events pseudo-event-form-listp) state)
  :short "Execute a proof."
  (b* (((mv hyps &) (defisar-formula-to-hyps+concl formula))
       ((er events)
        (defisar-commands
          commands name formula hyps nil nil nil
          disable rule-classes ctx state)))
    (value (rev events)))
  :prepwork
  ((defrulel rev-of-pseudo-event-form-listp
     (implies (pseudo-event-form-listp x)
              (pseudo-event-form-listp (rev x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defisar-fn (name formula proof disable rule-classes ctx state)
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
       ((unless (booleanp disable))
        (er-soft+ ctx t '(_)
                  "The :DISABLE input must be a boolean, ~
                   but it is ~x0 instead." disable))
       ((mv erp events state)
        (defisar-proof proof name formula disable rule-classes ctx state))
       ((when erp) (mv erp '(_) state)))
    (value `(progn
              (encapsulate ()
                (set-ignore-ok t)
                ,@events)
              (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defisar-macro-definition
  :short "Definition of the @(tsee defisar) macro."
  (defmacro defisar (name formula &key proof disable (rule-classes ':rewrite))
    `(make-event-terse (defisar-fn
                         ',name
                         ',formula
                         ',proof
                         ',disable
                         ',rule-classes
                         (cons 'defisar ',name)
                         state)
                       :suppress-errors nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defisar-macro-definition-synonym
  :short "Synonym of @(tsee defisar) in the @('\"ACL2\"') package."
  (defmacro acl2::defisar (&rest args)
    `(defisar ,@args)))
