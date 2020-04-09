; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 casesplit

 :item-state t

 :item-wrld t

 :item-ctx t

 :items

 ("@('old'),
   @('conditions'),
   @('theorems'),
   @('new-name'),
   @('new-enable'),
   @('thm-name'),
   @('thm-enable'),
   @('verify-guards'),
   @('hints'),
   @('print'), and
   @('show-only')
   are the homonymous inputs to @(tsee casesplit),
   before being processed.
   These formal parameters have no types because they may be any values."

  "@('call') is the call to @(tsee casesplit) supplied by the user."

  "@('old$'),
   @('conditions$'),
   @('theorems$'),
   @('new-name$'),
   @('new-enable$'),
   @('thm-name$'),
   @('thm-enable$'),
   @('non-executable$'),
   @('verify-guards$'),
   @('hints$'),
   @('print$'), and
   @('show-only$')
   are the results of processing
   the homonymous inputs (without the @('$')) to @(tsee casesplit).
   Some are identical to the corresponding inputs,
   but they have types implied by their successful validation,
   performed when they are processed."

  "@('hyps') is the list @('(hyp1 ... hypp hyp0)') of hypotheses
   of the theorems named in the @('theorems') input, in the same order."

  "@('news') is the list @('(new1 ... newp new0)') of right-hand sides
   of the theorems named in the @('theorems') input, in the same order."

  "@('appcond-thm-names') is an alist
   from the keywords that identify the applicability conditions
   to the corresponding generated theorem names."

  "@('new-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the new function."

  "@('names-to-avoid') is a cumulative list of names of generated events,
   used to ensure the absence of name clashes in the generated events."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions casesplit)

(define negate-terms ((terms pseudo-term-listp))
  :returns (negated-terms pseudo-term-listp :hyp (pseudo-term-listp terms))
  (cond ((endp terms) nil)
        (t (cons (dumb-negate-lit (car terms))
                 (negate-terms (cdr terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing casesplit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-old (old verify-guards ctx state)
  :returns (mv erp
               (old$ "A @(tsee symbolp) that is
                      the name of the target function
                      of the transformation,
                      denoted by the @('old') input.")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* (((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-number-of-results$ old$ 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value nil))))
    (value old$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-condition
  ((cond "An element of @('conditions').")
   (pos posp "Position of @('cond') in @('conditions'), 1-based.")
   (old$ symbolp)
   (verify-guards$ booleanp)
   ctx
   state)
  :returns (mv erp
               (condition$ "A @(tsee pseudo-termp) that is
                            the translation of @('cond').")
               state)
  :mode :program
  :short "Process an element of the @('conditions') input."
  (b* ((wrld (w state))
       (description (msg "The ~n0 element of the second input" (list pos)))
       ((er (list term stobjs-out)) (ensure-term$ cond description t nil))
       (description (msg "The term ~x0 that denotes the ~n1 condition"
                         cond (list pos)))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old$ wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if verify-guards$
                   (ensure-term-guard-verified-exec-fns$
                    term
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old$ (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (ensure-term-does-not-call$ term old$
                                           description t nil)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-conditions (conditions
                                      (old$ symbolp)
                                      (verify-guards$ booleanp)
                                      ctx
                                      state)
  :returns (mv erp
               (conditions$ "A @(tsee pseudo-term-listp).")
               state)
  :mode :program
  :short "Process the @('conditions') input."
  (b* (((unless (true-listp conditions))
        (er-soft+ ctx t nil
                  "The second input must be a true list, ~
                   but it is ~x0 instead." conditions))
       ((unless (consp conditions))
        (er-soft+ ctx t nil
                  "The second input must be a non-empty list, ~
                   but it is ~x0 instead." conditions))
       (pos 1))
    (casesplit-process-conditions-aux conditions
                                      pos
                                      old$
                                      verify-guards$
                                      ctx state))

  :prepwork
  ((define casesplit-process-conditions-aux (conditions
                                             (pos posp)
                                             (old$ symbolp)
                                             (verify-guards$ booleanp)
                                             ctx
                                             state)
     :returns (mv erp
                  conditions$ ; PSEUDO-TERM-LISTP
                  state)
     :mode :program
     :parents nil
     (cond ((endp conditions) (value nil))
           (t (b* (((er cond$) (casesplit-process-condition
                                (car conditions) pos
                                old$ verify-guards$
                                ctx state))
                   ((er conditions$) (casesplit-process-conditions-aux
                                      (cdr conditions) (1+ pos)
                                      old$ verify-guards$
                                      ctx state)))
                (value (cons cond$ conditions$))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-theorem
  ((thm "An element of @('theorems').")
   (pos posp "Position of @('thm') in @('theorems'), 1-based.")
   (old$ symbolp)
   ctx
   state)
  :returns (mv erp
               (hyp-new "A tuple @('(hyp new)') satisfying
                         @('(typed-tuplep pseudo-termp
                                          pseudo-termp
                                          hyp-new)').")
               state)
  :verify-guards nil
  :short "Process an element of the @('theorems') input."
  :long
  (xdoc::topstring-p
   "If successful,
    return the terms @('hypk') and @('newk') described in the documentation
    (assuming that @('thm') is @('thmk')),
    in translated form.")
  (b* ((wrld (w state))
       (description (msg "The ~n0 element of the third input" (list pos)))
       ((unless (theorem-namep thm wrld))
        (er-soft+ ctx t nil
                  "~@0 must be the name of a theorem, but it is ~x1 instead."
                  description thm))
       (formula (thm-formula+ thm wrld))
       (description (msg "The formula ~x0 of the theorem ~x1 ~
                          specified as ~@2"
                         formula thm (msg-downcase-first description)))
       ((when (or (variablep formula)
                  (fquotep formula)
                  (flambda-applicationp formula)
                  (not (member-eq (ffn-symb formula) '(implies equal)))))
        (er-soft+ ctx t nil
                  "~@0 must be an implication or an equality." description))
       (formula (if (eq (ffn-symb formula) 'equal)
                    `(implies 't ,formula)
                  formula))
       (hyp (fargn formula 1))
       (concl (fargn formula 2))
       (description (msg "The conclusion ~x0 of ~@1"
                         concl (msg-downcase-first description)))
       ((when (or (variablep concl)
                  (fquotep concl)
                  (flambda-applicationp concl)
                  (not (eq (ffn-symb concl) 'equal))))
        (er-soft+ ctx t nil "~@0 must be an equality." description))
       (left-side (fargn concl 1))
       (description (msg "The left-hand side ~x0 of ~@1"
                         left-side (msg-downcase-first description)))
       (formals (formals+ old$ wrld))
       ((unless (equal left-side `(,old$ ,@formals)))
        (er-soft+ ctx t nil
                  "~@0 must be ~
                   a call of ~x1 on its formal parameters ~x2."
                  description old$ formals))
       (new (fargn concl 2)))
    (value (list hyp new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-theorems (theorems
                                    (old$ symbolp)
                                    (conditions$ pseudo-term-listp)
                                    ctx
                                    state)
  :returns (mv erp
               (hyps-news "A tuple @('(hyps news)') satisfying
                           @('(typed-tuple pseudo-term-listp
                                           pseudo-term-listp
                                           hyps-news)').")
               state)
  :verify-guards nil
  :short "Process the @('theorems') input."
  (b* (((unless (true-listp theorems))
        (er-soft+ ctx t nil
                  "The third input must be a true list, ~
                   but it is ~x0 instead." theorems))
       ((unless (= (len theorems) (1+ (len conditions$))))
        (er-soft+ ctx t nil
                  "The length of the third input must be ~
                   one plus the length ~x0 of the second input, ~
                   but it is ~x1 instead."
                  (len conditions$) (len theorems)))
       (pos 1))
    (casesplit-process-theorems-aux theorems pos old$ ctx state))

  :prepwork
  ((define casesplit-process-theorems-aux (theorems
                                           (pos posp)
                                           (old$ symbolp)
                                           ctx
                                           state)
     :returns (mv erp
                  hyps-news ; (TYPED-TUPLE PSEUDO-TERM-LISTP PSEUDO-TERM-LISTP)
                  state)
     :verify-guards nil
     :parents nil
     (cond ((endp theorems) (value (list nil nil)))
           (t (b* (((er (list hyp new)) (casesplit-process-theorem
                                         (car theorems) pos
                                         old$
                                         ctx state))
                   ((er (list hyps news)) (casesplit-process-theorems-aux
                                           (cdr theorems) (1+ pos)
                                           old$
                                           ctx state)))
                (value (list (cons hyp hyps)
                             (cons new news)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-process-thm-name (thm-name
                                    (old$ symbolp)
                                    (new-name$ symbolp)
                                    ctx
                                    state)
  :returns (mv erp
               (thm-name$ "A @(tsee symbolp).")
               state)
  :verify-guards nil
  :short "Process the @(':thm-name') input."
  (b* (((er &) (ensure-symbol$ thm-name "The :THM-NAME input" t nil))
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

(define casesplit-process-inputs (old
                                  conditions
                                  theorems
                                  new-name
                                  new-enable
                                  thm-name
                                  thm-enable
                                  verify-guards
                                  hints
                                  print
                                  show-only
                                  ctx
                                  state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    conditions$
                                    hyps
                                    news
                                    new-name$
                                    new-enable$
                                    thm-name$
                                    verify-guards$
                                    hints$)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-term-listp
                                         pseudo-term-listp
                                         pseudo-term-listp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         symbol-alistp
                                         result)'),
                        where @('old$') is
                        the result of @(tsee casesplit-process-old),
                        @('conditions$') is
                        the result of @(tsee casesplit-process-conditions),
                        @('hyps') and @('news') are
                        the result of @(tsee casesplit-process-theorems),
                        @('new-name$') is
                        the result of @(tsee process-input-new-name),
                        @('new-enable$') indicates whether
                        the new function should be enabled or not,
                        @('thm-name$') is
                        the result of @(tsee casesplit-process-thm-name),
                        @('verify-guards$') indicates whether the guards of
                        the new function should be verified or not, and
                        @('hints$') is
                        the result of @(tsee evmac-process-input-hints).")
               state)
  :mode :program
  :short "Process all the inputs."
  :long
  (xdoc::topstring-p
   "The inputs are processed
    in the order in which they appear in the documentation,
    except that @(':verify-guards') is processed just before @('conditions')
    because the result of processing @(':verify-guards')
    is used to process @('conditions').
    @('old') is processed before @(':verify-guards')
    because the result of processing @('old')
    is used to process @(':verify-guards').
    @(':verify-guards') is also used to process @('old'),
    but it is only tested for equality with @('t')
    (see @(tsee casesplit-process-old)).")
  (b* ((wrld (w state))
       ((er old$) (casesplit-process-old old verify-guards ctx state))
       ((er verify-guards$) (ensure-boolean-or-auto-and-return-boolean$
                             verify-guards
                             (guard-verified-p old$ wrld)
                             "The :VERIFY-GUARDS input" t nil))
       ((er conditions$) (casesplit-process-conditions
                          conditions old$ verify-guards$ ctx state))
       ((er (list hyps news)) (casesplit-process-theorems
                               theorems old$ conditions$ ctx state))
       ((er new-name$) (process-input-new-name new-name old$ ctx state))
       ((er new-enable$) (ensure-boolean-or-auto-and-return-boolean$
                          new-enable
                          (fundef-enabledp old state)
                          "The :NEW-ENABLE input" t nil))
       ((er thm-name$) (casesplit-process-thm-name
                        thm-name old$ new-name$ ctx state))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((er hints$) (evmac-process-input-hints hints ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 conditions$
                 hyps
                 news
                 new-name$
                 new-enable$
                 thm-name$
                 verify-guards$
                 hints$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation casesplit
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-name-from-parts ((prefix stringp)
                                               (k natp)
                                               (suffix stringp))
  :returns (name symbolp "A keyword.")
  :short "Create the name (keyword) of an applicability condition
          from its parts."
  :long
  (xdoc::topstring-p
   "All the applicability condition names consist of
    a prefix (@('thm') or @('cond') or @('new'))
    a number @('k'),
    and a suffix (@('-hyp') or @('-guard')).")
  (intern (str::cat prefix (str::natstr k) suffix) "KEYWORD"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-thm-hyp-name ((k natp))
  :returns (name symbolp "A keyword.")
  :short "Name of the applicability condition @(':thmk-hyp')."
  (casesplit-gen-appcond-name-from-parts "THM" k "-HYP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-cond-guard-name ((k posp))
  :returns (name symbolp "A keyword.")
  :short "Name of the applicability condition @(':condk-guard')."
  (casesplit-gen-appcond-name-from-parts "COND" k "-GUARD"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-new-guard-name ((k natp))
  :returns (name symbolp "A keyword.")
  :short "Name of the applicability condition @(':newk-guard')."
  (casesplit-gen-appcond-name-from-parts "NEW" k "-GUARD"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-thm-hyp
  ((k natp)
   (conditions$ pseudo-term-listp)
   (hyps pseudo-term-listp))
  :guard (and (= (len hyps) (1+ (len conditions$)))
              (<= k (len conditions$)))
  :returns (appcond "An @(tsee evmac-appcondp).")
  :mode :program
  :short "Generate the applicability condition @('thmk-hyp')."
  :long
  (xdoc::topstring-p
   "Recall that @('hyps') is @('(hyp1 ... hypp hyp0)').")
  (b* ((name (casesplit-gen-appcond-thm-hyp-name k))
       (antecedent-conjuncts (if (= k 0)
                                 (negate-terms conditions$)
                               (append (negate-terms (take (1- k) conditions$))
                                       (list (nth (1- k) conditions$)))))
       (antecedent (conjoin antecedent-conjuncts))
       (consequent (if (= k 0)
                       (car (last hyps))
                     (nth (1- k) hyps)))
       (formula (implicate antecedent consequent)))
    (make-evmac-appcond :name name :formula formula)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-cond-guard
  ((k posp)
   (old$ symbolp)
   (conditions$ pseudo-term-listp)
   state)
  :guard (<= k (len conditions$))
  :returns (appcond "An @(tsee evmac-appcondp).")
  :mode :program
  :short "Generate the applicability condition @('condk-guard')."
  (b* ((wrld (w state))
       (name (casesplit-gen-appcond-cond-guard-name k))
       (old-guard (uguard old$ wrld))
       (antecedent-conjuncts (cons old-guard
                                   (negate-terms (take (1- k) conditions$))))
       (antecedent (conjoin antecedent-conjuncts))
       (consequent (term-guard-obligation (nth (1- k) conditions$) state))
       (formula (implicate antecedent consequent)))
    (make-evmac-appcond :name name :formula formula)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appcond-new-guard
  ((k natp)
   (old$ symbolp)
   (conditions$ pseudo-term-listp)
   (news pseudo-term-listp)
   state)
  :guard (and (= (len news) (1+ (len conditions$)))
              (<= k (len conditions$)))
  :returns (appcond "An @(tsee evmac-appcondp).")
  :mode :program
  :short "Generate the applicability condition @('newk-guard')."
  :long
  (xdoc::topstring-p
   "Recall that @('news') is @('(new1 ... newp new0)').")
  (b* ((wrld (w state))
       (name (casesplit-gen-appcond-new-guard-name k))
       (old-guard (uguard old$ wrld))
       (antecedent-conjuncts (if (= k 0)
                                 (cons old-guard
                                       (negate-terms conditions$))
                               (append (list old-guard)
                                       (negate-terms (take (1- k) conditions$))
                                       (list (nth (1- k) conditions$)))))
       (antecedent (conjoin antecedent-conjuncts))
       (new (if (= k 0)
                (car (last news))
              (nth (1- k) news)))
       (consequent (term-guard-obligation new state))
       (formula (implicate antecedent consequent)))
    (make-evmac-appcond :name name :formula formula)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appconds-thm-hyp
  ((conditions$ pseudo-term-listp)
   (hyps pseudo-term-listp)
   (wrld plist-worldp))
  :guard (= (len hyps) (1+ (len conditions$)))
  :returns (appconds "An @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions
          @('thm1-hyp'), ..., @('thmp-hyp'), @('thm0-hyp'), in that order."
  (append (casesplit-gen-appconds-thm-hyp-aux (len conditions$)
                                              conditions$
                                              hyps
                                              wrld
                                              nil)
          (list (casesplit-gen-appcond-thm-hyp 0 conditions$ hyps)))

  :prepwork
  ((define casesplit-gen-appconds-thm-hyp-aux
     ((k natp)
      (conditions$ pseudo-term-listp)
      (hyps pseudo-term-listp)
      (wrld plist-worldp)
      (acc symbol-alistp))
     :guard (and (= (len hyps) (1+ (len conditions$)))
                 (<= k (len conditions$)))
     :returns appconds ; EVMAC-APPCOND-LISTP
     :parents nil
     :mode :program
     (b* (((when (zp k)) acc)
          (appcond (casesplit-gen-appcond-thm-hyp k conditions$ hyps))
          (acc (cons appcond acc)))
       (casesplit-gen-appconds-thm-hyp-aux
        (1- k) conditions$ hyps wrld acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appconds-cond-guard
  ((old$ symbolp)
   (conditions$ pseudo-term-listp)
   state)
  :returns (appconds "An @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions
          @('cond1-guard'), ..., @('condp-guard'), in that order."
  (casesplit-gen-appconds-cond-guard-aux (len conditions$)
                                         old$
                                         conditions$
                                         state
                                         nil)

  :prepwork
  ((define casesplit-gen-appconds-cond-guard-aux
     ((k natp)
      (old$ symbolp)
      (conditions$ pseudo-term-listp)
      state
      (acc symbol-alistp))
     :guard (<= k (len conditions$))
     :returns appconds ; EVMAC-APPCOND-LISTP
     :mode :program
     :parents nil
     (b* (((when (zp k)) acc)
          (appcond (casesplit-gen-appcond-cond-guard k old$ conditions$ state))
          (acc (cons appcond acc)))
       (casesplit-gen-appconds-cond-guard-aux
        (1- k) old$ conditions$ state acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appconds-new-guard
  ((old$ symbolp)
   (conditions$ pseudo-term-listp)
   (news pseudo-term-listp)
   state)
  :guard (equal (len news) (1+ (len conditions$)))
  :returns (appconds "An @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions
          @('new1-guard'), ..., @('newp-guard'), @('new0-guard'),
          in that order."
  (append (casesplit-gen-appconds-new-guard-aux (len conditions$)
                                                old$
                                                conditions$
                                                news
                                                state
                                                nil)
          (list (casesplit-gen-appcond-new-guard
                 0 old$ conditions$ news state)))

  :prepwork
  ((define casesplit-gen-appconds-new-guard-aux
     ((k natp)
      (old$ symbolp)
      (conditions$
       pseudo-term-listp)
      (news pseudo-term-listp)
      state
      (acc symbol-alistp))
     :guard (and (= (len news) (1+ (len conditions$)))
                 (<= k (len conditions$)))
     :returns appconds ; EVMAC-APPCOND-LISTP
     :mode :program
     (b* (((when (zp k)) acc)
          (appcond (casesplit-gen-appcond-new-guard
                    k old$ conditions$ news state))
          (acc (cons appcond acc)))
       (casesplit-gen-appconds-new-guard-aux
        (1- k) old$ conditions$ news state acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-appconds ((old$ symbolp)
                                (conditions$ pseudo-term-listp)
                                (hyps pseudo-term-listp)
                                (news pseudo-term-listp)
                                (verify-guards$ booleanp)
                                state)
  :guard (and (= (len hyps) (1+ (len conditions$)))
              (= (len news) (1+ (len conditions$))))
  :returns (appconds "An @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions
          that are present for the current call of the transformation,
          in the order given in the reference documentation."
  (if verify-guards$
      (append (casesplit-gen-appconds-thm-hyp
               conditions$ hyps (w state))
              (casesplit-gen-appconds-cond-guard
               old$ conditions$ state)
              (casesplit-gen-appconds-new-guard
               old$ conditions$ news state))
    (casesplit-gen-appconds-thm-hyp conditions$ hyps (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-new-fn ((old$ symbolp)
                              (conditions$ pseudo-term-listp)
                              (news pseudo-term-listp)
                              (new-name$ symbolp)
                              (new-enable$ booleanp)
                              (verify-guards$ booleanp)
                              (appcond-thm-names symbol-symbol-alistp)
                              (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the new function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the new function is determined by
     whether the new function must be enabled or not.")
   (xdoc::p
    "The new function has the same formal arguments as the old function.")
   (xdoc::p
    "The body of the new function is obtained
     as shown in the reference documentation.
     Starting with the term @('new0'),
     we recursively wrap the term with @('(if condk newk ...)'),
     thus creating a nest of @(tsee if)s that, when untranslated,
     have the @(tsee cond) structure described in the reference documentation
     (except when @('p') is 1,
     in which case the @(tsee if) remains an @(tsee if),
     which seems appropriate anyhow).
     The new function is never recursive,
     so it needs no measure, well-founded relation, or termination hints.")
   (xdoc::p
    "The new function has the same guard as the old function.")
   (xdoc::p
    "The guards are verified as shown in the template file.
     The @('appcond-thm-names') alist is in the same order
     as the applicability conditions are listed in the reference documentation,
     so we remove the first @('p') elements to obtain
     the applicability condition theorem names to use in the guard hints.
     We also use the guard theorem of @('old'),
     which may be needed to discharge the guard obligations
     within the guard term of @('old')."))
  (b* ((macro (function-intro-macro new-enable$ nil))
       (formals (formals old$ wrld))
       (new0 (car (last news)))
       (body
        (casesplit-gen-new-fn-body (len conditions$) conditions$ news new0))
       (body (untranslate body nil wrld))
       (guard (uguard old$ wrld))
       (guard-appcond-thm-names (nthcdr (len news) appcond-thm-names))
       (guard-hints? (and verify-guards$
                          `(("Goal"
                             :in-theory nil
                             :use (,@(strip-cdrs guard-appcond-thm-names)
                                   (:guard-theorem ,old$))))))
       (local-event
        `(local
          (,macro ,new-name$ (,@formals)
                  (declare (xargs
                            :guard ,guard
                            :verify-guards ,verify-guards$
                            ,@(if verify-guards$
                                  (list :guard-hints guard-hints?)
                                nil)))
                  ,body)))
       (exported-event
        `(,macro ,new-name$ (,@formals)
                 (declare (xargs :guard ,guard
                                 :verify-guards ,verify-guards$))
                 ,body)))
    (mv local-event exported-event))

  :prepwork
  ((local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
   (define casesplit-gen-new-fn-body ((k natp)
                                      (conditions$ pseudo-term-listp)
                                      (news pseudo-term-listp)
                                      (acc pseudo-termp))
     :returns (term pseudo-termp :hyp (and (pseudo-termp acc)
                                           (pseudo-term-listp conditions$)
                                           (pseudo-term-listp news)))
     :parents nil
     (b* (((when (zp k)) acc)
          (condk (nth (1- k) conditions$))
          (newk (nth (1- k) news))
          (acc `(if ,condk ,newk ,acc)))
       (casesplit-gen-new-fn-body (1- k) conditions$ news acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-old-to-new-thm ((old$ symbolp)
                                      (theorems$ symbol-listp)
                                      (new-name$ symbolp)
                                      (thm-name$ symbolp)
                                      (thm-enable$ booleanp)
                                      (appcond-thm-names symbol-symbol-alistp)
                                      (new-unnorm-name symbolp)
                                      (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the old and new functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the theorem is determined by
     whether the theorem must be enabled or not.")
   (xdoc::p
    "The formula of the theorem equates old and new function.")
   (xdoc::p
    "The theorem is proved as shown in the template file.
     The @('appcond-thm-names') alist is in the same order
     as the applicability conditions are listed in the reference documentation,
     so we take the first @('p') elements to obtain
     the applicability condition theorem names to use in the guard hints;
     note that, if @('verify-guards$') is @('nil'),
     these are all the applicability conditions,
     because there are no guard-related applicability conditions.
     We also use the theorem names specified in the @('theorems') input."))
  (b* ((macro (theorem-intro-macro thm-enable$))
       (formals (formals old$ wrld))
       (formula `(equal (,old$ ,@formals)
                        (,new-name$ ,@formals)))
       (formula (untranslate formula t wrld))
       (thm-hyp-appcond-thm-names (take (len theorems$)
                                        appcond-thm-names))
       (hints `(("Goal"
                 :in-theory '(,new-unnorm-name)
                 :use (,@(strip-cdrs thm-hyp-appcond-thm-names)
                       ,@theorems$))))
       (local-event `(local
                      (,macro ,thm-name$
                              ,formula
                              :hints ,hints)))
       (exported-event `(,macro ,thm-name$
                                ,formula)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-gen-everything ((old$ symbolp)
                                  (conditions$ pseudo-term-listp)
                                  (theorems$ symbol-listp)
                                  (hyps pseudo-term-listp)
                                  (news pseudo-term-listp)
                                  (new-name$ symbolp)
                                  (new-enable$ booleanp)
                                  (thm-name$ symbolp)
                                  (thm-enable$ booleanp)
                                  (verify-guards$ booleanp)
                                  (hints$ symbol-alistp)
                                  (print$ evmac-input-print-p)
                                  (show-only$ booleanp)
                                  (call pseudo-event-formp)
                                  ctx
                                  state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :short "Generate the top-level event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a @(tsee progn) that consists of
     the expansion of @(tsee casesplit) (the @(tsee encapsulate)),
     followed by an event to extend the transformation table,
     optionally followed by events to print the exported events
     (if specified by the @(':print') input).
     The @(tsee progn) ends with @(':invisible')
     to avoid printing a return value.")
   (xdoc::p
    "The @(tsee encapsulate) starts with some implicitly local events to
     ensure logic mode and
     avoid errors due to
     ignored or irrelevant formals in the generated function.
     Other implicitly local events remove any default and override hints,
     to prevent such hints from sabotaging the generated proofs;
     this removal is done after proving the applicability conditions,
     in case their proofs rely on the default or override hints.")
   (xdoc::p
    "The @(tsee encapsulate) also includes events
     to locally install the non-normalized definition
     of the new function,
     because the generated proofs are based on the unnormalized body.")
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
  (b* ((wrld (w state))
       (names-to-avoid (list new-name$ thm-name$))
       (appconds (casesplit-gen-appconds old$
                                         conditions$
                                         hyps
                                         news
                                         verify-guards$
                                         state))
       ((er (list appcond-thm-events
                  appcond-thm-names
                  names-to-avoid))
        (evmac-appcond-theorems-no-extra-hints
         appconds hints$ names-to-avoid print$ ctx state))
       ((mv new-fn-local-event
            new-fn-exported-event) (casesplit-gen-new-fn
            old$
            conditions$
            news
            new-name$
            new-enable$
            verify-guards$
            appcond-thm-names
            wrld))
       ((mv new-unnorm-event
            new-unnorm-name) (install-not-normalized-event new-name$
            t
            names-to-avoid
            wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event) (casesplit-gen-old-to-new-thm
            old$
            theorems$
            new-name$
            thm-name$
            thm-enable$
            appcond-thm-names
            new-unnorm-name
            wrld))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@appcond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,new-fn-local-event
                             ,new-unnorm-event
                             ,old-to-new-thm-local-event
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        (value '(value-triple :invisible)))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print$ '(:result :info :all))
                      `(,@(and (member-eq print$ '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-fn-exported-event)
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)))))
    (value
     `(progn
        ,encapsulate+
        ,transformation-table-event
        ,@print-result
        (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define casesplit-fn (old
                      conditions
                      theorems
                      new-name
                      new-enable
                      thm-name
                      thm-enable
                      verify-guards
                      hints
                      print
                      show-only
                      (call pseudo-event-formp)
                      ctx
                      state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (casesplit-implementation)
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
                  conditions$
                  hyps
                  news
                  new-name$
                  new-enable$
                  thm-name$
                  verify-guards$
                  hints$)) (casesplit-process-inputs old
                                                     conditions
                                                     theorems
                                                     new-name
                                                     new-enable
                                                     thm-name
                                                     thm-enable
                                                     verify-guards
                                                     hints
                                                     print
                                                     show-only
                                                     ctx state))
       ((er event) (casesplit-gen-everything old$
                                             conditions$
                                             theorems
                                             hyps
                                             news
                                             new-name$
                                             new-enable$
                                             thm-name$
                                             thm-enable
                                             verify-guards$
                                             hints$
                                             print
                                             show-only
                                             call
                                             ctx
                                             state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection casesplit-macro-definition
  :parents (casesplit-implementation)
  :short "Definition of the @(tsee casesplit) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee casesplit-fn).")
   (xdoc::@def "casesplit"))
  (defmacro casesplit (&whole
                       call
                       ;; mandatory inputs:
                       old
                       conditions
                       theorems
                       ;; optional inputs:
                       &key
                       (new-name ':auto)
                       (new-enable ':auto)
                       (thm-name ':auto)
                       (thm-enable 't)
                       (verify-guards ':auto)
                       (hints 'nil)
                       (print ':result)
                       (show-only 'nil))
    `(make-event-terse (casesplit-fn ',old
                                     ',conditions
                                     ',theorems
                                     ',new-name
                                     ',new-enable
                                     ',thm-name
                                     ',thm-enable
                                     ',verify-guards
                                     ',hints
                                     ',print
                                     ',show-only
                                     ',call
                                     (cons 'casesplit ',old)
                                     state)
                       :suppress-errors ,(not print))))
