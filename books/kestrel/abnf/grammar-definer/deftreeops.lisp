; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-parser/executable")
(include-book "../notation/syntax-abstraction")

(include-book "kestrel/error-checking/ensure-value-is-constant-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "std/lists/len" :dir :system)
(include-book "kestrel/std/system/constant-value" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel alistp-when-symbol-alistp
  (implies (symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 deftreeops

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input "grammar")

  (xdoc::evmac-topic-implementation-item-input "prefix")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ deftreeops-table
  :parents (deftreeops-implementation)
  :short "Table of @(tsee deftreeops) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for detecting redundant calls."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deftreeops-table-definition
  :short "Definition of the table of @(tsee deftreeops) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the calls themselves as keys,
     and nothing (i.e. @('nil')) as values.
     We only need to check if
     a call has already been successfully made or not;
     the table is like a set of calls."))

  (table deftreeops-table nil nil
    :guard (and (pseudo-event-formp acl2::key)
                (null acl2::val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-table-lookup ((call pseudo-event-formp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "Look up a @(tsee deftreeops) call in the table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns a boolean, saying whether the call is in the table or not."))
  (consp (assoc-equal call (table-alist+ 'deftreeops-table wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-table-add ((call pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Event to record a @(tsee deftreeops) call in the table."
  `(table deftreeops-table ',call nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing deftreeops)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-grammar (grammar (ctx ctxp) state)
  :returns (mv erp (grammar acl2::symbolp) state)
  :short "Process the @('*grammar*') input."
  (b* (((er &) (ensure-value-is-constant-name$ grammar
                                               "The *GRAMMAR* input"
                                               t
                                               nil))
       (rules (constant-value grammar (w state)))
       ((unless (and (rulelistp rules)
                     (consp rules)))
        (er-soft+ ctx t nil
                  "The *GRAMMAR* input is the name of a constant, ~
                   but its value ~x0 is not a non-empty ABNF grammar."
                  rules)))
    (value grammar))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-constant-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-prefix (prefix (ctx ctxp) state)
  :returns (mv erp (prefix acl2::symbolp) state)
  :short "Process the @(':prefix') input."
  (b* (((er &) (ensure-value-is-symbol$ prefix "The :PREFIX input" t nil)))
    (value prefix))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-symbol)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *deftreeops-allowed-options*
  :short "Keyword options accepted by @(tsee deftreeops)."
  (list :prefix)
  ///
  (assert-event (keyword-listp *deftreeops-allowed-options*))
  (assert-event (no-duplicatesp-eq *deftreeops-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-inputs ((args true-listp) (ctx ctxp) state)
  :returns (mv erp
               (val (std::tuple (grammar acl2::symbolp)
                                (prefix acl2::symbolp)
                                val))
               state)
  :short "Process all the inputs."
  (b* (((fun (irr)) (list nil nil))
       ((mv erp grammar options)
        (partition-rest-and-keyword-args args *deftreeops-allowed-options*))
       ((when (or erp
                  (not (consp grammar))
                  (not (endp (cdr grammar)))))
        (er-soft+ ctx t (irr)
                  "The inputs must be the constant name for the grammar ~
                   followed by the options ~&0."
                  *deftreeops-allowed-options*))
       (grammar (car grammar))
       ((er grammar :iferr (irr))
        (deftreeops-process-grammar grammar ctx state))
       (prefix-option (assoc-eq :prefix options))
       ((unless (consp prefix-option))
        (er-soft+ ctx t (irr) "The :PREFIX input must be supplied."))
       (prefix (cdr prefix-option))
       ((er prefix :iferr (irr))
        (deftreeops-process-prefix prefix ctx state)))
    (value (list grammar prefix)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation deftreeops)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-match ((grammar acl2::symbolp)
                                  (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the first of the specialized matching predicates."
  (b* ((cst-matchp (add-suffix-to-fn prefix "-MATCHP"))
       (cst-matchp$ (add-suffix-to-fn cst-matchp "$")))
    `((define ,cst-matchp$ ((tree treep) (elem elementp))
        :returns (yes/no booleanp)
        (and (tree-terminatedp tree)
             (tree-match-element-p tree elem ,grammar))
        :hooks (:fix))
      (defmacro ,cst-matchp (tree elem)
        (declare (xargs :guard (acl2::stringp elem)))
        (b* (((mv err elem rest)
              (parse-element (string=>nats elem)))
             ((when err) (er hard ',cst-matchp "~@0" err))
             ((when (consp rest))
              (er hard ',cst-matchp
                  "Extra: ~s0" (nats=>string rest)))
             (elem (abstract-element elem)))
          `(,',cst-matchp$ ,tree ',elem)))
      (table acl2::macro-aliases-table
        ',cst-matchp
        ',cst-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-list-elem-match ((grammar acl2::symbolp)
                                            (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the second of the specialized matching predicates."
  (b* ((cst-list-elem-matchp (add-suffix-to-fn prefix "-LIST-ELEM-MATCHP"))
       (cst-list-elem-matchp$ (add-suffix-to-fn cst-list-elem-matchp "$")))
    `((define ,cst-list-elem-matchp$ ((trees tree-listp) (elem elementp))
        :returns (yes/no booleanp)
        (and (tree-list-terminatedp trees)
             (tree-list-match-element-p trees elem ,grammar))
        :hooks (:fix))
      (defmacro ,cst-list-elem-matchp (trees elem)
        (declare (xargs :guard (acl2::stringp elem)))
        (b* (((mv err elem rest)
              (parse-element (string=>nats elem)))
             ((when err) (er hard ',cst-list-elem-matchp "~@0" err))
             ((when (consp rest))
              (er hard ',cst-list-elem-matchp
                  "Extra: ~s0" (nats=>string rest)))
             (elem (abstract-element elem)))
          `(,',cst-list-elem-matchp$ ,trees ',elem)))
      (table acl2::macro-aliases-table
        ',cst-list-elem-matchp
        ',cst-list-elem-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-list-rep-match ((grammar acl2::symbolp)
                                           (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the third of the specialized matching predicates."
  (b* ((cst-list-rep-matchp (add-suffix-to-fn prefix "-LIST-REP-MATCHP"))
       (cst-list-rep-matchp$ (add-suffix-to-fn cst-list-rep-matchp "$")))
    `((define ,cst-list-rep-matchp$ ((trees tree-listp) (rep repetitionp))
        :returns (yes/no booleanp)
        (and (tree-list-terminatedp trees)
             (tree-list-match-repetition-p trees rep ,grammar))
        :hooks (:fix))
      (defmacro ,cst-list-rep-matchp (trees rep)
        (declare (xargs :guard (acl2::stringp rep)))
        (b* (((mv err rep rest)
              (parse-repetition (string=>nats rep)))
             ((when err) (er hard ',cst-list-rep-matchp "~@0" err))
             ((when (consp rest))
              (er hard ',cst-list-rep-matchp
                  "Extra: ~s0" (nats=>string rest)))
             (rep (abstract-repetition rep)))
          `(,',cst-list-rep-matchp$ ,trees ',rep)))
      (table acl2::macro-aliases-table
        ',cst-list-rep-matchp
        ',cst-list-rep-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-list-list-conc-match ((grammar acl2::symbolp)
                                                 (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the fourth of the specialized matching predicates."
  (b* ((cst-list-list-conc-matchp
        (add-suffix-to-fn prefix "-LIST-LIST-CONC-MATCHP"))
       (cst-list-list-conc-matchp$
        (add-suffix-to-fn cst-list-list-conc-matchp "$")))
    `((define ,cst-list-list-conc-matchp$ ((treess tree-list-listp)
                                           (conc concatenationp))
        :returns (yes/no booleanp)
        (and (tree-list-list-terminatedp treess)
             (tree-list-list-match-concatenation-p treess conc ,grammar))
        :hooks (:fix))
      (defmacro ,cst-list-list-conc-matchp (treess conc)
        (declare (xargs :guard (acl2::stringp conc)))
        (b* (((mv err conc rest)
              (parse-concatenation (string=>nats conc)))
             ((when err) (er hard ',cst-list-list-conc-matchp "~@0" err))
             ((when (consp rest))
              (er hard ',cst-list-list-conc-matchp
                  "Extra: ~s0" (nats=>string rest)))
             (conc (abstract-concatenation conc)))
          `(,',cst-list-list-conc-matchp$ ,treess ',conc)))
      (table acl2::macro-aliases-table
        ',cst-list-list-conc-matchp
        ',cst-list-list-conc-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-list-list-alt-match ((grammar acl2::symbolp)
                                                (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the fifth of the specialized matching predicates."
  (b* ((cst-list-list-alt-matchp
        (add-suffix-to-fn prefix "-LIST-LIST-ALT-MATCHP"))
       (cst-list-list-alt-matchp$
        (add-suffix-to-fn cst-list-list-alt-matchp "$")))
    `((define ,cst-list-list-alt-matchp$ ((treess tree-list-listp)
                                          (alt alternationp))
        :returns (yes/no booleanp)
        (and (tree-list-list-terminatedp treess)
             (tree-list-list-match-alternation-p treess alt ,grammar))
        :hooks (:fix))
      (defmacro ,cst-list-list-alt-matchp (treess alt)
        (declare (xargs :guard (acl2::stringp alt)))
        (b* (((mv err alt rest)
              (parse-alternation (string=>nats alt)))
             ((when err) (er hard ',cst-list-list-alt-matchp "~@0" err))
             ((when (consp rest))
              (er hard ',cst-list-list-alt-matchp
                  "Extra: ~s0" (nats=>string rest)))
             (alt (abstract-alternation alt)))
          `(,',cst-list-list-alt-matchp$ ,treess ',alt)))
      (table acl2::macro-aliases-table
        ',cst-list-list-alt-matchp
        ',cst-list-list-alt-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-matchers ((grammar acl2::symbolp)
                                 (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the specialized matching predicates."
  (append (deftreeops-gen-cst-match grammar prefix)
          (deftreeops-gen-cst-list-elem-match grammar prefix)
          (deftreeops-gen-cst-list-rep-match grammar prefix)
          (deftreeops-gen-cst-list-list-conc-match grammar prefix)
          (deftreeops-gen-cst-list-list-alt-match grammar prefix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-everything ((grammar acl2::symbolp)
                                   (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  (b* ((matchers (deftreeops-gen-matchers grammar prefix))
       (event `(defsection ,(add-suffix grammar "-TREE-OPERATIONS")
                 :parents (,grammar)
                 :short ,(str::cat
                          "Tree operations specialized to @(tsee "
                          (str::downcase-string (symbol-name grammar))
                          ").")
                 ,@matchers)))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-fn ((args true-listp)
                       (call pseudo-event-formp)
                       (ctx ctxp)
                       state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (deftreeops-implementation)
  :short "Process the inputs and generate the events."
  (b* (((when (deftreeops-table-lookup call (w state)))
        (value '(value-triple :redundant)))
       ((er (list grammar prefix) :iferr '(_))
        (deftreeops-process-inputs args ctx state)))
    (value (deftreeops-gen-everything grammar prefix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deftreeops-macro-definition
  :parents (deftreeops-implementation)
  :short "Definition of the @(tsee deftreeops) macro."
  (defmacro deftreeops (&whole call &rest args)
    `(make-event (deftreeops-fn ',args ',call 'deftreeops state))))
