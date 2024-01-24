; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-parser/executable")
(include-book "../grammar-printer/executable")
(include-book "../notation/syntax-abstraction")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/std/system/constant-namep" :dir :system)
(include-book "kestrel/std/system/constant-value" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/error-value-tuples" :dir :system)
(include-book "std/typed-alists/string-symbol-alistp" :dir :system)
(include-book "std/typed-alists/string-symbollist-alistp" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 deftreeops

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input "grammar")

  (xdoc::evmac-topic-implementation-item-input "prefix"))

 :additional

 ((xdoc::p
   "The generation of the functions and theorems happens in two passes.
    In the first pass, we go through all the rule names defined by the rules,
    and generate some functions and theorems for each rule name
    that only depend on the rules that define the rule name and not others
    (i.e. those functions and theorems can be generated
    for each rule name independently from the others).
    In the second pass, we go again through all the rule names defined by rules,
    and generate more functions and theorems
    that may depend on functions and theorems for other rule names,
    generated during the first pass.
    The passes are indicated by @('pass1') and @('pass2') suffixes
    in the function names of the implementation.")))

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

(define deftreeops-process-grammar (grammar (wrld plist-worldp))
  :returns (mv erp
               (grammar acl2::symbolp)
               (rules rulelistp))
  :short "Process the @('*grammar*') input."
  (b* (((reterr) nil nil)
       ((unless (constant-namep grammar wrld))
        (reterr (msg "The *GRAMMAR* input ~x0 must be the name of a constant."
                     grammar)))
       (rules (constant-value grammar wrld))
       ((unless (and (rulelistp rules)
                     (consp rules)))
        (reterr (msg "The *GRAMMAR* input is the name of a constant, ~
                      but its value ~x0 is not a non-empty ABNF grammar."
                     rules))))
    (retok grammar rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-prefix (prefix)
  :returns (mv erp (prefix acl2::symbolp))
  :short "Process the @(':prefix') input."
  (b* (((reterr) nil)
       ((unless (acl2::symbolp prefix))
        (reterr (msg "The :PREFIX input ~x0 must be a symbol." prefix))))
    (retok prefix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *deftreeops-allowed-options*
  :short "Keyword options accepted by @(tsee deftreeops)."
  (list :prefix)
  ///
  (assert-event (keyword-listp *deftreeops-allowed-options*))
  (assert-event (no-duplicatesp-eq *deftreeops-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-inputs ((args true-listp) (wrld plist-worldp))
  :returns (mv erp
               (grammar acl2::symbolp)
               (rules rulelistp)
               (prefix acl2::symbolp))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil)
       ((mv erp grammar options)
        (partition-rest-and-keyword-args args *deftreeops-allowed-options*))
       ((when (or erp
                  (not (consp grammar))
                  (not (endp (cdr grammar)))))
        (reterr (msg "The inputs must be the constant name for the grammar ~
                      followed by the options ~&0."
                     *deftreeops-allowed-options*)))
       (grammar (car grammar))
       ((erp grammar rules) (deftreeops-process-grammar grammar wrld))
       (prefix-option (assoc-eq :prefix options))
       ((unless (consp prefix-option))
        (reterr (msg "The :PREFIX input must be supplied.")))
       (prefix (cdr prefix-option))
       ((erp prefix) (deftreeops-process-prefix prefix)))
    (retok grammar rules prefix))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation deftreeops)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-match-pred ((prefix acl2::symbolp))
  :returns (pred acl2::symbolp)
  :short "Name of the @('<prefix>-matchp') predicate."
  (add-suffix-to-fn prefix "-MATCHP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-elem-match-pred ((prefix acl2::symbolp))
  :returns (pred acl2::symbolp)
  :short "Name of the @('<prefix>-list-elem-matchp') predicate."
  (add-suffix-to-fn prefix "-LIST-ELEM-MATCHP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-rep-match-pred ((prefix acl2::symbolp))
  :returns (pred acl2::symbolp)
  :short "Name of the @('<prefix>-list-rep-matchp') predicate."
  (add-suffix-to-fn prefix "-LIST-REP-MATCHP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-conc-match-pred ((prefix acl2::symbolp))
  :returns (pred acl2::symbolp)
  :short "Name of the @('<prefix>-list-list-conc-matchp') predicate."
  (add-suffix-to-fn prefix "-LIST-LIST-CONC-MATCHP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-alt-match-pred ((prefix acl2::symbolp))
  :returns (pred acl2::symbolp)
  :short "Name of the @('<prefix>-list-list-alt-matchp') predicate."
  (add-suffix-to-fn prefix "-LIST-LIST-ALT-MATCHP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-cst-match ((grammar acl2::symbolp)
                                  (prefix acl2::symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the first of the specialized matching predicates."
  (b* ((cst-matchp (deftreeops-match-pred prefix))
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
  (b* ((cst-list-elem-matchp (deftreeops-elem-match-pred prefix))
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
  (b* ((cst-list-rep-matchp (deftreeops-rep-match-pred prefix))
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
  (b* ((cst-list-list-conc-matchp (deftreeops-conc-match-pred prefix))
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
  (b* ((cst-list-list-alt-matchp (deftreeops-alt-match-pred prefix))
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

(fty::defprod deftreeops-rep-info
  :short "Fixtype of @(tsee deftreeops) information about
          a repetition of an alternative of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This information consists of:")
   (xdoc::ul
    (xdoc::li
     "The name of the generated function
      that takes as input a tree that matches the rule name
      whose branches match the alternative,
      and that returns as output
      the list of trees that match the repetition of the alternative.")
    (xdoc::li
     "The name of the generated function
      that takes as input a tree that matches the rule name
      whose branches match the alternative,
      and that returns as output one of the trees in
      the list of trees that match the repetition of the alternative.")
    (xdoc::li
     "The name of the generated theorem saying that
      if a list of trees matches the repetition of the alternative of the rule
      then its length is within the repetition range
      and all its trees match the repetition's element.")))
  ((get-tree-list-fn acl2::symbol)
   (get-tree-fn acl2::symbol)
   (match-thm acl2::symbol))
  :pred deftreeops-rep-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist deftreeops-rep-info-list
  :short "Fixtype of @(tsee deftreeops) information about
          the list of repetitions that form an alternative of a rule."
  :elt-type deftreeops-rep-info
  :true-listp t
  :elementp-of-nil nil
  :pred deftreeops-rep-info-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod deftreeops-alt-info
  :short "Fixtype of @(tsee deftreeops) information about
          an alternative of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This information consists of:")
   (xdoc::ul
    (xdoc::li
     "A generated term over the branches of the tree
      (where the tree matches the rule name)
      that discriminates the alternative among the possible alternatives.
      This is @('nil') if the rule has just one alternative.")
    (xdoc::li
     "The name of the generated function
      that takes as input a tree that matches the rule name
      whose branches match the alternative,
      and that returns as output
      the list of lists of trees that match the alternative.")
    (xdoc::li
     "The name of the generated theorem saying that
      if a list of lists of trees matches the alternative of the rule
      then its length is the length of the alternative
      and each list of trees in the list matches the corresponding repetition.")
    (xdoc::li
     "The information about the repetitions that form the alternative.")))
  ((discriminant-term "A term.")
   (get-tree-list-list-fn acl2::symbol)
   (match-thm acl2::symbol)
   (rep-infos deftreeops-rep-info-list))
  :pred deftreeops-alt-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist deftreeops-alt-info-list
  :short "Fixtype of @(tsee deftreeops) information about
          the list of alternatives of a rule."
  :elt-type deftreeops-alt-info
  :true-listp t
  :elementp-of-nil nil
  :pred deftreeops-alt-info-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod deftreeops-rulename-info
  :short "Fixtype of @(tsee deftreeops) information about a rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This information consists of:")
   (xdoc::ul
    (xdoc::li
     "The name of the generated theorem saying that
      if a tree matches the rule name
      then it is a non-leaf tree.")
    (xdoc::li
     "The name of the generated theorem saying that
      if a tree matches the rule name
      then its rule name is that rule name.")
    (xdoc::li
     "The name of the generated theorem saying that
      if a tree matches the rule name
      then its branches match the alternation that defines the rule name.")
    (xdoc::li
     "The name of the generated theorem saying that
      if a list of lists of trees
      match the alternation that defines the rule name
      then the list of lists of trees matches one of the alternatives;
      this is a disjunctive theorem, unless there is just one alternative.")
    (xdoc::li
     "The name of the generated theorem saying that
      the fact that a list of lists of trees matches
      an alternative that defines the rule name
      is equivalent to a term over the list of lists of trees
      that discriminates the alternative from the others;
      this is the @('discriminant-term') in @(tsee deftreeops-alt-info).
      This theorem is a conjunction of
      an equivalence for each alternative that defines the rule name.")
    (xdoc::li
     "The name of the generated function
      that takes as input a tree that matches the rule name
      and returns as output a positive integer
      indicating the alternative matched by the branches of the tree.")
    (xdoc::li
     "The information about the alternatives that define the rule name.")))
  ((nonleaf-thm acl2::symbol)
   (rulename-thm acl2::symbol)
   (match-thm acl2::symbol)
   (alt-disj-thm acl2::symbol)
   (alt-equiv-thm acl2::symbol)
   (check-alt-fn acl2::symbol)
   (alt-infos deftreeops-alt-info-list))
  :pred deftreeops-rulename-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist deftreeops-rulename-info-alist
  :short "Fixtype of alists from rule names to information about rule names."
  :key-type rulename
  :val-type deftreeops-rulename-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred deftreeops-rulename-info-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rep-fns+thms+info
  ((rep repetitionp)
   (i posp "Indentifies the alternative, starting from 1.")
   (rulename-upstring acl2::stringp "Rule name normalized in uppercase.")
   (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-rep-infop))
  :short "Generate the functions and theorems and information for
          a repetition of an alternative of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate some of these,
     namely the matching theorem.
     For now, we generate it only if the repetition
     consists of exactly one element."))
  (b* (((unless (equal (repetition->range rep)
                       (make-repeat-range :min 1 :max (nati-finite 1))))
        (mv nil
            (make-deftreeops-rep-info
             :get-tree-list-fn nil
             :get-tree-fn nil
             :match-thm nil)))
       (match-thm (packn-pos
                   (list prefix '-match-alt i '-rep1- rulename-upstring)
                   prefix))
       (rep-match (deftreeops-rep-match-pred prefix))
       (match (deftreeops-match-pred prefix))
       (elem (repetition->element rep))
       (match-thm-event
        `(defruled ,match-thm
           (implies (,rep-match csts
                                ,(pretty-print-repetition rep))
                    (and (equal (len csts) 1)
                         (,match (nth 0 csts)
                                 ,(pretty-print-element elem))))
           :in-theory
           '(,rep-match
             ,match
             tree-list-match-repetition-p-of-1-repetition
             tree-terminatedp-of-car-when-tree-list-terminatedp
             (:e nati-finite)
             (:e repeat-range)
             (:e repetition->element)
             (:e repetition->range)
             nth
             (:e zp)
             len)))
       (info (make-deftreeops-rep-info
              :get-tree-list-fn nil
              :get-tree-fn nil
              :match-thm match-thm)))
    (mv (list match-thm-event) info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rep-fns+thms+info-list ((conc concatenationp)
                                               (i posp)
                                               (rulename-upstring acl2::stringp)
                                               (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (infos deftreeops-rep-info-listp))
  :short "Lift @(tsee deftreeops-gen-rep-fns+thms+info) to
          lists of repetitions, i.e. to concatenations."
  (b* (((when (endp conc)) (mv nil nil))
       ((mv events info)
        (deftreeops-gen-rep-fns+thms+info
          (car conc) i rulename-upstring prefix))
       ((mv more-events more-info)
        (deftreeops-gen-rep-fns+thms+info-list
          (cdr conc) i rulename-upstring prefix)))
    (mv (append events more-events)
        (cons info more-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-alt-fns+thms+info ((conc concatenationp)
                                          (i posp)
                                          (discriminant-term "A term.")
                                          (rulename-upstring acl2::stringp)
                                          (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-alt-infop))
  :short "Generate the functions and theorems and information for
          an alternative of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate some of these,
     namely the matching theorem.
     For now, we generate it only if the concatenation
     consists of exactly one repetition."))
  (b* (((unless (and (consp conc)
                     (endp (cdr conc))))
        (mv nil
            (make-deftreeops-alt-info
             :discriminant-term nil
             :get-tree-list-list-fn nil
             :match-thm nil
             :rep-infos nil)))
       (match-thm (packn-pos (list prefix '-match-alt i '- rulename-upstring)
                             prefix))
       (conc-match (deftreeops-conc-match-pred prefix))
       (rep-match (deftreeops-rep-match-pred prefix))
       (rep (car conc))
       (match-thm-event
        `(defruled ,match-thm
           (implies (,conc-match cstss
                                 ,(pretty-print-concatenation conc))
                    (and (equal (len cstss) 1)
                         (,rep-match (nth 0 cstss)
                                     ,(pretty-print-repetition rep))))
           :in-theory
           '(,conc-match
             ,rep-match
             tree-list-list-match-concatenation-p-when-atom-concatenation
             tree-list-list-match-concatenation-p-of-cons-concatenation
             tree-list-terminatedp-of-car-when-tree-list-list-terminatedp
             nth
             (:e zp)
             len)))
       ((mv rep-events rep-infos)
        (deftreeops-gen-rep-fns+thms+info-list conc i rulename-upstring prefix))
       (info (make-deftreeops-alt-info
              :discriminant-term discriminant-term
              :get-tree-list-list-fn nil
              :match-thm match-thm
              :rep-infos rep-infos)))
    (mv (append (list match-thm-event)
                rep-events)
        info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-alt-fns+thms+info-list
  ((alt alternationp)
   (discriminant-terms "A list of terms.")
   (rulename-upstring acl2::stringp)
   (prefix acl2::symbolp))
  :guard (equal (len discriminant-terms) (len alt))
  :returns (mv (events pseudo-event-form-listp)
               (infos deftreeops-alt-info-listp))
  :short "Lift @(tsee deftreeops-gen-alt-fns+thms+info)
          to lists of concatenations, i.e. to alternatives."
  (deftreeops-gen-alt-fns+thms+info-list-aux
    alt 1 discriminant-terms rulename-upstring prefix)

  :prepwork
  ((define deftreeops-gen-alt-fns+thms+info-list-aux
     ((alt alternationp)
      (i posp)
      (discriminant-terms "A list of terms.")
      (rulename-upstring acl2::stringp)
      (prefix acl2::symbolp))
     :guard (equal (len discriminant-terms) (len alt))
     :returns (mv (events pseudo-event-form-listp)
                  (infos deftreeops-alt-info-listp))
     :parents nil
     (b* (((when (endp alt)) (mv nil nil))
          ((mv events info)
           (deftreeops-gen-alt-fns+thms+info
             (car alt)
             i
             (car discriminant-terms)
             rulename-upstring
             prefix))
          ((mv more-events more-info)
           (deftreeops-gen-alt-fns+thms+info-list-aux
             (cdr alt)
             (1+ i)
             (cdr discriminant-terms)
             rulename-upstring
             prefix)))
       (mv (append events more-events)
           (cons info more-info))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-discriminant-terms ((alt alternationp))
  :returns (mv (okp booleanp) (terms pseudo-term-listp))
  :short "Generate the terms to discriminate among
          two or more alternatives defining a rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support alternations of certain forms.
     The first result of this function returns
     @('t') if terms are generated, @('nil') otherwise.
     The second result is the list of terms,
     of the same length as the alternation.
     If the alternation consists of just one alternative,
     we return a single term @('t'),
     which makes sense since the alternative must be always that only one.")
   (xdoc::p
    "For now we only support alternations
     each of whose alternatives are singleton concatenations
     where each such concatenation consists of
     a repetition with range 1
     whose element is a rule name."))
  (b* (((when (and (consp alt)
                   (endp (cdr alt))))
        (mv t (list acl2::*t*))))
    (deftreeops-gen-discriminant-terms-aux alt))

  :prepwork
  ((define deftreeops-gen-discriminant-terms-aux ((alt alternationp))
     :returns (mv (okp booleanp) (terms pseudo-term-listp))
     :parents nil
     (b* (((when (endp alt)) (mv t nil))
          (conc (car alt))
          ((unless (and (consp conc)
                        (endp (cdr conc))))
           (mv nil nil))
          (rep (car conc))
          ((unless (equal (repetition->range rep)
                          (make-repeat-range :min 1
                                             :max (nati-finite 1))))
           (mv nil nil))
          (elem (repetition->element rep))
          ((unless (element-case elem :rulename))
           (mv nil nil))
          (rulename (element-rulename->get elem))
          (term `(equal (tree-nonleaf->rulename
                         (nth '0 (nth '0 (tree-nonleaf->branches cst))))
                        ',rulename))
          ((mv okp terms) (deftreeops-gen-discriminant-terms-aux (cdr alt)))
          ((unless okp) (mv nil nil)))
       (mv t (cons term terms)))
     ///
     (defret len-of-deftreeops-gen-discriminant-terms-aux
       (implies okp
                (equal (len terms)
                       (len alt))))))

  ///

  (defret len-of-deftreeops-gen-discriminant-terms
    (implies okp
             (equal (len terms)
                    (len alt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rulename-fns+thms+info-pass1
  ((rulename rulenamep)
   (alt alternationp "All the alternatives that define @('rulename').")
   (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-rulename-infop))
  :short "Generate the functions and theorems and information for a rule name
          (first pass; see @(tsee deftreeops-implementation))."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an incomplete @(tsee deftreeops-rulename-infop),
     which is completed by the second pass.")
   (xdoc::p
    "For now we only generate some of the events and information,
     namely the first four theorems in @(tsee deftreeops-rulename-info)."))
  (b* ((matchp (deftreeops-match-pred prefix))
       (alt-matchp (deftreeops-alt-match-pred prefix))
       (conc-matchp (deftreeops-conc-match-pred prefix))
       (rulename-string (rulename->get rulename))
       (rulename-upstring (str::upcase-string rulename-string))
       (nonleaf-thm
        (packn-pos (list prefix '-nonleaf-when- rulename-upstring)
                   prefix))
       (rulename-thm
        (packn-pos (list prefix '-rulename-when- rulename-upstring)
                   prefix))
       (match-thm
        (packn-pos (list prefix '-branches-match-alt-when- rulename-upstring)
                   prefix))
       (alt-disj-thm
        (packn-pos (list prefix '-alternatives-when- rulename-upstring)
                   prefix))
       (alt-string (pretty-print-alternation alt))
       (events
        `((defruled ,nonleaf-thm
            (implies (,matchp cst ,rulename-string)
                     (equal (tree-kind cst) :nonleaf))
            :in-theory '(,matchp
                         tree-nonleaf-when-match-rulename/group/option
                         (:e element-kind)
                         (:e member-equal)))
          (defruled ,rulename-thm
            (implies (,matchp cst ,rulename-string)
                     (equal (tree-nonleaf->rulename? cst)
                            (rulename ,rulename-string)))
            :in-theory '(,matchp
                         tree-rulename-when-match-rulename
                         (:e element-kind)
                         (:e element-rulename->get)
                         (:e rulename)))
          (defruled ,match-thm
            (implies (,matchp cst ,rulename-string)
                     (,alt-matchp
                      (tree-nonleaf->branches cst) ,alt-string))
            :in-theory '(,matchp
                         ,alt-matchp
                         tree-branches-match-alt-when-match-rulename
                         tree-terminatedp
                         (:e element-kind)
                         (:e element-rulename->get)
                         (:e lookup-rulename))
            :use ,nonleaf-thm)
          (defruled ,alt-disj-thm
            (implies (,alt-matchp cstss ,alt-string)
                     (or ,@(deftreeops-gen-rulename-fns+thms+info-pass1-aux
                             alt conc-matchp)))
            :do-not '(preprocess)
            :in-theory
            '(,alt-matchp
              ,conc-matchp
              tree-list-list-match-alternation-p-when-atom-alternation
              tree-list-list-match-alternation-p-of-cons-alternation))))
       ((mv okp terms) (deftreeops-gen-discriminant-terms alt))
       (terms (if okp terms (repeat (len alt) nil)))
       ((mv more-events alt-infos)
        (deftreeops-gen-alt-fns+thms+info-list
          alt terms rulename-upstring prefix))
       (info (make-deftreeops-rulename-info
              :nonleaf-thm nonleaf-thm
              :rulename-thm rulename-thm
              :match-thm match-thm
              :alt-disj-thm alt-disj-thm
              :alt-equiv-thm nil
              :check-alt-fn nil
              :alt-infos alt-infos)))
    (mv (append events more-events) info))

  :prepwork
  ((define deftreeops-gen-rulename-fns+thms+info-pass1-aux
     ((alt alternationp) (conc-matchp acl2::symbolp))
     :returns (disjuncts true-listp)
     :parents nil
     (cond ((endp alt) nil)
           (t (cons `(,conc-matchp
                      cstss
                      ,(pretty-print-concatenation (car alt)))
                    (deftreeops-gen-rulename-fns+thms+info-pass1-aux
                      (cdr alt) conc-matchp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rulename-fns+thms+info-pass1-list
  ((rules rulelistp)
   (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-rulename-info-alistp))
  :short "Generate the functions and theorems and information
          for all the rule names defined in a list of rules
          (first pass; see @(tsee deftreeops-implementation))."
  :long
  (xdoc::topstring
   (xdoc::p
    "This essentially lifts @(tsee deftreeops-gen-rulename-fns+thms+info)
     to lists, but the input is a list of rules,
     from which we obtain the list of rule names defined by the rules.
     We generate the functions and theorems and information for each rule name,
     not for each rule:
     because of the possibility of incremental rules in ABNF,
     a grammar may have multiple rules with the same rule name on the left,
     each of which contributes one or more alternatives.
     We iterate through the rules,
     keeping track of which rule names have been processed,
     so that we process each defined rule name exactly once."))
  (deftreeops-gen-rulename-fns+thms+info-pass1-list-aux rules nil prefix)

  :prepwork
  ((define deftreeops-gen-rulename-fns+thms+info-pass1-list-aux
     ((rules rulelistp)
      (done rulename-listp)
      (prefix acl2::symbolp))
     :returns (mv (events pseudo-event-form-listp)
                  (info deftreeops-rulename-info-alistp))
     (b* (((when (endp rules)) (mv nil nil))
          (rule (car rules))
          (rulename (rule->name rule))
          ((when (member-equal rulename done))
           (deftreeops-gen-rulename-fns+thms+info-pass1-list-aux
             (cdr rules) done prefix))
          (alt (lookup-rulename rulename rules))
          ((mv events info)
           (deftreeops-gen-rulename-fns+thms+info-pass1 rulename alt prefix))
          ((mv more-events more-info)
           (deftreeops-gen-rulename-fns+thms+info-pass1-list-aux
             (cdr rules) (cons rulename done) prefix)))
       (mv (append events more-events)
           (acons rulename info more-info)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rulename-fns+thms+info-pass2
  ((rulename rulenamep)
   (alt alternationp "All the alternatives that define @('rulename').")
   (prefix acl2::symbolp)
   (infos deftreeops-rulename-info-alistp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-rulename-infop))
  :short "Generate the functions and theorems and information for a rule name
          (second pass; see @(tsee deftreeops-implementation))."
  :long
  (xdoc::topstring
   (xdoc::p
    "Compared to @(tsee deftreeops-gen-rulename-fns+thms+info-pass1),
     this function also takes as argument the alist @('infos'),
     which is calculated by
     @(tsee deftreeops-gen-rulename-fns+thms+info-pass1-list)
     during the first pass.")
   (xdoc::p
    "This function does nothing for now,
     but we will move and add code here soon.
     The code will make use of the @('infos') alist,
     which is why there are two passes,
     as expoained in @(tsee deftreeops-implementation)."))
  (declare (ignore alt prefix)) ; temporary
  (b* ((info (cdr (assoc-equal rulename infos)))
       ((unless info)
        (raise "Internal error: rule name ~x0 not in alist ~x1." rulename infos)
        (mv nil (ec-call (deftreeops-rulename-info-fix :irrelevant)))))
    (mv nil (deftreeops-rulename-info-fix info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-rulename-fns+thms+info-pass2-list
  ((rules rulelistp)
   (prefix acl2::symbolp)
   (infos deftreeops-rulename-info-alistp))
  :returns (mv (events pseudo-event-form-listp)
               (new-infos deftreeops-rulename-info-alistp))
  :short "Generate the functions and theorems and information
          for all the rule names defined in a list of rules
          (second pass; see @(tsee deftreeops-implementation))."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to
     @(tsee deftreeops-gen-rulename-fns+thms+info-pass2-list),
     but it also takes as input the alist @('infos') calculated by
     @(tsee deftreeops-gen-rulename-fns+thms+info-pass1-list)
     during the first pass.
     That alist has incomplete information about the rule names,
     i.e. it only contains the information for the first pass.
     Here the information is completed with the one for the second pass,
     so an updated alist is built and returned."))
  (deftreeops-gen-rulename-fns+thms+info-pass2-list-aux rules nil prefix infos)

  :prepwork
  ((define deftreeops-gen-rulename-fns+thms+info-pass2-list-aux
     ((rules rulelistp)
      (done rulename-listp)
      (prefix acl2::symbolp)
      (infos deftreeops-rulename-info-alistp))
     :returns (mv (events pseudo-event-form-listp)
                  (new-infos deftreeops-rulename-info-alistp))
     (b* (((when (endp rules)) (mv nil nil))
          (rule (car rules))
          (rulename (rule->name rule))
          ((when (member-equal rulename done))
           (deftreeops-gen-rulename-fns+thms+info-pass2-list-aux
             (cdr rules) done prefix infos))
          (alt (lookup-rulename rulename rules))
          ((mv events info)
           (deftreeops-gen-rulename-fns+thms+info-pass2
             rulename alt prefix infos))
          ((mv more-events more-info)
           (deftreeops-gen-rulename-fns+thms+info-pass2-list-aux
             (cdr rules) (cons rulename done) prefix infos)))
       (mv (append events more-events)
           (acons rulename info more-info)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-all-rulenames-fns+thms+info ((rules rulelistp)
                                                    (prefix acl2::symbolp))
  :returns (mv (events pseudo-event-form-listp)
               (info deftreeops-rulename-info-alistp))
  :short "Generate the functions and theorems and information
          for all the rule names defined in a grammar."
  (b* (((mv events preliminary-infos)
        (deftreeops-gen-rulename-fns+thms+info-pass1-list
          rules prefix))
       ((mv more-events final-infos)
        (deftreeops-gen-rulename-fns+thms+info-pass2-list
          rules prefix preliminary-infos)))
    (mv (append events more-events) final-infos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-gen-everything ((grammar acl2::symbolp)
                                   (rules rulelistp)
                                   (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  (b* ((matchers (deftreeops-gen-matchers grammar prefix))
       ((mv rulename-events
            & ; rulename-info
        )
        (deftreeops-gen-all-rulenames-fns+thms+info rules prefix))
       (event `(defsection ,(add-suffix grammar "-TREE-OPERATIONS")
                 :parents (,grammar)
                 :short ,(str::cat
                          "Tree operations specialized to @(tsee "
                          (str::downcase-string (symbol-name grammar))
                          ").")
                 ,@matchers
                 ,@rulename-events)))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-process-inputs-and-gen-everything ((args true-listp)
                                                      (call pseudo-event-formp)
                                                      (wrld plist-worldp))
  :returns (mv erp (event pseudo-event-formp))
  :parents (deftreeops-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((when (deftreeops-table-lookup call wrld))
        (retok '(value-triple :redundant)))
       ((erp grammar rules prefix) (deftreeops-process-inputs args wrld)))
    (retok (deftreeops-gen-everything grammar rules prefix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftreeops-fn ((args true-listp)
                       (call pseudo-event-formp)
                       (ctx ctxp)
                       state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (deftreeops-implementation)
  :short "Event expansion of @(tsee deftreeops)."
  (b* (((mv erp event)
        (deftreeops-process-inputs-and-gen-everything args call (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deftreeops-macro-definition
  :parents (deftreeops-implementation)
  :short "Definition of @(tsee deftreeops)."
  (defmacro deftreeops (&whole call &rest args)
    `(make-event (deftreeops-fn ',args ',call 'deftreeops state))))
