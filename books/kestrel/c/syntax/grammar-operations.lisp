; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "grammar")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-operations
  :parents (concrete-syntax)
  :short "Operations on CSTs (concrete syntax trees)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently @(tsee abnf::deftreeops) works on fixed grammars,
     while our @(see grammar) is parameterized over the dialect.
     We are defining @(tsee abnf::deftreeops)-like operations
     on our parameterized grammar;
     we may eventually extend that tool to work on parameterized grammars.")
   (xdoc::p
    "This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As an initial baseline, we use ABNF::DEFTREEOPS on
; one instance of our parameterized grammar.
; We plan to generalize this.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *grammar-c17*
  :short "Grammar constant for the C17 dialect without extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since currently @(tsee abnf::deftreeops) (used below)
     only operates on grammar constants,
     we pick a particular C dialect to start,
     defining a grammar constant for it.
     We plan to generalize @(tsee abnf::deftreeops)
     to operate on parameterized grammars,
     specifically a function like @(tsee grammar-for)."))
  (grammar-for (c::make-dialect :std (c::standard-c17))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar-c17* :prefix c17-cst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Below we define operations parameterized over the dialect.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cst-matchp$ ((tree abnf::treep)
                     (elem abnf::elementp)
                     (dialect c::dialectp))
  :returns (yes/no booleanp)
  :short "Check if a CST matches a grammar element."
  (and (abnf::tree-terminatedp tree)
       (abnf::tree-match-element-p tree elem (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-matchp (tree elem dialect)
  (declare (xargs :guard (stringp elem)))
  :short "Check if a CST matches a textual grammar element."
  (b* (((mv err elem rest) (abnf::parse-element (acl2::string=>nats elem)))
       ((when err) (er hard 'cst-matchp "~@0" err))
       ((when (consp rest))
        (er hard 'cst-matchp "Extra: ~s0" (acl2::nats=>string rest)))
       (elem (abnf::abstract-element elem)))
    `(cst-matchp$ ,tree ',elem ,dialect)))

;;;;;;;;;;;;;;;;;;;;

(define cst-list-elem-matchp$ ((trees abnf::tree-listp)
                               (elem abnf::elementp)
                               (dialect c::dialectp))
  :returns (yes/no booleanp)
  :short "Check if each CST in a list matches a grammar element."
  (and (abnf::tree-list-terminatedp trees)
       (abnf::tree-list-match-element-p trees elem (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-list-elem-matchp (trees elem dialect)
  (declare (xargs :guard (stringp elem)))
  :short "Check if each CST in a list matches a textual grammar element."
  (b* (((mv err elem rest) (abnf::parse-element (acl2::string=>nats elem)))
       ((when err) (er hard 'cst-list-elem-matchp "~@0" err))
       ((when (consp rest))
        (er hard 'cst-list-elem-matchp "Extra: ~s0" (acl2::nats=>string rest)))
       (elem (abnf::abstract-element elem)))
    `(cst-list-elem-matchp$ ,trees ',elem ,dialect)))

;;;;;;;;;;;;;;;;;;;;

(define cst-list-rep-matchp$ ((trees abnf::tree-listp)
                              (rep abnf::repetitionp)
                              (dialect c::dialectp))
  :returns (yes/no booleanp)
  :short "Check if a list of CSTs matches a grammar repetition."
  (and (abnf::tree-list-terminatedp trees)
       (abnf::tree-list-match-repetition-p trees rep (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-list-rep-matchp (trees rep dialect)
  (declare (xargs :guard (stringp rep)))
  :short "Check if a list of CSTs matches a textual grammar repetition."
  (b* (((mv err rep rest) (abnf::parse-repetition (acl2::string=>nats rep)))
       ((when err) (er hard 'cst-list-rep-matchp "~@0" err))
       ((when (consp rest))
        (er hard 'cst-list-rep-matchp "Extra: ~s0" (acl2::nats=>string rest)))
       (rep (abnf::abstract-repetition rep)))
    `(cst-list-rep-matchp$ ,trees ',rep ,dialect)))

;;;;;;;;;;;;;;;;;;;;

(define cst-list-list-conc-matchp$ ((treess abnf::tree-list-listp)
                                    (conc abnf::concatenationp)
                                    (dialect c::dialectp))
  :returns (yes/no booleanp)
  :short "Check if a list of lists of CSTs matches a grammar concatenation."
  (and (abnf::tree-list-list-terminatedp treess)
       (abnf::tree-list-list-match-concatenation-p
        treess conc (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-list-list-conc-matchp (treess conc dialect)
  (declare (xargs :guard (acl2::stringp conc)))
  :short "Check if a list of lists of CSTs matches
          a textual grammar concatenation."
  (b* (((mv err conc rest)
        (abnf::parse-concatenation (acl2::string=>nats conc)))
       ((when err) (er hard 'cst-list-list-conc-matchp "~@0" err))
       ((when (consp rest))
        (er hard 'cst-list-list-conc-matchp
            "Extra: ~s0" (acl2::nats=>string rest)))
       (conc (abnf::abstract-concatenation conc)))
    `(cst-list-list-conc-matchp$ ,treess ',conc ,dialect)))

;;;;;;;;;;;;;;;;;;;;

(define cst-list-list-alt-matchp$ ((treess abnf::tree-list-listp)
                                   (alt abnf::alternationp)
                                   (dialect c::dialectp))
  :returns (yes/no booleanp)
  :short "Check if a list of lists of CSTs matches a grammar alternation."
  (and (abnf::tree-list-list-terminatedp treess)
       (abnf::tree-list-list-match-alternation-p
        treess alt (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-list-list-alt-matchp (treess alt dialect)
  (declare (xargs :guard (acl2::stringp alt)))
  :short "Check if a list of lists of CSTs matches
          a textual grammar alternation."
  (b* (((mv err alt rest) (abnf::parse-alternation (acl2::string=>nats alt)))
       ((when err) (er hard 'cst-list-list-alt-matchp "~@0" err))
       ((when (consp rest))
        (er hard 'cst-list-list-alt-matchp
            "Extra: ~s0" (acl2::nats=>string rest)))
       (alt (abnf::abstract-alternation alt)))
    `(cst-list-list-alt-matchp$ ,treess ',alt ,dialect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cst-%x21-23-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x21-23" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x21-23-nat-bounds
    (implies (cst-matchp cst "%x21-23" dialect)
             (and (<= 33 (cst-%x21-23-nat cst dialect))
                  (<= (cst-%x21-23-nat cst dialect) 35)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x21-26-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x21-26" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x21-26-nat-bounds
    (implies (cst-matchp cst "%x21-26" dialect)
             (and (<= 33 (cst-%x21-26-nat cst dialect))
                  (<= (cst-%x21-26-nat cst dialect) 38)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x21-29-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x21-29" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x21-29-nat-bounds
    (implies (cst-matchp cst "%x21-29" dialect)
             (and (<= 33 (cst-%x21-29-nat cst dialect))
                  (<= (cst-%x21-29-nat cst dialect) 41)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x21-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x21-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x21-2f-nat-bounds
    (implies (cst-matchp cst "%x21-2f" dialect)
             (and (<= 33 (cst-%x21-2f-nat cst dialect))
                  (<= (cst-%x21-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x23-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x23-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x23-2f-nat-bounds
    (implies (cst-matchp cst "%x23-2f" dialect)
             (and (<= 35 (cst-%x23-2f-nat cst dialect))
                  (<= (cst-%x23-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x24-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x24-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x24-2f-nat-bounds
    (implies (cst-matchp cst "%x24-2f" dialect)
             (and (<= 36 (cst-%x24-2f-nat cst dialect))
                  (<= (cst-%x24-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x25-26-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x25-26" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x25-26-nat-bounds
    (implies (cst-matchp cst "%x25-26" dialect)
             (and (<= 37 (cst-%x25-26-nat cst dialect))
                  (<= (cst-%x25-26-nat cst dialect) 38)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x25-29-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x25-29" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x25-29-nat-bounds
    (implies (cst-matchp cst "%x25-29" dialect)
             (and (<= 37 (cst-%x25-29-nat cst dialect))
                  (<= (cst-%x25-29-nat cst dialect) 41)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x25-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x25-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x25-2f-nat-bounds
    (implies (cst-matchp cst "%x25-2f" dialect)
             (and (<= 37 (cst-%x25-2f-nat cst dialect))
                  (<= (cst-%x25-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x28-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x28-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x28-2f-nat-bounds
    (implies (cst-matchp cst "%x28-2f" dialect)
             (and (<= 40 (cst-%x28-2f-nat cst dialect))
                  (<= (cst-%x28-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x2b-2e-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x2b-2e" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x2b-2e-nat-bounds
    (implies (cst-matchp cst "%x2b-2e" dialect)
             (and (<= 43 (cst-%x2b-2e-nat cst dialect))
                  (<= (cst-%x2b-2e-nat cst dialect) 46)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x2b-2f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x2b-2f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x2b-2f-nat-bounds
    (implies (cst-matchp cst "%x2b-2f" dialect)
             (and (<= 43 (cst-%x2b-2f-nat cst dialect))
                  (<= (cst-%x2b-2f-nat cst dialect) 47)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x30-37-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x30-37" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x30-37-nat-bounds
    (implies (cst-matchp cst "%x30-37" dialect)
             (and (<= 48 (cst-%x30-37-nat cst dialect))
                  (<= (cst-%x30-37-nat cst dialect) 55)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x30-39-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x30-39" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x30-39-nat-bounds
    (implies (cst-matchp cst "%x30-39" dialect)
             (and (<= 48 (cst-%x30-39-nat cst dialect))
                  (<= (cst-%x30-39-nat cst dialect) 57)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x31-39-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x31-39" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x31-39-nat-bounds
    (implies (cst-matchp cst "%x31-39" dialect)
             (and (<= 49 (cst-%x31-39-nat cst dialect))
                  (<= (cst-%x31-39-nat cst dialect) 57)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x3a-3d-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x3a-3d" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x3a-3d-nat-bounds
    (implies (cst-matchp cst "%x3a-3d" dialect)
             (and (<= 58 (cst-%x3a-3d-nat cst dialect))
                  (<= (cst-%x3a-3d-nat cst dialect) 61)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x3a-3f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x3a-3f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x3a-3f-nat-bounds
    (implies (cst-matchp cst "%x3a-3f" dialect)
             (and (<= 58 (cst-%x3a-3f-nat cst dialect))
                  (<= (cst-%x3a-3f-nat cst dialect) 63)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x41-46-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x41-46" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x41-46-nat-bounds
    (implies (cst-matchp cst "%x41-46" dialect)
             (and (<= 65 (cst-%x41-46-nat cst dialect))
                  (<= (cst-%x41-46-nat cst dialect) 70)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x41-5a-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x41-5a" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x41-5a-nat-bounds
    (implies (cst-matchp cst "%x41-5a" dialect)
             (and (<= 65 (cst-%x41-5a-nat cst dialect))
                  (<= (cst-%x41-5a-nat cst dialect) 90)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x5b-5f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x5b-5f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x5b-5f-nat-bounds
    (implies (cst-matchp cst "%x5b-5f" dialect)
             (and (<= 91 (cst-%x5b-5f-nat cst dialect))
                  (<= (cst-%x5b-5f-nat cst dialect) 95)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x5d-5f-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x5d-5f" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x5d-5f-nat-bounds
    (implies (cst-matchp cst "%x5d-5f" dialect)
             (and (<= 93 (cst-%x5d-5f-nat cst dialect))
                  (<= (cst-%x5d-5f-nat cst dialect) 95)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x61-66-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x61-66" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x61-66-nat-bounds
    (implies (cst-matchp cst "%x61-66" dialect)
             (and (<= 97 (cst-%x61-66-nat cst dialect))
                  (<= (cst-%x61-66-nat cst dialect) 102)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x61-7a-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x61-7a" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x61-7a-nat-bounds
    (implies (cst-matchp cst "%x61-7a" dialect)
             (and (<= 97 (cst-%x61-7a-nat cst dialect))
                  (<= (cst-%x61-7a-nat cst dialect) 122)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x7b-7e-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x7b-7e" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x7b-7e-nat-bounds
    (implies (cst-matchp cst "%x7b-7e" dialect)
             (and (<= 123 (cst-%x7b-7e-nat cst dialect))
                  (<= (cst-%x7b-7e-nat cst dialect) 126)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x80-2029-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x80-2029" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x80-2029-nat-bounds
    (implies (cst-matchp cst "%x80-2029" dialect)
             (and (<= 128 (cst-%x80-2029-nat cst dialect))
                  (<= (cst-%x80-2029-nat cst dialect) 8233)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x202f-2065-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x202f-2065" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x202f-2065-nat-bounds
    (implies (cst-matchp cst "%x202f-2065" dialect)
             (and (<= 8239 (cst-%x202f-2065-nat cst dialect))
                  (<= (cst-%x202f-2065-nat cst dialect) 8293)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%x206a-d7ff-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%x206a-d7ff" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%x206a-d7ff-nat-bounds
    (implies (cst-matchp cst "%x206a-d7ff" dialect)
             (and (<= 8298 (cst-%x206a-d7ff-nat cst dialect))
                  (<= (cst-%x206a-d7ff-nat cst dialect) 55295)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;

(define cst-%xe000-10ffff-nat ((cst abnf::treep) (dialect c::dialectp))
  :guard (cst-matchp cst "%xe000-10ffff" dialect)
  :returns (nat natp)
  :short "Return the natural number at the leaf of
          a CST that matches the indicated range."
  (declare (ignore dialect))
  (lnfix (nth 0 (abnf::tree-leafterm->get cst)))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$
                                           abnf::tree-match-element-p
                                           abnf::tree-match-num-val-p)))

  ///

  (defrule cst-%xe000-10ffff-nat-bounds
    (implies (cst-matchp cst "%xe000-10ffff" dialect)
             (and (<= 57344 (cst-%xe000-10ffff-nat cst dialect))
                  (<= (cst-%xe000-10ffff-nat cst dialect) 1114111)))
    :rule-classes :linear
    :enable (cst-matchp$
             abnf::tree-match-element-p
             abnf::tree-match-num-val-p
             nfix
             nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add more operations
