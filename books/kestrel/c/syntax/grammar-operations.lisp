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
  :short "Check if a list of ASTs matches a grammar repetition."
  (and (abnf::tree-list-terminatedp trees)
       (abnf::tree-list-match-repetition-p trees rep (grammar-for dialect))))

;;;;;;;;;;

(defmacro+ cst-list-rep-matchp (trees rep dialect)
  (declare (xargs :guard (stringp rep)))
  :short "Check if a list of ASTs matches a textual grammar repetition."
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

; TODO: add more operations
