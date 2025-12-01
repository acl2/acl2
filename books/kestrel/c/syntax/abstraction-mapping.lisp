; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "kestrel/c/syntax/abstract-syntax-trees" :dir :system)
(include-book "kestrel/c/syntax/concrete-syntax" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstraction-mapping
  :parents (abstract-syntax)
  :short "Syntax abstraction mapping."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the mapping from concrete syntax to abstract syntax.
     The mapping maps concrete syntax trees (CSTs),
     which are defined by the ABNF grammar,
     to abstract syntax trees (ASTs),
     which are defined as fixtypes in the abstract syntax,
     or to data that is part of those ASTs.")
   (xdoc::p
    "This mapping formalizes the relation between concrete and abstract syntax.
     In particular, it is needed
     to express formal properties of our parser and printer.")
   (xdoc::p
    "The definition of this syntax abstraction mapping is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-uppercase-letter ((cst abnf::treep))
  :guard (cst-matchp cst "uppercase-letter")
  :returns (achar characterp)
  :short "Abstract an @('uppercase-letter') CST
          to an ACL2 uppercase letter character."
  (b* ((cst (cst-uppercase-letter-conc-rep-elem cst))
       (nat (cst-%x41-5a-nat cst)))
    (code-char nat))
  :hooks (:fix))

(define abs-lowercase-letter ((cst abnf::treep))
  :guard (cst-matchp cst "lowercase-letter")
  :returns (achar characterp)
  :short "Abstract a @('lowercase-letter') CST
          to an ACL2 lowercase letter character."
  (b* ((cst (cst-lowercase-letter-conc-rep-elem cst))
       (nat (cst-%x61-7a-nat cst)))
    (code-char nat))
  :hooks (:fix))

(define abs-letter ((cst abnf::treep))
  :guard (cst-matchp cst "letter")
  :returns (achar characterp)
  :short "Abstract a @('letter') CST to an ACL2 letter character."
  (case (cst-letter-conc? cst)
    (1 (abs-uppercase-letter (cst-letter-conc1-rep-elem cst)))
    (2 (abs-lowercase-letter (cst-letter-conc2-rep-elem cst))))
  :hooks (:fix))

(define abs-digit ((cst abnf::treep))
  :guard (cst-matchp cst "digit")
  :returns (achar characterp)
  :short "Abstract a @('digit') CST to an ACL2 digit character."
  (b* ((cst (cst-digit-conc-rep-elem cst))
       (nat (cst-%x30-39-nat cst)))
    (code-char nat))
  :hooks (:fix))

; TODO: continue
