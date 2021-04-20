; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book does a check to see if any obvious symbols are missing from
; *acl2-exports*.  The idea is that a documented symbol in the "ACL2"
; package, even if imported into the "ACL2" package, should be in
; *acl2-exports* if it has a 'const, 'formals, or 'macro-body property.
; -- unless it's explicitly excluded by virtue of belonging to the constant
; *acl2-exports-exclusions* defined in this book.

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, this book should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defun raw-acl2-exports1 (x pkg-witness wrld allp acc)

; Extend acc with a list of all documented symbols in the package of symbol
; pkg-witness, perhaps restricted to those with certain properties if allp is
; nil; see raw-acl2-exports.

  (declare (xargs :guard (and (alistp x)
                              (symbolp pkg-witness)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (cond ((endp x) acc)
        (t
         (raw-acl2-exports1
          (cdr x)
          pkg-witness
          wrld
          allp
          (let ((sym (caar x)))
            (cond
             ((and (symbolp sym)

; Warning: keep the properties considere below in sync with the notion of
; "export-worthy" described in raw-acl2-exports.

                   (eq (intern-in-package-of-symbol (symbol-name sym)
                                                    pkg-witness)
                       sym)
                   (or allp
                       (getprop sym 'const nil 'current-acl2-world wrld)
                       (not (eq (getprop sym 'formals t 'current-acl2-world
                                         wrld)
                                t))
                       (getprop sym 'macro-body nil 'current-acl2-world wrld)))
              (cons sym acc))
             (t acc)))))))

(defun raw-acl2-exports (allp wrld)

; Return a list of all documented symbols in the ACL2 package, except that if
; allp is nil, then only those symbols are returned that have certain
; "export-worthy" ACL2 properties: 'const, 'formals, or 'macro-body.  Warning:
; keep that list of properties in sync with raw-acl2-exports1.

  (declare (xargs :guard (plist-worldp wrld)))
  (let ((doc-alist *acl2-system-documentation*))
    (cond ((alistp doc-alist)
           (raw-acl2-exports1 doc-alist
                              (pkg-witness "ACL2")
                              wrld
                              allp
                              nil))
          (t (er hard? 'raw-acl2-exports
                 "Expected ~x0 to be an alistp!")))))

(defthm symbol-listp-revappend
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (revappend x y))))

(defthm symbol-listp-raw-acl2-exports1
  (implies (symbol-listp acc)
           (symbol-listp (raw-acl2-exports1 x pkg-witness wrld allp acc))))

(defthm symbol-listp-raw-acl2-exports
  (symbol-listp (raw-acl2-exports allp wrld))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((raw-acl2-exports allp wrld)))))

(defconst *acl2-exports-exclusions*
  '(*UNTROUBLESOME-CHARACTERS*
    ADD-DIVE-INTO-MACRO
    BDD
    BOOK-HASH
    CHECK-SUM
    COMP-GCL
    COUNT ; defined in books/coi/bags/basic.lisp
    DEFUN-MODE
    DIVE-INTO-MACROS-TABLE
    ERROR1
    FIND-RULES-OF-RUNE
    LOOP-STOPPER
    MBE1
    NON-LINEAR-ARITHMETIC
    NORMALIZE

; The addition of pos-listp to *acl2-exports* interferes with certification
; books/centaur/vl/util/defs.lisp.

    POS-LISTP
    PROOF-BUILDER
    REDEFINED-NAMES
    REMOVE-DIVE-INTO-MACRO
    REWRITE
    SAFE-MODE
    TAG-TREE
    TYPE-SET
    USELESS-RUNES
    WATERFALL

; Some of the following might be added to *acl2-exports*, but perhaps not; they
; come from defpointers to system-utilities.

    ARGLISTP
    ALIST-KEYS-SUBSETP
    ALIST-TO-DOUBLETS
    ALL-CALLS
    ALL-FNNAMES
    ALL-FNNAMES-LST
    ALL-FNNAMES1
    BODY
    CONJOIN
    CONJOIN2
    CONS-COUNT-BOUNDED
    CONS-TERM
    CONS-TERM*
    DEFINED-CONSTANT
    DISJOIN
    DISJOIN2
    DUMB-NEGATE-LIT
    ENABLED-NUMEP
    ENABLED-RUNEP
    EVENS
    FARGN
    FARGS
    FCONS-TERM
    FCONS-TERM*
    FDEFUN-MODE
    FFN-SYMB
    FFN-SYMB-P
    FFNNAMEP
    FFNNAMEP-LST
    FIRST-KEYWORD
    FLAMBDA-APPLICATIONP
    FLAMBDAP
    FLATTEN-ANDS-IN-LIT
    FN-RUNE-NUME
    FN-SYMB
    FORMALS
    FSUBCOR-VAR
    FQUOTEP
    GENVAR
    GET-BRR-LOCAL
    GET-EVENT
    GET-SKIPPED-PROOFS-P
    IMPLICATE
    IO?
    KEYWORD-LISTP
    KNOWN-PACKAGE-ALIST
    LAMBDA-APPLICATIONP
    LAMBDA-BODY
    LAMBDA-FORMALS
    LEGAL-CONSTANTP
    LEGAL-VARIABLEP
    LOGICP
    MAKE-LAMBDA
    MAKE-LAMBDA-APPLICATION
    MAKE-LAMBDA-TERM
    MERGE-SORT-LEXORDER
    NVARIABLEP
    ODDS
    PACKN
    PACKN-POS
    PAIRLIS-X1
    PAIRLIS-X2
    PRETTYIFY-CLAUSE
    PROGRAMP
    RECURSIVEP
    REWRITE-LAMBDA-OBJECT
    RW-CACHE-STATE
    STOBJP
    STOBJS-IN
    STOBJS-OUT
    SUBCOR-VAR
    SUBLIS-VAR
    SUBST-EXPR
    SUBST-VAR
    SYMBOL-CLASS
    TRANS-EVAL
    TRANSLATE
    TRANSLATE-HINTS
    TRANSLATE-CMP
    TRANSLATE1
    TRANSLATE1-CMP
    TRANSLATE11
    VARIABLEP

; Symbols below should probably be added to *acl2-exports*.

    ALL-ATTACHMENTS
    LOGICAL-DEFUN
    VERIFY-GUARD-IMPLICATION
  ))

(defconst *special-ops*

; This list includes the operators that get special treatment when their calls
; are translated (in translate11).  Our expectation is that these are are all
; in *acl2-exports*.  (This list might be incomplete; e.g., probably loop$
; should be included.)

  '(quote
    lambda
    lambda$
    let
    mv
    mv-let
    pargs
    check-vars-not-free
    translate-and-test
    with-local-stobj
    stobj-let
    flet
    declare
    if
    mv-list
    return-last

; The following are not included because even though they get special handling
; in translate11, they don't need to be documented.

;   synp
;   makunbound-global
;   put-global
    ))

(defun missing-from-acl2-exports (wrld)

; Returns symbols with an ACL2 :doc topic that have an "export-worthy" ACL2
; property (see raw-acl2-exports), yet are not in *acl2-exports* or
; *acl2-exports-exclusions*.  These should be added to one or the other of
; those two lists (see assert-event that follows).

  (declare (xargs :guard (plist-worldp wrld)
                  :mode ; because of sort-symbol-listp
                  :program))
  (let ((expected (append *acl2-exports-exclusions* *acl2-exports*)))
    (union-eq (set-difference-eq *special-ops*
                                 expected)
              (set-difference-eq (raw-acl2-exports nil wrld)
                                 expected))))

(assert-event
 (null (missing-from-acl2-exports (w state)))
 :msg (msg "Each symbol in the following list should either be added to the ~
            constant ~x0 defined in the ACL2 source code, or else should be ~
            added to the constant ~x1 defined in this book, ~
            ~s2:~|  ~X34"
           '*acl2-exports*
           '*acl2-exports-exclusions*
           "check-acl2-exports.lisp"
           (sort-symbol-listp (missing-from-acl2-exports (w state)))
           nil))

; We close with two utilities that may be worth running on occasion.

; With the change after v4-2 for equality variants, and specifically with the
; use of remove-guard-holders rather than translate to deal with the LET
; introduced by LET-MBE, we need to disable raw-acl2-exports in order for (I
; think) forward-chaining to do its work in the guard proof for
; undocumented-acl2-exports.  It seems reasonable simply to disable
; raw-acl2-exports.
(in-theory (disable raw-acl2-exports))

(defun undocumented-acl2-exports (wrld)

; Returns symbols in *acl2-exports* without an ACL2 :doc topic.  Some may be
; worth documenting.

  (declare (xargs :guard (plist-worldp wrld)))

  (set-difference-eq *acl2-exports*
                     (raw-acl2-exports t wrld)))

(defun suspicious-acl2-exports (wrld)

; Return all documented symbols in the "ACL2" package that do not have any
; "export-worthy" property (see raw-acl2-exports).  As of this writing, these
; symbols are all appropriate for *acl2-exports*.

  (declare (xargs :guard (plist-worldp wrld)))
  (set-difference-eq (raw-acl2-exports t wrld)
                     (raw-acl2-exports nil wrld)))
