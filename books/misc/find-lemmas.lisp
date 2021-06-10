; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This code was revised and extended with the addition of find-defs and
; find-events in September 2020 by Mihir Mehta.  It remains to document
; find-defs and perhaps find-events.
; Future work: mutual-recursion is not yet supported.  It may be reasonably
; straightforward to modify find-events-fn to add such support, as follows.
; The key is to modify the use of the let-bound variable, namex, which is a
; list of names in the mutual-recursion case rather than a single name.  So
; instead of (formula namex t wrld) you can loop through the members of namex,
; collect their formulas, and conjoin them before calling all-fnnames; or,
; leave them as a list and call all-fnnames-lst instead of all-fnnames.

(in-package "ACL2")

(program)

(defun deref-macro-name-list (fns macro-aliases)
  (if (endp fns)
      nil
    (cons (deref-macro-name (car fns) macro-aliases)
          (deref-macro-name-list (cdr fns) macro-aliases))))

(defun find-events-fn (fns omit-boot-strap acc wrld-tail wrld types)
  (declare (xargs :mode :program))
  (if (or (endp wrld-tail)
          (and omit-boot-strap
               (and (eq (caar wrld-tail) 'command-landmark)
                    (eq (cadar wrld-tail) 'global-value)
                    (equal (access-command-tuple-form (cddar wrld-tail))
                           '(exit-boot-strap-mode)))))
      acc
    (let* ((trip (car wrld-tail))
           (ev-tuple (and (consp trip)
                          (eq (car trip) 'event-landmark)
                          (eq (cadr trip) 'global-value)
                          (cddr trip)))
           (type (and ev-tuple (access-event-tuple-type ev-tuple)))
           (namex (and type (access-event-tuple-namex ev-tuple)))
           (formula (and namex
                         (symbolp namex)
                         (member-eq type types)
                         (formula namex t wrld))))
      (if (and formula
               (subsetp-eq fns (all-fnnames formula)))
          (find-events-fn fns omit-boot-strap
                          (cons (access-event-tuple-form ev-tuple) acc)
                          (cdr wrld-tail)
                          wrld types)
        (find-events-fn fns omit-boot-strap acc (cdr wrld-tail) wrld types)))))

(defmacro find-events (fns &optional
                           (omit-boot-strap 't)
                           (types '(defthm defaxiom defchoose defun defuns)))
  (declare (xargs :guard (let ((fns (if (and (true-listp fns)
                                             (eq (car fns) 'quote)
                                             (eql (length fns) 2))
                                        (cadr fns)
                                      fns)))
                           (or (symbolp fns)
                               (symbol-listp fns)))))
  (let* ((fns (if (and (true-listp fns)
                       (eq (car fns) 'quote)
                       (eql (length fns) 2))
                  (cadr fns)
                fns))
         (fns (cond
               ((symbolp fns) (list fns))
               ((symbol-listp fns) fns)
               (t (er hard 'find-lemmas
                      "The first argument to find-events must be a symbol or ~
                       a list of symbols, but ~x0 is not."
                      fns))))
         (fns `(deref-macro-name-list ',fns (macro-aliases (w state)))))
    `(find-events-fn ,fns ',omit-boot-strap nil (w state) (w state) ',types)))

(defmacro find-lemmas (fns &optional
                           (omit-boot-strap 't))
  (declare (xargs :guard (let ((fns (if (and (true-listp fns)
                                             (eq (car fns) 'quote)
                                             (eql (length fns) 2))
                                        (cadr fns)
                                      fns)))
                           (or (symbolp fns)
                               (symbol-listp fns)))))

; (find-lemmas (fn1 fn2 ...)) returns all lemmas in which all of the indicated
; function symbols occur, except those lemmas in the ground-zero world.  In
; order to include those as well, give a second argument of nil:
; (find-lemmas (fn1 fn2 ...) nil).

; If fns is a symbol, then fns is replaced by (list fns).

  (let* ((fns (if (and (true-listp fns)
                       (eq (car fns) 'quote)
                       (eql (length fns) 2))
                  (cadr fns)
                fns))
         (fns (cond
               ((symbolp fns) (list fns))
               ((symbol-listp fns) fns)
               (t (er hard 'find-lemmas
                      "The first argument to find-lemmas must be a symbol or ~
                       a list of symbols, but ~x0 is not."
                      fns))))
         (fns `(deref-macro-name-list ',fns (macro-aliases (w state)))))
    `(find-events-fn ,fns ',omit-boot-strap nil (w state) (w state)
                     '(defthm defaxiom defchoose))))

(defmacro find-defs (fns &optional (omit-boot-strap 't))
  (declare (xargs :guard (let ((fns (if (and (true-listp fns)
                                             (eq (car fns) 'quote)
                                             (eql (length fns) 2))
                                        (cadr fns)
                                      fns)))
                           (or (symbolp fns)
                               (symbol-listp fns)))))
  (let* ((fns (if (and (true-listp fns)
                       (eq (car fns) 'quote)
                       (eql (length fns) 2))
                  (cadr fns)
                fns))
         (fns (cond
               ((symbolp fns) (list fns))
               ((symbol-listp fns) fns)
               (t (er hard 'find-defs
                      "The first argument to find-defs must be a symbol or ~
                       a list of symbols, but ~x0 is not."
                      fns))))
         (fns `(deref-macro-name-list ',fns (macro-aliases (w state)))))
    `(find-events-fn ,fns ',omit-boot-strap nil (w state) (w state)
                     '(defun defuns))))

; Documentation:

(include-book "xdoc/top" :dir :system)

(defxdoc find-lemmas
  :parents (debugging)
  :short "Find lemmas that mention specified function symbols"
  :long "<p>The @('find-lemmas') macro finds all lemmas that mention specified
 function symbols.  More precisely, @('(find-lemmas (fn1 fn2 ...))') evaluates
 to a list of all @(tsee defthm), @(tsee defaxiom), and @(tsee defchoose) @(see
 events) that mention all of the indicated function symbols: each @('fni') is
 either a function symbol or a macro-alias indicating a function symbol (see
 @(see macro-aliases-table)).</p>

 <p>By default, @('find-lemmas') ignores @(see events) built into ACL2 (that
 is, in the so-called ``ground-zero @(see world)'').  In
 order to include those as well, give a second argument of nil:
 @('(find-lemmas (fn1 fn2 ...) nil)').</p>

 <p>For convenience, you may specify a single symbol to represent a list
 containing exactly that symbol.</p>

 <p>The following example illustrates all the points above.  First, let us
 create an ACL2 session by including some book (for example) and then loading
 the \"find-lemmas\" book.</p>

 @({
 (include-book \"arithmetic/top-with-meta\" :dir :system)
 (include-book \"misc/find-lemmas\" :dir :system)
 })

 <p>The following log then shows some uses of @('find-lemmas').</p>

 @({
 ACL2 !>(find-lemmas (numerator denominator)) ; exclude built-in lemmas
 ((DEFTHM *-R-DENOMINATOR-R
          (EQUAL (* R (DENOMINATOR R))
                 (IF (RATIONALP R)
                     (NUMERATOR R)
                     (FIX R)))
          :HINTS ((\"Goal\" :USE ((:INSTANCE RATIONAL-IMPLIES2 (X R)))
                          :IN-THEORY (DISABLE RATIONAL-IMPLIES2))))
  (DEFTHM /R-WHEN-ABS-NUMERATOR=1
          (AND (IMPLIES (EQUAL (NUMERATOR R) 1)
                        (EQUAL (/ R) (DENOMINATOR R)))
               (IMPLIES (EQUAL (NUMERATOR R) -1)
                        (EQUAL (/ R) (- (DENOMINATOR R)))))
          :HINTS ((\"Goal\" :USE ((:INSTANCE RATIONAL-IMPLIES2 (X R)))
                          :IN-THEORY (DISABLE RATIONAL-IMPLIES2)))))
 ACL2 !>(find-lemmas (numerator denominator) nil) ; include built-in lemmas
 ((DEFAXIOM RATIONAL-IMPLIES1
            (IMPLIES (RATIONALP X)
                     (AND (INTEGERP (DENOMINATOR X))
                          (INTEGERP (NUMERATOR X))
                          (< 0 (DENOMINATOR X))))
            :RULE-CLASSES NIL)
  (DEFAXIOM RATIONAL-IMPLIES2
            (IMPLIES (RATIONALP X)
                     (EQUAL (* (/ (DENOMINATOR X)) (NUMERATOR X))
                            X)))
  (DEFAXIOM LOWEST-TERMS
            (IMPLIES (AND (INTEGERP N)
                          (RATIONALP X)
                          (INTEGERP R)
                          (INTEGERP Q)
                          (< 0 N)
                          (EQUAL (NUMERATOR X) (* N R))
                          (EQUAL (DENOMINATOR X) (* N Q)))
                     (EQUAL N 1))
            :RULE-CLASSES NIL)
  (DEFTHM *-R-DENOMINATOR-R
          (EQUAL (* R (DENOMINATOR R))
                 (IF (RATIONALP R)
                     (NUMERATOR R)
                     (FIX R)))
          :HINTS ((\"Goal\" :USE ((:INSTANCE RATIONAL-IMPLIES2 (X R)))
                          :IN-THEORY (DISABLE RATIONAL-IMPLIES2))))
  (DEFTHM /R-WHEN-ABS-NUMERATOR=1
          (AND (IMPLIES (EQUAL (NUMERATOR R) 1)
                        (EQUAL (/ R) (DENOMINATOR R)))
               (IMPLIES (EQUAL (NUMERATOR R) -1)
                        (EQUAL (/ R) (- (DENOMINATOR R)))))
          :HINTS ((\"Goal\" :USE ((:INSTANCE RATIONAL-IMPLIES2 (X R)))
                          :IN-THEORY (DISABLE RATIONAL-IMPLIES2)))))
 ACL2 !>(find-lemmas (+ * <)) ; + and * are macro-aliases (binary-+, binary-*)
 ((DEFTHM EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
          (IMPLIES (AND (<= 0 I)
                        (<= 0 J)
                        (FC (INTEGERP I))
                        (FC (INTEGERP J)))
                   (EQUAL (EXPT R (+ I J))
                          (* (EXPT R I) (EXPT R J))))))
 ACL2 !>(find-lemmas append) ; same as (find-lemmas (binary-append))
 ((DEFTHM APPEND-PRESERVES-RATIONAL-LISTP
          (IMPLIES (TRUE-LISTP X)
                   (EQUAL (RATIONAL-LISTP (APPEND X Y))
                          (AND (RATIONAL-LISTP X)
                               (RATIONAL-LISTP Y)))))
  (DEFTHM NAT-LISTP-OF-APPEND-WEAK
          (IMPLIES (TRUE-LISTP X)
                   (EQUAL (NAT-LISTP (APPEND X Y))
                          (AND (NAT-LISTP X) (NAT-LISTP Y))))))
 ACL2 !>
 })")
