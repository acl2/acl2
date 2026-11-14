; gf2span.lisp
;
; A quantifier-free, executable theory of F2 spans of matrix lists.
;
; Over F2 the span of a list of matrices is exactly the set of subset sums
; (XOR of a sublist), so span membership can be defined recursively with no
; quantifiers: x is in the span of (cons a mats) iff x is in the span of mats
; or x + a is in the span of mats.  This book develops that theory:
;
;   - recognizers bit-mat-list-p (structural) and bit-mat-listnp (dimensioned)
;   - in-spanp, the recursive executable span membership predicate
;   - basic span algebra: zero is in every span, spans grow monotonically,
;     every member of a list is in its span
;   - lincomb, explicit F2 linear combinations, with soundness (every linear
;     combination is in the span) and completeness (span-witness computes
;     coefficients reproducing any span member)
;   - closure of the span under bit-mat-add
;   - unit matrices, a spans-unitsp predicate, and the spanning theorem:
;     if all units are in the span, every matrix is (via an explicit
;     decomposition of a matrix into its unit summands)
;   - independence and nonvanishing of nontrivial linear combinations of
;     independent lists

(in-package "ACL2")

(include-book "bits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Matrix-level AC and cancellation support
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; bits.lisp does not export commutativity/associativity for bit-mat-add.
;; We derive them here from the list-level rules, following the same
;; cdr-cdr-induct technique used for mat-flat-of-bit-mat-add in bits.lisp.

(defruled bit-mat-add-commutative
  (equal (bit-mat-add a b)
         (bit-mat-add b a))
  :induct (cdr-cdr-induct a b)
  :enable (bit-mat-add bit-list-add-commutative))

(defruled bit-mat-add-associative
  (equal (bit-mat-add (bit-mat-add a b) c)
         (bit-mat-add a (bit-mat-add b c)))
  :enable (bit-mat-add bit-list-add-associative))

(defruled bit-mat-add-commutative-2
  (equal (bit-mat-add a (bit-mat-add b c))
         (bit-mat-add b (bit-mat-add a c)))
  :use (bit-mat-add-associative
        (:instance bit-mat-add-associative (a b) (b a))
        (:instance bit-mat-add-commutative))
  :enable (bit-mat-add-commutative))

;; Cancellation rules with the hypothesis on b FIRST: b is typically bound to
;; a small term like (car mats) whose (bit-matp b m n) hypothesis appears
;; literally in the goal, so the free variables m and n get bound there and
;; the hypothesis on a can then be relieved by rewriting.  The versions
;; exported by bits.lisp list the hypothesis on a first, which blocks free
;; variable binding when a is a large computed term.
(defrule bit-mat-add-cancel-1b
  (implies (and (bit-matp b m n)
                (bit-matp a m n))
           (equal (bit-mat-add b (bit-mat-add b a))
                  a)))

(defrule bit-mat-add-cancel-2b
  (implies (and (bit-matp b m n)
                (bit-matp a m n))
           (equal (bit-mat-add b (bit-mat-add a b))
                  a)))

;; Sum-first cancellation forms, complementing bit-mat-add-cancel-1/2.
(defrule bit-mat-add-cancel-3
  (implies (and (bit-matp b m n)
                (bit-matp a m n))
           (equal (bit-mat-add (bit-mat-add b a) b)
                  a))
  :use ((:instance bit-mat-add-commutative (a (bit-mat-add b a)))))

(defrule bit-mat-add-cancel-4
  (implies (and (bit-matp b m n)
                (bit-matp a m n))
           (equal (bit-mat-add (bit-mat-add a b) b)
                  a))
  :use ((:instance bit-mat-add-commutative (a (bit-mat-add a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recognizers for lists of bit matrices
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-mat-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bit-list-listp (car x))
         (bit-mat-list-p (cdr x)))))

(define bit-mat-listnp (x (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bit-matp (car x) m n)
         (bit-mat-listnp (cdr x) m n)))
  ///

  (defrule bit-mat-list-p-when-bit-mat-listnp
    (implies (bit-mat-listnp x m n)
             (bit-mat-list-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defrule bit-mat-listnp-of-append
    (implies (and (bit-mat-listnp x m n)
                  (bit-mat-listnp y m n))
             (bit-mat-listnp (append x y) m n))
    :induct (cdr-induct x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Span membership
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-spanp ((x bit-list-listp) (mats bit-mat-list-p) (m natp) (n natp))
  ;; x is in the F2-span of the list mats
  :returns (yes/no booleanp)
  (if (atom mats)
      (equal x (bit-mat0 m n))
    (or (in-spanp x (cdr mats) m n)
        (in-spanp (bit-mat-add x (car mats)) (cdr mats) m n))))

;; Concrete validation at 2x2 (row-major matrices as lists of rows):
;; E00 + E01 is in the span of (E00 E01); E10 is not.
(assert-event
 (and (equal (in-spanp '((1 1) (0 0))
                       '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             t)
      (equal (in-spanp '((0 0) (1 0))
                       '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             nil)
      (equal (in-spanp '((0 0) (0 0)) nil 2 2) t)
      (equal (in-spanp '((1 0) (0 0))
                       '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             t)
      (equal (in-spanp '((0 1) (0 0))
                       '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic span algebra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule zero-in-spanp
  (implies (bit-mat-listnp mats m n)
           (in-spanp (bit-mat0 m n) mats m n))
  :induct (cdr-induct mats)
  :enable (in-spanp bit-mat-listnp))

(defrule in-spanp-monotone
  (implies (in-spanp x mats m n)
           (in-spanp x (cons a mats) m n))
  :enable in-spanp)

(defrule member-in-spanp
  (implies (and (member-equal a mats)
                (bit-mat-listnp mats m n))
           (in-spanp a mats m n))
  :induct (cdr-induct mats)
  :enable (in-spanp bit-mat-listnp bit-mat-add-same))

;; Extending a span element by the head of the list: (car mats) + z is in the
;; span of mats whenever z is in the span of (cdr mats).
(defruled in-spanp-step
  (implies (and (bit-matp (car mats) m n)
                (bit-mat-listnp (cdr mats) m n)
                (bit-matp z m n)
                (consp mats)
                (in-spanp z (cdr mats) m n))
           (in-spanp (bit-mat-add (car mats) z) mats m n))
  :expand ((in-spanp (bit-mat-add (car mats) z) mats m n))
  :use ((:instance bit-mat-add-cancel-3 (b (car mats)) (a z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linear combinations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lincomb ((coeffs bit-list-p) (mats bit-mat-list-p) (m natp) (n natp))
  ;; The F2 linear combination of mats with the given coefficient bits:
  ;; the sum of those elements of mats whose coefficient is 1.
  :measure (acl2-count mats)
  :returns (x bit-list-listp :hyp (bit-mat-list-p mats))
  (if (atom mats)
      (bit-mat0 m n)
    (if (equal (car coeffs) 1)
        (bit-mat-add (car mats)
                     (lincomb (cdr coeffs) (cdr mats) m n))
      (lincomb (cdr coeffs) (cdr mats) m n)))
  ///

  (defrule bit-matp-of-lincomb
    (implies (bit-mat-listnp mats m n)
             (bit-matp (lincomb coeffs mats m n) m n))
    :induct (lincomb coeffs mats m n)
    :enable bit-mat-listnp))

;; Concrete validation at 2x2.
(assert-event
 (and (equal (lincomb '(1 1) '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             '((1 1) (0 0)))
      (equal (lincomb '(0 1) '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             '((0 1) (0 0)))
      (equal (lincomb '(0 0) '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
             '((0 0) (0 0)))))

;; Soundness: every linear combination lies in the span.
(defrule in-spanp-of-lincomb
  (implies (bit-mat-listnp mats m n)
           (in-spanp (lincomb coeffs mats m n) mats m n))
  :induct (lincomb coeffs mats m n)
  :enable (in-spanp-step in-spanp lincomb bit-mat-listnp))

;; Completeness: span-witness computes coefficients that reproduce any span
;; member as a linear combination.
(define span-witness ((x bit-list-listp) (mats bit-mat-list-p) (m natp) (n natp))
  :returns (coeffs bit-list-p)
  (if (atom mats)
      nil
    (if (in-spanp x (cdr mats) m n)
        (cons 0 (span-witness x (cdr mats) m n))
      (cons 1 (span-witness (bit-mat-add x (car mats)) (cdr mats) m n))))
  ///

  (defrule len-of-span-witness
    (equal (len (span-witness x mats m n))
           (len mats)))

  (defrule bit-listnp-of-span-witness
    (bit-listnp (span-witness x mats m n) (len mats))
    :enable bit-listnp))

;; Concrete validation: the witness of E00+E01 over (E00 E01) is (1 1).
(assert-event
 (equal (span-witness '((1 1) (0 0))
                      '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
        '(1 1)))

(defrule lincomb-of-span-witness
  (implies (and (in-spanp x mats m n)
                (bit-matp x m n)
                (bit-mat-listnp mats m n))
           (equal (lincomb (span-witness x mats m n) mats m n)
                  x))
  :induct (span-witness x mats m n)
  :enable (span-witness in-spanp lincomb bit-mat-listnp
           bit-mat-add-commutative
           bit-mat-add-associative
           bit-mat-add-commutative-2))

;; Linear combination of an XOR of coefficient vectors is the sum of the
;; linear combinations.  The :induct term makes ACL2 merge the induction
;; schemes of the two lincomb calls into one that cdrs c1, c2, and mats
;; together.
(defruled lincomb-of-bit-list-add
  (implies (and (bit-listnp c1 (len mats))
                (bit-listnp c2 (len mats))
                (bit-mat-listnp mats m n))
           (equal (lincomb (bit-list-add c1 c2) mats m n)
                  (bit-mat-add (lincomb c1 mats m n)
                               (lincomb c2 mats m n))))
  :induct (bit-mat-add (lincomb c1 mats m n)
                       (lincomb c2 mats m n))
  :enable (lincomb bit-list-add bit-mat-listnp bit-listnp
           bit-mat-add-commutative
           bit-mat-add-associative
           bit-mat-add-commutative-2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Closure of the span under addition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-spanp-closed-under-add
  (implies (and (in-spanp x mats m n)
                (in-spanp y mats m n)
                (bit-matp x m n)
                (bit-matp y m n)
                (bit-mat-listnp mats m n))
           (in-spanp (bit-mat-add x y) mats m n))
  :use ((:instance in-spanp-of-lincomb
                   (coeffs (bit-list-add (span-witness x mats m n)
                                         (span-witness y mats m n))))
        (:instance lincomb-of-bit-list-add
                   (c1 (span-witness x mats m n))
                   (c2 (span-witness y mats m n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit matrices
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The arithmetic book is included here, after the events above, so that the
;; proof environment of the first half of this book is unchanged.
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; Companion to bits.lisp's bit-mat-add-of-bit-mat0, with the zero as the
;; second argument.
(defrule bit-mat-add-of-bit-mat0-2
  (implies (bit-matp a m n)
           (equal (bit-mat-add a (bit-mat0 m n))
                  a))
  :use ((:instance bit-mat-add-commutative (b (bit-mat0 m n)))))

;; bit-unit-list is a VERBATIM copy of the definition in top.lisp (this book
;; does not include top.lisp), so that a future book including both sees a
;; redundant event rather than a clash.
(define bit-unit-list ((j natp) (n natp))
  :returns (l bit-list-p)
  (if (zp n)
      nil
    (if (zp j)
        (cons 1 (bit-listn0 (1- n)))
      (cons 0 (bit-unit-list (1- j) (1- n)))))
  ///

  (defrule bit-listnp-of-bit-unit-list
    (bit-listnp (bit-unit-list j n) n)
    :enable (bit-listnp)))

;; The unit matrix e_ij of shape m x n.  The body is identical to top.lisp's
;; bit-mat-unit; the name bit-mat-unit2 avoids a clash, since the two books
;; are siblings.  When a common ancestor or glue book exists, the two
;; definitions should be unified there.
(define bit-mat-unit2 ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit2 (1- i) j (1- m) n))))
  ///

  (defrule bit-matp-of-bit-mat-unit2
    (bit-matp (bit-mat-unit2 i j m n) m n)
    :enable (bit-matp)))

;; Concrete validation at 2x2: the four units.
(assert-event
 (and (equal (bit-mat-unit2 0 0 2 2) '((1 0) (0 0)))
      (equal (bit-mat-unit2 0 1 2 2) '((0 1) (0 0)))
      (equal (bit-mat-unit2 1 0 2 2) '((0 0) (1 0)))
      (equal (bit-mat-unit2 1 1 2 2) '((0 0) (0 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Counting one-entries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count-ones-list ((r bit-list-p))
  :returns (k natp)
  (if (atom r)
      0
    (+ (if (equal (car r) 1) 1 0)
       (count-ones-list (cdr r))))
  ///

  (defruled count-ones-list-zero-iff
    (implies (bit-listnp r n)
             (iff (equal (count-ones-list r) 0)
                  (equal r (bit-listn0 n))))
    :induct (bit-listnp r n)
    :enable (bit-listnp count-ones-list bit-listn0 repeat)))

(define count-ones-mat ((x bit-list-listp))
  :returns (k natp)
  (if (atom x)
      0
    (+ (count-ones-list (car x))
       (count-ones-mat (cdr x))))
  ///

  (defruled count-ones-mat-zero-iff
    (implies (bit-matp x m n)
             (iff (equal (count-ones-mat x) 0)
                  (equal x (bit-mat0 m n))))
    :induct (bit-matp x m n)
    :enable (bit-matp count-ones-mat count-ones-list-zero-iff
             bit-mat0 repeat)))

(assert-event
 (and (equal (count-ones-mat '((1 0) (0 1))) 2)
      (equal (count-ones-mat '((0 0) (0 0))) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Locating the first one-entry
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define first-one-col ((r bit-list-p))
  ;; Column of the first 1 in a row (row length if there is none)
  :returns (j natp)
  (if (atom r)
      0
    (if (equal (car r) 1)
        0
      (1+ (first-one-col (cdr r)))))
  ///

  (defruled first-one-col-bound
    (implies (and (bit-listnp r n)
                  (< 0 (count-ones-list r)))
             (< (first-one-col r) n))
    :induct (bit-listnp r n)
    :enable (bit-listnp count-ones-list first-one-col)))

(define first-one-row ((x bit-list-listp))
  ;; Row of the first 1 in a matrix (row count if there is none)
  :returns (i natp)
  (if (atom x)
      0
    (if (< 0 (count-ones-list (car x)))
        0
      (1+ (first-one-row (cdr x)))))
  ///

  (defruled first-one-row-bound
    (implies (and (bit-matp x m n)
                  (< 0 (count-ones-mat x)))
             (< (first-one-row x) m))
    :induct (bit-matp x m n)
    :enable (bit-matp count-ones-mat first-one-row)))

(define first-one-col-mat ((x bit-list-listp))
  ;; Column of the first 1 in a matrix, i.e. of the first 1 in row
  ;; (first-one-row x)
  :returns (j natp)
  (if (atom x)
      0
    (if (< 0 (count-ones-list (car x)))
        (first-one-col (car x))
      (first-one-col-mat (cdr x))))
  ///

  (defruled first-one-col-mat-bound
    (implies (and (bit-matp x m n)
                  (< 0 (count-ones-mat x)))
             (< (first-one-col-mat x) n))
    :induct (bit-matp x m n)
    :enable (bit-matp count-ones-mat first-one-col-mat
             first-one-col-bound)))

(assert-event
 (and (equal (first-one-row '((0 0) (0 1))) 1)
      (equal (first-one-col-mat '((0 0) (0 1))) 1)
      (equal (first-one-row '((1 0) (0 1))) 0)
      (equal (first-one-col-mat '((0 1) (1 0))) 1)))

;; Adding the unit at the first one-entry clears that entry and changes
;; nothing else, so the count of ones drops by exactly one.
(defruled count-ones-list-of-add-unit
  (implies (and (bit-listnp r n)
                (< 0 (count-ones-list r)))
           (equal (count-ones-list
                   (bit-list-add r (bit-unit-list (first-one-col r) n)))
                  (1- (count-ones-list r))))
  :induct (bit-listnp r n)
  :enable (bit-listnp count-ones-list first-one-col
           bit-unit-list bit-list-add))

(defruled count-ones-mat-of-add-unit
  (implies (and (bit-matp x m n)
                (< 0 (count-ones-mat x)))
           (equal (count-ones-mat
                   (bit-mat-add x (bit-mat-unit2 (first-one-row x)
                                                 (first-one-col-mat x)
                                                 m n)))
                  (1- (count-ones-mat x))))
  :induct (bit-matp x m n)
  :enable (bit-matp count-ones-mat first-one-row first-one-col-mat
           bit-mat-unit2 bit-mat-add count-ones-list-of-add-unit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Decomposing a matrix into units
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define units-of ((x bit-list-listp) (m natp) (n natp))
  ;; The list of unit matrices whose XOR is x, obtained by repeatedly
  ;; clearing the first one-entry; the count of ones is the measure.
  :returns (l bit-mat-list-p)
  :measure (count-ones-mat x)
  :hints (("Goal"
           :use ((:instance count-ones-mat-of-add-unit)
                 (:instance count-ones-mat-zero-iff))))
  (if (or (not (bit-matp x m n))
          (equal x (bit-mat0 m n)))
      nil
    (cons (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) m n)
          (units-of (bit-mat-add x (bit-mat-unit2 (first-one-row x)
                                                  (first-one-col-mat x)
                                                  m n))
                    m n))))

(assert-event
 (and (equal (units-of '((1 0) (0 1)) 2 2)
             '(((1 0) (0 0)) ((0 0) (0 1))))
      (equal (units-of '((1 1) (1 1)) 2 2)
             '(((1 0) (0 0)) ((0 1) (0 0)) ((0 0) (1 0)) ((0 0) (0 1))))
      (equal (units-of '((0 0) (0 0)) 2 2) nil)
      ;; XOR of the decomposition reassembles the matrix
      (equal (lincomb '(1 1) (units-of '((1 0) (0 1)) 2 2) 2 2)
             '((1 0) (0 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Enumerating all units
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-in-spanp ((l bit-mat-list-p) (mats bit-mat-list-p)
                     (m natp) (n natp))
  ;; every element of l is in the span of mats
  :returns (yes/no booleanp)
  (if (atom l)
      t
    (and (in-spanp (car l) mats m n)
         (all-in-spanp (cdr l) mats m n)))
  ///

  (defruled in-spanp-of-member-when-all-in-spanp
    (implies (and (all-in-spanp l mats m n)
                  (member-equal u l))
             (in-spanp u mats m n))
    :induct (cdr-induct l)
    :enable (all-in-spanp)))

(define unit-row ((i natp) (j natp) (m natp) (n natp))
  ;; the units e_{i,j'} of shape m x n for j <= j' < n
  :returns (l bit-mat-list-p)
  :measure (nfix (- (nfix n) (nfix j)))
  (if (>= (nfix j) (nfix n))
      nil
    (cons (bit-mat-unit2 i j m n)
          (unit-row i (1+ (nfix j)) m n)))
  ///

  (defrule bit-mat-listnp-of-unit-row
    (bit-mat-listnp (unit-row i j m n) m n)
    :induct (unit-row i j m n)
    :enable (unit-row bit-mat-listnp))

  (defruled member-of-unit-row
    (implies (and (natp j0) (natp j)
                  (<= j0 j) (< j (nfix n)))
             (member-equal (bit-mat-unit2 i j m n) (unit-row i j0 m n)))
    :induct (unit-row i j0 m n)
    :enable (unit-row)))

(local
 (defrule bit-mat-list-p-of-append
   (implies (bit-mat-list-p x)
            (equal (bit-mat-list-p (append x y))
                   (bit-mat-list-p y)))
   :induct (cdr-induct x)))

(local
 (defrule member-equal-of-append
   (iff (member-equal a (append x y))
        (or (member-equal a x) (member-equal a y)))
   :induct (cdr-induct x)))

(define all-units ((i natp) (j natp) (m natp) (n natp))
  ;; the units e_{i',j'} of shape m x n for i <= i' < m, j' < n (row i
  ;; starting at column j); (all-units 0 0 m n) is the standard basis
  :returns (l bit-mat-list-p)
  :measure (nfix (- (nfix m) (nfix i)))
  (if (>= (nfix i) (nfix m))
      nil
    (append (unit-row i j m n)
            (all-units (1+ (nfix i)) 0 m n)))
  ///

  (defrule bit-mat-listnp-of-all-units
    (bit-mat-listnp (all-units i j m n) m n)
    :induct (all-units i j m n)
    :enable (all-units bit-mat-listnp))

  (defruled member-of-all-units
    (implies (and (natp i0) (natp i) (<= i0 i) (< i (nfix m))
                  (natp j) (< j (nfix n)))
             (member-equal (bit-mat-unit2 i j m n) (all-units i0 0 m n)))
    :induct (all-units i0 0 m n)
    :enable (all-units member-of-unit-row)))

;; Concrete validation at 2x2: the standard basis, in row-major order.
(assert-event
 (equal (all-units 0 0 2 2)
        '(((1 0) (0 0)) ((0 1) (0 0)) ((0 0) (1 0)) ((0 0) (0 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The spanning theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define spans-unitsp ((mats bit-mat-list-p) (m natp) (n natp))
  ;; every unit matrix of shape m x n is in the span of mats
  :returns (yes/no booleanp)
  (all-in-spanp (all-units 0 0 m n) mats m n)
  ///

  (defruled unit-in-spanp-when-spans-unitsp
    (implies (and (spans-unitsp mats m n)
                  (natp i) (natp j) (natp m) (natp n)
                  (< i m) (< j n))
             (in-spanp (bit-mat-unit2 i j m n) mats m n))
    :enable (spans-unitsp)
    :use ((:instance in-spanp-of-member-when-all-in-spanp
                     (l (all-units 0 0 m n))
                     (u (bit-mat-unit2 i j m n)))
          (:instance member-of-all-units (i0 0)))))

;; If x + u and u are both in a span, so is x (add u back and cancel).
(defruled in-spanp-add-unit-back
  (implies (and (in-spanp (bit-mat-add x u) mats m n)
                (in-spanp u mats m n)
                (bit-matp x m n)
                (bit-matp u m n)
                (bit-mat-listnp mats m n))
           (in-spanp x mats m n))
  :use ((:instance in-spanp-closed-under-add
                   (x (bit-mat-add x u)) (y u))
        (:instance bit-mat-add-cancel-4 (a x) (b u))))

;; One step of the units-of decomposition, as a span fact: if clearing the
;; first one-entry of x lands in the span and the units are spanned, x is in
;; the span.
(defruled in-spanp-first-one-step
  (implies (and (in-spanp (bit-mat-add x (bit-mat-unit2 (first-one-row x)
                                                        (first-one-col-mat x)
                                                        m n))
                          mats m n)
                (spans-unitsp mats m n)
                (bit-matp x m n)
                (not (equal x (bit-mat0 m n)))
                (bit-mat-listnp mats m n)
                (natp m) (natp n))
           (in-spanp x mats m n))
  :use ((:instance in-spanp-add-unit-back
                   (u (bit-mat-unit2 (first-one-row x)
                                     (first-one-col-mat x) m n)))
        (:instance unit-in-spanp-when-spans-unitsp
                   (i (first-one-row x)) (j (first-one-col-mat x)))
        (:instance first-one-row-bound)
        (:instance first-one-col-mat-bound)
        (:instance count-ones-mat-zero-iff)))

;; The spanning theorem, in the form the companion span lemma consumes: a
;; list spanning all units spans every matrix.  Induction along the units-of
;; decomposition of x.
(defrule in-spanp-when-spans-unitsp
  (implies (and (spans-unitsp mats m n)
                (bit-matp x m n)
                (bit-mat-listnp mats m n)
                (natp m) (natp n))
           (in-spanp x mats m n))
  :induct (units-of x m n)
  :enable (in-spanp-first-one-step (:i units-of)))

;; The list of all units spans all units (every list is a subset of itself),
;; hence everything.

(local
 (defrule subsetp-equal-of-cons-right
   (implies (subsetp-equal l mats)
            (subsetp-equal l (cons a mats)))
   :induct (cdr-induct l)))

(local
 (defrule subsetp-equal-reflexive
   (subsetp-equal l l)
   :induct (cdr-induct l)))

(defruled all-in-spanp-when-subsetp
  (implies (and (subsetp-equal l mats)
                (bit-mat-listnp l m n)
                (bit-mat-listnp mats m n))
           (all-in-spanp l mats m n))
  :induct (cdr-induct l)
  :enable (all-in-spanp bit-mat-listnp))

(defrule spans-unitsp-of-all-units
  (spans-unitsp (all-units 0 0 m n) m n)
  :enable (spans-unitsp)
  :use ((:instance all-in-spanp-when-subsetp
                   (l (all-units 0 0 m n))
                   (mats (all-units 0 0 m n)))))

;; Units span everything: every m x n bit matrix is in the span of the
;; standard basis (all-units 0 0 m n).
(defrule in-spanp-of-all-units
  (implies (and (bit-matp x m n)
                (natp m) (natp n))
           (in-spanp x (all-units 0 0 m n) m n)))

(assert-event
 (and (spans-unitsp (all-units 0 0 2 2) 2 2)
      (in-spanp '((1 1) (0 1)) (all-units 0 0 2 2) 2 2)
      (in-spanp '((1 1) (1 1)) (all-units 0 0 2 2) 2 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Independence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define independentp ((mats bit-mat-list-p) (m natp) (n natp))
  ;; no element is in the span of the elements after it
  :returns (yes/no booleanp)
  (if (atom mats)
      t
    (and (not (in-spanp (car mats) (cdr mats) m n))
         (independentp (cdr mats) m n))))

(assert-event
 (and (equal (independentp '(((1 0) (0 0)) ((0 1) (0 0))) 2 2) t)
      (equal (independentp '(((1 0) (0 0)) ((1 0) (0 0))) 2 2) nil)
      (equal (independentp '(((1 0) (0 1)) ((1 0) (0 0)) ((0 0) (0 1))) 2 2)
             nil)
      (equal (independentp (all-units 0 0 2 2) 2 2) t)))

;; Nontrivial linear combinations of an independent list are nonzero.  In the
;; head-coefficient-1 case a vanishing combination would exhibit the head as
;; a linear combination, hence a span member, of the tail.
(defrule lincomb-nonzero-when-independentp
  (implies (and (independentp mats m n)
                (bit-listnp coeffs (len mats))
                (not (equal coeffs (bit-listn0 (len mats))))
                (bit-mat-listnp mats m n)
                (natp m) (natp n))
           (not (equal (lincomb coeffs mats m n) (bit-mat0 m n))))
  :induct (lincomb coeffs mats m n)
  :enable (lincomb independentp bit-mat-listnp bit-listnp
           bit-listn0 repeat (:i lincomb)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sums of independent lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mat-list-sum ((mats bit-mat-list-p) (m natp) (n natp))
  ;; the XOR of all elements of mats
  :returns (x bit-list-listp)
  (if (atom mats)
      (bit-mat0 m n)
    (bit-mat-add (car mats) (mat-list-sum (cdr mats) m n)))
  ///

  (defrule bit-matp-of-mat-list-sum
    (implies (bit-mat-listnp mats m n)
             (bit-matp (mat-list-sum mats m n) m n))
    :induct (cdr-induct mats)
    :enable (mat-list-sum bit-mat-listnp)))

(assert-event
 (equal (mat-list-sum '(((1 0) (0 0)) ((0 1) (0 0))) 2 2)
        '((1 1) (0 0))))

(local
 (defrule bit-listnp-of-repeat-1
   (implies (natp k)
            (bit-listnp (repeat k 1) k))
   :induct (dec-induct k)
   :enable (bit-listnp repeat)))

(defruled mat-list-sum-as-lincomb
  (implies (bit-mat-listnp mats m n)
           (equal (mat-list-sum mats m n)
                  (lincomb (repeat (len mats) 1) mats m n)))
  :induct (cdr-induct mats)
  :enable (mat-list-sum lincomb repeat bit-mat-listnp))

(local
 (defrule posp-of-len-when-consp
   (implies (consp x)
            (posp (len x)))))

(local
 (defrule repeat-1-not-repeat-0
   (implies (posp k)
            (not (equal (repeat k 1) (repeat k 0))))
   :enable (repeat)))

;; Corollary: the sum of a nonempty independent list is nonzero.  Applied to
;; independent sublists this gives the nonzero partial sums the grow-chain
;; argument needs.
(defrule mat-list-sum-nonzero-when-independentp
  (implies (and (independentp mats m n)
                (consp mats)
                (bit-mat-listnp mats m n)
                (natp m) (natp n))
           (not (equal (mat-list-sum mats m n) (bit-mat0 m n))))
  :enable (mat-list-sum-as-lincomb bit-listn0 repeat)
  :use ((:instance lincomb-nonzero-when-independentp
                   (coeffs (repeat (len mats) 1)))))
