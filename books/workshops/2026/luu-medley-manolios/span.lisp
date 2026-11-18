; The span lemma (computable-witness form, companion lemma:span).
;
; If sch is a correct scheme for n x n matrix multiplication over F2, then
; for any i, j < n and any chosen k < n, the unit matrix E_ij is the XOR,
; over the summands (A, B, C) of sch, of A scaled by B[j,k] * C[i,k].
;
; Part 1: a quantifier-free matrix extensionality package (mat-diff-pos).
;
; Part 2: the witness sum a-witness-sum (the computable XOR above), its
; entry evaluation against scheme-sum-entry, and the span lemma itself
; (span-lemma, companion lemma:span).
;
; Part 3: the B- and C-component mirrors.
;
; The matrix-level entry lemmas and the entry characterization of mm-tensor
; (companion lemma:mmt) live in mmt.lisp.

(in-package "ACL2")

(include-book "mmt")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: quantifier-free matrix extensionality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A computable witness for inequality of matrices: the first differing
;;; position.  Together with mat-diff-pos-correct this replaces the usual
;;; quantified extensionality principle -- two unequal dimensioned matrices
;;; differ at a valid position -- so entrywise equalities can be lifted to
;;; matrix equalities by contraposition, with no defun-sk.

(define first-diff-index (x y)
  :returns (i natp)
  (cond ((or (atom x) (atom y)) 0)
        ((equal (car x) (car y))
         (+ 1 (first-diff-index (cdr x) (cdr y))))
        (t 0)))

(defruled first-diff-index-bound
  (implies (and (true-listp x) (true-listp y)
                (equal (len x) (len y))
                (not (equal x y)))
           (< (first-diff-index x y) (len x)))
  :induct (cdr-cdr-induct x y)
  :enable (first-diff-index))

(defruled nth-of-first-diff-index
  (implies (and (true-listp x) (true-listp y)
                (equal (len x) (len y))
                (not (equal x y)))
           (not (equal (nth (first-diff-index x y) x)
                       (nth (first-diff-index x y) y))))
  :induct (cdr-cdr-induct x y)
  :enable (first-diff-index))

(define mat-diff-pos ((x true-listp) (y true-listp))
  :returns (pos consp)
  (let ((i (first-diff-index x y)))
    (cons i (first-diff-index (nth i x) (nth i y))))
  ///
  (defrule natp-of-car-of-mat-diff-pos
    (natp (car (mat-diff-pos x y)))
    :rule-classes :type-prescription)
  (defrule natp-of-cdr-of-mat-diff-pos
    (natp (cdr (mat-diff-pos x y)))
    :rule-classes :type-prescription))

(local
 (defruled true-listp-when-bit-list-listp
   (implies (bit-list-listp x)
            (true-listp x))))

(local
 (defruled true-listp-of-nth-row
   (implies (and (bit-matp x m n) (natp m) (< (nfix i) m))
            (true-listp (nth i x)))
   :use ((:instance bit-listnp-of-nth-when-bit-matp))
   :disable (bit-listnp-of-nth-when-bit-matp)
   :enable (bit-listnp-alt-def)))

(defruled mat-diff-pos-correct
  (implies (and (bit-matp x m n)
                (bit-matp y m n)
                (natp m) (natp n)
                (not (equal x y)))
           (let* ((pos (mat-diff-pos x y))
                  (i (car pos))
                  (j (cdr pos)))
             (and (< i m)
                  (< j n)
                  (not (equal (mat-entry i j x)
                              (mat-entry i j y))))))
  :do-not-induct t
  :enable (mat-diff-pos)
  :use ((:instance first-diff-index-bound)
        (:instance nth-of-first-diff-index)
        (:instance first-diff-index-bound
                   (x (nth (first-diff-index x y) x))
                   (y (nth (first-diff-index x y) y)))
        (:instance nth-of-first-diff-index
                   (x (nth (first-diff-index x y) x))
                   (y (nth (first-diff-index x y) y)))
        (:instance len-of-bit-matp (a x))
        (:instance len-of-bit-matp (a y))
        (:instance bit-listnp-of-nth-when-bit-matp
                   (x x) (i (first-diff-index x y)))
        (:instance bit-listnp-of-nth-when-bit-matp
                   (x y) (i (first-diff-index x y)))
        (:instance len-of-bit-listnp (x (nth (first-diff-index x y) x)))
        (:instance len-of-bit-listnp (x (nth (first-diff-index x y) y)))
        (:instance true-listp-of-nth-row (x x) (i (first-diff-index x y)))
        (:instance true-listp-of-nth-row (x y) (i (first-diff-index x y)))
        (:instance true-listp-when-bit-list-listp (x x))
        (:instance true-listp-when-bit-list-listp (x y)))
  :disable (bit-listnp-of-nth-when-bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the witness sum and the span lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The computable witness of the span lemma: the sum, over the summands
;;; (A, B, C) of a scheme, of those A whose coefficient B[j,k] * C[i,k] is 1.
;;; The guard is the dimensioned one, because the structural guard cannot
;;; promise rectangular factors and the mat-entry calls would then be out of
;;; range (nth off the end is nil, which is not an integer, so bitand's guard
;;; fails).  n is already a formal, so nothing new is threaded.  Guards are
;;; verified after the :returns theorem, which the bit-mat-add call needs.

(define a-witness-sum ((l mat-triple-listp) (i natp) (j natp) (k natp)
                       (n natp))
  :guard (and (summand-dim-listp l n) (< i n) (< j n) (< k n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (w bit-list-listp :hyp (mat-triple-listp l))
  :verify-guards :after-returns
  (if (atom l)
      (bit-mat0 n n)
    (if (equal (bitand (mat-entry j k (cadr (car l)))
                       (mat-entry i k (caddr (car l))))
               1)
        (bit-mat-add (car (car l))
                     (a-witness-sum (cdr l) i j k n))
      (a-witness-sum (cdr l) i j k n)))
  ///
  (defrule bit-matp-of-a-witness-sum
    (implies (and (summand-dim-listp l n)
                  (natp n))
             (bit-matp (a-witness-sum l i j k n) n n))))

;;; Entries of the witness sum are bits, in a free-variable-free form that
;;; can fire on the recursive call inside the 3b induction, where the
;;; dimension hypothesis is only derivable, not syntactically present.

(defrule bitp-of-mat-entry-of-a-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (< a n) (< b n))
           (bitp (mat-entry a b (a-witness-sum l i j k n))))
  :do-not-induct t
  :use ((:instance bitp-of-mat-entry
                   (x (a-witness-sum l i j k n)) (m n) (i a) (j b)))
  :disable (a-witness-sum))

;;; Entry evaluation: entry (a, b) of the witness sum is the scheme-sum
;;; entry at the flat index of ((a,b),(j,k),(i,k)).  Validated at n = 2 on
;;; the standard scheme and a proper sublist (resume-notes/span-check.lsp).
;;; mat-entry stays disabled so that the entry algebra of Stage 1 fires on
;;; mat-entry terms rather than their nth-nth expansions.

(defruled mat-entry-of-a-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (a-witness-sum l i j k n))
                  (scheme-sum-entry
                   (+ k (* i n) (* k n n) (* j n n n)
                      (* b n n n n) (* a n n n n n))
                   l)))
  :induct (a-witness-sum l i j k n)
  :enable (a-witness-sum scheme-sum-entry)
  :disable (tensor mat-entry))

;;; The entrywise chain: witness entry = scheme-sum entry [3b] = entry of
;;; the scheme's denotation [nth-of-scheme-sum] = entry of mm-tensor
;;; [correctness] = delta [Stage 2] = entry of the unit matrix [Stage 1].

(defruled span-lemma-entrywise
  (implies (and (correct-schemep sch n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (a-witness-sum sch i j k n))
                  (mat-entry a b (bit-mat-unit i j n n))))
  :do-not-induct t
  :enable (correct-schemep mat-entry-of-a-witness-sum)
  :disable (mm-tensor mat-entry a-witness-sum)
  :use ((:instance nth-of-scheme-sum
                   (l sch)
                   (idx (+ k (* i n) (* k n n) (* j n n n)
                           (* b n n n n) (* a n n n n n))))
        (:instance flat-index-upper-bound
                   (ia a) (ja b) (ib j) (jb k) (ic i) (jc k))
        (:instance nth-of-mm-tensor
                   (ia a) (ja b) (ib j) (jb k) (ic i) (jc k))))

;;; The span lemma (companion lemma:span, computable-witness form): on any
;;; correct scheme, for any i, j and any chosen k, the witness sum in the
;;; A-coordinate reconstructs the unit matrix E_ij.  Proof: were the two
;;; sides unequal, they would differ at the valid position mat-diff-pos
;;; gives -- both are n x n -- contradicting the entrywise chain there.

(defrule span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (a-witness-sum sch i j k n)
                  (bit-mat-unit i j n n)))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (mm-tensor a-witness-sum bit-mat-unit mat-entry)
  :use ((:instance mat-diff-pos-correct
                   (x (a-witness-sum sch i j k n))
                   (y (bit-mat-unit i j n n))
                   (m n) (n n))
        (:instance span-lemma-entrywise
                   (a (car (mat-diff-pos (a-witness-sum sch i j k n)
                                         (bit-mat-unit i j n n))))
                   (b (cdr (mat-diff-pos (a-witness-sum sch i j k n)
                                         (bit-mat-unit i j n n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: the B- and C-component versions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Mirror images of the A-component development.  The B-witness collects
;;; the B factors whose coefficient A[i,j] * C[i,k] is 1 and reconstructs
;;; E_jk for any chosen i; the C-witness collects the C factors whose
;;; coefficient A[i,j] * B[j,k] is 1 and reconstructs E_ik for any chosen j.
;;; Both validated at n = 2 (entry correspondence, on the standard scheme
;;; and a proper sublist) and n = 2, 3 (span) before proving.

(define b-witness-sum ((l mat-triple-listp) (i natp) (j natp) (k natp)
                       (n natp))
  :guard (and (summand-dim-listp l n) (< i n) (< j n) (< k n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (w bit-list-listp :hyp (mat-triple-listp l))
  :verify-guards :after-returns
  (if (atom l)
      (bit-mat0 n n)
    (if (equal (bitand (mat-entry i j (car (car l)))
                       (mat-entry i k (caddr (car l))))
               1)
        (bit-mat-add (cadr (car l))
                     (b-witness-sum (cdr l) i j k n))
      (b-witness-sum (cdr l) i j k n)))
  ///
  (defrule bit-matp-of-b-witness-sum
    (implies (and (summand-dim-listp l n)
                  (natp n))
             (bit-matp (b-witness-sum l i j k n) n n))))

(defrule bitp-of-mat-entry-of-b-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (< a n) (< b n))
           (bitp (mat-entry a b (b-witness-sum l i j k n))))
  :do-not-induct t
  :use ((:instance bitp-of-mat-entry
                   (x (b-witness-sum l i j k n)) (m n) (i a) (j b)))
  :disable (b-witness-sum))

(defruled mat-entry-of-b-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (b-witness-sum l i j k n))
                  (scheme-sum-entry
                   (+ k (* i n) (* b n n) (* a n n n)
                      (* j n n n n) (* i n n n n n))
                   l)))
  :induct (b-witness-sum l i j k n)
  :enable (b-witness-sum scheme-sum-entry)
  :disable (tensor mat-entry))

(defruled b-span-lemma-entrywise
  (implies (and (correct-schemep sch n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (b-witness-sum sch i j k n))
                  (mat-entry a b (bit-mat-unit j k n n))))
  :do-not-induct t
  :enable (correct-schemep mat-entry-of-b-witness-sum)
  :disable (mm-tensor mat-entry b-witness-sum)
  :use ((:instance nth-of-scheme-sum
                   (l sch)
                   (idx (+ k (* i n) (* b n n) (* a n n n)
                           (* j n n n n) (* i n n n n n))))
        (:instance flat-index-upper-bound
                   (ia i) (ja j) (ib a) (jb b) (ic i) (jc k))
        (:instance nth-of-mm-tensor
                   (ia i) (ja j) (ib a) (jb b) (ic i) (jc k))))

(defrule b-span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (b-witness-sum sch i j k n)
                  (bit-mat-unit j k n n)))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (mm-tensor b-witness-sum bit-mat-unit mat-entry)
  :use ((:instance mat-diff-pos-correct
                   (x (b-witness-sum sch i j k n))
                   (y (bit-mat-unit j k n n))
                   (m n) (n n))
        (:instance b-span-lemma-entrywise
                   (a (car (mat-diff-pos (b-witness-sum sch i j k n)
                                         (bit-mat-unit j k n n))))
                   (b (cdr (mat-diff-pos (b-witness-sum sch i j k n)
                                         (bit-mat-unit j k n n)))))))

(define c-witness-sum ((l mat-triple-listp) (i natp) (j natp) (k natp)
                       (n natp))
  :guard (and (summand-dim-listp l n) (< i n) (< j n) (< k n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (w bit-list-listp :hyp (mat-triple-listp l))
  :verify-guards :after-returns
  (if (atom l)
      (bit-mat0 n n)
    (if (equal (bitand (mat-entry i j (car (car l)))
                       (mat-entry j k (cadr (car l))))
               1)
        (bit-mat-add (caddr (car l))
                     (c-witness-sum (cdr l) i j k n))
      (c-witness-sum (cdr l) i j k n)))
  ///
  (defrule bit-matp-of-c-witness-sum
    (implies (and (summand-dim-listp l n)
                  (natp n))
             (bit-matp (c-witness-sum l i j k n) n n))))

(defrule bitp-of-mat-entry-of-c-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (< a n) (< b n))
           (bitp (mat-entry a b (c-witness-sum l i j k n))))
  :do-not-induct t
  :use ((:instance bitp-of-mat-entry
                   (x (c-witness-sum l i j k n)) (m n) (i a) (j b)))
  :disable (c-witness-sum))

(defruled mat-entry-of-c-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (c-witness-sum l i j k n))
                  (scheme-sum-entry
                   (+ b (* a n) (* k n n) (* j n n n)
                      (* j n n n n) (* i n n n n n))
                   l)))
  :induct (c-witness-sum l i j k n)
  :enable (c-witness-sum scheme-sum-entry)
  :disable (tensor mat-entry))

(defruled c-span-lemma-entrywise
  (implies (and (correct-schemep sch n)
                (natp n)
                (natp a) (natp b) (natp i) (natp j) (natp k)
                (< a n) (< b n) (< i n) (< j n) (< k n))
           (equal (mat-entry a b (c-witness-sum sch i j k n))
                  (mat-entry a b (bit-mat-unit i k n n))))
  :do-not-induct t
  :enable (correct-schemep mat-entry-of-c-witness-sum)
  :disable (mm-tensor mat-entry c-witness-sum)
  :use ((:instance nth-of-scheme-sum
                   (l sch)
                   (idx (+ b (* a n) (* k n n) (* j n n n)
                           (* j n n n n) (* i n n n n n))))
        (:instance flat-index-upper-bound
                   (ia i) (ja j) (ib j) (jb k) (ic a) (jc b))
        (:instance nth-of-mm-tensor
                   (ia i) (ja j) (ib j) (jb k) (ic a) (jc b))))

(defrule c-span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (c-witness-sum sch i j k n)
                  (bit-mat-unit i k n n)))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (mm-tensor c-witness-sum bit-mat-unit mat-entry)
  :use ((:instance mat-diff-pos-correct
                   (x (c-witness-sum sch i j k n))
                   (y (bit-mat-unit i k n n))
                   (m n) (n n))
        (:instance c-span-lemma-entrywise
                   (a (car (mat-diff-pos (c-witness-sum sch i j k n)
                                         (bit-mat-unit i k n n))))
                   (b (cdr (mat-diff-pos (c-witness-sum sch i j k n)
                                         (bit-mat-unit i k n n)))))))
