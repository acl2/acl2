; The parity argument for the companion paper's lemma:zero-subset.
;
; A multiset of UNIT SUMMANDS -- summands each of whose three factors is a
; unit matrix (bit-mat-unit i j n n) -- whose scheme-sum is zero has every
; member occurring an even number of times.
;
; Deliverable 1: a computable recognizer unit-matp with index decoder
; unit-index-of, unit summand recognizers, and decoder correctness both
; ways, plus injectivity through the decoders.
;
; Deliverable 2: the flat index unit-flat-index of a unit summand (the one
; position where its tensor is 1) and the support lemma: the tensor of a
; unit summand x, read at the flat index of a unit summand s, is 1 exactly
; when x = s.  Plus injectivity of the flat index.
;
; Deliverable 3: the parity theorem: if a list of unit summands has zero
; scheme-sum, every member occurs an even number of times.
;
; All definitions and lemma formulations validated by execution at n = 2
; before proving (par-probe*.lsp).

(in-package "ACL2")

(include-book "mmt")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deliverable 1: unit matrices, their decoder, unit summands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Index of the first 1 in a bit list, or nil if there is none.

(define bit-list-first-one (x)
  :returns (i (or (null i) (natp i)) :rule-classes :type-prescription)
  (cond ((atom x) nil)
        ((equal (car x) 1) 0)
        (t (b* ((r (bit-list-first-one (cdr x))))
             (and r (+ 1 r))))))

;;; Position (i . j) of the first 1 entry of a matrix in row-major order,
;;; or nil if the matrix is all zero.

(define mat-first-one (a)
  :returns (pos (or (null pos)
                    (and (consp pos) (natp (car pos)) (natp (cdr pos))))
                :hints (("Goal" :induct (mat-first-one a))))
  (if (atom a)
      nil
    (b* ((j (bit-list-first-one (car a))))
      (if j
          (cons 0 j)
        (b* ((r (mat-first-one (cdr a))))
          (and r (cons (+ 1 (car r)) (cdr r)))))))
  ///
  (defrule consp-of-mat-first-one
    (iff (consp (mat-first-one a))
         (mat-first-one a))
    :induct (mat-first-one a)
    :enable mat-first-one)
  (defrule natp-of-car-of-mat-first-one
    (implies (mat-first-one a)
             (natp (car (mat-first-one a))))
    :rule-classes (:rewrite :type-prescription)
    :induct (mat-first-one a)
    :enable mat-first-one)
  (defrule natp-of-cdr-of-mat-first-one
    (implies (mat-first-one a)
             (natp (cdr (mat-first-one a))))
    :rule-classes (:rewrite :type-prescription)
    :induct (mat-first-one a)
    :enable mat-first-one))

;;; The decoder: the candidate unit index of a, bounds-checked against the
;;; intended dimensions.  For a = (bit-mat-unit i j m n) with i < m, j < n
;;; this returns (i . j); the recognizer below then verifies the candidate
;;; exactly, so no further structure is checked here.

(define unit-index-of (a (m natp) (n natp))
  :returns (pos (or (null pos)
                    (and (consp pos) (natp (car pos)) (natp (cdr pos)))))
  (b* ((pos (mat-first-one a))
       ((unless pos) nil)
       (i (car pos))
       (j (cdr pos))
       ((unless (and (< i (nfix m)) (< j (nfix n)))) nil))
    pos)
  ///
  (defrule unit-index-of-shape
    (implies (unit-index-of a m n)
             (and (consp (unit-index-of a m n))
                  (natp (car (unit-index-of a m n)))
                  (natp (cdr (unit-index-of a m n)))
                  (< (car (unit-index-of a m n)) (nfix m))
                  (< (cdr (unit-index-of a m n)) (nfix n))))
    :enable unit-index-of))

;;; a IS some unit matrix (bit-mat-unit i j m n): well-dimensioned, with a
;;; decodable candidate index that reconstructs a exactly.

(define unit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  (b* ((pos (unit-index-of a m n)))
    (and (bit-matp a m n)
         (consp pos)
         (equal a (bit-mat-unit (car pos) (cdr pos) m n)))))

;;; A unit summand: dimensioned, with all three factors unit matrices.

(define unit-summandp (s (n natp))
  :returns (yes/no booleanp)
  (and (summand-dimp s n)
       (unit-matp (car s) n n)
       (unit-matp (cadr s) n n)
       (unit-matp (caddr s) n n)))

(define unit-summand-listp (l (n natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (unit-summandp (car l) n)
         (unit-summand-listp (cdr l) n))))

;;; Decoder correctness, encode-then-decode direction: the decoder reads
;;; the index pair back off a unit matrix.

(local
 (defruled bit-list-first-one-of-bit-listn0
   (equal (bit-list-first-one (bit-listn0 n)) nil)
   :induct (dec-induct n)
   :enable (bit-list-first-one bit-listn0 repeat)))

(local
 (defruled bit-list-first-one-of-bit-unit-list
   (implies (and (natp j) (natp n) (< j n))
            (equal (bit-list-first-one (bit-unit-list j n)) j))
   :induct (dec-dec-induct j n)
   :enable (bit-list-first-one bit-unit-list)))

(local
 (defruled mat-first-one-of-bit-mat-unit
   (implies (and (natp i) (natp j) (natp m) (natp n)
                 (< i m) (< j n))
            (equal (mat-first-one (bit-mat-unit i j m n)) (cons i j)))
   :induct (dec-dec-induct i m)
   :enable (mat-first-one bit-mat-unit
            bit-list-first-one-of-bit-listn0
            bit-list-first-one-of-bit-unit-list)))

(defrule unit-index-of-of-bit-mat-unit
  (implies (and (natp i) (natp j) (natp m) (natp n) (< i m) (< j n))
           (equal (unit-index-of (bit-mat-unit i j m n) m n) (cons i j)))
  :enable (unit-index-of mat-first-one-of-bit-mat-unit))

(defrule unit-matp-of-bit-mat-unit
  (implies (and (natp i) (natp j) (natp m) (natp n) (< i m) (< j n))
           (unit-matp (bit-mat-unit i j m n) m n))
  :enable (unit-matp))

;;; Decode-then-encode direction: a unit matrix is exactly the unit at its
;;; decoded index, and the decoded index is in range.

(defruled unit-matp-decode
  (implies (and (unit-matp a m n)
                (natp m) (natp n))
           (and (natp (car (unit-index-of a m n)))
                (natp (cdr (unit-index-of a m n)))
                (< (car (unit-index-of a m n)) m)
                (< (cdr (unit-index-of a m n)) n)
                (equal (bit-mat-unit (car (unit-index-of a m n))
                                     (cdr (unit-index-of a m n))
                                     m n)
                       a)))
  :enable (unit-matp)
  :use ((:instance unit-index-of-shape)))

(defrule bit-matp-when-unit-matp
  (implies (unit-matp a m n)
           (bit-matp a m n))
  :enable (unit-matp))

;;; A summand is the list of its three factors.

(local
 (defruled list-of-len-1
   (implies (and (true-listp x) (equal (len x) 1))
            (equal (list (car x)) x))))

(defruled summand-reconstruct
  (implies (mat-triplep s)
           (equal (list (car s) (cadr s) (caddr s)) s))
  :use ((:instance list-of-len-1 (x (cddr s)))))

;;; Injectivity through the decoders: two unit summands with the same
;;; decoded index triples are equal.

(defrule unit-summand-equal-when-equal-indices
  (implies (and (natp n)
                (unit-summandp s1 n) (unit-summandp s2 n)
                (equal (unit-index-of (car s1) n n)
                       (unit-index-of (car s2) n n))
                (equal (unit-index-of (cadr s1) n n)
                       (unit-index-of (cadr s2) n n))
                (equal (unit-index-of (caddr s1) n n)
                       (unit-index-of (caddr s2) n n)))
           (equal s1 s2))
  :rule-classes nil
  :do-not-induct t
  :enable (unit-summandp)
  :use ((:instance unit-matp-decode (a (car s1)) (m n) (n n))
        (:instance unit-matp-decode (a (car s2)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s1)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s2)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s1)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s2)) (m n) (n n))
        (:instance summand-reconstruct (s s1))
        (:instance summand-reconstruct (s s2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deliverable 2: the flat index of a unit summand and the support lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The flat index determined by the three decoded index pairs, with the
;;; same index arithmetic as nth-of-tensor: for factor indices (ia,ja),
;;; (ib,jb), (ic,jc), the index is
;;;   jc + ic*n + jb*n^2 + ib*n^3 + ja*n^4 + ia*n^5.
;;; On a unit summand this is the one position where its tensor holds a 1.

(define unit-flat-index ((s mat-triplep) (n natp))
  :returns (idx natp)
  (b* ((pa (unit-index-of (car s) n n))
       (pb (unit-index-of (cadr s) n n))
       (pc (unit-index-of (caddr s) n n))
       (ia (nfix (car pa)))
       (ja (nfix (cdr pa)))
       (ib (nfix (car pb)))
       (jb (nfix (cdr pb)))
       (ic (nfix (car pc)))
       (jc (nfix (cdr pc)))
       (n (nfix n)))
    (+ jc (* ic n) (* jb n n) (* ib n n n)
       (* ja n n n n) (* ia n n n n n))))

;;; Injectivity restated on the index components, as the support lemma's
;;; delta product delivers them.

(local
 (defrule equal-when-parts-equal
   (implies (and (consp p) (consp q)
                 (equal (car p) (car q))
                 (equal (cdr p) (cdr q)))
            (equal p q))
   :rule-classes nil))

(defrule unit-summand-equal-when-equal-index-components
  (implies (and (natp n)
                (unit-summandp s1 n) (unit-summandp s2 n)
                (equal (car (unit-index-of (car s1) n n))
                       (car (unit-index-of (car s2) n n)))
                (equal (cdr (unit-index-of (car s1) n n))
                       (cdr (unit-index-of (car s2) n n)))
                (equal (car (unit-index-of (cadr s1) n n))
                       (car (unit-index-of (cadr s2) n n)))
                (equal (cdr (unit-index-of (cadr s1) n n))
                       (cdr (unit-index-of (cadr s2) n n)))
                (equal (car (unit-index-of (caddr s1) n n))
                       (car (unit-index-of (caddr s2) n n)))
                (equal (cdr (unit-index-of (caddr s1) n n))
                       (cdr (unit-index-of (caddr s2) n n))))
           (equal s1 s2))
  :rule-classes nil
  :do-not-induct t
  :enable (unit-summandp unit-matp)
  :use (unit-summand-equal-when-equal-indices
        (:instance equal-when-parts-equal
                   (p (unit-index-of (car s1) n n))
                   (q (unit-index-of (car s2) n n)))
        (:instance equal-when-parts-equal
                   (p (unit-index-of (cadr s1) n n))
                   (q (unit-index-of (cadr s2) n n)))
        (:instance equal-when-parts-equal
                   (p (unit-index-of (caddr s1) n n))
                   (q (unit-index-of (caddr s2) n n)))))

;;; The flat index of a unit summand lies below n^6.

(defrule unit-flat-index-upper-bound
  (implies (and (unit-summandp s n) (natp n))
           (< (unit-flat-index s n) (* n n n n n n)))
  :rule-classes (:rewrite :linear)
  :do-not-induct t
  :enable (unit-flat-index unit-summandp)
  :use ((:instance unit-matp-decode (a (car s)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s)) (m n) (n n))
        (:instance flat-index-upper-bound
                   (ia (car (unit-index-of (car s) n n)))
                   (ja (cdr (unit-index-of (car s) n n)))
                   (ib (car (unit-index-of (cadr s) n n)))
                   (jb (cdr (unit-index-of (cadr s) n n)))
                   (ic (car (unit-index-of (caddr s) n n)))
                   (jc (cdr (unit-index-of (caddr s) n n)))
                   (n n))))

;;; Entry of a unit matrix as a delta in its decoded index.

(defruled mat-entry-of-unit-matp
  (implies (and (unit-matp x n n)
                (natp n) (natp a) (natp b) (< a n) (< b n))
           (equal (mat-entry a b x)
                  (if (and (equal a (car (unit-index-of x n n)))
                           (equal b (cdr (unit-index-of x n n))))
                      1 0)))
  :do-not-induct t
  :use ((:instance unit-matp-decode (a x) (m n) (n n))
        (:instance mat-entry-of-bit-mat-unit
                   (a a) (b b)
                   (i (car (unit-index-of x n n)))
                   (j (cdr (unit-index-of x n n)))
                   (m n) (n n)))
  :disable (mat-entry mat-entry-of-bit-mat-unit bit-mat-unit))

;;; THE support lemma: the tensor of a unit summand x, read at the flat
;;; index of a unit summand s, is 1 exactly when x = s.  Validated at n = 2
;;; (par-probe1.lsp): a unit summand's tensor holds a single 1, at its own
;;; flat index, and 0 at the flat index of any different unit summand.

(defruled nth-of-summand-tensor-of-unit-summands
  (implies (and (unit-summandp s n) (unit-summandp x n) (natp n))
           (equal (nth (unit-flat-index s n) (summand-tensor x))
                  (if (equal x s) 1 0)))
  :do-not-induct t
  :enable (unit-summandp unit-flat-index mat-entry-of-unit-matp)
  :disable (mat-entry tensor nth-of-tensor)
  :use ((:instance unit-summand-equal-when-equal-index-components
                   (s1 x) (s2 s))
        (:instance unit-matp-decode (a (car s)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s)) (m n) (n n))
        (:instance nth-of-tensor
                   (a (car x)) (b (cadr x)) (c (caddr x))
                   (ia (car (unit-index-of (car s) n n)))
                   (ja (cdr (unit-index-of (car s) n n)))
                   (ib (car (unit-index-of (cadr s) n n)))
                   (jb (cdr (unit-index-of (cadr s) n n)))
                   (ic (car (unit-index-of (caddr s) n n)))
                   (jc (cdr (unit-index-of (caddr s) n n)))
                   (n n))))

;;; Injectivity of the flat index: base-n digit blocks are injective, so
;;; the six digits are determined by the flat index, so distinct unit
;;; summands have distinct flat indices.

(local
 (defruled times-lower-bound2
   (implies (and (integerp i) (< 0 i) (natp k))
            (<= k (* i k)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defrule block-index-injective
   (implies (and (natp x1) (natp x2) (natp y1) (natp y2) (natp m)
                 (< x1 m) (< x2 m)
                 (equal (+ x1 (* y1 m)) (+ x2 (* y2 m))))
            (and (equal x1 x2) (equal y1 y2)))
   :rule-classes nil
   :do-not-induct t
   :use ((:instance times-lower-bound2 (i (- y1 y2)) (k m))
         (:instance times-lower-bound2 (i (- y2 y1)) (k m)))))

(local
 (defruled pair-index-upper-bound2
   (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
            (< (+ j (* i n)) (* n n)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(defrule flat-index-injective
  (implies (and (natp n)
                (natp ia1) (natp ja1) (natp ib1)
                (natp jb1) (natp ic1) (natp jc1)
                (< ia1 n) (< ja1 n) (< ib1 n) (< jb1 n) (< ic1 n) (< jc1 n)
                (natp ia2) (natp ja2) (natp ib2)
                (natp jb2) (natp ic2) (natp jc2)
                (< ia2 n) (< ja2 n) (< ib2 n) (< jb2 n) (< ic2 n) (< jc2 n)
                (equal (+ jc1 (* ic1 n) (* jb1 n n) (* ib1 n n n)
                          (* ja1 n n n n) (* ia1 n n n n n))
                       (+ jc2 (* ic2 n) (* jb2 n n) (* ib2 n n n)
                          (* ja2 n n n n) (* ia2 n n n n n))))
           (and (equal ia1 ia2) (equal ja1 ja2) (equal ib1 ib2)
                (equal jb1 jb2) (equal ic1 ic2) (equal jc1 jc2)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance block-index-injective
                   (x1 (+ jc1 (* ic1 n))) (x2 (+ jc2 (* ic2 n)))
                   (y1 (+ jb1 (* ib1 n) (* ja1 n n) (* ia1 n n n)))
                   (y2 (+ jb2 (* ib2 n) (* ja2 n n) (* ia2 n n n)))
                   (m (* n n)))
        (:instance block-index-injective
                   (x1 (+ jb1 (* ib1 n))) (x2 (+ jb2 (* ib2 n)))
                   (y1 (+ ja1 (* ia1 n))) (y2 (+ ja2 (* ia2 n)))
                   (m (* n n)))
        (:instance block-index-injective
                   (x1 jc1) (x2 jc2) (y1 ic1) (y2 ic2) (m n))
        (:instance block-index-injective
                   (x1 jb1) (x2 jb2) (y1 ib1) (y2 ib2) (m n))
        (:instance block-index-injective
                   (x1 ja1) (x2 ja2) (y1 ia1) (y2 ia2) (m n))
        (:instance pair-index-upper-bound2 (i ic1) (j jc1))
        (:instance pair-index-upper-bound2 (i ic2) (j jc2))
        (:instance pair-index-upper-bound2 (i ib1) (j jb1))
        (:instance pair-index-upper-bound2 (i ib2) (j jb2))))

(defrule unit-flat-index-injective
  (implies (and (natp n)
                (unit-summandp s1 n) (unit-summandp s2 n)
                (equal (unit-flat-index s1 n) (unit-flat-index s2 n)))
           (equal s1 s2))
  :rule-classes nil
  :do-not-induct t
  :enable (unit-flat-index unit-summandp)
  :use ((:instance unit-matp-decode (a (car s1)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s1)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s1)) (m n) (n n))
        (:instance unit-matp-decode (a (car s2)) (m n) (n n))
        (:instance unit-matp-decode (a (cadr s2)) (m n) (n n))
        (:instance unit-matp-decode (a (caddr s2)) (m n) (n n))
        (:instance unit-summand-equal-when-equal-index-components)
        (:instance flat-index-injective
                   (ia1 (car (unit-index-of (car s1) n n)))
                   (ja1 (cdr (unit-index-of (car s1) n n)))
                   (ib1 (car (unit-index-of (cadr s1) n n)))
                   (jb1 (cdr (unit-index-of (cadr s1) n n)))
                   (ic1 (car (unit-index-of (caddr s1) n n)))
                   (jc1 (cdr (unit-index-of (caddr s1) n n)))
                   (ia2 (car (unit-index-of (car s2) n n)))
                   (ja2 (cdr (unit-index-of (car s2) n n)))
                   (ib2 (car (unit-index-of (cadr s2) n n)))
                   (jb2 (cdr (unit-index-of (cadr s2) n n)))
                   (ic2 (car (unit-index-of (caddr s2) n n)))
                   (jc2 (cdr (unit-index-of (caddr s2) n n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deliverable 3: the parity theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count-occurrences (s l)
  :returns (c natp)
  (cond ((atom l) 0)
        ((equal s (car l)) (+ 1 (count-occurrences s (cdr l))))
        (t (count-occurrences s (cdr l)))))

;;; Bridges from the unit-summand recognizers.

(defrule summand-dim-listp-when-unit-summand-listp
  (implies (unit-summand-listp l n)
           (summand-dim-listp l n))
  :induct (cdr-induct l)
  :enable (unit-summand-listp unit-summandp))

(defruled unit-summandp-when-member
  (implies (and (unit-summand-listp l n) (member-equal s l))
           (unit-summandp s n))
  :induct (cdr-induct l)
  :enable (unit-summand-listp))

;;; Parity of a successor.

(defruled evenp-of-plus-1
  (implies (natp c)
           (equal (evenp (+ 1 c)) (not (evenp c))))
  :induct (dec-induct c)
  :enable (evenp))

;;; The xor fold over the list, read at s's flat index, is the parity of
;;; the number of occurrences of s: by the support lemma each summand
;;; contributes 1 exactly when it IS s.  Validated at n = 2 in
;;; par-probe1.lsp (a list with s three times and other units once gives
;;; entry 1; with s twice, entry 0).

(defruled scheme-sum-entry-at-unit-flat-index
  (implies (and (unit-summand-listp l n) (unit-summandp s n) (natp n))
           (equal (scheme-sum-entry (unit-flat-index s n) l)
                  (if (evenp (count-occurrences s l)) 0 1)))
  :induct (cdr-induct l)
  :enable (scheme-sum-entry count-occurrences unit-summand-listp
           nth-of-summand-tensor-of-unit-summands evenp-of-plus-1)
  :disable (summand-tensor tensor mat-entry unit-flat-index evenp))

;;; THE PARITY THEOREM (companion lemma:zero-subset, parity step): in a
;;; list of unit summands whose scheme-sum is zero, every member occurs an
;;; even number of times.  Proof: read the zero sum at the member's flat
;;; index; the entry there is the parity of its occurrence count.

(defrule even-count-occurrences-when-zero-scheme-sum
  (implies (and (unit-summand-listp l n) (natp n)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n)))
                (member-equal s l))
           (evenp (count-occurrences s l)))
  :do-not-induct t
  :disable (scheme-sum unit-flat-index count-occurrences
            unit-summand-listp nth-of-bit-listn0)
  :use ((:instance unit-summandp-when-member)
        (:instance summand-dim-listp-when-unit-summand-listp)
        (:instance unit-flat-index-upper-bound)
        (:instance nth-of-scheme-sum (idx (unit-flat-index s n)))
        (:instance scheme-sum-entry-at-unit-flat-index)
        (:instance nth-of-bit-listn0
                   (i (unit-flat-index s n))
                   (k (* n n n n n n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deliverable 4: the obag hook
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; On a bagp (an ordered list), occs and in walk the list itself, so they
;;; agree with count-occurrences and member-equal.

(defruled occs-is-count-occurrences
  (implies (obag::bagp l)
           (equal (obag::occs s l) (count-occurrences s l)))
  :induct (cdr-induct l)
  :enable (count-occurrences
           obag::occs obag::head obag::tail obag::emptyp
           obag::bfix obag::bagp))

(defruled in-is-member-equal
  (implies (obag::bagp l)
           (iff (obag::in s l) (member-equal s l)))
  :induct (cdr-induct l)
  :enable (obag::in obag::head obag::tail obag::emptyp
           obag::bfix obag::bagp))

;;; The obag corollary of the parity theorem: an obag of unit summands
;;; with zero scheme-sum has even multiplicity at every member.

(defrule even-occs-when-zero-scheme-sum
  (implies (and (obag::bagp l)
                (unit-summand-listp l n) (natp n)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n)))
                (obag::in s l))
           (evenp (obag::occs s l)))
  :do-not-induct t
  :disable (scheme-sum count-occurrences unit-summand-listp evenp)
  :use ((:instance occs-is-count-occurrences)
        (:instance in-is-member-equal)
        (:instance even-count-occurrences-when-zero-scheme-sum)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The general-index support lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The full form of the support lemma: the tensor of a unit summand is 1
;;; at its flat index and 0 at every other index below n^6.  The proof
;;; decomposes an arbitrary index into its six base-n digits (floor/mod
;;; facts from ihs, scoped to this encapsulate), evaluates the entry as a
;;; delta product over those digits, and identifies "all six deltas hold"
;;; with "idx = unit-flat-index" through flat-index-injective.  Validated
;;; at n = 2 in par-probe1.lsp (each unit summand's tensor holds exactly
;;; one 1, at its flat index).

(encapsulate
  ()
  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (in-theory (disable floor mod)))

  (local
   (defruled fm-elim
     (implies (and (natp x) (posp m))
              (equal (+ (mod x m) (* m (floor x m))) x))))

  (local
   (defruled mod-bounds2
     (implies (and (natp x) (posp m))
              (and (natp (mod x m)) (< (mod x m) m)))))

  (local
   (defruled floor-nat2
     (implies (and (natp x) (posp m))
              (natp (floor x m)))))

  (local
   (defruled floor-upper2
     (implies (and (natp x) (posp m) (posp k) (< x (* m k)))
              (< (floor x m) k))
     :hints (("Goal" :nonlinearp t
              :use ((:instance floor-bounded-by-/ (x x) (y m)))))))

  (local
   (defruled floor-floor2
     (implies (and (natp x) (posp m) (posp k))
              (equal (floor (floor x m) k) (floor x (* m k))))))

  (local
   (defrule scale-eq
     (implies (equal a b)
              (equal (* c a) (* c b)))
     :rule-classes nil))

  ;; The floor-mod elimination, pre-scaled by a constant factor, so the
  ;; five level equations chain by linear arithmetic alone.

  (local
   (defrule fm-elim-scaled
     (implies (and (natp x) (posp m) (natp c))
              (equal (+ (* c (mod x m)) (* c m (floor x m))) (* c x)))
     :rule-classes nil
     :use ((:instance fm-elim)
           (:instance scale-eq (a (+ (mod x m) (* m (floor x m))))
                      (b x) (c c)))))

  ;; The base-n digits of idx < n^6 are in range and reconstruct idx.

  (local
   (defrule digit-decomposition
     (implies (and (natp idx) (posp n) (< idx (* n n n n n n)))
              (and (natp (mod idx n)) (< (mod idx n) n)
                   (natp (mod (floor idx n) n))
                   (< (mod (floor idx n) n) n)
                   (natp (mod (floor idx (* n n)) n))
                   (< (mod (floor idx (* n n)) n) n)
                   (natp (mod (floor idx (* n n n)) n))
                   (< (mod (floor idx (* n n n)) n) n)
                   (natp (mod (floor idx (* n n n n)) n))
                   (< (mod (floor idx (* n n n n)) n) n)
                   (natp (floor idx (* n n n n n)))
                   (< (floor idx (* n n n n n)) n)
                   (equal (+ (mod idx n)
                             (* (mod (floor idx n) n) n)
                             (* (mod (floor idx (* n n)) n) n n)
                             (* (mod (floor idx (* n n n)) n) n n n)
                             (* (mod (floor idx (* n n n n)) n) n n n n)
                             (* (floor idx (* n n n n n)) n n n n n))
                          idx)))
     :rule-classes nil
     :do-not-induct t
     :use ((:instance fm-elim-scaled (x idx) (m n) (c 1))
           (:instance fm-elim-scaled (x (floor idx n)) (m n) (c n))
           (:instance fm-elim-scaled (x (floor idx (* n n))) (m n)
                      (c (* n n)))
           (:instance fm-elim-scaled (x (floor idx (* n n n))) (m n)
                      (c (* n n n)))
           (:instance fm-elim-scaled (x (floor idx (* n n n n))) (m n)
                      (c (* n n n n)))
           (:instance floor-floor2 (x idx) (m n) (k n))
           (:instance floor-floor2 (x idx) (m (* n n)) (k n))
           (:instance floor-floor2 (x idx) (m (* n n n)) (k n))
           (:instance floor-floor2 (x idx) (m (* n n n n)) (k n))
           (:instance floor-nat2 (x idx) (m n))
           (:instance floor-nat2 (x idx) (m (* n n)))
           (:instance floor-nat2 (x idx) (m (* n n n)))
           (:instance floor-nat2 (x idx) (m (* n n n n)))
           (:instance floor-nat2 (x idx) (m (* n n n n n)))
           (:instance mod-bounds2 (x idx) (m n))
           (:instance mod-bounds2 (x (floor idx n)) (m n))
           (:instance mod-bounds2 (x (floor idx (* n n))) (m n))
           (:instance mod-bounds2 (x (floor idx (* n n n))) (m n))
           (:instance mod-bounds2 (x (floor idx (* n n n n))) (m n))
           (:instance floor-upper2 (x idx) (m (* n n n n n)) (k n)))))

  ;; The general-index support lemma.

)
