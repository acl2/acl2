; Completeness: every list of matrix triples that multiplies matrices is,
; once its zero summands are dropped, a correct scheme.
;
; This is the converse of adequacy (adequacy.lisp).  A list l of n x n
; matrix triples (A, B, C) denotes the algorithm eval-scheme: on inputs D
; and F it forms (A . D)(B . F) for each triple and returns the sum of the
; products scaled onto the C factors.  Theorem completeness says that if
; this algorithm returns D F for all n x n inputs D and F (the quantified
; computes-productp), then the bag of the nonzero triples of l
; (list-to-scheme) is a correct scheme: it is well formed and its tensor is
; the matrix multiplication tensor mm-tensor.
;
; The argument is entrywise.  Only the n^4 pairs of unit inputs
; (E_ia,ja, E_ib,jb) matter: the executable agrees-on-unitsp checks the
; algorithm against the product on all of them, and the quantified
; hypothesis implies it (agrees-on-unitsp-when-computes-productp).  On unit
; inputs the inner products (A . E_ia,ja) and (B . E_ib,jb) read off the
; entries A[ia,ja] and B[ib,jb], so entry (ic, jc) of the algorithm's output
; is the xor over the triples of A[ia,ja] B[ib,jb] C[ic,jc], which is entry
; (ia,ja,ib,jb,ic,jc) of the list's scheme-sum by the entry law nth-of-tensor
; (mat-entry-of-eval-scheme-at-units).  On the other side, entry (ic, jc) of
; E_ia,ja E_ib,jb is [ic = ia][ja = ib][jc = jb], which is the same entry of
; mm-tensor by nth-of-mm-tensor.  So the two flat n^6-bit tensors agree at
; every six-digit index, hence at every index below n^6 (digit
; decomposition), hence are equal (first-diff-index):
; scheme-sum-when-agrees-on-units.  Dropping zero summands and moving to a
; bag does not change the scheme-sum (scheme-sum-of-list-to-scheme), and
; the result is a scheme (schemep-of-list-to-scheme) of rank at most the
; length of the list (scheme-rank-of-list-to-scheme).
;
; Validated by execution at n = 2 before proving: on the standard scheme
; and on a hand-made list with a zero summand and a duplicated summand,
; agreement holds, list-to-scheme is correct, and every intermediate
; identity holds at all 64 six-digit indices; the checks are the local
; assert-event forms at the end.

(in-package "ACL2")

(include-book "adequacy")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; bitxor-of-0-arg1 rewrites (bitxor 0 x) to (getbit 0 x); this puts it back
;; when x is known to be a bit (as in adequacy.lisp).
(local
 (defrule getbit-0-of-bit
   (implies (bitp x)
            (equal (getbit 0 x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: agreement on unit inputs, the scheme a list denotes, and the
;;; correctness of the algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The algorithm agrees with the product on all pairs of unit inputs
;;; (E_gh, E_ij) with g, h, i, j < n, as four nested downward recursions in
;;; the style of mm-tensor-3/2/1: level 4 runs j, level 3 runs i, level 2
;;; runs h, level 1 runs g.

(define agrees-on-units-4 ((l mat-triple-listp) (g natp) (h natp) (i natp)
                           (j natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp j)
      t
    (and (equal (eval-scheme l (bit-mat-unit g h n n) (bit-mat-unit i (1- j) n n) n)
                (bit-mat-mul (bit-mat-unit g h n n) (bit-mat-unit i (1- j) n n) n))
         (agrees-on-units-4 l g h i (1- j) n))))

(define agrees-on-units-3 ((l mat-triple-listp) (g natp) (h natp) (i natp)
                           (n natp))
  :returns (yes/no booleanp)
  (if (zp i)
      t
    (and (agrees-on-units-4 l g h (1- i) n n)
         (agrees-on-units-3 l g h (1- i) n))))

(define agrees-on-units-2 ((l mat-triple-listp) (g natp) (h natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp h)
      t
    (and (agrees-on-units-3 l g (1- h) n n)
         (agrees-on-units-2 l g (1- h) n))))

(define agrees-on-units-1 ((l mat-triple-listp) (g natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp g)
      t
    (and (agrees-on-units-2 l (1- g) n n)
         (agrees-on-units-1 l (1- g) n))))

(define agrees-on-unitsp ((l mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  (agrees-on-units-1 l n n))

;;; The scheme a list denotes: its summands as a bag, zero summands dropped.

(define list-to-scheme ((l mat-triple-listp) (n natp))
  :returns (sch obag::bagp)
  (insert-all-nonzero l nil n))

;;; The algorithm is correct: it returns the product on all n x n inputs.
;;; This is the only quantifier in the development; it is here so that the
;;; final theorem reads "if the algorithm is correct".

(defun-sk computes-productp (l n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-scheme l d f n)
                          (bit-mat-mul d f n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: agreement on all unit pairs gives agreement at each pair
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Level by level: a level's check covers every smaller index at its own
;;; position and every index below n at the positions inside it.

(defruled agrees-on-units-4-implies
  (implies (and (agrees-on-units-4 l g h i j n)
                (natp j) (natp jj) (< jj j))
           (equal (eval-scheme l (bit-mat-unit g h n n) (bit-mat-unit i jj n n) n)
                  (bit-mat-mul (bit-mat-unit g h n n) (bit-mat-unit i jj n n) n)))
  :induct (agrees-on-units-4 l g h i j n)
  :enable agrees-on-units-4
  :disable (eval-scheme bit-mat-mul bit-mat-unit))

(defruled agrees-on-units-3-implies
  (implies (and (agrees-on-units-3 l g h i n)
                (natp n) (natp i) (natp ii) (natp jj) (< ii i) (< jj n))
           (equal (eval-scheme l (bit-mat-unit g h n n) (bit-mat-unit ii jj n n) n)
                  (bit-mat-mul (bit-mat-unit g h n n) (bit-mat-unit ii jj n n) n)))
  :induct (agrees-on-units-3 l g h i n)
  :enable (agrees-on-units-3 agrees-on-units-4-implies)
  :disable (eval-scheme bit-mat-mul bit-mat-unit))

(defruled agrees-on-units-2-implies
  (implies (and (agrees-on-units-2 l g h n)
                (natp n) (natp h) (natp hh) (natp ii) (natp jj)
                (< hh h) (< ii n) (< jj n))
           (equal (eval-scheme l (bit-mat-unit g hh n n) (bit-mat-unit ii jj n n) n)
                  (bit-mat-mul (bit-mat-unit g hh n n) (bit-mat-unit ii jj n n) n)))
  :induct (agrees-on-units-2 l g h n)
  :enable (agrees-on-units-2 agrees-on-units-3-implies)
  :disable (eval-scheme bit-mat-mul bit-mat-unit))

(defruled agrees-on-units-1-implies
  (implies (and (agrees-on-units-1 l g n)
                (natp n) (natp g) (natp gg) (natp hh) (natp ii) (natp jj)
                (< gg g) (< hh n) (< ii n) (< jj n))
           (equal (eval-scheme l (bit-mat-unit gg hh n n) (bit-mat-unit ii jj n n) n)
                  (bit-mat-mul (bit-mat-unit gg hh n n) (bit-mat-unit ii jj n n) n)))
  :induct (agrees-on-units-1 l g n)
  :enable (agrees-on-units-1 agrees-on-units-2-implies)
  :disable (eval-scheme bit-mat-mul bit-mat-unit))

(defruled agrees-on-unitsp-implies
  (implies (and (agrees-on-unitsp l n)
                (natp n) (natp g) (natp h) (natp i) (natp j)
                (< g n) (< h n) (< i n) (< j n))
           (equal (eval-scheme l (bit-mat-unit g h n n) (bit-mat-unit i j n n) n)
                  (bit-mat-mul (bit-mat-unit g h n n) (bit-mat-unit i j n n) n)))
  :enable (agrees-on-unitsp agrees-on-units-1-implies)
  :disable (eval-scheme bit-mat-mul bit-mat-unit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: the entry chain at a pair of unit inputs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The index letters follow nth-of-tensor (ia ja ib jb ic jc): the first
;;; unit is E_ia,ja, the second E_ib,jb, and (ic, jc) is the output entry.
;;; (Letters sorting after n would be normalized to (* n ic) and miss the
;;; (* ic n) pattern of the entry laws.)

;;; The inner product with a unit matrix in the second position reads off
;;; an entry; adequacy.lisp has the first-position form.

(defruled bit-list-dot-commutative
  (equal (bit-list-dot x y)
         (bit-list-dot y x))
  :induct (cdr-cdr-induct x y)
  :enable bit-list-dot)

(defruled mat-dot-of-bit-mat-unit-arg2
  (implies (and (bit-matp a n n)
                (natp n) (natp ib) (natp jb)
                (< ib n) (< jb n))
           (equal (mat-dot a (bit-mat-unit ib jb n n))
                  (mat-entry ib jb a)))
  :do-not-induct t
  :enable (mat-dot)
  :use ((:instance bit-list-dot-commutative
                   (x (mat-flat a)) (y (mat-flat (bit-mat-unit ib jb n n))))
        (:instance mat-dot-of-bit-mat-unit (d a) (i ib) (j jb)))
  :disable (mat-entry))

;;; mat-entry-of-bit-mat-add and mat-entry-of-bit-mat-scale carry their
;;; dimensions as free variables; this form binds n through the eval-scheme
;;; term, in the shape the induction below produces.

(defruled mat-entry-of-bit-mat-add-scale-eval-scheme
  (implies (and (bit-matp c n n)
                (summand-dim-listp sch n)
                (natp n) (natp ic) (natp jc) (< ic n) (< jc n))
           (equal (mat-entry ic jc (bit-mat-add (bit-mat-scale s c)
                                                (eval-scheme sch d f n)))
                  (bitxor (bitand s (mat-entry ic jc c))
                          (mat-entry ic jc (eval-scheme sch d f n)))))
  :do-not-induct t
  :disable (mat-entry)
  :use ((:instance mat-entry-of-bit-mat-add
                   (x (bit-mat-scale s c)) (y (eval-scheme sch d f n))
                   (m n) (i ic) (j jc))
        (:instance mat-entry-of-bit-mat-scale
                   (b s) (a c) (m n) (i ic) (j jc))))

;;; Entry (ic, jc) of the algorithm's output on unit inputs is the
;;; scheme-sum entry at the flat index of (ia,ja,ib,jb,ic,jc): each summand
;;; contributes A[ia,ja] B[ib,jb] C[ic,jc], by nth-of-tensor.

(defruled mat-entry-of-eval-scheme-at-units
  (implies (and (summand-dim-listp l n)
                (natp n) (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (mat-entry ic jc (eval-scheme l (bit-mat-unit ia ja n n)
                                                (bit-mat-unit ib jb n n) n))
                  (scheme-sum-entry (+ jc (* ic n) (* jb n n) (* ib n n n)
                                       (* ja n n n n) (* ia n n n n n))
                                    l)))
  :induct (eval-scheme l (bit-mat-unit ia ja n n) (bit-mat-unit ib jb n n) n)
  :enable (eval-scheme scheme-sum-entry
           mat-entry-of-bit-mat-add-scale-eval-scheme
           mat-dot-of-bit-mat-unit-arg2
           bitand-commutative-2)
  :disable (mat-entry tensor bit-mat-unit))

;;; The product of two unit matrices, entrywise: E_ia,ja E_ib,jb has a 1 at
;;; (ia, jb) when ja = ib and is zero otherwise.

(defruled mat-mul-entry-of-units
  (implies (and (natp n) (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (natp hh)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n) (<= hh n))
           (equal (mat-mul-entry (bit-mat-unit ia ja n n) (bit-mat-unit ib jb n n)
                                 ic jc hh n)
                  (if (and (equal ic ia) (equal ja ib) (equal jc jb) (< ja hh)) 1 0)))
  :induct (mat-mul-entry (bit-mat-unit ia ja n n) (bit-mat-unit ib jb n n) ic jc hh n)
  :enable (mat-mul-entry)
  :disable (mat-entry bit-mat-unit))

(defruled mat-entry-of-bit-mat-mul-of-units
  (implies (and (natp n) (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (mat-entry ic jc (bit-mat-mul (bit-mat-unit ia ja n n)
                                                (bit-mat-unit ib jb n n) n))
                  (if (and (equal ic ia) (equal ja ib) (equal jc jb)) 1 0)))
  :do-not-induct t
  :enable (mat-mul-entry-of-units)
  :disable (mat-entry bit-mat-unit bit-mat-mul)
  :use ((:instance mat-entry-of-bit-mat-mul
                   (d (bit-mat-unit ia ja n n)) (f (bit-mat-unit ib jb n n))
                   (k ic) (l jc))))

;;; The entrywise chain at the flat index of (ia,ja,ib,jb,ic,jc): entry of
;;; scheme-sum [nth-of-scheme-sum] = entry of the algorithm's output
;;; [mat-entry-of-eval-scheme-at-units] = entry of the product of the units
;;; [agreement] = delta = entry of mm-tensor [nth-of-mm-tensor].

(defruled nth-of-scheme-sum-when-agrees-at-pair
  (implies (and (summand-dim-listp l n)
                (natp n) (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n)
                (equal (eval-scheme l (bit-mat-unit ia ja n n) (bit-mat-unit ib jb n n) n)
                       (bit-mat-mul (bit-mat-unit ia ja n n) (bit-mat-unit ib jb n n) n)))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n) (* ja n n n n) (* ia n n n n n))
                       (scheme-sum l n))
                  (nth (+ jc (* ic n) (* jb n n) (* ib n n n) (* ja n n n n) (* ia n n n n n))
                       (mm-tensor n))))
  :do-not-induct t
  :disable (mat-entry bit-mat-unit bit-mat-mul eval-scheme scheme-sum mm-tensor
            tensor nth-of-scheme-sum)
  :use ((:instance nth-of-scheme-sum
                   (idx (+ jc (* ic n) (* jb n n) (* ib n n n) (* ja n n n n) (* ia n n n n n))))
        (:instance flat-index-upper-bound)
        (:instance mat-entry-of-eval-scheme-at-units)
        (:instance mat-entry-of-bit-mat-mul-of-units)
        (:instance nth-of-mm-tensor)))

(defruled nth-of-scheme-sum-when-agrees-on-units
  (implies (and (summand-dim-listp l n)
                (agrees-on-unitsp l n)
                (natp n) (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n) (* ja n n n n) (* ia n n n n n))
                       (scheme-sum l n))
                  (nth (+ jc (* ic n) (* jb n n) (* ib n n n) (* ja n n n n) (* ia n n n n n))
                       (mm-tensor n))))
  :do-not-induct t
  :disable (mat-entry bit-mat-unit bit-mat-mul eval-scheme scheme-sum mm-tensor)
  :use ((:instance agrees-on-unitsp-implies (g ia) (h ja) (i ib) (j jb))
        nth-of-scheme-sum-when-agrees-at-pair))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: every index below n^6, and the flat-list extensionality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Any index below n^6 is a six-digit index: its base-n digits are in
;;; range and reconstruct it.  The floor/mod facts come from ihs, scoped to
;;; this encapsulate; the construction is the one parity.lisp uses for its
;;; general-index support lemma.

(encapsulate
  ()
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

  ;; The two tensors agree at every index below n^6.

  (defruled nth-of-scheme-sum-when-agrees-on-units-any-index
    (implies (and (summand-dim-listp l n)
                  (agrees-on-unitsp l n)
                  (natp n) (< 0 n)
                  (natp idx) (< idx (* n n n n n n)))
             (equal (nth idx (scheme-sum l n))
                    (nth idx (mm-tensor n))))
    :do-not-induct t
    :disable (scheme-sum mm-tensor floor mod)
    :use ((:instance digit-decomposition)
          (:instance nth-of-scheme-sum-when-agrees-on-units
                     (ia (floor idx (* n n n n n)))
                     (ja (mod (floor idx (* n n n n)) n))
                     (ib (mod (floor idx (* n n n)) n))
                     (jb (mod (floor idx (* n n)) n))
                     (ic (mod (floor idx n) n))
                     (jc (mod idx n))))))

;;; Theorem 1: two bit lists of length n^6 that agree at every index are
;;; equal.  Were they unequal, first-diff-index would give a valid index
;;; where they differ (first-diff-index-bound, nth-of-first-diff-index in
;;; span.lisp), contradicting the previous lemma there.

(defrule scheme-sum-when-agrees-on-units
  (implies (and (summand-dim-listp l n)
                (natp n) (< 0 n)
                (agrees-on-unitsp l n))
           (equal (scheme-sum l n)
                  (mm-tensor n)))
  :do-not-induct t
  :disable (scheme-sum mm-tensor)
  :use ((:instance first-diff-index-bound
                   (x (scheme-sum l n)) (y (mm-tensor n)))
        (:instance nth-of-first-diff-index
                   (x (scheme-sum l n)) (y (mm-tensor n)))
        (:instance nth-of-scheme-sum-when-agrees-on-units-any-index
                   (idx (first-diff-index (scheme-sum l n) (mm-tensor n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 5: the scheme a list denotes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Inserting the nonzero summands of l into a scheme s adds the sum of l:
;;; a zero summand has the zero tensor (tensor-when-zero-a/b/c) and
;;; insertion into a bag adds the tensor (scheme-sum-of-insert).

(defruled scheme-sum-of-insert-all-nonzero
  (implies (and (obag::bagp s)
                (summand-listp s n)
                (summand-dim-listp l n)
                (natp n))
           (equal (scheme-sum (insert-all-nonzero l s n) n)
                  (bit-list-add (scheme-sum l n) (scheme-sum s n))))
  :induct (insert-all-nonzero l s n)
  :enable (insert-all-nonzero scheme-sum scheme-sum-of-insert
           tensor-when-zero-a tensor-when-zero-b tensor-when-zero-c
           bit-list-add-associative)
  :disable (tensor))

;;; Theorem 2.

(defrule scheme-sum-of-list-to-scheme
  (implies (and (summand-dim-listp l n)
                (natp n))
           (equal (scheme-sum (list-to-scheme l n) n)
                  (scheme-sum l n)))
  :do-not-induct t
  :enable (list-to-scheme)
  :use ((:instance scheme-sum-of-insert-all-nonzero (s nil)))
  :expand ((scheme-sum nil n)))

;;; Theorem 3.

(defrule schemep-of-list-to-scheme
  (implies (and (summand-dim-listp l n)
                (natp n))
           (schemep (list-to-scheme l n) n))
  :do-not-induct t
  :enable (list-to-scheme)
  :use ((:instance schemep-of-insert-all-nonzero (s nil))))

;;; Theorem 4.  schemep stays closed so that Theorem 3 applies to it (both
;;; correct-schemep and schemep are non-recursive and would otherwise be
;;; expanded before the rewriter sees them).

(defrule correct-schemep-when-agrees-on-units
  (implies (and (summand-dim-listp l n)
                (natp n) (< 0 n)
                (agrees-on-unitsp l n))
           (correct-schemep (list-to-scheme l n) n))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (list-to-scheme scheme-sum mm-tensor schemep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 6: completeness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The quantified hypothesis at a pair of inputs, as a rewrite rule.  (The
;;; -necc theorem of a defun-sk rewrites its whole quantified body, so it
;;; never fires on its own.)

(defruled eval-scheme-when-computes-productp
  (implies (and (computes-productp l n)
                (bit-matp d n n)
                (bit-matp f n n))
           (equal (eval-scheme l d f n)
                  (bit-mat-mul d f n)))
  :use computes-productp-necc)

;;; Level by level, along the recursions of agrees-on-unitsp.

(defruled agrees-on-units-4-when-computes-productp
  (implies (and (computes-productp l n) (natp n))
           (agrees-on-units-4 l g h i j n))
  :induct (agrees-on-units-4 l g h i j n)
  :enable (agrees-on-units-4 eval-scheme-when-computes-productp)
  :disable (eval-scheme bit-mat-mul bit-mat-unit computes-productp))

(defruled agrees-on-units-3-when-computes-productp
  (implies (and (computes-productp l n) (natp n))
           (agrees-on-units-3 l g h i n))
  :induct (agrees-on-units-3 l g h i n)
  :enable (agrees-on-units-3 agrees-on-units-4-when-computes-productp)
  :disable (computes-productp))

(defruled agrees-on-units-2-when-computes-productp
  (implies (and (computes-productp l n) (natp n))
           (agrees-on-units-2 l g h n))
  :induct (agrees-on-units-2 l g h n)
  :enable (agrees-on-units-2 agrees-on-units-3-when-computes-productp)
  :disable (computes-productp))

(defruled agrees-on-units-1-when-computes-productp
  (implies (and (computes-productp l n) (natp n))
           (agrees-on-units-1 l g n))
  :induct (agrees-on-units-1 l g n)
  :enable (agrees-on-units-1 agrees-on-units-2-when-computes-productp)
  :disable (computes-productp))

;;; Theorem 5a.

(defrule agrees-on-unitsp-when-computes-productp
  (implies (and (summand-dim-listp l n)
                (natp n)
                (computes-productp l n))
           (agrees-on-unitsp l n))
  :enable (agrees-on-unitsp agrees-on-units-1-when-computes-productp)
  :disable (computes-productp))

;;; Theorem 5b, the headline: a correct algorithm is a correct scheme.

(defrule completeness
  (implies (and (summand-dim-listp l n)
                (natp n) (< 0 n)
                (computes-productp l n))
           (correct-schemep (list-to-scheme l n) n))
  :do-not-induct t
  :disable (list-to-scheme computes-productp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 7: the rank bound
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Insertion into a bag adds one element; dropping zero summands can only
;;; lose some.

(defruled len-of-insert-bag
  (implies (obag::bagp s)
           (equal (len (obag::insert x s))
                  (+ 1 (len s))))
  :induct (obag::insert x s)
  :enable (obag::insert obag::bagp obag::head obag::tail
           obag::emptyp obag::bfix))

(defruled len-of-insert-all-nonzero
  (implies (obag::bagp s)
           (<= (len (insert-all-nonzero l s n))
               (+ (len l) (len s))))
  :induct (insert-all-nonzero l s n)
  :enable (insert-all-nonzero len-of-insert-bag))

;;; Theorem 6.

(defrule scheme-rank-of-list-to-scheme
  (<= (scheme-rank (list-to-scheme l n))
      (len l))
  :enable (list-to-scheme scheme-rank)
  :use ((:instance len-of-insert-all-nonzero (s nil))))
