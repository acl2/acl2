; The entry characterization of the matrix multiplication tensor
; (companion lemma:mmt).
;
; Stage 1: matrix-level entry lemmas -- mat-entry through bit-mat-add,
; bit-mat0, and bit-mat-unit (delta form).
;
; Stage 2: entry characterization of the matrix multiplication tensor
; (companion lemma:mmt): the entry of (mm-tensor n) at the flat index of
; ((ia,ja),(ib,jb),(ic,jc)) is 1 exactly when ja = ib, ia = ic and jb = jc.

(in-package "ACL2")

(include-book "entry")
(include-book "mm-tensor")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 1: matrix-level entry lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Rows of a dimensioned matrix are dimensioned bit lists.  The core states
;;; the row count as (len x) so its hypotheses are stable under cdr-dec
;;; induction; the exported form recovers the m-statement via len-of-bit-matp.

(local
 (defruled bit-listnp-of-nth-when-bit-matp-core
   (implies (and (bit-matp x (len x) n)
                 (< (nfix i) (len x)))
            (bit-listnp (nth i x) n))
   :induct (cdr-dec-induct x i)
   :enable bit-matp))

(defrule bit-listnp-of-nth-when-bit-matp
  (implies (and (bit-matp x m n)
                (natp m)
                (< (nfix i) m))
           (bit-listnp (nth i x) n))
  :do-not-induct t
  :use (bit-listnp-of-nth-when-bit-matp-core
        (:instance len-of-bit-matp (a x))))

;;; nth through bit-mat-add, at the row level.

(defruled nth-row-of-bit-mat-add
  (implies (and (< (nfix i) (len x))
                (< (nfix i) (len y)))
           (equal (nth i (bit-mat-add x y))
                  (bit-list-add (nth i x) (nth i y))))
  :induct (list (cdr-dec-induct x i) (cdr-dec-induct y i))
  :enable bit-mat-add)

;;; Entry of a sum is the xor of the entries.

(defrule mat-entry-of-bit-mat-add
  (implies (and (bit-matp x m n)
                (bit-matp y m n)
                (natp m) (natp n)
                (natp i) (natp j)
                (< i m) (< j n))
           (equal (mat-entry i j (bit-mat-add x y))
                  (bitxor (mat-entry i j x) (mat-entry i j y))))
  :do-not-induct t
  :use ((:instance nth-row-of-bit-mat-add)
        (:instance len-of-bit-matp (a x))
        (:instance len-of-bit-matp (a y))
        (:instance bit-listnp-of-nth-when-bit-matp (x x))
        (:instance bit-listnp-of-nth-when-bit-matp (x y))
        (:instance len-of-bit-listnp (x (nth i x)))
        (:instance len-of-bit-listnp (x (nth i y)))))

;;; Entries of the zero matrix, via its rows.

(defruled nth-row-of-bit-mat0
  (implies (< (nfix a) (nfix m))
           (equal (nth a (bit-mat0 m n))
                  (bit-listn0 n)))
  :enable (bit-mat0))

(defrule mat-entry-of-bit-mat0
  (implies (and (natp i) (natp j)
                (< i (nfix m)) (< j (nfix n)))
           (equal (mat-entry i j (bit-mat0 m n))
                  0))
  :enable (nth-row-of-bit-mat0))

;;; Entries of the unit matrix: a delta.  Row a of e_ij is the unit list at
;;; column j when a = i and the zero list otherwise; a unit list is a delta
;;; in its own index.

(defruled nth-row-of-bit-mat-unit
  (implies (and (natp a) (natp i) (natp m)
                (< a m) (< i m))
           (equal (nth a (bit-mat-unit i j m n))
                  (if (equal a i)
                      (bit-unit-list j n)
                    (bit-listn0 n))))
  :induct (list (dec-dec-induct a i) (dec-dec-induct a m))
  :enable (bit-mat-unit nth-row-of-bit-mat0)
  :expand ((bit-mat-unit i j m n)))

(defruled nth-of-bit-unit-list
  (implies (and (natp b) (natp j) (natp n)
                (< b n) (< j n))
           (equal (nth b (bit-unit-list j n))
                  (if (equal b j) 1 0)))
  :induct (list (dec-dec-induct b j) (dec-dec-induct b n))
  :enable (bit-unit-list)
  :expand ((bit-unit-list j n)))

(defrule mat-entry-of-bit-mat-unit
  (implies (and (natp a) (natp b) (natp i) (natp j)
                (natp m) (natp n)
                (< a m) (< b n) (< i m) (< j n))
           (equal (mat-entry a b (bit-mat-unit i j m n))
                  (if (and (equal a i) (equal b j)) 1 0)))
  :do-not-induct t
  :enable (nth-row-of-bit-mat-unit nth-of-bit-unit-list))

;;; Entries of a dimensioned matrix are bits.

(defrule bitp-of-mat-entry
  (implies (and (bit-matp x m n)
                (natp m) (natp n)
                (natp i) (natp j)
                (< i m) (< j n))
           (bitp (mat-entry i j x)))
  :do-not-induct t
  :use ((:instance bit-listnp-of-nth-when-bit-matp (x x))
        (:instance bitp-of-nth-when-bit-listnp (x (nth i x)) (i j))))

;; The same fact in the shape the guard prover needs: guard obligations from
;; bitxor/bitand are stated with integerp, and a :rewrite rule concluding bitp
;; does not fire on an integerp goal.
(defruled integerp-of-mat-entry
  (implies (and (bit-matp x m n)
                (natp m) (natp n)
                (natp i) (natp j)
                (< i m) (< j n))
           (integerp (mat-entry i j x)))
  :do-not-induct t
  :disable mat-entry
  :use (bitp-of-mat-entry))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 2: entry characterization of mm-tensor (companion lemma:mmt)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The flat index of six sub-n digits lies below n^6.  Nonlinear arithmetic
;;; cannot digest the six-variable statement whole, so it is built from five
;;; instances of a single block step, each a four-variable nonlinear fact.

(local
 (defruled block-index-upper-bound
   (implies (and (natp x) (natp y) (natp m) (natp n)
                 (< x m) (< y n))
            (< (+ x (* y m)) (* n m)))
   :hints (("Goal" :nonlinearp t))))

(defruled flat-index-upper-bound
  (implies (and (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (natp n)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (< (+ jc (* ic n) (* jb n n) (* ib n n n)
                 (* ja n n n n) (* ia n n n n n))
              (* n n n n n n)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance block-index-upper-bound
                            (x jc) (y ic) (m n) (n n))
                 (:instance block-index-upper-bound
                            (x (+ jc (* ic n))) (y jb)
                            (m (* n n)) (n n))
                 (:instance block-index-upper-bound
                            (x (+ jc (* ic n) (* jb n n))) (y ib)
                            (m (* n n n)) (n n))
                 (:instance block-index-upper-bound
                            (x (+ jc (* ic n) (* jb n n) (* ib n n n)))
                            (y ja) (m (* n n n n)) (n n))
                 (:instance block-index-upper-bound
                            (x (+ jc (* ic n) (* jb n n) (* ib n n n)
                                  (* ja n n n n)))
                            (y ia) (m (* n n n n n)) (n n))))))

;;; Per-level entry lemmas, innermost sum first.  Each level is a
;;; bit-list-add fold, so nth-of-bit-list-add splits the head from the tail,
;;; nth-of-tensor and mat-entry-of-bit-mat-unit reduce the head to a delta
;;; product, and the induction hypothesis covers the tail.  Each core
;;; carries the flat-index bound as an explicit hypothesis: the bound
;;; mentions no induction variable, so it survives into the inductive
;;; subgoals, where the nth lemmas need it to relieve their index-in-range
;;; hypotheses.  The exported forms discharge the bound once, via
;;; flat-index-upper-bound.

(local
 (defruled nth-of-mm-tensor-3-core
   (implies (and (natp n)
                 (natp i) (natp j) (natp k)
                 (< i n) (< j n) (<= k n)
                 (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                 (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n)
                 (< (+ jc (* ic n) (* jb n n) (* ib n n n)
                       (* ja n n n n) (* ia n n n n n))
                    (* n n n n n n)))
            (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                           (* ja n n n n) (* ia n n n n n))
                        (mm-tensor-3 i j k n))
                   (if (and (equal ia i) (equal ja j) (equal ib j)
                            (equal ic i) (equal jb jc) (< jc k))
                       1 0)))
   :hints (("Goal"
            :induct (dec-induct k)
            :in-theory (e/d (mm-tensor-3) (tensor))))))

(defruled nth-of-mm-tensor-3
  (implies (and (natp n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (<= k n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                       (mm-tensor-3 i j k n))
                  (if (and (equal ia i) (equal ja j) (equal ib j)
                           (equal ic i) (equal jb jc) (< jc k))
                      1 0)))
  :hints (("Goal"
           :do-not-induct t
           :use (flat-index-upper-bound nth-of-mm-tensor-3-core))))

(local
 (defruled nth-of-mm-tensor-2-core
   (implies (and (natp n)
                 (natp i) (natp j)
                 (< i n) (<= j n)
                 (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                 (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n)
                 (< (+ jc (* ic n) (* jb n n) (* ib n n n)
                       (* ja n n n n) (* ia n n n n n))
                    (* n n n n n n)))
            (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                           (* ja n n n n) (* ia n n n n n))
                        (mm-tensor-2 i j n))
                   (if (and (equal ia i) (equal ic i) (equal ja ib)
                            (equal jb jc) (< ja j))
                       1 0)))
   :hints (("Goal"
            :induct (dec-induct j)
            :in-theory (e/d (mm-tensor-2 nth-of-mm-tensor-3) (tensor))))))

(defruled nth-of-mm-tensor-2
  (implies (and (natp n)
                (natp i) (natp j)
                (< i n) (<= j n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                       (mm-tensor-2 i j n))
                  (if (and (equal ia i) (equal ic i) (equal ja ib)
                           (equal jb jc) (< ja j))
                      1 0)))
  :hints (("Goal"
           :do-not-induct t
           :use (flat-index-upper-bound nth-of-mm-tensor-2-core))))

(local
 (defruled nth-of-mm-tensor-1-core
   (implies (and (natp n)
                 (natp i) (<= i n)
                 (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                 (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n)
                 (< (+ jc (* ic n) (* jb n n) (* ib n n n)
                       (* ja n n n n) (* ia n n n n n))
                    (* n n n n n n)))
            (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                           (* ja n n n n) (* ia n n n n n))
                        (mm-tensor-1 i n))
                   (if (and (equal ia ic) (equal ja ib)
                            (equal jb jc) (< ia i))
                       1 0)))
   :hints (("Goal"
            :induct (dec-induct i)
            :in-theory (e/d (mm-tensor-1 nth-of-mm-tensor-2) (tensor))))))

(defruled nth-of-mm-tensor-1
  (implies (and (natp n)
                (natp i) (<= i n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                       (mm-tensor-1 i n))
                  (if (and (equal ia ic) (equal ja ib)
                           (equal jb jc) (< ia i))
                      1 0)))
  :hints (("Goal"
           :do-not-induct t
           :use (flat-index-upper-bound nth-of-mm-tensor-1-core))))

;;; The entry characterization of the matrix multiplication tensor.

(defrule nth-of-mm-tensor
  (implies (and (natp n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                       (mm-tensor n))
                  (if (and (equal ia ic) (equal ja ib) (equal jb jc))
                      1 0)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable mm-tensor)
           :use ((:instance nth-of-mm-tensor-1 (i n))))))
