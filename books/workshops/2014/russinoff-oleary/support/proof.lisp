(in-package "RTL")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 18.90 sec. vs. 27.20 sec.
(value-triple (set-gc-strategy :delay))

(include-book "rtl/rel11/lib/top" :dir :system)   ;; The basic RTL library

(include-book "rtl/rel11/lib/mult" :dir :system)  ;; The Booth multiplication book

(include-book "rtl/rel11/lib/gl" :dir :system)    ;; Connect lib with gl

(include-book "arithmetic-5/top" :dir :system)   ;; It's hard to do any arithmetic without this

(include-book "imul")                            ;; The IMUL model

;;***********************************************************************************
;; Utility functions
;;***********************************************************************************

;; a[m], ..., a[n-1] are all 64-bit vectors:

(defun all-bvecp (a m n)
  (declare (xargs :measure (nfix (- n m))))
  (if (and (natp m) (natp n) (< m n))
      (and (bvecp (ag m a) 64)
           (all-bvecp a (1+ m) n))
    t))

(defthm all-bvecp-integerp
  (implies (and (all-bvecp a m n)
                (natp n)
                (natp m)
                (natp k)
                (<= m k)
                (< k n))
           (integerp (ag k a)))
  :rule-classes (:rewrite :type-prescription))

(defthm all-bvecp-bvecp
  (implies (and (all-bvecp a m n)
                (natp n)
                (natp m)
                (natp k)
                (<= m k)
                (< k n))
           (bvecp (ag k a) 64))
  :rule-classes (:rewrite :type-prescription))

(defthm all-bvecp-leq
  (implies (and (all-bvecp a m p)
                (natp m)
                (natp n)
                (natp p)
                (<= m n)
                (<= n p))
           (all-bvecp a m n)))

(defthm all-bvecp-subrange
  (implies (and (all-bvecp a q p)
                (natp m)
                (natp n)
                (natp p)
                (natp q)
                (<= q m)
                (<= m n)
                (<= n p))
           (all-bvecp a m n)))

;; (a[0] + ... + a[k-1])[63:0]:

(defun sum-simple (a k)
  (if (zp k)
      0
    (bits (+ (ag (1- k) a) (sum-simple a (1- k)))
          63 0)))

(defthm bvecp-sum-simple
  (bvecp (sum-simple a n) 64)
  :rule-classes (:rewrite :type-prescription))

;; a[m] + .. + a[n]:

(defun sum-range (a m n)
  (if (or (zp n) (<= n m))
      0
    (+ (ag (1- n) a) (sum-range a m (1- n)))))

(defthm integerp-sum-range
  (implies (and (all-bvecp a m n)
                (natp m)
                (natp n)
                (<= m n))
           (integerp (sum-range a m n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (nats n))))

(defthmd sum-range-sum-simple
  (implies (and (natp n)
                (all-bvecp a 0 n))
           (equal (bits (sum-range a 0 n) 63 0)
                  (sum-simple a n)))
  :hints (("Goal" :in-theory (enable sum-range sum-simple))
          ("Subgoal *1/5" :in-theory (enable sum-range sum-simple)
                          :use ((:instance bits-bits-sum
                                           (x (sum-range a 0 (+ -1 n)))
                                           (y (ag (+ -1 n) a))
                                           (k 63)
                                           (i 63)
                                           (j 0))))))

;; Sums of sums of adjacent ranges:

(defthm sum-ranges
  (implies (and (natp m)
                (natp n)
                (natp k)
                (<= m k)
                (<= k n)
                (all-bvecp a m n))
           (equal (+ (sum-range a m k) (sum-range a k n))
                  (sum-range a m n)))
  :rule-classes ()
  :hints (("Goal" :induct (nats n))))

;; This lemma is critical in the analysis of the compression tree:

(defthmd sum-range-split
  (implies (and (all-bvecp a m n)
                (natp m)
                (natp n)
                (< m n)
                (evenp (+ m n)))
           (equal (bits (sum-range a m n) 63 0)
                  (bits (+ (bits (sum-range a m (/ (+ m n) 2)) 63 0)
                           (bits (sum-range a (/ (+ m n) 2) n) 63 0))
                        63 0)))
  :hints (("Goal" :use ((:instance sum-ranges (k (/ (+ m n) 2)))))))


;;***********************************************************************************
;; Booth
;;***********************************************************************************

;; The function Booth computes an array of 3-bit encodings of the
;; Booth digits (theta k y), 0 <= k < 17:

(acl2::def-gl-thm encode-lemma
  :hyp (and (bvecp y 32)
            (natp k)
            (< k 17))
  :concl (equal (encode (bits (* 2 y) (+ 2 (* 2 k)) (* 2 k)))
                (cat (neg (theta k y)) 1 (abs (theta k y)) 2))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat y 32)))

(in-theory (disable encode))

(defthm booth-recursion-1
  (implies (and (natp k)
                (natp j)
                (< j k))
           (equal (ag j (booth-loop-0 k y35 a))
                  (ag j a))))

(defthm booth-recursion-2
  (implies (and (natp y)
                (natp k)
                (natp j)
                (<= k j)
                (< j 17))
           (equal (ag j (booth-loop-0 k y35 a))
                  (encode (bits y35 (+ (* 2 j) 2) (* 2 j)))))
  :hints (("Subgoal *1/3" :expand (:free (k) (booth-loop-0 k y35 a)))))

(defthm booth-lemma
  (implies (and (bvecp y 32)
                (natp k)
                (< k 17))
           (equal (ag k (booth y))
                  (cat (neg (theta k y)) 1 (abs (theta k y)) 2))))

(in-theory (disable booth))


;;***********************************************************************************
;; PartialProducts
;;***********************************************************************************

;; The function PartialProducts computes an array of the partial
;; products (bmux4 (theta k y) x 33), 0 <= k < 17:

(defthm partialproducts-recursion-1
  (implies (and (natp j)
                (natp k)
                (< j k))
           (equal (ag j (partialproducts-loop-0 k x m21 pp))
                  (ag j pp))))

(defthm partialproducts-recursion-2
  (implies (and (natp k)
                (natp j)
                (<= k j)
                (< j 17))
           (equal (ag j (partialproducts-loop-0 k x m21 pp))
                  (let ((row (case (bits (ag j m21) 1 0)
                               (2 (bits (ash x 1) 32 0))
                               (1 x)
                               (t 0))))
                    (bits (if1 (bitn (ag j m21) 2)
                               (lognot row)
                              row)
                          32 0))))
  :hints (("subgoal *1/1" :expand
                          ((:free (pp) (partialproducts-loop-0 k x m21 pp))
                           (:free (pp) (partialproducts-loop-0 0 x m21 pp))))))

(acl2::def-gl-thm partialproducts-lemma
  :hyp (and (bvecp x 32)
            (bvecp y 32)
            (natp k)
            (< k 17))
  :concl (equal (ag k (partialproducts (booth y) x))
                (bmux4 (theta k y) x 33))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat x 32) (:nat y 32)))

(in-theory (disable partialproducts theta bmux4))


;;***********************************************************************************
;; Align
;;***********************************************************************************

;; The function Align computes an array of the aligned partial products
;; (bits (pp4p-theta k x y 33) 63 0):

(defthm sign-bits-recursion-1
  (implies (and (natp j)
                (natp k)
                (< j k))
           (mv-let (sb psb) (align-loop-1 k bds sb0 psb0)
             (declare (ignore psb))
             (equal (ag j sb)
                    (ag j sb0)))))

(defthm sign-bits-recursion-2
  (implies (and (natp j)
                (natp k)
                (<= j k))
           (mv-let (sb psb) (align-loop-1 k bds sb0 psb0)
             (declare (ignore sb))
             (equal (ag j psb)
                    (ag j psb0)))))

(defthm sign-bits-recursion-3
  (implies (and (natp x)
                (natp k)
                (natp j)
                (<= k j)
                (< j 17))
           (mv-let (sb psb) (align-loop-1 k bds sb0 psb0)
             (and (equal (ag j sb)
                         (bitn (ag j bds) 2))
                  (equal (ag (1+ j) psb)
                         (bitn (ag j bds) 2)))))
  :hints (("Subgoal *1/3" :expand
                          ((:free (j bds sb psb) (align-loop-1 j bds sb psb))))))

(defthm sign-bits-lemma
  (implies (and (bvecp y 32)
                (natp k)
                (< k 17))
           (mv-let (sb psb) (align-loop-1 0 (booth y) () ())
             (and (equal (ag k sb)
                         (neg (theta k y)))
                  (equal (ag (1+ k) psb)
                         (neg (theta k y)))))))

(defthm align-recursion-1
  (implies (and (natp j)
                (natp k)
                (< j k))
           (let ((tble (align-loop-0 k pp psb sb tble0)))
             (equal (ag j tble)
                    (ag j tble0)))))

(defthm align-recursion-2
  (implies (and (natp k)
                (natp j)
                (<= k j)
                (< j 17))
           (equal (ag j (align-loop-0 k pp psb sb tble0))
                  (if (zp j)
                      (bits (setbitn (setbitn (setbitn (setbits 0 67 (+ (* 2 j) 32) (* 2 j) (ag j pp))
                                                       67 33 (ag j sb))
                                              67 34 (ag j sb))
                                     67 35 (lognot1 (ag j sb)))
                            63 0)
                    (bits (setbitn (setbitn (setbitn (setbits 0 67 (+ (* 2 j) 32) (* 2 j) (ag j pp))
                                                     67 (- (* 2 j) 2) (ag j psb))
                                            67 (+ (* 2 j) 33) (lognot1 (ag j sb)))
                                   67 (+ (* 2 j) 34) 1)
                          63 0))))
  :hints (("subgoal *1/1" :expand ((:free (j bds sb psb) (align-loop-0 j pp psb sb tble0))))))

(acl2::def-gl-thm align-lemma
  :hyp (and (bvecp x 32)
            (bvecp y 32)
            (natp k)
            (< k 17))
  :concl (equal (ag k (align (booth y) (partialproducts (booth y) x)))
                (bits (pp4p-theta k x y 33) 63 0))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat x 32) (:nat y 32)))

(defthm bvecp-align
  (implies (and (bvecp x 32)
                (bvecp y 32)
                (natp k)
                (< k 17))
           (bvecp (ag k (align (booth y) (partialproducts (booth y) x))) 64))
  :rule-classes (:rewrite :type-prescription))

(defthm all-bvecp-align
  (implies (and (bvecp x 32)
                (bvecp y 32)
                (natp m))
           (all-bvecp (align (booth y) (partialproducts (booth y) x)) m 17)))

(in-theory (disable align bmux4 neg pp4-theta pp4p-theta))

(defthm sum-simple-pp4p-theta
  (implies (and (bvecp x 32)
                (bvecp y 32)
                (natp k)
                (<= k 17))
           (equal (sum-simple (align (booth y) (partialproducts (booth y) x)) k)
                  (bits (sum-pp4p-theta x y k 33) 63 0))))

;; The following is a consequence of booth4-corollary-2:

(defthm sum-simple-align-prod
  (implies (and (bvecp x 32) (bvecp y 32))
           (equal (sum-simple (align (booth y) (partialproducts (booth y) x)) 17)
                  (* x y)))
  :hints (("Goal" :in-theory (e/d (bvecp-monotone) (bits-bits))
                  :use ((:instance bvecp-product (m 32) (n 32))
                        (:instance bits-bits (x (sum-pp4p-theta x y 17 33))
                                             (i 66) (j 0) (k 63) (l 0))
                        (:instance booth4-corollary-2 (n 33) (m 17))))))


;;***********************************************************************************
;; Sum
;;***********************************************************************************

;; The function Sum computes the sum of the aligned partial products by means of a
;; 17:2 compression tree and a final 64-bit adder.

;; The compression tree consists of 7 4:2 compressors and 1 3:2 compressor.  The
;; functionality of these components is proved automatically by gl:

(acl2::def-gl-thm compress32-lemma
  :hyp  (and (bvecp in0 64)
             (bvecp in1 64)
             (bvecp in2 64))
  :concl (mv-let (out0 out1)
                 (compress32 in0 in1 in2)
                 (and (bvecp out0 64)
                      (bvecp out1 64)
                      (equal (bits (+ in0 in1 in2) 63 0)
                             (bits (+ out0 out1) 63 0))))
  :g-bindings (gl::auto-bindings (:mix (:nat in0 64)
                                       (:nat in1 64)
                                       (:nat in2 64))))

(acl2::def-gl-thm compress42-lemma
  :hyp  (and (bvecp in0 64)
             (bvecp in1 64)
             (bvecp in2 64)
             (bvecp in3 64))
  :concl (mv-let (out0 out1)
                 (compress42 in0 in1 in2 in3)
                 (and (bvecp out0 64)
                      (bvecp out1 64)
                      (equal (bits (+ in0 in1 in2 in3) 63 0)
                             (bits (+ out0 out1) 63 0))))
  :g-bindings (gl::auto-bindings (:mix (:nat in0 64)
                                       (:nat in1 64)
                                       (:nat in2 64)
                                       (:nat in3 64))))

(in-theory (disable compress32 compress42))

;; The compression is performed in 4 stages.

;; Level 1 compresses the first 16 entries to 8 vectors using 4 4:2 compressors:

(defun level1 (in)
  (sum-loop-1 0 in ()))

;; Level 2 compresses the output of level 1 to 4 vectors using 2 4:2 compressors:

(defun level2 (a1)
  (sum-loop-0 0 a1 ()))

;; Level 3 compresses the output of level 2 to 2 vectors using a 4:2 compressor:

(defun level3 (a2)
  (mv-let (temp-0 temp-1)
           (compress42 (ag 0 a2) (ag 1 a2) (ag 2 a2) (ag 3 a2))
           (as 1 temp-1 (as 0 temp-0 a2))))

;; Level 3 combines the output of level 3 and the last array entry with a 3:2 compressor:

(defun level4 (a3 in)
  (mv-let (temp-0 temp-1)
          (compress32 (ag 0 a3) (ag 1 a3) (ag 16 in))
          (as 1 temp-1 (as 0 temp-0 ()))))

;; The adder is applied to the output of the level 4:

(defthm sum-rewrite
  (equal (sum in)
         (let ((comp (level4 (level3 (level2 (level1 in))) in)))
           (bits (+ (ag 0 comp) (ag 1 comp)) 63 0))))

(in-theory (disable sum))

;; For each level, through repeated applications of the lemma bits-sum-range,
;; we show that the sum of the outputs is the sum of the inputs (mod 2^(64)).
;; For each of the first 3 levels, we must also show that the outputs are all
;; 64-bit vectors in order to apply bits-sum-range to the next level.


(defthm level1-all-bvecp
  (implies (all-bvecp in 0 17)
           (all-bvecp (level1 in) 0 8))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand ((:free (k a1) (sum-loop-1 k in a1))))))

(defthm level1-4-2
  (implies (and (all-bvecp in 0 17) (member i '(0 4 8 12) ) (= j (+ 4 i)))
           (equal (bits (sum-range in i j) 63 0)
                  (bits (sum-range (level1 in) (/ i 2) (/ j 2)) 63 0)))
  :hints (("Goal" :expand ((:free (k a1) (sum-loop-1 k in a1))))))

(in-theory (disable level1))

(defthm level1-sum
  (implies (all-bvecp in 0 17)
           (equal (bits (sum-range in 0 16) 63 0)
                  (bits (sum-range (level1 in) 0 8) 63 0)))
  :hints (("Goal" :in-theory (enable sum-range-split))))

(defthm level2-all-bvecp
  (implies (all-bvecp a1 0 8)
           (all-bvecp (level2 a1) 0 4))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand ((:free (k a2) (sum-loop-0 k a1 a2))))))

(defthm a2-4-2
  (implies (and (all-bvecp a1 0 8) (member i '(0 4)) (= j (+ 4 i)))
           (equal (bits (sum-range a1 i j) 63 0)
                  (bits (sum-range (level2 a1) (/ i 2) (/ j 2)) 63 0)))
  :hints (("Goal" :expand ((:free (k a2) (sum-loop-0 k a1 a2))
                           (:free (a m n) (sum-range a m n))))))

(in-theory (disable level2))

(defthm level2-sum
  (implies (all-bvecp a1 0 8)
           (equal (bits (sum-range a1 0 8) 63 0)
                  (bits (sum-range (level2 a1) 0 4) 63 0)))
  :hints (("Goal" :in-theory (enable sum-range-split))))

(defthm level3-all-bvecp
  (implies (all-bvecp a2 0 4)
           (all-bvecp (level3 a2) 0 2))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand ((:free (a m n) (all-bvecp a m n))))))

(defthm level3-sum
  (implies (all-bvecp a2 0 4)
           (equal (bits (sum-range a2 0 4) 63 0)
                  (bits (sum-range (level3 a2) 0 2) 63 0)))
  :hints (("Goal" :expand ((:free (a m n) (sum-range a m n))))))

(in-theory (disable level3))

(defthm level4-sum
  (implies (and (bvecp (ag 16 in) 64)
                (all-bvecp a3 0 2))
           (equal (bits (+ (ag 16 in) (sum-range a3 0 2)) 63 0)
                  (bits (+ (ag 0 (level4 a3 in))
                           (ag 1 (level4 a3 in)))
                         63 0)))
  :hints (("Goal" :expand ((:free (a m n) (sum-range a m n))))))

(in-theory (disable level4))

;; Combine the preceding results:

(defthm sum-sum-range
  (implies (all-bvecp in 0 17)
           (equal (sum in)
                  (bits (sum-range in 0 17) 63 0)))
  :hints (("Goal" :in-theory (disable bits-bits-sum)
                  :use ((:instance bits-bits-sum
                                   (x (sum-range (level3 (level2 (level1 in))) 0 2))
                                   (y (ag 16 in))
                                   (i 63) (j 0) (k 63))
                        (:instance bits-bits-sum
                                   (x (sum-range in 0 16))
                                   (y (ag 16 in))
                                   (i 63) (j 0) (k 63))))))

(in-theory (disable sum-rewrite))

;; Combine the lemmas sum-sum-range and sum-range-sum-simple:

(in-theory (enable sum-range-sum-simple))

(defthm sum-sum-simple
  (implies (all-bvecp in 0 17)
           (equal (sum in)
                  (sum-simple in 17))))

;;***********************************************************************************
;; Final Theorem
;;***********************************************************************************

;; The main result follows from sum-sum-simple sum-simple-align-prod:

(defthm imul-thm
  (implies (and (bvecp s1 32)
                (bvecp s2 32))
           (equal (imul s1 s2)
                  (* s1 s2))))
