; x-outer.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/outer.lisp
; produced by rename.py in this directory; do not edit by hand.
; outer.lisp -- Outer (tensor) products of F_2 vectors.
;
; A rank-one order-3 tensor A (x) B (x) C is represented by
; (outer3 A B C) = (outer A (outer B C)), a bit vector of length
; |A|*|B|*|C| whose coordinate (a,b,c) sits at index a*|B|*|C| + b*|C| + c.
; This matches the definition (A (x) B (x) C)_{g,h,i,j,k,l} = A_{g,h} B_{i,j} C_{k,l}
; of the paper, with matrix entry (i,j) stored at index i*n+j.

(in-package "ACL2")

(include-book "x-bitvec")

;;; ------------------------------------------------------------------
;;; Scaling a vector by a bit
;;; ------------------------------------------------------------------

(defun x-bv-scale (b v)
  (declare (xargs :guard (and (bitp b) (x-bvp v))))
  (if (eql b 1) v (x-bv-zero (len v))))

(defthm x-bvp-of-bv-scale (implies (x-bvp v) (x-bvp (x-bv-scale b v))))
(defthm x-len-of-bv-scale (equal (len (x-bv-scale b v)) (len v)))

(defthm x-bv-scale-of-bxor
  (implies (and (bitp a) (bitp b) (x-bvp v))
           (equal (x-bv-scale (x-bxor a b) v)
                  (x-bv+ (x-bv-scale a v) (x-bv-scale b v)))))

(defthm x-bv-scale-of-bv+
  (implies (and (x-bvp v) (x-bvp w) (equal (len v) (len w)))
           (equal (x-bv-scale b (x-bv+ v w))
                  (x-bv+ (x-bv-scale b v) (x-bv-scale b w)))))

(defthm x-nth-of-bv-scale
  (implies (and (x-bvp v) (natp i) (< i (len v)))
           (equal (nth i (x-bv-scale b v)) (x-band b (nth i v)))))

(defthm x-bv-scale-of-zero
  (equal (x-bv-scale b (x-bv-zero L)) (x-bv-zero L)))

;;; ------------------------------------------------------------------
;;; Outer product of two vectors
;;; ------------------------------------------------------------------

(defun x-outer (u v)
  (declare (xargs :guard (and (x-bvp u) (x-bvp v))))
  (if (atom u)
      nil
    (append (x-bv-scale (car u) v) (x-outer (cdr u) v))))

(defthm x-bvp-of-outer (implies (and (x-bvp u) (x-bvp v)) (x-bvp (x-outer u v))))
(defthm x-true-listp-of-outer (true-listp (x-outer u v)))
(defthm x-len-of-outer (equal (len (x-outer u v)) (* (len u) (len v))))

(defthm x-outer-of-bv+-left
  (implies (and (x-bvp u) (x-bvp w) (equal (len u) (len w)) (x-bvp v))
           (equal (x-outer (x-bv+ u w) v)
                  (x-bv+ (x-outer u v) (x-outer w v))))
  :hints (("Goal" :induct (x-bv+ u w))))

(defthm x-outer-of-bv+-right
  (implies (and (x-bvp u) (x-bvp v) (x-bvp w) (equal (len v) (len w)))
           (equal (x-outer u (x-bv+ v w))
                  (x-bv+ (x-outer u v) (x-outer u w))))
  :hints (("Goal" :induct (x-outer u v))))

(defthm x-outer-of-zero-left
  (equal (x-outer (x-bv-zero L) v) (x-bv-zero (* (nfix L) (len v))))
  :hints (("Goal" :induct (x-bv-zero L))
          ("Subgoal *1/2" :use ((:instance x-bv-zero-of-append-len
                                           (a (len v)) (b (* (1- L) (len v))))))))

(defthm x-outer-of-zero-right
  (implies (x-bvp u)
           (equal (x-outer u (x-bv-zero L)) (x-bv-zero (* (len u) (nfix L)))))
  :hints (("Goal" :induct (x-outer u v))
          ("Subgoal *1/2" :use ((:instance x-bv-zero-of-append-len
                                           (a (nfix L)) (b (* (len (cdr u)) (nfix L))))))))

;; Coordinates: entry (i,j) of u (x) v is u_i v_j.
(defthm x-times-ge-when-pos
  (implies (and (integerp i) (<= 1 i) (natp L))
           (<= L (* i L)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm x-nth-of-outer
  (implies (and (x-bvp u) (x-bvp v) (natp i) (natp j)
                (< i (len u)) (< j (len v)))
           (equal (nth (+ (* i (len v)) j) (x-outer u v))
                  (x-band (nth i u) (nth j v))))
  :hints (("Goal" :induct (x-ind-xk u i))
          ("Subgoal *1/2" :cases ((zp i)))))

;; Nonzero vectors have a nonzero outer product.
(defthm x-outer-nonzero
  (implies (and (x-bvp u) (x-bvp v)
                (not (equal u (x-bv-zero (len u))))
                (not (equal v (x-bv-zero (len v)))))
           (not (equal (x-outer u v) (x-bv-zero (* (len u) (len v))))))
  :hints (("Goal"
           :use ((:instance x-nth-of-outer
                            (i (x-bv-first-one u)) (j (x-bv-first-one v)))
                 (:instance x-nth-of-bv-zero
                            (i (+ (* (x-bv-first-one u) (len v)) (x-bv-first-one v)))
                            (L (* (len u) (len v))))
                 (:instance x-bv-first-one-witness (x u))
                 (:instance x-bv-first-one-witness (x v)))
           :in-theory (disable x-nth-of-outer x-nth-of-bv-zero x-bv-first-one-witness))))

;;; ------------------------------------------------------------------
;;; Rank-one order-3 tensors
;;; ------------------------------------------------------------------

(defun x-outer3 (A B C)
  (declare (xargs :guard (and (x-bvp A) (x-bvp B) (x-bvp C))))
  (x-outer A (x-outer B C)))

(defthm x-bvp-of-outer3
  (implies (and (x-bvp A) (x-bvp B) (x-bvp C)) (x-bvp (x-outer3 A B C))))
(defthm x-len-of-outer3
  (equal (len (x-outer3 A B C)) (* (len A) (* (len B) (len C)))))

;; Linearity in each factor.
(defthm x-outer3-of-bv+-1
  (implies (and (x-bvp A) (x-bvp A2) (equal (len A) (len A2)) (x-bvp B) (x-bvp C))
           (equal (x-outer3 (x-bv+ A A2) B C)
                  (x-bv+ (x-outer3 A B C) (x-outer3 A2 B C)))))

(defthm x-outer3-of-bv+-2
  (implies (and (x-bvp A) (x-bvp B) (x-bvp B2) (equal (len B) (len B2)) (x-bvp C))
           (equal (x-outer3 A (x-bv+ B B2) C)
                  (x-bv+ (x-outer3 A B C) (x-outer3 A B2 C)))))

(defthm x-outer3-of-bv+-3
  (implies (and (x-bvp A) (x-bvp B) (x-bvp C) (x-bvp C2) (equal (len C) (len C2)))
           (equal (x-outer3 A B (x-bv+ C C2))
                  (x-bv+ (x-outer3 A B C) (x-outer3 A B C2)))))

(defthm x-outer3-of-zero-1
  (equal (x-outer3 (x-bv-zero L) B C) (x-bv-zero (* (nfix L) (* (len B) (len C))))))
(defthm x-outer3-of-zero-2
  (implies (x-bvp A)
           (equal (x-outer3 A (x-bv-zero L) C) (x-bv-zero (* (len A) (* (nfix L) (len C)))))))
(defthm x-outer3-of-zero-3
  (implies (and (x-bvp A) (x-bvp B))
           (equal (x-outer3 A B (x-bv-zero L)) (x-bv-zero (* (len A) (* (len B) (nfix L)))))))

(defthm x-outer3-nonzero
  (implies (and (x-bvp A) (x-bvp B) (x-bvp C)
                (not (equal A (x-bv-zero (len A))))
                (not (equal B (x-bv-zero (len B))))
                (not (equal C (x-bv-zero (len C)))))
           (not (equal (x-outer3 A B C) (x-bv-zero (* (len A) (* (len B) (len C)))))))
  :hints (("Goal" :in-theory (disable x-outer-nonzero)
                  :use ((:instance x-outer-nonzero (u B) (v C))
                        (:instance x-outer-nonzero (u A) (v (x-outer B C)))))))

;; Coordinate (a,b,c) of A (x) B (x) C is A_a B_b C_c.
(defun x-tidx3 (LB LC a b c)
  (declare (xargs :guard (and (natp LB) (natp LC) (natp a) (natp b) (natp c))))
  (+ (* a (* LB LC)) (* b LC) c))

(defthm x-nth-of-outer3
  (implies (and (x-bvp A) (x-bvp B) (x-bvp C) (natp ia) (natp ib) (natp ic)
                (< ia (len A)) (< ib (len B)) (< ic (len C)))
           (equal (nth (x-tidx3 (len B) (len C) ia ib ic) (x-outer3 A B C))
                  (x-band (nth ia A) (x-band (nth ib B) (nth ic C)))))
  :hints (("Goal" :in-theory (disable x-nth-of-outer)
                  :use ((:instance x-nth-of-outer (u B) (v C) (i ib) (j ic))
                        (:instance x-nth-of-outer (u A) (v (x-outer B C)) (i ia)
                                   (j (+ (* ib (len C)) ic)))))))

;; Mixed-radix arithmetic.
(defthm x-mixed-radix-lt
  (implies (and (natp x) (natp y) (natp L) (< x L) (< y L)
                (integerp p) (integerp q) (< p q))
           (< (+ x (* p L)) (+ y (* q L))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm x-mixed-radix-unique
  (implies (and (natp x) (natp y) (natp L) (< x L) (< y L)
                (integerp p) (integerp q))
           (equal (equal (+ x (* p L)) (+ y (* q L)))
                  (and (equal x y) (equal p q))))
  :hints (("Goal" :use ((:instance x-mixed-radix-lt)
                        (:instance x-mixed-radix-lt (x y) (y x) (p q) (q p)))))
  :rule-classes nil)

(defthm x-digit-bound
  (implies (and (natp b) (natp c) (natp LB) (natp LC) (< b LB) (< c LC))
           (< (+ c (* b LC)) (* LB LC)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

;; tidx3 is injective on the coordinate box.
(defthm x-tidx3-injective
  (implies (and (natp a) (natp b) (natp c) (natp a2) (natp b2) (natp c2)
                (natp LB) (natp LC)
                (< b LB) (< c LC) (< b2 LB) (< c2 LC))
           (equal (equal (x-tidx3 LB LC a b c) (x-tidx3 LB LC a2 b2 c2))
                  (and (equal a a2) (equal b b2) (equal c c2))))
  :hints (("Goal" :in-theory (enable x-tidx3)
                  :use ((:instance x-mixed-radix-unique
                                   (x (+ c (* b LC))) (y (+ c2 (* b2 LC)))
                                   (L (* LB LC)) (p a) (q a2))
                        (:instance x-mixed-radix-unique
                                   (x c) (y c2) (L LC) (p b) (q b2))
                        (:instance x-digit-bound)
                        (:instance x-digit-bound (b b2) (c c2))))))

(defthm x-tidx3-bound
  (implies (and (natp a) (natp b) (natp c) (natp LA) (natp LB) (natp LC)
                (< a LA) (< b LB) (< c LC))
           (< (x-tidx3 LB LC a b c) (* LA (* LB LC))))
  :hints (("Goal" :use ((:instance x-digit-bound (b a) (c (+ c (* b LC))) (LB LA) (LC (* LB LC))))))
  :rule-classes :linear)

;;; ------------------------------------------------------------------
;;; Unique factorization of nonzero rank-one tensors over F_2
;;; (remark after Definition 2.2 of the paper)
;;; ------------------------------------------------------------------

(defthm x-outer3-factor-A-unique
  (implies (and (x-bvp A) (x-bvp B) (x-bvp C) (x-bvp A2) (x-bvp B2) (x-bvp C2)
                (equal (len A) (len A2)) (equal (len B) (len B2)) (equal (len C) (len C2))
                (not (equal A (x-bv-zero (len A))))
                (not (equal A2 (x-bv-zero (len A))))
                (not (equal B2 (x-bv-zero (len B))))
                (not (equal C2 (x-bv-zero (len C))))
                (equal (x-outer3 A B C) (x-outer3 A2 B2 C2)))
           (equal A A2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance x-bv-extensionality (x A) (y A2))
                 (:instance x-nth-of-outer3
                            (ia (x-bv-diff-index A A2)) (ib (x-bv-first-one B2)) (ic (x-bv-first-one C2)))
                 (:instance x-nth-of-outer3 (A A2) (B B2) (C C2)
                            (ia (x-bv-diff-index A A2)) (ib (x-bv-first-one B2)) (ic (x-bv-first-one C2)))
                 (:instance x-nth-of-outer3
                            (ia (x-bv-first-one A2)) (ib (x-bv-first-one B2)) (ic (x-bv-first-one C2)))
                 (:instance x-nth-of-outer3 (A A2) (B B2) (C C2)
                            (ia (x-bv-first-one A2)) (ib (x-bv-first-one B2)) (ic (x-bv-first-one C2)))
                 (:instance x-bv-diff-index-witness (x A) (y A2))
                 (:instance x-bv-first-one-witness (x A2))
                 (:instance x-bv-first-one-witness (x B2))
                 (:instance x-bv-first-one-witness (x C2)))
           :in-theory (disable x-nth-of-outer3 x-bv-diff-index-witness x-bv-first-one-witness
                               x-outer3 x-tidx3))))
