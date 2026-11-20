; outer.lisp -- Outer (tensor) products of F_2 vectors.
;
; A rank-one order-3 tensor A (x) B (x) C is represented by
; (outer3 A B C) = (outer A (outer B C)), a bit vector of length
; |A|*|B|*|C| whose coordinate (a,b,c) sits at index a*|B|*|C| + b*|C| + c.
; This matches the definition (A (x) B (x) C)_{g,h,i,j,k,l} = A_{g,h} B_{i,j} C_{k,l}
; of the paper, with matrix entry (i,j) stored at index i*n+j.

(in-package "ACL2")

(include-book "bitvec")

;;; ------------------------------------------------------------------
;;; Scaling a vector by a bit
;;; ------------------------------------------------------------------

(defun bv-scale (b v)
  (declare (xargs :guard (and (bitp b) (bvp v))))
  (if (eql b 1) v (bv-zero (len v))))

(defthm bvp-of-bv-scale (implies (bvp v) (bvp (bv-scale b v))))
(defthm len-of-bv-scale (equal (len (bv-scale b v)) (len v)))

(defthm bv-scale-of-bxor
  (implies (and (bitp a) (bitp b) (bvp v))
           (equal (bv-scale (bxor a b) v)
                  (bv+ (bv-scale a v) (bv-scale b v)))))

(defthm bv-scale-of-bv+
  (implies (and (bvp v) (bvp w) (equal (len v) (len w)))
           (equal (bv-scale b (bv+ v w))
                  (bv+ (bv-scale b v) (bv-scale b w)))))

(defthm nth-of-bv-scale
  (implies (and (bvp v) (natp i) (< i (len v)))
           (equal (nth i (bv-scale b v)) (band b (nth i v)))))

(defthm bv-scale-of-zero
  (equal (bv-scale b (bv-zero L)) (bv-zero L)))

;;; ------------------------------------------------------------------
;;; Outer product of two vectors
;;; ------------------------------------------------------------------

(defun outer (u v)
  (declare (xargs :guard (and (bvp u) (bvp v))))
  (if (atom u)
      nil
    (append (bv-scale (car u) v) (outer (cdr u) v))))

(defthm bvp-of-outer (implies (and (bvp u) (bvp v)) (bvp (outer u v))))
(defthm true-listp-of-outer (true-listp (outer u v)))
(defthm len-of-outer (equal (len (outer u v)) (* (len u) (len v))))

(defthm outer-of-bv+-left
  (implies (and (bvp u) (bvp w) (equal (len u) (len w)) (bvp v))
           (equal (outer (bv+ u w) v)
                  (bv+ (outer u v) (outer w v))))
  :hints (("Goal" :induct (bv+ u w))))

(defthm outer-of-bv+-right
  (implies (and (bvp u) (bvp v) (bvp w) (equal (len v) (len w)))
           (equal (outer u (bv+ v w))
                  (bv+ (outer u v) (outer u w))))
  :hints (("Goal" :induct (outer u v))))

(defthm outer-of-zero-left
  (equal (outer (bv-zero L) v) (bv-zero (* (nfix L) (len v))))
  :hints (("Goal" :induct (bv-zero L))
          ("Subgoal *1/2" :use ((:instance bv-zero-of-append-len
                                           (a (len v)) (b (* (1- L) (len v))))))))

(defthm outer-of-zero-right
  (implies (bvp u)
           (equal (outer u (bv-zero L)) (bv-zero (* (len u) (nfix L)))))
  :hints (("Goal" :induct (outer u v))
          ("Subgoal *1/2" :use ((:instance bv-zero-of-append-len
                                           (a (nfix L)) (b (* (len (cdr u)) (nfix L))))))))

;; Coordinates: entry (i,j) of u (x) v is u_i v_j.
(defthm times-ge-when-pos
  (implies (and (integerp i) (<= 1 i) (natp L))
           (<= L (* i L)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm nth-of-outer
  (implies (and (bvp u) (bvp v) (natp i) (natp j)
                (< i (len u)) (< j (len v)))
           (equal (nth (+ (* i (len v)) j) (outer u v))
                  (band (nth i u) (nth j v))))
  :hints (("Goal" :induct (ind-xk u i))
          ("Subgoal *1/2" :cases ((zp i)))))

;; Nonzero vectors have a nonzero outer product.
(defthm outer-nonzero
  (implies (and (bvp u) (bvp v)
                (not (equal u (bv-zero (len u))))
                (not (equal v (bv-zero (len v)))))
           (not (equal (outer u v) (bv-zero (* (len u) (len v))))))
  :hints (("Goal"
           :use ((:instance nth-of-outer
                            (i (bv-first-one u)) (j (bv-first-one v)))
                 (:instance nth-of-bv-zero
                            (i (+ (* (bv-first-one u) (len v)) (bv-first-one v)))
                            (L (* (len u) (len v))))
                 (:instance bv-first-one-witness (x u))
                 (:instance bv-first-one-witness (x v)))
           :in-theory (disable nth-of-outer nth-of-bv-zero bv-first-one-witness))))

;;; ------------------------------------------------------------------
;;; Rank-one order-3 tensors
;;; ------------------------------------------------------------------

(defun outer3 (A B C)
  (declare (xargs :guard (and (bvp A) (bvp B) (bvp C))))
  (outer A (outer B C)))

(defthm bvp-of-outer3
  (implies (and (bvp A) (bvp B) (bvp C)) (bvp (outer3 A B C))))
(defthm len-of-outer3
  (equal (len (outer3 A B C)) (* (len A) (* (len B) (len C)))))

;; Linearity in each factor.
(defthm outer3-of-bv+-1
  (implies (and (bvp A) (bvp A2) (equal (len A) (len A2)) (bvp B) (bvp C))
           (equal (outer3 (bv+ A A2) B C)
                  (bv+ (outer3 A B C) (outer3 A2 B C)))))

(defthm outer3-of-bv+-2
  (implies (and (bvp A) (bvp B) (bvp B2) (equal (len B) (len B2)) (bvp C))
           (equal (outer3 A (bv+ B B2) C)
                  (bv+ (outer3 A B C) (outer3 A B2 C)))))

(defthm outer3-of-bv+-3
  (implies (and (bvp A) (bvp B) (bvp C) (bvp C2) (equal (len C) (len C2)))
           (equal (outer3 A B (bv+ C C2))
                  (bv+ (outer3 A B C) (outer3 A B C2)))))

(defthm outer3-of-zero-1
  (equal (outer3 (bv-zero L) B C) (bv-zero (* (nfix L) (* (len B) (len C))))))
(defthm outer3-of-zero-2
  (implies (bvp A)
           (equal (outer3 A (bv-zero L) C) (bv-zero (* (len A) (* (nfix L) (len C)))))))
(defthm outer3-of-zero-3
  (implies (and (bvp A) (bvp B))
           (equal (outer3 A B (bv-zero L)) (bv-zero (* (len A) (* (len B) (nfix L)))))))

(defthm outer3-nonzero
  (implies (and (bvp A) (bvp B) (bvp C)
                (not (equal A (bv-zero (len A))))
                (not (equal B (bv-zero (len B))))
                (not (equal C (bv-zero (len C)))))
           (not (equal (outer3 A B C) (bv-zero (* (len A) (* (len B) (len C)))))))
  :hints (("Goal" :in-theory (disable outer-nonzero)
                  :use ((:instance outer-nonzero (u B) (v C))
                        (:instance outer-nonzero (u A) (v (outer B C)))))))

;; Coordinate (a,b,c) of A (x) B (x) C is A_a B_b C_c.
(defun tidx3 (LB LC a b c)
  (declare (xargs :guard (and (natp LB) (natp LC) (natp a) (natp b) (natp c))))
  (+ (* a (* LB LC)) (* b LC) c))

(defthm nth-of-outer3
  (implies (and (bvp A) (bvp B) (bvp C) (natp ia) (natp ib) (natp ic)
                (< ia (len A)) (< ib (len B)) (< ic (len C)))
           (equal (nth (tidx3 (len B) (len C) ia ib ic) (outer3 A B C))
                  (band (nth ia A) (band (nth ib B) (nth ic C)))))
  :hints (("Goal" :in-theory (disable nth-of-outer)
                  :use ((:instance nth-of-outer (u B) (v C) (i ib) (j ic))
                        (:instance nth-of-outer (u A) (v (outer B C)) (i ia)
                                   (j (+ (* ib (len C)) ic)))))))

;; Mixed-radix arithmetic.
(defthm mixed-radix-lt
  (implies (and (natp x) (natp y) (natp L) (< x L) (< y L)
                (integerp p) (integerp q) (< p q))
           (< (+ x (* p L)) (+ y (* q L))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm mixed-radix-unique
  (implies (and (natp x) (natp y) (natp L) (< x L) (< y L)
                (integerp p) (integerp q))
           (equal (equal (+ x (* p L)) (+ y (* q L)))
                  (and (equal x y) (equal p q))))
  :hints (("Goal" :use ((:instance mixed-radix-lt)
                        (:instance mixed-radix-lt (x y) (y x) (p q) (q p)))))
  :rule-classes nil)

(defthm digit-bound
  (implies (and (natp b) (natp c) (natp LB) (natp LC) (< b LB) (< c LC))
           (< (+ c (* b LC)) (* LB LC)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

;; tidx3 is injective on the coordinate box.
(defthm tidx3-injective
  (implies (and (natp a) (natp b) (natp c) (natp a2) (natp b2) (natp c2)
                (natp LB) (natp LC)
                (< b LB) (< c LC) (< b2 LB) (< c2 LC))
           (equal (equal (tidx3 LB LC a b c) (tidx3 LB LC a2 b2 c2))
                  (and (equal a a2) (equal b b2) (equal c c2))))
  :hints (("Goal" :in-theory (enable tidx3)
                  :use ((:instance mixed-radix-unique
                                   (x (+ c (* b LC))) (y (+ c2 (* b2 LC)))
                                   (L (* LB LC)) (p a) (q a2))
                        (:instance mixed-radix-unique
                                   (x c) (y c2) (L LC) (p b) (q b2))
                        (:instance digit-bound)
                        (:instance digit-bound (b b2) (c c2))))))

(defthm tidx3-bound
  (implies (and (natp a) (natp b) (natp c) (natp LA) (natp LB) (natp LC)
                (< a LA) (< b LB) (< c LC))
           (< (tidx3 LB LC a b c) (* LA (* LB LC))))
  :hints (("Goal" :use ((:instance digit-bound (b a) (c (+ c (* b LC))) (LB LA) (LC (* LB LC))))))
  :rule-classes :linear)

;;; ------------------------------------------------------------------
;;; Unique factorization of nonzero rank-one tensors over F_2
;;; (remark after Definition 2.2 of the paper)
;;; ------------------------------------------------------------------

(defthm outer3-factor-A-unique
  (implies (and (bvp A) (bvp B) (bvp C) (bvp A2) (bvp B2) (bvp C2)
                (equal (len A) (len A2)) (equal (len B) (len B2)) (equal (len C) (len C2))
                (not (equal A (bv-zero (len A))))
                (not (equal A2 (bv-zero (len A))))
                (not (equal B2 (bv-zero (len B))))
                (not (equal C2 (bv-zero (len C))))
                (equal (outer3 A B C) (outer3 A2 B2 C2)))
           (equal A A2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance bv-extensionality (x A) (y A2))
                 (:instance nth-of-outer3
                            (ia (bv-diff-index A A2)) (ib (bv-first-one B2)) (ic (bv-first-one C2)))
                 (:instance nth-of-outer3 (A A2) (B B2) (C C2)
                            (ia (bv-diff-index A A2)) (ib (bv-first-one B2)) (ic (bv-first-one C2)))
                 (:instance nth-of-outer3
                            (ia (bv-first-one A2)) (ib (bv-first-one B2)) (ic (bv-first-one C2)))
                 (:instance nth-of-outer3 (A A2) (B B2) (C C2)
                            (ia (bv-first-one A2)) (ib (bv-first-one B2)) (ic (bv-first-one C2)))
                 (:instance bv-diff-index-witness (x A) (y A2))
                 (:instance bv-first-one-witness (x A2))
                 (:instance bv-first-one-witness (x B2))
                 (:instance bv-first-one-witness (x C2)))
           :in-theory (disable nth-of-outer3 bv-diff-index-witness bv-first-one-witness
                               outer3 tidx3))))
