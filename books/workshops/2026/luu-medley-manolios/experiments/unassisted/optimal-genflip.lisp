; optimal-genflip.lisp -- Appendix B of the paper (Theorem B.1, optimal
; generalized flip reduction).
;
; For a group A (x) sum_i B_i (x) C_i of N summands, a generalized flip
; is a change of basis B, C |-> BG, G^{-1}C (genflip-basis.lisp).  The
; number of surviving summands is the number of j with (BG)_j /= 0 and
; (G^{-1}C)_j /= 0.  Theorem B.1: the minimum over G of the survivors is
; rank(T_BC), the (tensor) rank of the order-2 tensor sum_i B_i (x) C_i,
; i.e. the least number of simple tensors u (x) v summing to it.
;
; Part 1 (this file, lower bound): every generalized flip leaves at
; least rank(T_BC) survivors, because the survivors themselves form a
; decomposition of T_BC.
;
; Part 2 (counting lemma): an injective linear map F_2^s -> F_2^s'
; forces s <= s'.  Used for the optimality direction.

(in-package "ACL2")

(include-book "genflip-basis")
(include-book "genflip")

;;; ------------------------------------------------------------------
;;; Survivors and tensor rank
;;; ------------------------------------------------------------------

;; The surviving pairs of a decomposition: those with both factors nonzero.
(defun survivors (LB LC Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom Bs) (mv nil nil))
        (t (mv-let (rb rc) (survivors LB LC (cdr Bs) (cdr Cs))
             (if (or (equal (car Bs) (bv-zero LB)) (equal (car Cs) (bv-zero LC)))
                 (mv rb rc)
               (mv (cons (car Bs) rb) (cons (car Cs) rc)))))))

(defun num-survivors (LB LC Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (rb rc) (survivors LB LC Bs Cs) (declare (ignore rc)) (len rb)))

;; Dropping zero pairs does not change the tensor.
(defthm outer-of-zero-pair
  (implies (and (natp LB) (natp LC) (bvp B) (bvp C) (equal (len B) LB) (equal (len C) LC)
                (or (equal B (bv-zero LB)) (equal C (bv-zero LC))))
           (equal (outer B C) (bv-zero (* LB LC))))
  :hints (("Goal" :in-theory (disable outer-of-zero-left outer-of-zero-right outer-of-zero-left-any)
                  :use ((:instance outer-of-zero-left (L LB) (v C))
                        (:instance outer-of-zero-right (u B) (L LC))))))

(defthm T2-of-survivors
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs) (equal (len Bs) (len Cs)))
           (equal (T2 LB LC (mv-nth 0 (survivors LB LC Bs Cs)) (mv-nth 1 (survivors LB LC Bs Cs)))
                  (T2 LB LC Bs Cs)))
  :hints (("Goal" :induct (ind-2lists Bs Cs)
                  :in-theory (disable outer-of-zero-pair))
          ("Subgoal *1/2" :use ((:instance outer-of-zero-pair (B (car Bs)) (C (car Cs)))))))

(defthm survivors-bv-listp
  (implies (and (bv-listp LB Bs) (bv-listp LC Cs) (equal (len Bs) (len Cs)))
           (and (bv-listp LB (mv-nth 0 (survivors LB LC Bs Cs)))
                (bv-listp LC (mv-nth 1 (survivors LB LC Bs Cs)))
                (equal (len (mv-nth 1 (survivors LB LC Bs Cs)))
                       (len (mv-nth 0 (survivors LB LC Bs Cs))))))
  :hints (("Goal" :induct (ind-2lists Bs Cs))))

;; "T has a decomposition into at most k simple tensors."
(defun-sk has-decomp (LB LC T2val k)
  (exists (Us Vs)
          (and (bv-listp LB Us) (bv-listp LC Vs) (equal (len Us) (len Vs))
               (<= (len Us) k)
               (equal (T2 LB LC Us Vs) T2val))))

;; rank(T) <= r  means  (has-decomp LB LC T r).  The rank is the least such r;
;; we do not need it as a function.

;;; ------------------------------------------------------------------
;;; Lower bound: survivors of any generalized flip decompose T_BC
;;; ------------------------------------------------------------------

;; Theorem B.1, lower bound: for every invertible G (sum_j g_j (x) h_j = I),
;; the number of survivors is at least the rank of T_BC.
(defthm genflip-survivors-decompose-T2
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (equal (len Bs) (len Cs))
                (bv-listp (len Bs) gs) (bv-listp (len Cs) hs) (equal (len gs) (len hs))
                (equal (rows-sum2 (len Bs) (len Cs) gs hs) (identity-rows (len Cs))))
           (has-decomp LB LC (T2 LB LC Bs Cs)
                       (num-survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))))
  :hints (("Goal" :in-theory (disable change-of-basis-preserves-T2 T2-of-survivors survivors-bv-listp)
                  :use (change-of-basis-preserves-T2
                        (:instance T2-of-survivors (Bs (new-facs LB Bs gs)) (Cs (new-facs LC Cs hs)))
                        (:instance survivors-bv-listp (Bs (new-facs LB Bs gs)) (Cs (new-facs LC Cs hs)))
                        (:instance has-decomp-suff
                                   (T2val (T2 LB LC Bs Cs))
                                   (k (num-survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs)))
                                   (Us (mv-nth 0 (survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))))
                                   (Vs (mv-nth 1 (survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs)))))))))

;; Equivalently: if T_BC has no decomposition with fewer than r terms, no
;; generalized flip leaves fewer than r survivors.
(defthm genflip-lower-bound
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (equal (len Bs) (len Cs))
                (bv-listp (len Bs) gs) (bv-listp (len Cs) hs) (equal (len gs) (len hs))
                (equal (rows-sum2 (len Bs) (len Cs) gs hs) (identity-rows (len Cs)))
                (natp r)
                (not (has-decomp LB LC (T2 LB LC Bs Cs) (1- r))))
           (<= r (num-survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable genflip-survivors-decompose-T2 has-decomp
                                      change-of-basis-preserves-T2 T2-of-survivors survivors-bv-listp)
                  :use (change-of-basis-preserves-T2
                        (:instance T2-of-survivors (Bs (new-facs LB Bs gs)) (Cs (new-facs LC Cs hs)))
                        (:instance survivors-bv-listp (Bs (new-facs LB Bs gs)) (Cs (new-facs LC Cs hs)))
                        (:instance has-decomp-suff
                                   (T2val (T2 LB LC Bs Cs)) (k (1- r))
                                   (Us (mv-nth 0 (survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))))
                                   (Vs (mv-nth 1 (survivors LB LC (new-facs LB Bs gs) (new-facs LC Cs hs)))))))))

;;; ------------------------------------------------------------------
;;; Counting lemma: an injective linear map F_2^s -> F_2^s' forces s <= s'
;;; ------------------------------------------------------------------

;; All bit vectors of length s.
(defun cons0-all (lst)
  (declare (xargs :guard t))
  (if (atom lst) nil (cons (cons 0 (car lst)) (cons0-all (cdr lst)))))
(defun cons1-all (lst)
  (declare (xargs :guard t))
  (if (atom lst) nil (cons (cons 1 (car lst)) (cons1-all (cdr lst)))))

(defun all-bvs (s)
  (declare (xargs :guard (natp s)))
  (if (zp s)
      (list nil)
    (append (cons0-all (all-bvs (1- s))) (cons1-all (all-bvs (1- s))))))

(defthm len-of-cons0-all (equal (len (cons0-all lst)) (len lst)))
(defthm len-of-cons1-all (equal (len (cons1-all lst)) (len lst)))
(defthm len-of-all-bvs (equal (len (all-bvs s)) (expt 2 (nfix s))))

(defthm member-of-cons0-all
  (iff (member-equal x (cons0-all lst))
       (and (consp x) (equal (car x) 0) (member-equal (cdr x) lst))))
(defthm member-of-cons1-all
  (iff (member-equal x (cons1-all lst))
       (and (consp x) (equal (car x) 1) (member-equal (cdr x) lst))))

(defthm member-of-all-bvs
  (iff (member-equal x (all-bvs s))
       (and (bvp x) (equal (len x) (nfix s))))
  :hints (("Goal" :induct (ind-xk x s))))

(defthm no-duplicatesp-of-cons0-all
  (implies (no-duplicatesp-equal lst) (no-duplicatesp-equal (cons0-all lst))))
(defthm no-duplicatesp-of-cons1-all
  (implies (no-duplicatesp-equal lst) (no-duplicatesp-equal (cons1-all lst))))
(defthm no-duplicatesp-of-all-bvs
  (no-duplicatesp-equal (all-bvs s)))

;; A duplicate-free list contained in another list is no longer than it.
(defthm subsetp-remove1-when-not-member
  (implies (and (subsetp-equal z y) (not (member-equal a z)))
           (subsetp-equal z (remove1-equal a y)))
  :hints (("Goal" :induct (len z))))

(defthm subsetp-cdr-remove1-car
  (implies (and (no-duplicatesp-equal x) (subsetp-equal x y) (consp x))
           (subsetp-equal (cdr x) (remove1-equal (car x) y)))
  :hints (("Goal" :use ((:instance subsetp-remove1-when-not-member (z (cdr x)) (a (car x)))))))

(defun ind-sub (x y) (if (atom x) (list x y) (ind-sub (cdr x) (remove1-equal (car x) y))))

(defthm len-le-when-subsetp-no-dups
  (implies (and (no-duplicatesp-equal x) (subsetp-equal x y) (true-listp y))
           (<= (len x) (len y)))
  :hints (("Goal" :induct (ind-sub x y)
                  :in-theory (disable subsetp-cdr-remove1-car))
          ("Subgoal *1/2" :use (subsetp-cdr-remove1-car)))
  :rule-classes nil)

;; Images of a list of coefficient vectors under x |-> sum_i x_i U_i.
(defun map-col-comb (L Urows lst)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom lst) nil
    (cons (col-comb L Urows (car lst)) (map-col-comb L Urows (cdr lst)))))

(defthm len-of-map-col-comb (equal (len (map-col-comb L Urows lst)) (len lst)))

(defthm subsetp-map-col-comb-all-bvs
  (implies (and (natp L) (bv-listp L Urows))
           (subsetp-equal (map-col-comb L Urows lst) (all-bvs L)))
  :hints (("Goal" :induct (map-col-comb L Urows lst))))

;; Composition: (x U) V = x (U V), where U V has rows (col-comb Vrows U_i).
(defun rows-times (L Vrows Urows)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Urows) nil
    (cons (col-comb L Vrows (car Urows)) (rows-times L Vrows (cdr Urows)))))

(defthm col-comb-assoc
  (implies (and (natp L) (natp M) (bv-listp L Vrows) (bv-listp M Urows) (bvp x)
                (equal (len x) (len Urows)))
           (equal (col-comb L Vrows (col-comb M Urows x))
                  (col-comb L (rows-times L Vrows Urows) x)))
  :hints (("Goal" :induct (ind-2lists Urows x))))

;; Injectivity from a trivial kernel:  f(x) = f(y)  =>  f(x+y) = 0  =>  x = y.
(defun-sk trivial-kernel (L Urows s)
  (forall (x)
          (implies (and (bvp x) (equal (len x) s)
                        (equal (col-comb L Urows x) (bv-zero L)))
                   (equal x (bv-zero s)))))

(defthm col-comb-injective
  (implies (and (natp L) (bv-listp L Urows) (equal (len Urows) s)
                (trivial-kernel L Urows s)
                (bvp x) (bvp y) (equal (len x) s) (equal (len y) s)
                (equal (col-comb L Urows x) (col-comb L Urows y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable trivial-kernel-necc col-comb-of-bv+)
                  :use ((:instance trivial-kernel-necc (x (bv+ x y)))
                        (:instance col-comb-of-bv+ (Cs Urows) (m x) (m2 y))))))

;; A preimage of a member of the image list.
(defun preimage (L Urows v lst)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom lst) nil)
        ((equal (col-comb L Urows (car lst)) v) (car lst))
        (t (preimage L Urows v (cdr lst)))))

(defthm preimage-works
  (implies (member-equal v (map-col-comb L Urows lst))
           (and (member-equal (preimage L Urows v lst) lst)
                (equal (col-comb L Urows (preimage L Urows v lst)) v))))

(defthm no-duplicatesp-of-map-col-comb
  (implies (and (natp L) (bv-listp L Urows) (equal (len Urows) s)
                (trivial-kernel L Urows s)
                (bv-listp s lst) (no-duplicatesp-equal lst))
           (no-duplicatesp-equal (map-col-comb L Urows lst)))
  :hints (("Goal" :induct (map-col-comb L Urows lst)
                  :in-theory (disable preimage-works))
          ("Subgoal *1/2" :use ((:instance preimage-works (v (col-comb L Urows (car lst))) (lst (cdr lst)))
                                (:instance col-comb-injective (x (car lst))
                                           (y (preimage L Urows (col-comb L Urows (car lst)) (cdr lst))))))))

(defthm bv-listp-of-cons0-all
  (implies (and (natp s) (bv-listp s lst)) (bv-listp (1+ s) (cons0-all lst))))
(defthm bv-listp-of-cons1-all
  (implies (and (natp s) (bv-listp s lst)) (bv-listp (1+ s) (cons1-all lst))))
(defthm bv-listp-of-all-bvs
  (implies (natp s) (bv-listp s (all-bvs s)))
  :hints (("Goal" :induct (all-bvs s)
                  :in-theory (disable bv-listp-of-cons0-all bv-listp-of-cons1-all))
          ("Subgoal *1/2" :use ((:instance bv-listp-of-cons0-all (s (1- s)) (lst (all-bvs (1- s))))
                                (:instance bv-listp-of-cons1-all (s (1- s)) (lst (all-bvs (1- s))))))))

(defthm expt-2-monotone
  (implies (and (natp a) (natp b) (<= (expt 2 a) (expt 2 b)))
           (<= a b))
  :rule-classes nil)

;; The counting lemma: a linear map F_2^s -> F_2^L with trivial kernel
;; forces s <= L.
(defthm trivial-kernel-implies-le
  (implies (and (natp L) (natp s) (bv-listp L Urows) (equal (len Urows) s)
                (trivial-kernel L Urows s))
           (<= s L))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable no-duplicatesp-of-map-col-comb subsetp-map-col-comb-all-bvs)
                  :use ((:instance no-duplicatesp-of-map-col-comb (lst (all-bvs s)))
                        (:instance subsetp-map-col-comb-all-bvs (lst (all-bvs s)))
                        (:instance len-le-when-subsetp-no-dups
                                   (x (map-col-comb L Urows (all-bvs s))) (y (all-bvs L)))
                        (:instance expt-2-monotone (a s) (b L))))))

;;; ------------------------------------------------------------------
;;; Part 3: a decomposition whose B factors are in reduced echelon form
;;; and whose C factors are independent is a shortest decomposition
;;; ------------------------------------------------------------------

;; xor_j u_j[p] v_j[q]  (coordinate (p,q) of sum_j u_j (x) v_j)
(defun dot-coords (p q Us Vs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Us) 0
    (bxor (band (nth p (car Us)) (nth q (car Vs)))
          (dot-coords p q (cdr Us) (cdr Vs)))))

(defthm nth-of-T2
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (natp p) (natp q) (< p L) (< q L))
           (equal (nth (+ (* p L) q) (T2 L L Us Vs))
                  (dot-coords p q Us Vs)))
  :hints (("Goal" :induct (ind-2lists Us Vs)
                  :in-theory (disable nth-of-outer digit-bound))
          ("Subgoal *1/2" :use ((:instance nth-of-outer (u (car Us)) (v (car Vs)) (i p) (j q))
                                (:instance digit-bound (b p) (c q) (LB L) (LC L))))
          ("Subgoal *1/1" :use ((:instance digit-bound (b p) (c q) (LB L) (LC L))))))

;; The p-th coordinates of all u_j, as a bit vector of length (len Us).
(defun coords-at (p Us)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Us) nil (cons (nth p (car Us)) (coords-at p (cdr Us)))))

(defthm bvp-of-coords-at
  (implies (and (natp L) (bv-listp L Us) (natp p) (< p L)) (bvp (coords-at p Us)))
  :hints (("Goal" :induct (coords-at p Us))))
(defthm len-of-coords-at (equal (len (coords-at p Us)) (len Us)))

;; Row p of sum_j u_j (x) v_j is sum_j u_j[p] v_j.
(defthm nth-of-col-comb-coords
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (natp p) (natp q) (< p L) (< q L))
           (equal (nth q (col-comb L Vs (coords-at p Us)))
                  (dot-coords p q Us Vs)))
  :hints (("Goal" :induct (ind-2lists Us Vs))))

;; Equal tensors have equal rows.
(defthm rows-equal-when-T2-equal
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (natp p) (< p L)
                (equal (T2 L L Us Vs) (T2 L L Bs Cs)))
           (equal (col-comb L Vs (coords-at p Us))
                  (col-comb L Cs (coords-at p Bs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth-of-T2 nth-of-col-comb-coords bv-diff-index-witness)
                  :use ((:instance bv-extensionality
                                   (x (col-comb L Vs (coords-at p Us)))
                                   (y (col-comb L Cs (coords-at p Bs))))
                        (:instance bv-diff-index-witness
                                   (x (col-comb L Vs (coords-at p Us)))
                                   (y (col-comb L Cs (coords-at p Bs))))
                        (:instance nth-of-col-comb-coords
                                   (q (bv-diff-index (col-comb L Vs (coords-at p Us))
                                                     (col-comb L Cs (coords-at p Bs)))))
                        (:instance nth-of-col-comb-coords (Us Bs) (Vs Cs)
                                   (q (bv-diff-index (col-comb L Vs (coords-at p Us))
                                                     (col-comb L Cs (coords-at p Bs)))))
                        (:instance nth-of-T2
                                   (q (bv-diff-index (col-comb L Vs (coords-at p Us))
                                                     (col-comb L Cs (coords-at p Bs)))))
                        (:instance nth-of-T2 (Us Bs) (Vs Cs)
                                   (q (bv-diff-index (col-comb L Vs (coords-at p Us))
                                                     (col-comb L Cs (coords-at p Bs)))))))))

;; Reduced echelon form: pivot coordinates P = (p_0 ... p_{s-1}) with
;; B_k[p_i] = delta_ik, i.e. (coords-at p_i Bs) = (unit s i).
(defun pivots-from (P Bs s i)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom P) t
    (and (natp (car P))
         (equal (coords-at (car P) Bs) (unit s i))
         (pivots-from (cdr P) Bs s (1+ i)))))

;; Pivot coordinates are naturals below L.
(defun all-below (P L)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom P) t (and (natp (car P)) (< (car P) L) (all-below (cdr P) L))))

;; U_i = (coords-at p_i Us) for the pivots p_i of P.
(defun pivot-rows (P Us)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom P) nil (cons (coords-at (car P) Us) (pivot-rows (cdr P) Us))))

(defthm len-of-pivot-rows (equal (len (pivot-rows P Us)) (len P)))
(defthm bv-listp-of-pivot-rows
  (implies (and (natp L) (bv-listp L Us) (all-below P L))
           (bv-listp (len Us) (pivot-rows P Us))))

(defun ind-nat-list2 (i x) (if (zp i) (list i x) (ind-nat-list2 (1- i) (cdr x))))

(defthm cons-nth-nthcdr
  (implies (and (natp i) (< i (len x)))
           (equal (cons (nth i x) (nthcdr (+ 1 i) x)) (nthcdr i x)))
  :hints (("Goal" :induct (ind-nat-list2 i x) :in-theory (enable nthcdr))))

(defthm nthcdr-of-len-is-nil
  (implies (and (true-listp x) (natp i) (<= (len x) i))
           (equal (nthcdr i x) nil))
  :hints (("Goal" :induct (ind-nat-list2 i x) :in-theory (enable nthcdr))))

;; With the tensors equal and the B's in echelon form, the rows of the
;; Us-Vs decomposition at the pivots reproduce the C's:
;;   (col-comb L Vs U_i) = C_i,  i.e.  (rows-times L Vs (pivot-rows P Us)) = (nthcdr i Cs).
(defthm rows-times-pivot-rows
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (equal (T2 L L Us Vs) (T2 L L Bs Cs))
                (all-below P L) (natp i) (equal (+ i (len P)) (len Cs))
                (pivots-from P Bs (len Cs) i))
           (equal (rows-times L Vs (pivot-rows P Us)) (nthcdr i Cs)))
  :hints (("Goal" :induct (ind-Bs-i P i)
                  :in-theory (disable col-comb-of-unit))
          ("Subgoal *1/2" :use ((:instance rows-equal-when-T2-equal (p (car P)))
                                (:instance col-comb-of-unit (Cs Cs) (N (len Cs)))))))

;; Hence sum_i x_i C_i = col-comb Vs (sum_i x_i U_i): a zero combination of
;; the U_i gives a zero combination of the C_i.
(defthm pivot-rows-trivial-kernel
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (equal (T2 L L Us Vs) (T2 L L Bs Cs))
                (all-below P L) (equal (len P) (len Cs))
                (pivots-from P Bs (len Cs) 0)
                (trivial-kernel L Cs (len Cs)))
           (trivial-kernel (len Us) (pivot-rows P Us) (len Cs)))
  :hints (("Goal" :in-theory (disable rows-times-pivot-rows col-comb-assoc trivial-kernel-necc)
                  :expand ((trivial-kernel (len Us) (pivot-rows P Us) (len Cs)))
                  :use ((:instance rows-times-pivot-rows (i 0))
                        (:instance col-comb-assoc (Vrows Vs) (M (len Us)) (Urows (pivot-rows P Us))
                                   (x (trivial-kernel-witness (len Us) (pivot-rows P Us) (len Cs))))
                        (:instance trivial-kernel-necc (Urows Cs) (s (len Cs))
                                   (x (trivial-kernel-witness (len Us) (pivot-rows P Us) (len Cs))))))))

;; Part 3 theorem: an echelon/independent decomposition of length s forces
;; every decomposition to have at least s terms.
(defthm echelon-decomp-is-shortest
  (implies (and (natp L) (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (equal (T2 L L Us Vs) (T2 L L Bs Cs))
                (all-below P L) (equal (len P) (len Cs))
                (pivots-from P Bs (len Cs) 0)
                (trivial-kernel L Cs (len Cs)))
           (<= (len Cs) (len Us)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pivot-rows-trivial-kernel)
                  :use (pivot-rows-trivial-kernel
                        (:instance trivial-kernel-implies-le (L (len Us)) (s (len Cs))
                                   (Urows (pivot-rows P Us)))))))


;;; ------------------------------------------------------------------
;;; Part 4a: elementary pair flips on lists, and their composition
;;; ------------------------------------------------------------------

;; flip(i,j):  X_j += X_i,  Y_i += Y_j   (the pairwise flip of Def. 2.3
;; inside the group; as a change of basis it is G = I + E_ij = G^{-1}).
(defun flipX (i j Xs)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth j (bv+ (nth j Xs) (nth i Xs)) Xs))

(defun flipY (i j Ys)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth i (bv+ (nth i Ys) (nth j Ys)) Ys))

(defthm bv-listp-of-update-nth
  (implies (and (natp L) (bv-listp L Xs) (natp j) (< j (len Xs)) (bvp v) (equal (len v) L))
           (bv-listp L (update-nth j v Xs)))
  :hints (("Goal" :induct (ind-xk Xs j) :in-theory (disable bv-listp-member))))

(defthm len-of-update-nth-in-range
  (implies (and (natp j) (< j (len Xs)))
           (equal (len (update-nth j v Xs)) (len Xs))))

(defthm bv-listp-nth
  (implies (and (natp L) (bv-listp L Xs) (natp j) (< j (len Xs)))
           (and (bvp (nth j Xs)) (equal (len (nth j Xs)) L)))
  :hints (("Goal" :induct (ind-xk Xs j) :in-theory (disable bv-listp-member))))

(defthm bv-listp-of-flipX
  (implies (and (natp L) (bv-listp L Xs) (natp i) (natp j) (< i (len Xs)) (< j (len Xs)))
           (and (bv-listp L (flipX i j Xs)) (equal (len (flipX i j Xs)) (len Xs)))))
(defthm bv-listp-of-flipY
  (implies (and (natp L) (bv-listp L Ys) (natp i) (natp j) (< i (len Ys)) (< j (len Ys)))
           (and (bv-listp L (flipY i j Ys)) (equal (len (flipY i j Ys)) (len Ys)))))

(defun ind-2lists-nat2 (x y j) (if (atom x) (list x y j) (ind-2lists-nat2 (cdr x) (cdr y) (1- j))))

;; T2 as a sum over indices, to reason about update-nth.
(defthm T2-as-outer-of-nth
  (implies (and (natp LB) (natp LC) (bv-listp LB Xs) (bv-listp LC Ys) (equal (len Xs) (len Ys))
                (natp j) (< j (len Xs)))
           (equal (T2 LB LC Xs Ys)
                  (bv+ (outer (nth j Xs) (nth j Ys))
                       (T2 LB LC (update-nth j (bv-zero LB) Xs) Ys))))
  :rule-classes nil
  :hints (("Goal" :induct (ind-2lists-nat2 Xs Ys j))))
