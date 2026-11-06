; genflip-basis.lisp -- Section 5.2 of the paper, change-of-basis view of
; generalized flips:
;
;   A (x) (sum_i B_i (x) C_i) = A (x) ([B_1 ... B_N] G G^{-1} [C_1 ... C_N]^T)
;
; for any invertible G in GL_N(F_2).  We represent G by its columns
; g_1..g_N and G^{-1} by its rows h_1..h_N (bit vectors of length N);
; G G^{-1} = I says sum_j g_j (x) h_j = I (as N x N matrices, kept as
; lists of rows).  The new factors are (BG)_j = sum_i (g_j)_i B_i and
; (G^{-1}C)_j = sum_k (h_j)_k C_k.  The theorem says the order-2 tensor
; sum_i B_i (x) C_i, hence the group's contribution A (x) (...), is
; unchanged.  The pairwise flip is the case N = 2, G = [[1,0],[1,1]].

(in-package "ACL2")

(include-book "mmt")

;;; ------------------------------------------------------------------
;;; Linear combinations and order-2 tensor sums
;;; ------------------------------------------------------------------

;; sum_i g_i V_i  (g a bit vector aligned with the list Vs)
(defun col-comb (L Vs g)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Vs)
      (bv-zero L)
    (bv+ (bv-scale (car g) (car Vs)) (col-comb L (cdr Vs) (cdr g)))))

;; sum_i B_i (x) C_i
(defun T2 (LB LC Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Bs)
      (bv-zero (* LB LC))
    (bv+ (outer (car Bs) (car Cs)) (T2 LB LC (cdr Bs) (cdr Cs)))))

;; Phi(M) = sum_i B_i (x) (sum_k M_ik C_k), M given by rows aligned with Bs.
(defun Phi (LB LC Bs Cs rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Bs)
      (bv-zero (* LB LC))
    (bv+ (outer (car Bs) (col-comb LC Cs (car rows)))
         (Phi LB LC (cdr Bs) Cs (cdr rows)))))

;; The rows of the rank-one matrix g (x) h.
(defun rows-outer (g h)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom g) nil (cons (bv-scale (car g) h) (rows-outer (cdr g) h))))

(defun rows+ (M1 M2)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom M1) nil (cons (bv+ (car M1) (car M2)) (rows+ (cdr M1) (cdr M2)))))

(defun zero-rows (N)
  (declare (xargs :guard (natp N)))
  (if (zp N) nil (cons (bv-zero N) (zero-rows (1- N)))))

;; sum_j g_j (x) h_j
(defun rows-sum (N gs hs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom gs)
      (zero-rows N)
    (rows+ (rows-outer (car gs) (car hs)) (rows-sum N (cdr gs) (cdr hs)))))

(defun id-rows-from (N i)
  (declare (xargs :guard (and (natp N) (natp i)) :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N))
      nil
    (cons (unit N i) (id-rows-from N (1+ i)))))

(defun identity-rows (N)
  (declare (xargs :guard (natp N)))
  (id-rows-from N 0))

(defun new-facs (L Vs gs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom gs) nil (cons (col-comb L Vs (car gs)) (new-facs L Vs (cdr gs)))))

;;; ------------------------------------------------------------------
;;; Basic facts
;;; ------------------------------------------------------------------

(defun ind-3lists (x y z)
  (if (atom x) (list x y z) (ind-3lists (cdr x) (cdr y) (cdr z))))

(defun ind-2lists (x y)
  (if (atom x) (list x y) (ind-2lists (cdr x) (cdr y))))

(defun ind-2lists-nat (x N)
  (if (atom x) (list x N) (ind-2lists-nat (cdr x) (1- N))))

(defthm bvp-of-col-comb (implies (bv-listp L Vs) (bvp (col-comb L Vs g))))
(defthm len-of-col-comb (implies (bv-listp L Vs) (equal (len (col-comb L Vs g)) (nfix L))))

(defthm bv-scale-of-bv-scale
  (implies (and (bitp a) (bitp b) (bvp v))
           (equal (bv-scale a (bv-scale b v)) (bv-scale (band a b) v))))

;; Lemma A: col-comb Cs (b h) = b (col-comb Cs h)
(defthm col-comb-of-bv-scale
  (implies (and (bv-listp L Cs) (bitp b) (bvp h))
           (equal (col-comb L Cs (bv-scale b h))
                  (bv-scale b (col-comb L Cs h))))
  :hints (("Goal" :induct (col-comb L Cs h))))

;; col-comb is linear in the coefficient vector.
(defthm col-comb-of-bv+
  (implies (and (bv-listp L Cs) (bvp m) (bvp m2) (equal (len m) (len m2)))
           (equal (col-comb L Cs (bv+ m m2))
                  (bv+ (col-comb L Cs m) (col-comb L Cs m2))))
  :hints (("Goal" :induct (ind-3lists Cs m m2))))

(defthm outer-of-bv-scale-left
  (implies (and (bitp b) (bvp u) (bvp v))
           (equal (outer (bv-scale b u) v) (outer u (bv-scale b v))))
  :hints (("Goal" :induct (outer u v))))

(defthm outer-of-zero-left-any
  (equal (outer (bv-zero L) v) (bv-zero (* (nfix L) (len v)))))

(defthm bvp-of-T2 (bvp (T2 LB LC Bs Cs)))
(defthm bvp-of-Phi (bvp (Phi LB LC Bs Cs rows)))
(defthm len-of-Phi
  (implies (and (bv-listp LB Bs) (bv-listp LC Cs) (natp LB) (natp LC))
           (equal (len (Phi LB LC Bs Cs rows)) (* LB LC))))

(defthm col-comb-of-zero
  (implies (bv-listp L Cs)
           (equal (col-comb L Cs (bv-zero N)) (bv-zero (nfix L))))
  :hints (("Goal" :induct (ind-2lists-nat Cs N))))

;; Lemma B: (sum g_i B_i) (x) (sum h_k C_k) = Phi(rows-outer g h)
(defthm outer-of-col-combs
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (bvp g) (bvp h) (equal (len g) (len Bs)))
           (equal (outer (col-comb LB Bs g) (col-comb LC Cs h))
                  (Phi LB LC Bs Cs (rows-outer g h))))
  :hints (("Goal" :induct (ind-2lists Bs g)
                  :in-theory (disable outer-of-bv-scale-left)
                  :expand ((rows-outer g h)))
          ("Subgoal *1/2" :use ((:instance outer-of-bv-scale-left (b (car g)) (u (car Bs))
                                           (v (col-comb LC Cs h)))))))

;; Lemma C: Phi is additive in the matrix.
(defthm Phi-of-rows+
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (bv-listp (len Cs) M1) (bv-listp (len Cs) M2)
                (equal (len M1) (len Bs)) (equal (len M2) (len Bs)))
           (equal (Phi LB LC Bs Cs (rows+ M1 M2))
                  (bv+ (Phi LB LC Bs Cs M1) (Phi LB LC Bs Cs M2))))
  :hints (("Goal" :induct (ind-3lists Bs M1 M2))))

;;; ------------------------------------------------------------------
;;; Assembly
;;; ------------------------------------------------------------------

(defun zero-rows-of (NB NC)
  (declare (xargs :guard (and (natp NB) (natp NC))))
  (if (zp NB) nil (cons (bv-zero NC) (zero-rows-of (1- NB) NC))))

;; sum_j g_j (x) h_j, as NB rows of length NC
(defun rows-sum2 (NB NC gs hs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom gs)
      (zero-rows-of NB NC)
    (rows+ (rows-outer (car gs) (car hs)) (rows-sum2 NB NC (cdr gs) (cdr hs)))))

(defthm bv-listp-of-rows-outer
  (implies (and (bvp g) (bvp h) (equal (len h) (nfix N)))
           (bv-listp N (rows-outer g h))))
(defthm len-of-rows-outer (equal (len (rows-outer g h)) (len g)))
(defthm bv-listp-of-rows+
  (implies (and (bv-listp NC M1) (bv-listp NC M2) (equal (len M1) (len M2)))
           (bv-listp NC (rows+ M1 M2)))
  :hints (("Goal" :induct (ind-2lists M1 M2))))
(defthm len-of-rows+ (equal (len (rows+ M1 M2)) (len M1)))
(defthm bv-listp-of-zero-rows-of (bv-listp NC (zero-rows-of NB NC)))
(defthm len-of-zero-rows-of (equal (len (zero-rows-of NB NC)) (nfix NB)))

(defthm bv-listp-of-rows-sum2
  (implies (and (natp NB) (natp NC) (bv-listp NB gs) (bv-listp NC hs) (equal (len gs) (len hs)))
           (and (bv-listp NC (rows-sum2 NB NC gs hs))
                (equal (len (rows-sum2 NB NC gs hs)) NB)))
  :hints (("Goal" :induct (ind-2lists gs hs))))

(defthm col-comb-of-atom
  (implies (and (bv-listp L Cs) (atom g))
           (equal (col-comb L Cs g) (bv-zero (nfix L)))))

(defthm Phi-of-zero-rows
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs))
           (equal (Phi LB LC Bs Cs (zero-rows-of NB NC))
                  (bv-zero (* LB LC))))
  :hints (("Goal" :induct (ind-2lists-nat Bs NB))))

;; Lemma D: T2 of the transformed factors is Phi of sum_j g_j (x) h_j.
(defthm T2-of-new-facs
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (bv-listp (len Bs) gs) (bv-listp (len Cs) hs) (equal (len gs) (len hs)))
           (equal (T2 LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))
                  (Phi LB LC Bs Cs (rows-sum2 (len Bs) (len Cs) gs hs))))
  :hints (("Goal" :induct (ind-2lists gs hs)
                  :in-theory (disable outer-of-col-combs Phi-of-rows+))
          ("Subgoal *1/2" :use ((:instance outer-of-col-combs (g (car gs)) (h (car hs)))
                                (:instance Phi-of-rows+
                                           (M1 (rows-outer (car gs) (car hs)))
                                           (M2 (rows-sum2 (len Bs) (len Cs) (cdr gs) (cdr hs))))))))

;; Lemma E: Phi of the identity is T2.
(defun ind-list-nat-nat (x i N)
  (if (atom x) (list x i N) (ind-list-nat-nat (cdr x) (1- i) (1- N))))

(defthm col-comb-of-unit-0
  (implies (and (natp L) (bv-listp L Cs) (consp Cs) (posp N))
           (equal (col-comb L Cs (unit N 0)) (car Cs)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable col-comb-of-zero unit-when-negative)
                  :expand ((col-comb L Cs (unit N 0)) (unit N 0))
                  :use ((:instance unit-when-negative (L (1- N)) (k -1))
                        (:instance col-comb-of-zero (Cs (cdr Cs)) (N (1- N)))))))

(defthm col-comb-of-unit
  (implies (and (natp L) (bv-listp L Cs) (natp i) (< i (len Cs)) (natp N) (<= (len Cs) N))
           (equal (col-comb L Cs (unit N i)) (nth i Cs)))
  :hints (("Goal" :induct (ind-list-nat-nat Cs i N)
                  :in-theory (disable col-comb-of-unit-0))
          ("Subgoal *1/2" :cases ((zp i))
                          :use ((:instance col-comb-of-unit-0)))))

(defun ind-Bs-i (Bs i) (if (atom Bs) (list Bs i) (ind-Bs-i (cdr Bs) (1+ i))))

(defun ind-nat-list (i Cs) (if (zp i) (list i Cs) (ind-nat-list (1- i) (cdr Cs))))

(defthm cdr-of-nthcdr-local
  (implies (natp i) (equal (cdr (nthcdr i Cs)) (nthcdr (+ 1 i) Cs)))
  :hints (("Goal" :induct (ind-nat-list i Cs) :in-theory (enable nthcdr))))

(defthm Phi-of-id-rows-from
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (natp i) (equal (+ i (len Bs)) (len Cs)))
           (equal (Phi LB LC Bs Cs (id-rows-from (len Cs) i))
                  (T2 LB LC Bs (nthcdr i Cs))))
  :hints (("Goal" :induct (ind-Bs-i Bs i)
                  :in-theory (disable col-comb-of-unit))
          ("Subgoal *1/2" :use ((:instance col-comb-of-unit (L LC) (N (len Cs))))
                          :expand ((id-rows-from (len Cs) i)
                                   (T2 LB LC Bs (nthcdr i Cs))))))

(defthm Phi-of-identity-rows
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (equal (len Bs) (len Cs)))
           (equal (Phi LB LC Bs Cs (identity-rows (len Cs)))
                  (T2 LB LC Bs Cs)))
  :hints (("Goal" :use ((:instance Phi-of-id-rows-from (i 0))))))

;; The change-of-basis theorem of Section 5.2:
;;   if  sum_j g_j (x) h_j = I  (i.e. G G^{-1} = I),
;;   then sum_j (BG)_j (x) (G^{-1}C)_j = sum_i B_i (x) C_i.
(defthm change-of-basis-preserves-T2
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs)
                (equal (len Bs) (len Cs))
                (bv-listp (len Bs) gs) (bv-listp (len Cs) hs) (equal (len gs) (len hs))
                (equal (rows-sum2 (len Bs) (len Cs) gs hs) (identity-rows (len Cs))))
           (equal (T2 LB LC (new-facs LB Bs gs) (new-facs LC Cs hs))
                  (T2 LB LC Bs Cs)))
  :hints (("Goal" :in-theory (disable T2-of-new-facs Phi-of-identity-rows)
                  :use (T2-of-new-facs Phi-of-identity-rows))))

;; The group A (x) sum_i B_i (x) C_i as a list of summands (A B_i C_i).
(defun group (A Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom Bs) nil (cons (list A (car Bs) (car Cs)) (group A (cdr Bs) (cdr Cs)))))

(defthm len-of-T2
  (implies (and (natp LB) (natp LC) (bv-listp LB Bs) (bv-listp LC Cs) (equal (len Bs) (len Cs)))
           (equal (len (T2 LB LC Bs Cs)) (* LB LC)))
  :hints (("Goal" :induct (ind-2lists Bs Cs))))

(defthm triple-sum-of-group
  (implies (and (natp LB) (natp LC) (bvp A) (equal (len A) L) (natp L)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (equal LB L) (equal LC L))
           (equal (triple-sum L (group A Bs Cs))
                  (outer A (T2 LB LC Bs Cs))))
  :hints (("Goal" :induct (ind-2lists Bs Cs)
                  :in-theory (enable rank1 outer3))))

(defthm new-facs-bv-listp
  (implies (bv-listp L Vs)
           (and (bv-listp L (new-facs L Vs gs))
                (equal (len (new-facs L Vs gs)) (len gs)))))

;; Hence a generalized flip with any invertible G keeps the group's
;; contribution to the scheme unchanged.
(defthm change-of-basis-preserves-group-sum
  (implies (and (natp L) (bvp A) (equal (len A) L)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) (len Cs))
                (bv-listp (len Bs) gs) (bv-listp (len Cs) hs) (equal (len gs) (len hs))
                (equal (rows-sum2 (len Bs) (len Cs) gs hs) (identity-rows (len Cs))))
           (equal (triple-sum L (group A (new-facs L Bs gs) (new-facs L Cs hs)))
                  (triple-sum L (group A Bs Cs))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable change-of-basis-preserves-T2 triple-sum-of-group)
                  :use ((:instance change-of-basis-preserves-T2 (LB L) (LC L))
                        (:instance triple-sum-of-group (LB L) (LC L))
                        (:instance triple-sum-of-group (LB L) (LC L)
                                   (Bs (new-facs L Bs gs)) (Cs (new-facs L Cs hs)))))))

;; The ordinary flip is the case N = 2, G = [[1,0],[1,1]] = G^{-1}:
;; columns g_1 = (1,1), g_2 = (0,1); rows h_1 = (1,0), h_2 = (1,1).
(defthm pairwise-flip-matrix-is-invertible
  (equal (rows-sum2 2 2 '((1 1) (0 1)) '((1 0) (1 1))) (identity-rows 2)))

(defthm pairwise-flip-as-change-of-basis
  (implies (and (natp L) (bvp A) (equal (len A) L)
                (bvp B1) (bvp B2) (bvp C1) (bvp C2)
                (equal (len B1) L) (equal (len B2) L) (equal (len C1) L) (equal (len C2) L))
           (equal (triple-sum L (list (list A (bv+ B1 B2) C1) (list A B2 (bv+ C1 C2))))
                  (triple-sum L (list (list A B1 C1) (list A B2 C2)))))
  :hints (("Goal" :in-theory (disable change-of-basis-preserves-group-sum)
                  :use ((:instance change-of-basis-preserves-group-sum
                                   (Bs (list B1 B2)) (Cs (list C1 C2))
                                   (gs '((1 1) (0 1))) (hs '((1 0) (1 1))))))))
