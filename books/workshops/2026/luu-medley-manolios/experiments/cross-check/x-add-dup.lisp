; x-add-dup.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/add-dup.lisp
; produced by rename.py in this directory; do not edit by hand.
; add-dup.lisp -- Lemma 4.3 of the paper (add-duplicate-sum).
;
; Given summands s = A(x)B(x)C and u = A'(x)B'(x)C' of a scheme sch, with
; X = A + A' nonzero, there is a flip/plus path from sch to
;      sch (+) { X(x)B(x)C, X(x)B(x)C }.
; The path is the one of Figure 1 of the paper: plus_A, plus_B, plus_A,
; flip_A when B /= B', and plus_A, plus_A when B = B'.  Everything is
; stated for a generic position p (with lo/hi the two other positions).

(in-package "ACL2")

(include-book "x-span")

;;; ------------------------------------------------------------------
;;; Record lemmas for fac / set-fac on summands
;;; ------------------------------------------------------------------

(defthm x-fac-of-set-fac-same
  (implies (x-posp3 p)
           (equal (x-fac p (x-set-fac p v s)) v))
  :hints (("Goal" :in-theory (enable x-fac x-set-fac x-posp3))))

(defthm x-fac-of-set-fac-other
  (implies (and (x-posp3 p) (x-posp3 q) (not (equal p q)))
           (equal (x-fac q (x-set-fac p v s)) (x-fac q s)))
  :hints (("Goal" :in-theory (enable x-fac x-set-fac x-posp3))))

(defthm x-set-fac-of-set-fac-same
  (implies (x-posp3 p)
           (equal (x-set-fac p v (x-set-fac p w s)) (x-set-fac p v s)))
  :hints (("Goal" :in-theory (enable x-set-fac x-posp3))))

(defthm x-set-fac-of-fac-same
  (implies (and (x-posp3 p) (true-listp s) (equal (len s) 3))
           (equal (x-set-fac p (x-fac p s) s) s))
  :hints (("Goal" :in-theory (enable x-fac x-set-fac x-posp3))))

(defthm x-set-fac-of-set-fac-other-commute
  (implies (and (x-posp3 p) (x-posp3 q) (not (equal p q)))
           (equal (x-set-fac q v (x-set-fac p w s))
                  (x-set-fac p w (x-set-fac q v s))))
  :hints (("Goal" :in-theory (enable x-set-fac x-posp3))))

(defthm x-set-fac-of-fac-under-set-fac-other
  (implies (and (x-posp3 p) (x-posp3 q) (not (equal p q)) (true-listp s) (equal (len s) 3))
           (equal (x-set-fac q (x-fac q s) (x-set-fac p v s))
                  (x-set-fac p v s)))
  :hints (("Goal" :in-theory (enable x-fac x-set-fac x-posp3))))

(defthm x-true-listp-of-set-fac (true-listp (x-set-fac p v s))
  :hints (("Goal" :in-theory (enable x-set-fac))))
(defthm x-len-of-set-fac (equal (len (x-set-fac p v s)) 3)
  :hints (("Goal" :in-theory (enable x-set-fac))))

(defthm x-posp3-of-other-lo (x-posp3 (x-other-lo p))
  :hints (("Goal" :in-theory (enable x-posp3 x-other-lo))))
(defthm x-posp3-of-other-hi (x-posp3 (x-other-hi p))
  :hints (("Goal" :in-theory (enable x-posp3 x-other-hi))))
(defthm x-other-lo-not-p (implies (x-posp3 p) (not (equal (x-other-lo p) p)))
  :hints (("Goal" :in-theory (enable x-posp3 x-other-lo))))
(defthm x-other-hi-not-p (implies (x-posp3 p) (not (equal (x-other-hi p) p)))
  :hints (("Goal" :in-theory (enable x-posp3 x-other-hi))))
(defthm x-other-lo-not-other-hi (not (equal (x-other-lo p) (x-other-hi p)))
  :hints (("Goal" :in-theory (enable x-other-lo x-other-hi))))
(defthm x-other-lo-not-other-hi-2 (not (equal (x-other-hi p) (x-other-lo p)))
  :hints (("Goal" :in-theory (enable x-other-lo x-other-hi))))

(defthm x-summandp-facts
  (implies (x-summandp L s)
           (and (true-listp s) (equal (len s) 3)
                (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s))
                (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))
                (not (equal (car s) (x-bv-zero L)))
                (not (equal (cadr s) (x-bv-zero L)))
                (not (equal (caddr s) (x-bv-zero L)))))
  :rule-classes nil)

(defthm x-summandp-facts-rw
  (implies (x-summandp L s)
           (and (true-listp s) (equal (len s) 3)
                (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s)))))

(defthm x-summandp-facts-fc
  (implies (x-summandp L s)
           (and (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))
                (not (equal (car s) (x-bv-zero L)))
                (not (equal (cadr s) (x-bv-zero L)))
                (not (equal (caddr s) (x-bv-zero L)))))
  :rule-classes :forward-chaining)

(defthm x-fac-nonzero-when-summandp
  (implies (and (x-summandp L s) (x-posp3 p))
           (not (equal (x-fac p s) (x-bv-zero L))))
  :hints (("Goal" :in-theory (enable x-fac x-posp3))))

(defthm x-bvp-of-fac-when-summandp
  (implies (x-summandp L s) (x-bvp (x-fac p s)))
  :hints (("Goal" :in-theory (enable x-fac))))

(defthm x-len-of-fac-when-summandp
  (implies (x-summandp L s) (equal (len (x-fac p s)) (nfix L)))
  :hints (("Goal" :in-theory (enable x-fac))))

(defthm x-triplep-of-set-fac-when-summandp
  (implies (and (x-summandp L s) (x-bvp v) (equal (len v) (nfix L)))
           (x-triplep L (x-set-fac p v s)))
  :hints (("Goal" :in-theory (enable x-set-fac))))

(defthm x-zero-summandp-of-set-fac
  (implies (and (x-summandp L s) (x-posp3 p))
           (equal (x-zero-summandp L (x-set-fac p v s))
                  (equal v (x-bv-zero L))))
  :hints (("Goal" :in-theory (enable x-set-fac x-posp3))))

(defthm x-summandp-of-set-fac
  (implies (and (posp L) (x-summandp L s) (x-posp3 p) (x-bvp v) (equal (len v) L))
           (equal (x-summandp L (x-set-fac p v s))
                  (not (equal v (x-bv-zero L)))))
  :hints (("Goal" :in-theory (e/d (x-summandp) (x-zero-summandp x-triplep x-set-fac)))))

(in-theory (disable x-summandp))

;; Two summands that differ in some factor are different.
(defthm x-not-equal-set-fac-when-fac-differs-1
  (implies (and (x-posp3 p) (not (equal (x-fac p u) v)))
           (not (equal u (x-set-fac p v s)))))

(defthm x-not-equal-set-fac-when-fac-differs-2
  (implies (and (x-posp3 p) (not (equal (x-fac p u) v)))
           (not (equal (x-set-fac p v s) u))))

(defthm x-not-equal-set-fac-set-fac-when-fac-differs
  (implies (and (x-posp3 p) (not (equal v w)))
           (not (equal (x-set-fac p v s) (x-set-fac p w s2)))))

(defthm x-not-equal-set-fac-other-when-fac-differs
  (implies (and (x-posp3 p) (x-posp3 q) (not (equal p q)) (not (equal (x-fac p s) v)))
           (not (equal (x-set-fac p v s) (x-set-fac q w s)))))

;;; ------------------------------------------------------------------
;;; Explicit forms of the moves
;;; ------------------------------------------------------------------

(defthm x-apply-plus-move-explicit
  (implies (and (posp L) (x-posp3 p) (x-summandp L tgt) (x-summandp L piv)
                (not (equal (x-bv+ (x-fac p tgt) (x-fac p piv)) (x-bv-zero L))))
           (equal (x-apply-move L (x-plus-move p piv tgt) S)
                  (append (remove1-equal tgt S)
                          (list (x-set-fac p (x-bv+ (x-fac p tgt) (x-fac p piv)) tgt)
                                (x-set-fac p (x-fac p piv) tgt)))))
  :hints (("Goal" :in-theory (enable x-apply-move x-plus-results x-plus-move))))

(defthm x-apply-flip-move-first-zero
  (implies (and (posp L) (x-posp3 p) (x-summandp L s) (x-summandp L u)
                (equal (x-bv+ (x-fac (x-other-hi p) s) (x-fac (x-other-hi p) u)) (x-bv-zero L))
                (not (equal (x-bv+ (x-fac (x-other-lo p) u) (x-fac (x-other-lo p) s)) (x-bv-zero L))))
           (equal (x-apply-move L (x-flip-move p s u) sch)
                  (append (remove1-equal u (remove1-equal s sch))
                          (list (x-set-fac (x-other-lo p)
                                         (x-bv+ (x-fac (x-other-lo p) u) (x-fac (x-other-lo p) s))
                                         u)))))
  :hints (("Goal" :in-theory (enable x-apply-move x-flip-results x-flip-move))))

(defthm x-plus-move-ok
  (implies (and (x-posp3 p) (true-listp piv) (true-listp tgt)
                (member-equal piv S) (member-equal tgt (remove1-equal piv S)))
           (x-move-ok-p (x-plus-move p piv tgt) S))
  :hints (("Goal" :in-theory (enable x-move-ok-p x-plus-move))))

(defthm x-flip-move-ok
  (implies (and (x-posp3 p) (true-listp s) (true-listp u)
                (member-equal s sch) (member-equal u (remove1-equal s sch))
                (equal (x-fac p s) (x-fac p u)))
           (x-move-ok-p (x-flip-move p s u) sch))
  :hints (("Goal" :in-theory (enable x-move-ok-p x-flip-move))))

(in-theory (disable x-plus-move x-flip-move x-delete-pair-move))

;;; ------------------------------------------------------------------
;;; List helpers
;;; ------------------------------------------------------------------

(defthm x-member-remove1-when-different
  (implies (and (member-equal u S) (not (equal u s1)))
           (member-equal u (remove1-equal s1 S)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-remove1-of-append-when-member-first
  (implies (member-equal a x)
           (equal (remove1-equal a (append x y))
                  (append (remove1-equal a x) y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-perm-append-list-1
  (perm (append x (list a)) (cons a x))
  :hints (("Goal" :use ((:instance perm-of-append (x x) (y (list a)))))))

(defthm x-perm-append-list-2
  (perm (append x (list a b)) (list* a b x))
  :hints (("Goal" :use ((:instance perm-of-append (x x) (y (list a b)))))))

(defthm x-perm-rotate-4
  (perm (list* a b c d R) (list* c d a b R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append)))))

(defthm x-perm-rotate-4-append
  (perm (list* a b (append R (list c d))) (list* c d a b R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append x-perm-rotate-4 x-perm-append-list-2))
                  :use ((:instance x-perm-append-list-2 (x R) (a c) (b d))
                        (:instance x-perm-rotate-4)))))

(defthm x-perm-rotate-3
  (perm (list* a b c R) (list* b c a R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append)))))

(defthm x-perm-rotate-3-append
  (perm (cons x (append R (list a b))) (list* a b x R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append x-perm-rotate-4 x-perm-append-list-2))
                  :use ((:instance x-perm-append-list-2 (x R) (a a) (b b))))))

(defthm x-perm-step4-shape
  (perm (list* a b (append R (list b))) (list* b b (cons a R)))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append x-perm-rotate-4 x-perm-append-list-2 x-perm-append-list-1))
                  :use ((:instance x-perm-append-list-1 (x R) (a b))))))

(defcong perm perm (cons a x) 2
  :hints (("Goal" :in-theory (enable perm remove1-equal))))

(defthm x-perm-cons-remove1-when-member
  (implies (and (member-equal a x) (true-listp x))
           (perm (cons a (remove1-equal a x)) x))
  :hints (("Goal" :in-theory (enable perm remove1-equal))))

(defthm x-remove1-of-cons-different
  (implies (not (equal a b))
           (equal (remove1-equal a (cons b x)) (cons b (remove1-equal a x))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-remove1-of-cons-same
  (equal (remove1-equal a (cons a x)) x)
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-true-listp-of-remove1
  (implies (true-listp x) (true-listp (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-summand-listp-member-fc
  (implies (and (member-equal s x) (x-summand-listp L x))
           (x-summandp L s))
  :rule-classes :forward-chaining)

(defthm x-member-remove1-swap
  (implies (and (member-equal s x) (member-equal u (remove1-equal s x)))
           (member-equal s (remove1-equal u x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;;; ------------------------------------------------------------------
;;; The path of Lemma 4.3
;;; ------------------------------------------------------------------

;; s = (A at p, B at lo, C at hi), u = (A', B', C').
(defun x-add-dup-path (p s u)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((lo (x-other-lo p))
         (X (x-bv+ (x-fac p s) (x-fac p u)))
         (sX (x-set-fac p X s))
         (sA2 (x-set-fac p (x-fac p u) s))
         (B (x-fac lo s))
         (B2 (x-fac lo u))
         (sXBB2 (x-set-fac lo (x-bv+ B B2) sX))
         (sXB2 (x-set-fac lo B2 sX)))
    (if (equal B B2)
        (list (x-plus-move p u s)
              (x-plus-move p sX sA2))
      (list (x-plus-move p u s)
            (x-plus-move lo u sX)
            (x-plus-move p sXBB2 sA2)
            (x-flip-move p sXBB2 sXB2)))))

;; Algebraic facts used along the path (over F_2).
(defthm x-bv+-x-with-x-plus-y
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y)))
           (equal (x-bv+ y (x-bv+ x y)) x))
  :hints (("Goal" :use ((:instance x-bv+-self-in-middle (x y) (y x))))))

(defthm x-bv+-y-with-x-plus-y
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y)))
           (equal (x-bv+ x (x-bv+ x y)) y)))

(defthm x-bv+-plus-ne-first
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (not (equal y (x-bv-zero (len x)))))
           (not (equal (x-bv+ x y) x)))
  :hints (("Goal" :use ((:instance x-bv+-cancel-left (x x) (y y) (z (x-bv-zero (len x))))))))

(defthm x-bv+-plus-ne-second
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (not (equal x (x-bv-zero (len x)))))
           (not (equal (x-bv+ x y) y)))
  :hints (("Goal" :use ((:instance x-bv+-cancel-left (x y) (y x) (z (x-bv-zero (len x))))))))

(defthm x-bv+-plus-ne-first-alt
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (not (equal y (x-bv-zero (len x)))))
           (not (equal x (x-bv+ x y))))
  :hints (("Goal" :use x-bv+-plus-ne-first)))

(defthm x-bv+-plus-ne-second-alt
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (not (equal x (x-bv-zero (len x)))))
           (not (equal y (x-bv+ x y))))
  :hints (("Goal" :use x-bv+-plus-ne-second)))

(encapsulate ()
  (local (in-theory (disable x-summandp-facts-rw)))

  ;; Step 1 (both cases): plus on p with pivot u replacing s.
  (defthm x-add-dup-step1
    (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L))))
             (and (x-move-ok-p (x-plus-move p u s) sch)
                  (perm (x-apply-move L (x-plus-move p u s) sch)
                        (list* (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                               (x-set-fac p (x-fac p u) s)
                               (remove1-equal s sch)))))
    :hints (("Goal" :in-theory (disable x-summandp-of-set-fac)
                    :do-not-induct t
                    :use ((:instance x-summandp-facts (s s))
                          (:instance x-summandp-facts (s u)))))))

(encapsulate ()
  (local (in-theory (disable x-summandp-facts-rw x-summandp-of-set-fac)))

  ;; Step 2 (B /= B'): plus on lo with pivot u replacing sX.
  (defthm x-add-dup-step2
    (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L)))
                  (not (equal (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))))
             (let* ((lo (x-other-lo p))
                    (X (x-bv+ (x-fac p s) (x-fac p u)))
                    (sX (x-set-fac p X s))
                    (sA2 (x-set-fac p (x-fac p u) s))
                    (R (remove1-equal s sch))
                    (T1 (list* sX sA2 R))
                    (sXBB2 (x-set-fac lo (x-bv+ (x-fac lo s) (x-fac lo u)) sX))
                    (sXB2 (x-set-fac lo (x-fac lo u) sX)))
               (and (x-move-ok-p (x-plus-move lo u sX) T1)
                    (perm (x-apply-move L (x-plus-move lo u sX) T1)
                          (list* sXBB2 sXB2 sA2 R)))))
    :hints (("Goal" :in-theory (disable x-apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance x-summandp-facts (s s))
                          (:instance x-summandp-facts (s u))
                          (:instance x-bv+-equal-zero (x (x-fac (x-other-lo p) s)) (y (x-fac (x-other-lo p) u)))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-summandp-of-set-fac (v (x-bv+ (x-fac p s) (x-fac p u))))
                          (:instance x-perm-rotate-3-append
                                     (x (x-set-fac p (x-fac p u) s))
                                     (R (remove1-equal s sch))
                                     (a (x-set-fac (x-other-lo p)
                                                 (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (b (x-set-fac (x-other-lo p) (x-fac (x-other-lo p) u)
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))))
                          (:instance x-apply-plus-move-explicit
                                     (p (x-other-lo p)) (piv u)
                                     (tgt (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (S (list* (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                                               (x-set-fac p (x-fac p u) s)
                                               (remove1-equal s sch)))))))))

(encapsulate ()
  (local (in-theory (disable x-summandp-facts-rw x-summandp-of-set-fac)))

  ;; Step 3 (B /= B'): plus on p with pivot X(x)(B+B')(x)C replacing A'(x)B(x)C.
  (defthm x-add-dup-step3
    (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L)))
                  (not (equal (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))))
             (let* ((lo (x-other-lo p))
                    (X (x-bv+ (x-fac p s) (x-fac p u)))
                    (sX (x-set-fac p X s))
                    (sA2 (x-set-fac p (x-fac p u) s))
                    (R (remove1-equal s sch))
                    (sXBB2 (x-set-fac lo (x-bv+ (x-fac lo s) (x-fac lo u)) sX))
                    (sXB2 (x-set-fac lo (x-fac lo u) sX))
                    (T2 (list* sXBB2 sXB2 sA2 R)))
               (and (x-move-ok-p (x-plus-move p sXBB2 sA2) T2)
                    (perm (x-apply-move L (x-plus-move p sXBB2 sA2) T2)
                          (list* s sX sXBB2 sXB2 R)))))
    :hints (("Goal" :in-theory (disable x-apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance x-summandp-facts (s s))
                          (:instance x-summandp-facts (s u))
                          (:instance x-bv+-equal-zero (x (x-fac (x-other-lo p) s)) (y (x-fac (x-other-lo p) u)))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-summandp-of-set-fac (v (x-bv+ (x-fac p s) (x-fac p u))))
                          (:instance x-summandp-of-set-fac (v (x-fac p u)))
                          (:instance x-summandp-of-set-fac (p (x-other-lo p))
                                     (s (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (v (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))))
                          (:instance x-perm-rotate-4-append
                                     (a (x-set-fac (x-other-lo p)
                                                 (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (b (x-set-fac (x-other-lo p) (x-fac (x-other-lo p) u)
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (R (remove1-equal s sch))
                                     (c s)
                                     (d (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                          (:instance x-apply-plus-move-explicit
                                     (piv (x-set-fac (x-other-lo p)
                                                   (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                   (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (tgt (x-set-fac p (x-fac p u) s))
                                     (S (list* (x-set-fac (x-other-lo p)
                                                        (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                        (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                               (x-set-fac (x-other-lo p) (x-fac (x-other-lo p) u)
                                                        (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                               (x-set-fac p (x-fac p u) s)
                                               (remove1-equal s sch))))))))

  ;; Step 4 (B /= B'): flip on p of X(x)(B+B')(x)C and X(x)B'(x)C.
  (defthm x-add-dup-step4
    (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L)))
                  (not (equal (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))))
             (let* ((lo (x-other-lo p))
                    (X (x-bv+ (x-fac p s) (x-fac p u)))
                    (sX (x-set-fac p X s))
                    (R (remove1-equal s sch))
                    (sXBB2 (x-set-fac lo (x-bv+ (x-fac lo s) (x-fac lo u)) sX))
                    (sXB2 (x-set-fac lo (x-fac lo u) sX))
                    (T3 (list* s sX sXBB2 sXB2 R)))
               (and (x-move-ok-p (x-flip-move p sXBB2 sXB2) T3)
                    (perm (x-apply-move L (x-flip-move p sXBB2 sXB2) T3)
                          (list* sX sX sch)))))
    :hints (("Goal" :in-theory (disable x-apply-flip-move-first-zero perm-of-cons-arg1 perm-of-cons-arg2
                                        x-set-fac-of-set-fac-other-commute)
                    :do-not-induct t
                    :use ((:instance x-summandp-facts (s s))
                          (:instance x-summandp-facts (s u))
                          (:instance x-bv+-equal-zero (x (x-fac (x-other-lo p) s)) (y (x-fac (x-other-lo p) u)))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-summandp-of-set-fac (v (x-bv+ (x-fac p s) (x-fac p u))))
                          (:instance x-summandp-of-set-fac (p (x-other-lo p))
                                     (s (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (v (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))))
                          (:instance x-summandp-of-set-fac (p (x-other-lo p))
                                     (s (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (v (x-fac (x-other-lo p) u)))
                          (:instance x-fac-nonzero-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-fac-nonzero-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-fac-nonzero-when-summandp (p p) (s u))
                          (:instance x-fac-nonzero-when-summandp (p p) (s s))
                          (:instance x-bv+-plus-ne-first (x (x-fac (x-other-lo p) s)) (y (x-fac (x-other-lo p) u)))
                          (:instance x-bv+-plus-ne-first (x (x-fac p s)) (y (x-fac p u)))
                          (:instance x-bv+-plus-ne-second (x (x-fac p s)) (y (x-fac p u)))
                          (:instance x-perm-step4-shape
                                     (a s) (b (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (R (remove1-equal s sch)))
                          (:instance x-perm-cons-remove1-when-member (a s) (x sch))
                          (:instance x-apply-flip-move-first-zero
                                     (s (x-set-fac (x-other-lo p)
                                                 (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (u (x-set-fac (x-other-lo p) (x-fac (x-other-lo p) u)
                                                 (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                                     (sch (list* s
                                               (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                                               (x-set-fac (x-other-lo p)
                                                        (x-bv+ (x-fac (x-other-lo p) s) (x-fac (x-other-lo p) u))
                                                        (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                               (x-set-fac (x-other-lo p) (x-fac (x-other-lo p) u)
                                                        (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                               (remove1-equal s sch))))))))

  ;; Step 2' (B = B'): plus on p with pivot X(x)B(x)C replacing A'(x)B(x)C.
  (defthm x-add-dup-step2b
    (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L))))
             (let* ((X (x-bv+ (x-fac p s) (x-fac p u)))
                    (sX (x-set-fac p X s))
                    (sA2 (x-set-fac p (x-fac p u) s))
                    (R (remove1-equal s sch))
                    (T1 (list* sX sA2 R)))
               (and (x-move-ok-p (x-plus-move p sX sA2) T1)
                    (perm (x-apply-move L (x-plus-move p sX sA2) T1)
                          (list* sX sX sch)))))
    :hints (("Goal" :in-theory (disable x-apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance x-summandp-facts (s s))
                          (:instance x-summandp-facts (s u))
                          (:instance x-bv+-equal-zero (x (x-fac (x-other-lo p) s)) (y (x-fac (x-other-lo p) u)))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-len-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s s))
                          (:instance x-bvp-of-fac-when-summandp (p (x-other-lo p)) (s u))
                          (:instance x-summandp-of-set-fac (v (x-bv+ (x-fac p s) (x-fac p u))))
                          (:instance x-summandp-of-set-fac (v (x-fac p u)))
                          (:instance x-perm-rotate-3-append
                                     (x (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (R (remove1-equal s sch))
                                     (a s) (b (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)))
                          (:instance x-perm-cons-remove1-when-member (a s) (x sch))
                          (:instance x-perm-rotate-3 (a s)
                                     (b (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (c (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (R (remove1-equal s sch)))
                          (:instance x-apply-plus-move-explicit
                                     (piv (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s))
                                     (tgt (x-set-fac p (x-fac p u) s))
                                     (S (list* (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                                               (x-set-fac p (x-fac p u) s)
                                               (remove1-equal s sch)))))))))

;;; ------------------------------------------------------------------
;;; Lemma 4.3
;;; ------------------------------------------------------------------

(defthm x-add-dup-lemma
  (implies (and (posp L) (x-summand-listp L sch) (x-posp3 p)
                (member-equal s sch) (member-equal u (remove1-equal s sch))
                (not (equal (x-bv+ (x-fac p s) (x-fac p u)) (x-bv-zero L))))
           (and (x-path-ok-p L (x-add-dup-path p s u) sch)
                (perm (x-apply-path L (x-add-dup-path p s u) sch)
                      (list* (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                             (x-set-fac p (x-bv+ (x-fac p s) (x-fac p u)) s)
                             sch))))
  :hints (("Goal" :in-theory (disable x-summandp-facts-rw x-summandp-of-set-fac
                                      x-plus-move-ok x-flip-move-ok
                                      x-apply-plus-move-explicit x-apply-flip-move-first-zero
                                      x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                      x-perm-rotate-4-append x-perm-step4-shape
                                      x-perm-append-list-1 x-perm-append-list-2
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      x-set-fac-of-set-fac-other-commute
                                      x-perm-cons-remove1-when-member)
                  :do-not-induct t)))

(in-theory (disable x-add-dup-path))
