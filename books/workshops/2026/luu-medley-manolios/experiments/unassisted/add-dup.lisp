; add-dup.lisp -- Lemma 4.3 of the paper (add-duplicate-sum).
;
; Given summands s = A(x)B(x)C and u = A'(x)B'(x)C' of a scheme sch, with
; X = A + A' nonzero, there is a flip/plus path from sch to
;      sch (+) { X(x)B(x)C, X(x)B(x)C }.
; The path is the one of Figure 1 of the paper: plus_A, plus_B, plus_A,
; flip_A when B /= B', and plus_A, plus_A when B = B'.  Everything is
; stated for a generic position p (with lo/hi the two other positions).

(in-package "ACL2")

(include-book "span")

;;; ------------------------------------------------------------------
;;; Record lemmas for fac / set-fac on summands
;;; ------------------------------------------------------------------

(defthm fac-of-set-fac-same
  (implies (posp3 p)
           (equal (fac p (set-fac p v s)) v))
  :hints (("Goal" :in-theory (enable fac set-fac posp3))))

(defthm fac-of-set-fac-other
  (implies (and (posp3 p) (posp3 q) (not (equal p q)))
           (equal (fac q (set-fac p v s)) (fac q s)))
  :hints (("Goal" :in-theory (enable fac set-fac posp3))))

(defthm set-fac-of-set-fac-same
  (implies (posp3 p)
           (equal (set-fac p v (set-fac p w s)) (set-fac p v s)))
  :hints (("Goal" :in-theory (enable set-fac posp3))))

(defthm set-fac-of-fac-same
  (implies (and (posp3 p) (true-listp s) (equal (len s) 3))
           (equal (set-fac p (fac p s) s) s))
  :hints (("Goal" :in-theory (enable fac set-fac posp3))))

(defthm set-fac-of-set-fac-other-commute
  (implies (and (posp3 p) (posp3 q) (not (equal p q)))
           (equal (set-fac q v (set-fac p w s))
                  (set-fac p w (set-fac q v s))))
  :hints (("Goal" :in-theory (enable set-fac posp3))))

(defthm set-fac-of-fac-under-set-fac-other
  (implies (and (posp3 p) (posp3 q) (not (equal p q)) (true-listp s) (equal (len s) 3))
           (equal (set-fac q (fac q s) (set-fac p v s))
                  (set-fac p v s)))
  :hints (("Goal" :in-theory (enable fac set-fac posp3))))

(defthm true-listp-of-set-fac (true-listp (set-fac p v s))
  :hints (("Goal" :in-theory (enable set-fac))))
(defthm len-of-set-fac (equal (len (set-fac p v s)) 3)
  :hints (("Goal" :in-theory (enable set-fac))))

(defthm posp3-of-other-lo (posp3 (other-lo p))
  :hints (("Goal" :in-theory (enable posp3 other-lo))))
(defthm posp3-of-other-hi (posp3 (other-hi p))
  :hints (("Goal" :in-theory (enable posp3 other-hi))))
(defthm other-lo-not-p (implies (posp3 p) (not (equal (other-lo p) p)))
  :hints (("Goal" :in-theory (enable posp3 other-lo))))
(defthm other-hi-not-p (implies (posp3 p) (not (equal (other-hi p) p)))
  :hints (("Goal" :in-theory (enable posp3 other-hi))))
(defthm other-lo-not-other-hi (not (equal (other-lo p) (other-hi p)))
  :hints (("Goal" :in-theory (enable other-lo other-hi))))
(defthm other-lo-not-other-hi-2 (not (equal (other-hi p) (other-lo p)))
  :hints (("Goal" :in-theory (enable other-lo other-hi))))

(defthm summandp-facts
  (implies (summandp L s)
           (and (true-listp s) (equal (len s) 3)
                (bvp (car s)) (bvp (cadr s)) (bvp (caddr s))
                (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))
                (not (equal (car s) (bv-zero L)))
                (not (equal (cadr s) (bv-zero L)))
                (not (equal (caddr s) (bv-zero L)))))
  :rule-classes nil)

(defthm summandp-facts-rw
  (implies (summandp L s)
           (and (true-listp s) (equal (len s) 3)
                (bvp (car s)) (bvp (cadr s)) (bvp (caddr s)))))

(defthm summandp-facts-fc
  (implies (summandp L s)
           (and (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))
                (not (equal (car s) (bv-zero L)))
                (not (equal (cadr s) (bv-zero L)))
                (not (equal (caddr s) (bv-zero L)))))
  :rule-classes :forward-chaining)

(defthm fac-nonzero-when-summandp
  (implies (and (summandp L s) (posp3 p))
           (not (equal (fac p s) (bv-zero L))))
  :hints (("Goal" :in-theory (enable fac posp3))))

(defthm bvp-of-fac-when-summandp
  (implies (summandp L s) (bvp (fac p s)))
  :hints (("Goal" :in-theory (enable fac))))

(defthm len-of-fac-when-summandp
  (implies (summandp L s) (equal (len (fac p s)) (nfix L)))
  :hints (("Goal" :in-theory (enable fac))))

(defthm triplep-of-set-fac-when-summandp
  (implies (and (summandp L s) (bvp v) (equal (len v) (nfix L)))
           (triplep L (set-fac p v s)))
  :hints (("Goal" :in-theory (enable set-fac))))

(defthm zero-summandp-of-set-fac
  (implies (and (summandp L s) (posp3 p))
           (equal (zero-summandp L (set-fac p v s))
                  (equal v (bv-zero L))))
  :hints (("Goal" :in-theory (enable set-fac posp3))))

(defthm summandp-of-set-fac
  (implies (and (posp L) (summandp L s) (posp3 p) (bvp v) (equal (len v) L))
           (equal (summandp L (set-fac p v s))
                  (not (equal v (bv-zero L)))))
  :hints (("Goal" :in-theory (e/d (summandp) (zero-summandp triplep set-fac)))))

(in-theory (disable summandp))

;; Two summands that differ in some factor are different.
(defthm not-equal-set-fac-when-fac-differs-1
  (implies (and (posp3 p) (not (equal (fac p u) v)))
           (not (equal u (set-fac p v s)))))

(defthm not-equal-set-fac-when-fac-differs-2
  (implies (and (posp3 p) (not (equal (fac p u) v)))
           (not (equal (set-fac p v s) u))))

(defthm not-equal-set-fac-set-fac-when-fac-differs
  (implies (and (posp3 p) (not (equal v w)))
           (not (equal (set-fac p v s) (set-fac p w s2)))))

(defthm not-equal-set-fac-other-when-fac-differs
  (implies (and (posp3 p) (posp3 q) (not (equal p q)) (not (equal (fac p s) v)))
           (not (equal (set-fac p v s) (set-fac q w s)))))

;;; ------------------------------------------------------------------
;;; Explicit forms of the moves
;;; ------------------------------------------------------------------

(defthm apply-plus-move-explicit
  (implies (and (posp L) (posp3 p) (summandp L tgt) (summandp L piv)
                (not (equal (bv+ (fac p tgt) (fac p piv)) (bv-zero L))))
           (equal (apply-move L (plus-move p piv tgt) S)
                  (append (remove1-equal tgt S)
                          (list (set-fac p (bv+ (fac p tgt) (fac p piv)) tgt)
                                (set-fac p (fac p piv) tgt)))))
  :hints (("Goal" :in-theory (enable apply-move plus-results plus-move))))

(defthm apply-flip-move-first-zero
  (implies (and (posp L) (posp3 p) (summandp L s) (summandp L u)
                (equal (bv+ (fac (other-hi p) s) (fac (other-hi p) u)) (bv-zero L))
                (not (equal (bv+ (fac (other-lo p) u) (fac (other-lo p) s)) (bv-zero L))))
           (equal (apply-move L (flip-move p s u) sch)
                  (append (remove1-equal u (remove1-equal s sch))
                          (list (set-fac (other-lo p)
                                         (bv+ (fac (other-lo p) u) (fac (other-lo p) s))
                                         u)))))
  :hints (("Goal" :in-theory (enable apply-move flip-results flip-move))))

(defthm plus-move-ok
  (implies (and (posp3 p) (true-listp piv) (true-listp tgt)
                (member-equal piv S) (member-equal tgt (remove1-equal piv S)))
           (move-ok-p (plus-move p piv tgt) S))
  :hints (("Goal" :in-theory (enable move-ok-p plus-move))))

(defthm flip-move-ok
  (implies (and (posp3 p) (true-listp s) (true-listp u)
                (member-equal s sch) (member-equal u (remove1-equal s sch))
                (equal (fac p s) (fac p u)))
           (move-ok-p (flip-move p s u) sch))
  :hints (("Goal" :in-theory (enable move-ok-p flip-move))))

(in-theory (disable plus-move flip-move delete-pair-move))

;;; ------------------------------------------------------------------
;;; List helpers
;;; ------------------------------------------------------------------

(defthm member-remove1-when-different
  (implies (and (member-equal u S) (not (equal u s1)))
           (member-equal u (remove1-equal s1 S)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm remove1-of-append-when-member-first
  (implies (member-equal a x)
           (equal (remove1-equal a (append x y))
                  (append (remove1-equal a x) y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm perm-append-list-1
  (perm (append x (list a)) (cons a x))
  :hints (("Goal" :use ((:instance perm-of-append (x x) (y (list a)))))))

(defthm perm-append-list-2
  (perm (append x (list a b)) (list* a b x))
  :hints (("Goal" :use ((:instance perm-of-append (x x) (y (list a b)))))))

(defthm perm-rotate-4
  (perm (list* a b c d R) (list* c d a b R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append)))))

(defthm perm-rotate-4-append
  (perm (list* a b (append R (list c d))) (list* c d a b R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append perm-rotate-4 perm-append-list-2))
                  :use ((:instance perm-append-list-2 (x R) (a c) (b d))
                        (:instance perm-rotate-4)))))

(defthm perm-rotate-3
  (perm (list* a b c R) (list* b c a R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append)))))

(defthm perm-rotate-3-append
  (perm (cons x (append R (list a b))) (list* a b x R))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append perm-rotate-4 perm-append-list-2))
                  :use ((:instance perm-append-list-2 (x R) (a a) (b b))))))

(defthm perm-step4-shape
  (perm (list* a b (append R (list b))) (list* b b (cons a R)))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal)
                                  (perm-of-append perm-rotate-4 perm-append-list-2 perm-append-list-1))
                  :use ((:instance perm-append-list-1 (x R) (a b))))))

(defcong perm perm (cons a x) 2
  :hints (("Goal" :in-theory (enable perm remove1-equal))))

(defthm perm-cons-remove1-when-member
  (implies (and (member-equal a x) (true-listp x))
           (perm (cons a (remove1-equal a x)) x))
  :hints (("Goal" :in-theory (enable perm remove1-equal))))

(defthm remove1-of-cons-different
  (implies (not (equal a b))
           (equal (remove1-equal a (cons b x)) (cons b (remove1-equal a x))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm remove1-of-cons-same
  (equal (remove1-equal a (cons a x)) x)
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm true-listp-of-remove1
  (implies (true-listp x) (true-listp (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm summand-listp-member-fc
  (implies (and (member-equal s x) (summand-listp L x))
           (summandp L s))
  :rule-classes :forward-chaining)

(defthm member-remove1-swap
  (implies (and (member-equal s x) (member-equal u (remove1-equal s x)))
           (member-equal s (remove1-equal u x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;;; ------------------------------------------------------------------
;;; The path of Lemma 4.3
;;; ------------------------------------------------------------------

;; s = (A at p, B at lo, C at hi), u = (A', B', C').
(defun add-dup-path (p s u)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((lo (other-lo p))
         (X (bv+ (fac p s) (fac p u)))
         (sX (set-fac p X s))
         (sA2 (set-fac p (fac p u) s))
         (B (fac lo s))
         (B2 (fac lo u))
         (sXBB2 (set-fac lo (bv+ B B2) sX))
         (sXB2 (set-fac lo B2 sX)))
    (if (equal B B2)
        (list (plus-move p u s)
              (plus-move p sX sA2))
      (list (plus-move p u s)
            (plus-move lo u sX)
            (plus-move p sXBB2 sA2)
            (flip-move p sXBB2 sXB2)))))

;; Algebraic facts used along the path (over F_2).
(defthm bv+-x-with-x-plus-y
  (implies (and (bvp x) (bvp y) (equal (len x) (len y)))
           (equal (bv+ y (bv+ x y)) x))
  :hints (("Goal" :use ((:instance bv+-self-in-middle (x y) (y x))))))

(defthm bv+-y-with-x-plus-y
  (implies (and (bvp x) (bvp y) (equal (len x) (len y)))
           (equal (bv+ x (bv+ x y)) y)))

(defthm bv+-plus-ne-first
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (not (equal y (bv-zero (len x)))))
           (not (equal (bv+ x y) x)))
  :hints (("Goal" :use ((:instance bv+-cancel-left (x x) (y y) (z (bv-zero (len x))))))))

(defthm bv+-plus-ne-second
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (not (equal x (bv-zero (len x)))))
           (not (equal (bv+ x y) y)))
  :hints (("Goal" :use ((:instance bv+-cancel-left (x y) (y x) (z (bv-zero (len x))))))))

(defthm bv+-plus-ne-first-alt
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (not (equal y (bv-zero (len x)))))
           (not (equal x (bv+ x y))))
  :hints (("Goal" :use bv+-plus-ne-first)))

(defthm bv+-plus-ne-second-alt
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (not (equal x (bv-zero (len x)))))
           (not (equal y (bv+ x y))))
  :hints (("Goal" :use bv+-plus-ne-second)))

(encapsulate ()
  (local (in-theory (disable summandp-facts-rw)))

  ;; Step 1 (both cases): plus on p with pivot u replacing s.
  (defthm add-dup-step1
    (implies (and (posp L) (summand-listp L sch) (posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L))))
             (and (move-ok-p (plus-move p u s) sch)
                  (perm (apply-move L (plus-move p u s) sch)
                        (list* (set-fac p (bv+ (fac p s) (fac p u)) s)
                               (set-fac p (fac p u) s)
                               (remove1-equal s sch)))))
    :hints (("Goal" :in-theory (disable summandp-of-set-fac)
                    :do-not-induct t
                    :use ((:instance summandp-facts (s s))
                          (:instance summandp-facts (s u)))))))

(encapsulate ()
  (local (in-theory (disable summandp-facts-rw summandp-of-set-fac)))

  ;; Step 2 (B /= B'): plus on lo with pivot u replacing sX.
  (defthm add-dup-step2
    (implies (and (posp L) (summand-listp L sch) (posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L)))
                  (not (equal (fac (other-lo p) s) (fac (other-lo p) u))))
             (let* ((lo (other-lo p))
                    (X (bv+ (fac p s) (fac p u)))
                    (sX (set-fac p X s))
                    (sA2 (set-fac p (fac p u) s))
                    (R (remove1-equal s sch))
                    (T1 (list* sX sA2 R))
                    (sXBB2 (set-fac lo (bv+ (fac lo s) (fac lo u)) sX))
                    (sXB2 (set-fac lo (fac lo u) sX)))
               (and (move-ok-p (plus-move lo u sX) T1)
                    (perm (apply-move L (plus-move lo u sX) T1)
                          (list* sXBB2 sXB2 sA2 R)))))
    :hints (("Goal" :in-theory (disable apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance summandp-facts (s s))
                          (:instance summandp-facts (s u))
                          (:instance bv+-equal-zero (x (fac (other-lo p) s)) (y (fac (other-lo p) u)))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance summandp-of-set-fac (v (bv+ (fac p s) (fac p u))))
                          (:instance perm-rotate-3-append
                                     (x (set-fac p (fac p u) s))
                                     (R (remove1-equal s sch))
                                     (a (set-fac (other-lo p)
                                                 (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (b (set-fac (other-lo p) (fac (other-lo p) u)
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s))))
                          (:instance apply-plus-move-explicit
                                     (p (other-lo p)) (piv u)
                                     (tgt (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (S (list* (set-fac p (bv+ (fac p s) (fac p u)) s)
                                               (set-fac p (fac p u) s)
                                               (remove1-equal s sch)))))))))

(encapsulate ()
  (local (in-theory (disable summandp-facts-rw summandp-of-set-fac)))

  ;; Step 3 (B /= B'): plus on p with pivot X(x)(B+B')(x)C replacing A'(x)B(x)C.
  (defthm add-dup-step3
    (implies (and (posp L) (summand-listp L sch) (posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L)))
                  (not (equal (fac (other-lo p) s) (fac (other-lo p) u))))
             (let* ((lo (other-lo p))
                    (X (bv+ (fac p s) (fac p u)))
                    (sX (set-fac p X s))
                    (sA2 (set-fac p (fac p u) s))
                    (R (remove1-equal s sch))
                    (sXBB2 (set-fac lo (bv+ (fac lo s) (fac lo u)) sX))
                    (sXB2 (set-fac lo (fac lo u) sX))
                    (T2 (list* sXBB2 sXB2 sA2 R)))
               (and (move-ok-p (plus-move p sXBB2 sA2) T2)
                    (perm (apply-move L (plus-move p sXBB2 sA2) T2)
                          (list* s sX sXBB2 sXB2 R)))))
    :hints (("Goal" :in-theory (disable apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance summandp-facts (s s))
                          (:instance summandp-facts (s u))
                          (:instance bv+-equal-zero (x (fac (other-lo p) s)) (y (fac (other-lo p) u)))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance summandp-of-set-fac (v (bv+ (fac p s) (fac p u))))
                          (:instance summandp-of-set-fac (v (fac p u)))
                          (:instance summandp-of-set-fac (p (other-lo p))
                                     (s (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (v (bv+ (fac (other-lo p) s) (fac (other-lo p) u))))
                          (:instance perm-rotate-4-append
                                     (a (set-fac (other-lo p)
                                                 (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (b (set-fac (other-lo p) (fac (other-lo p) u)
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (R (remove1-equal s sch))
                                     (c s)
                                     (d (set-fac p (bv+ (fac p s) (fac p u)) s)))
                          (:instance apply-plus-move-explicit
                                     (piv (set-fac (other-lo p)
                                                   (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                   (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (tgt (set-fac p (fac p u) s))
                                     (S (list* (set-fac (other-lo p)
                                                        (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                        (set-fac p (bv+ (fac p s) (fac p u)) s))
                                               (set-fac (other-lo p) (fac (other-lo p) u)
                                                        (set-fac p (bv+ (fac p s) (fac p u)) s))
                                               (set-fac p (fac p u) s)
                                               (remove1-equal s sch))))))))

  ;; Step 4 (B /= B'): flip on p of X(x)(B+B')(x)C and X(x)B'(x)C.
  (defthm add-dup-step4
    (implies (and (posp L) (summand-listp L sch) (posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L)))
                  (not (equal (fac (other-lo p) s) (fac (other-lo p) u))))
             (let* ((lo (other-lo p))
                    (X (bv+ (fac p s) (fac p u)))
                    (sX (set-fac p X s))
                    (R (remove1-equal s sch))
                    (sXBB2 (set-fac lo (bv+ (fac lo s) (fac lo u)) sX))
                    (sXB2 (set-fac lo (fac lo u) sX))
                    (T3 (list* s sX sXBB2 sXB2 R)))
               (and (move-ok-p (flip-move p sXBB2 sXB2) T3)
                    (perm (apply-move L (flip-move p sXBB2 sXB2) T3)
                          (list* sX sX sch)))))
    :hints (("Goal" :in-theory (disable apply-flip-move-first-zero perm-of-cons-arg1 perm-of-cons-arg2
                                        set-fac-of-set-fac-other-commute)
                    :do-not-induct t
                    :use ((:instance summandp-facts (s s))
                          (:instance summandp-facts (s u))
                          (:instance bv+-equal-zero (x (fac (other-lo p) s)) (y (fac (other-lo p) u)))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance summandp-of-set-fac (v (bv+ (fac p s) (fac p u))))
                          (:instance summandp-of-set-fac (p (other-lo p))
                                     (s (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (v (bv+ (fac (other-lo p) s) (fac (other-lo p) u))))
                          (:instance summandp-of-set-fac (p (other-lo p))
                                     (s (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (v (fac (other-lo p) u)))
                          (:instance fac-nonzero-when-summandp (p (other-lo p)) (s u))
                          (:instance fac-nonzero-when-summandp (p (other-lo p)) (s s))
                          (:instance fac-nonzero-when-summandp (p p) (s u))
                          (:instance fac-nonzero-when-summandp (p p) (s s))
                          (:instance bv+-plus-ne-first (x (fac (other-lo p) s)) (y (fac (other-lo p) u)))
                          (:instance bv+-plus-ne-first (x (fac p s)) (y (fac p u)))
                          (:instance bv+-plus-ne-second (x (fac p s)) (y (fac p u)))
                          (:instance perm-step4-shape
                                     (a s) (b (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (R (remove1-equal s sch)))
                          (:instance perm-cons-remove1-when-member (a s) (x sch))
                          (:instance apply-flip-move-first-zero
                                     (s (set-fac (other-lo p)
                                                 (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (u (set-fac (other-lo p) (fac (other-lo p) u)
                                                 (set-fac p (bv+ (fac p s) (fac p u)) s)))
                                     (sch (list* s
                                               (set-fac p (bv+ (fac p s) (fac p u)) s)
                                               (set-fac (other-lo p)
                                                        (bv+ (fac (other-lo p) s) (fac (other-lo p) u))
                                                        (set-fac p (bv+ (fac p s) (fac p u)) s))
                                               (set-fac (other-lo p) (fac (other-lo p) u)
                                                        (set-fac p (bv+ (fac p s) (fac p u)) s))
                                               (remove1-equal s sch))))))))

  ;; Step 2' (B = B'): plus on p with pivot X(x)B(x)C replacing A'(x)B(x)C.
  (defthm add-dup-step2b
    (implies (and (posp L) (summand-listp L sch) (posp3 p)
                  (member-equal s sch) (member-equal u (remove1-equal s sch))
                  (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L))))
             (let* ((X (bv+ (fac p s) (fac p u)))
                    (sX (set-fac p X s))
                    (sA2 (set-fac p (fac p u) s))
                    (R (remove1-equal s sch))
                    (T1 (list* sX sA2 R)))
               (and (move-ok-p (plus-move p sX sA2) T1)
                    (perm (apply-move L (plus-move p sX sA2) T1)
                          (list* sX sX sch)))))
    :hints (("Goal" :in-theory (disable apply-plus-move-explicit perm-of-cons-arg1 perm-of-cons-arg2)
                    :do-not-induct t
                    :use ((:instance summandp-facts (s s))
                          (:instance summandp-facts (s u))
                          (:instance bv+-equal-zero (x (fac (other-lo p) s)) (y (fac (other-lo p) u)))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance len-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s s))
                          (:instance bvp-of-fac-when-summandp (p (other-lo p)) (s u))
                          (:instance summandp-of-set-fac (v (bv+ (fac p s) (fac p u))))
                          (:instance summandp-of-set-fac (v (fac p u)))
                          (:instance perm-rotate-3-append
                                     (x (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (R (remove1-equal s sch))
                                     (a s) (b (set-fac p (bv+ (fac p s) (fac p u)) s)))
                          (:instance perm-cons-remove1-when-member (a s) (x sch))
                          (:instance perm-rotate-3 (a s)
                                     (b (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (c (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (R (remove1-equal s sch)))
                          (:instance apply-plus-move-explicit
                                     (piv (set-fac p (bv+ (fac p s) (fac p u)) s))
                                     (tgt (set-fac p (fac p u) s))
                                     (S (list* (set-fac p (bv+ (fac p s) (fac p u)) s)
                                               (set-fac p (fac p u) s)
                                               (remove1-equal s sch)))))))))

;;; ------------------------------------------------------------------
;;; Lemma 4.3
;;; ------------------------------------------------------------------

(defthm add-dup-lemma
  (implies (and (posp L) (summand-listp L sch) (posp3 p)
                (member-equal s sch) (member-equal u (remove1-equal s sch))
                (not (equal (bv+ (fac p s) (fac p u)) (bv-zero L))))
           (and (path-ok-p L (add-dup-path p s u) sch)
                (perm (apply-path L (add-dup-path p s u) sch)
                      (list* (set-fac p (bv+ (fac p s) (fac p u)) s)
                             (set-fac p (bv+ (fac p s) (fac p u)) s)
                             sch))))
  :hints (("Goal" :in-theory (disable summandp-facts-rw summandp-of-set-fac
                                      plus-move-ok flip-move-ok
                                      apply-plus-move-explicit apply-flip-move-first-zero
                                      perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                      perm-rotate-4-append perm-step4-shape
                                      perm-append-list-1 perm-append-list-2
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      set-fac-of-set-fac-other-commute
                                      perm-cons-remove1-when-member)
                  :do-not-induct t)))

(in-theory (disable add-dup-path))
