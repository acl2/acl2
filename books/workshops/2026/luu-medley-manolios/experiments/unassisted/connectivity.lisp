; connectivity.lisp -- Theorem 4.1 of the paper:
;   Over F_2, for every n >= 2, the directed matrix multiplication flip
;   graph whose edges are flip and plus transformations is strongly
;   connected.
;
; Proof (as in the paper): given schemes S and S', use Lemma 4.4 to add
; two copies of every summand of S', reaching S (+) S' (+) S'.  The
; sub-multiset S (+) S' sums to M + M = 0, so Lemma 4.5 removes it,
; leaving S'.

(in-package "ACL2")

(include-book "zero-subset")

;;; ------------------------------------------------------------------
;;; Adding two copies of every summand of S2
;;; ------------------------------------------------------------------

(defun add-all-path (n S S2)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S2)
      nil
    (let ((u (car S2)))
      (append (add-arb-path n S (fac 0 u) (fac 1 u) (fac 2 u))
              (add-all-path n (list* u u S) (cdr S2))))))

(defun dup2 (X)
  (declare (xargs :guard t))
  (if (atom X) nil (list* (car X) (car X) (dup2 (cdr X)))))

(defthm perm-append-cons
  (perm (append x (cons a y)) (cons a (append x y)))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append))
                  :induct (len x))))

(defthm perm-dup2
  (implies (true-listp X)
           (perm (dup2 X) (append X X)))
  :hints (("Goal" :in-theory (disable perm-of-append perm-append-cons perm-of-cons-arg1
                                      perm-of-cons-arg2)
                  :induct (dup2 X))
          ("Subgoal *1/2" :use ((:instance perm-append-cons (x (cdr X)) (a (car X)) (y (cdr X)))))))

(defthm summand-listp-of-list*-pair-2
  (equal (summand-listp L (list* a a S))
         (and (summandp L a) (summand-listp L S))))

(defthm add-all-path-correct
  (implies (and (schemep n S) (<= 2 n) (summand-listp (sq n) S2))
           (and (path-ok-p (sq n) (add-all-path n S S2) S)
                (perm (apply-path (sq n) (add-all-path n S S2) S)
                      (append S (dup2 S2)))))
  :hints (("Goal" :induct (add-all-path n S S2)
                  :in-theory (disable perm-of-append perm-append-cons perm-of-cons-arg1
                                      perm-of-cons-arg2 perm-append-list-1 perm-append-list-2
                                      perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                      perm-rotate-4-append perm-step4-shape
                                      perm-split-shape perm-split-shape-2
                                      perm-cons-remove1-when-member))
          ("Subgoal *1/2" :use ((:instance perm-append-cons (x S) (a (car S2))
                                           (y (cons (car S2) (dup2 (cdr S2)))))
                                (:instance perm-append-cons (x S) (a (car S2)) (y (dup2 (cdr S2))))
                                (:instance schemep-of-list*-pair (a (car S2)))
                                (:instance list-of-facs (s (car S2)))
                                (:instance summandp-facts (L (sq n)) (s (car S2)))))))

;;; ------------------------------------------------------------------
;;; Theorem 4.1 (flip-plus connectivity over F_2)
;;; ------------------------------------------------------------------

(defun connect-path (n S S2)
  (declare (xargs :guard t :verify-guards nil))
  (append (add-all-path n S S2)
          (zero-subset-path n (append S S2) S2)))

(defthm triple-sum-of-append-of-schemes
  (implies (and (schemep n S) (schemep n S2))
           (equal (triple-sum (sq n) (append S S2)) (bv-zero (tlen (sq n)))))
  :hints (("Goal" :in-theory (disable triple-sum-of-append)
                  :use ((:instance triple-sum-of-append (L (sq n)) (x S) (y S2))))))

(defthm perm-S-dup2-as-append
  (implies (and (true-listp S) (true-listp S2))
           (perm (append S (dup2 S2)) (append (append S S2) S2)))
  :hints (("Goal" :in-theory (disable perm-of-append perm-dup2)
                  :use (perm-dup2
                        (:instance perm-implies-perm-append-2 (x S) (y (dup2 S2))
                                   (y-equiv (append S2 S2)))))))

(defthm schemep-of-triple-append
  (implies (and (schemep n S) (schemep n S2))
           (schemep n (append (append S S2) S2)))
  :hints (("Goal" :in-theory (disable triple-sum-of-append)
                  :use ((:instance triple-sum-of-append (L (sq n)) (x (append S S2)) (y S2))
                        (:instance triple-sum-of-append (L (sq n)) (x S) (y S2))))))

(defthm flip-graph-strongly-connected
  (implies (and (<= 2 n) (schemep n S) (schemep n S2))
           (and (path-ok-p (sq n) (connect-path n S S2) S)
                (perm (apply-path (sq n) (connect-path n S S2) S) S2)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-append perm-of-cons-arg1 perm-of-cons-arg2
                                      perm-of-append-of-cons perm-of-append-of-cdr-and-cons-of-car
                                      add-all-path-correct zero-subset-lemma
                                      perm-S-dup2-as-append)
                  :use (add-all-path-correct
                        (:instance zero-subset-lemma (R (append S S2)) (rest S2))
                        (:instance perm-S-dup2-as-append)))))
