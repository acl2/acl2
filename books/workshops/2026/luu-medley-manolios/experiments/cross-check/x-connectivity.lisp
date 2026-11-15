; x-connectivity.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/connectivity.lisp
; produced by rename.py in this directory; do not edit by hand.
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

(include-book "x-zero-subset")

;;; ------------------------------------------------------------------
;;; Adding two copies of every summand of S2
;;; ------------------------------------------------------------------

(defun x-add-all-path (n S S2)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S2)
      nil
    (let ((u (car S2)))
      (append (x-add-arb-path n S (x-fac 0 u) (x-fac 1 u) (x-fac 2 u))
              (x-add-all-path n (list* u u S) (cdr S2))))))

(defun x-dup2 (X)
  (declare (xargs :guard t))
  (if (atom X) nil (list* (car X) (car X) (x-dup2 (cdr X)))))

(defthm x-perm-append-cons
  (perm (append x (cons a y)) (cons a (append x y)))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append))
                  :induct (len x))))

(defthm x-perm-dup2
  (implies (true-listp X)
           (perm (x-dup2 X) (append X X)))
  :hints (("Goal" :in-theory (disable perm-of-append x-perm-append-cons perm-of-cons-arg1
                                      perm-of-cons-arg2)
                  :induct (x-dup2 X))
          ("Subgoal *1/2" :use ((:instance x-perm-append-cons (x (cdr X)) (a (car X)) (y (cdr X)))))))

(defthm x-summand-listp-of-list*-pair-2
  (equal (x-summand-listp L (list* a a S))
         (and (x-summandp L a) (x-summand-listp L S))))

(defthm x-add-all-path-correct
  (implies (and (x-schemep n S) (<= 2 n) (x-summand-listp (x-sq n) S2))
           (and (x-path-ok-p (x-sq n) (x-add-all-path n S S2) S)
                (perm (x-apply-path (x-sq n) (x-add-all-path n S S2) S)
                      (append S (x-dup2 S2)))))
  :hints (("Goal" :induct (x-add-all-path n S S2)
                  :in-theory (disable perm-of-append x-perm-append-cons perm-of-cons-arg1
                                      perm-of-cons-arg2 x-perm-append-list-1 x-perm-append-list-2
                                      x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                      x-perm-rotate-4-append x-perm-step4-shape
                                      x-perm-split-shape x-perm-split-shape-2
                                      x-perm-cons-remove1-when-member))
          ("Subgoal *1/2" :use ((:instance x-perm-append-cons (x S) (a (car S2))
                                           (y (cons (car S2) (x-dup2 (cdr S2)))))
                                (:instance x-perm-append-cons (x S) (a (car S2)) (y (x-dup2 (cdr S2))))
                                (:instance x-schemep-of-list*-pair (a (car S2)))
                                (:instance x-list-of-facs (s (car S2)))
                                (:instance x-summandp-facts (L (x-sq n)) (s (car S2)))))))

;;; ------------------------------------------------------------------
;;; Theorem 4.1 (flip-plus connectivity over F_2)
;;; ------------------------------------------------------------------

(defun x-connect-path (n S S2)
  (declare (xargs :guard t :verify-guards nil))
  (append (x-add-all-path n S S2)
          (x-zero-subset-path n (append S S2) S2)))

(defthm x-triple-sum-of-append-of-schemes
  (implies (and (x-schemep n S) (x-schemep n S2))
           (equal (x-triple-sum (x-sq n) (append S S2)) (x-bv-zero (x-tlen (x-sq n)))))
  :hints (("Goal" :in-theory (disable x-triple-sum-of-append)
                  :use ((:instance x-triple-sum-of-append (L (x-sq n)) (x S) (y S2))))))

(defthm x-perm-S-dup2-as-append
  (implies (and (true-listp S) (true-listp S2))
           (perm (append S (x-dup2 S2)) (append (append S S2) S2)))
  :hints (("Goal" :in-theory (disable perm-of-append x-perm-dup2)
                  :use (x-perm-dup2
                        (:instance perm-implies-perm-append-2 (x S) (y (x-dup2 S2))
                                   (y-equiv (append S2 S2)))))))

(defthm x-schemep-of-triple-append
  (implies (and (x-schemep n S) (x-schemep n S2))
           (x-schemep n (append (append S S2) S2)))
  :hints (("Goal" :in-theory (disable x-triple-sum-of-append)
                  :use ((:instance x-triple-sum-of-append (L (x-sq n)) (x (append S S2)) (y S2))
                        (:instance x-triple-sum-of-append (L (x-sq n)) (x S) (y S2))))))

(defthm x-flip-graph-strongly-connected
  (implies (and (<= 2 n) (x-schemep n S) (x-schemep n S2))
           (and (x-path-ok-p (x-sq n) (x-connect-path n S S2) S)
                (perm (x-apply-path (x-sq n) (x-connect-path n S S2) S) S2)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-append perm-of-cons-arg1 perm-of-cons-arg2
                                      perm-of-append-of-cons perm-of-append-of-cdr-and-cons-of-car
                                      x-add-all-path-correct x-zero-subset-lemma
                                      x-perm-S-dup2-as-append)
                  :use (x-add-all-path-correct
                        (:instance x-zero-subset-lemma (R (append S S2)) (rest S2))
                        (:instance x-perm-S-dup2-as-append)))))
