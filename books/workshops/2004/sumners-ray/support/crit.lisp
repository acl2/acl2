(in-package "ACL2")
(include-book "basis")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;; definitions for example critical section system ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((i *) => *)) (local (defun i (n) n)))

(define-system critical
 (in-critical (n) nil
   (if (in-critical n-)
       (/= (i n) (critical-id n-))
     (= (status (i n) n-) :try)))

 (critical-id (n) nil
   (if (and (not (in-critical n-))
            (= (status (i n) n-) :try))
       (i n)
     (critical-id n-)))

 (status (p n) :idle
   (if (/= (i n) p) (status p n-)
     (case (status p n-)
           (:try (if (in-critical n-) :try :critical))
           (:critical :idle)
           (t :try)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;; definitions for example critical section system ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((a) => *) ((b) => *))
  (local (defun a () 1)) (local (defun b () 2))
  (defthm a-/=-b (not (equal (a) (b))))
  (defthm a-non-nil (not (equal (a) nil)))
  (defthm b-non-nil (not (equal (b) nil))))

; Added after v7-2 by Matt K. since the define-system just below introduces a
; non-recursive definition with a measure.
(set-bogus-measure-ok t)

(define-system critical-spec
 (ok (n) t
   (not (and (= (status (a) n-) :critical)
             (= (status (b) n-) :critical)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; proof of invariant ok via inductive invariant ;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; we have to use a different versions of the above functions which are
; defined on natural time rather than the abstracted t+,t-,tzp time
; defined in basis.lisp.

(mutual-recursion
 (defun in-critical* (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) nil
     (let ((n- (1- n)))
       (if (in-critical* n-)
           (/= (i n) (critical-id* n-))
         (= (status* (i n) n-) :try)))))

 (defun critical-id* (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) nil
     (let ((n- (1- n)))
       (if (and (not (in-critical* n-))
                (= (status* (i n) n-) :try))
           (i n)
         (critical-id* n-)))))

 (defun status* (p n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) :idle
     (let ((n- (1- n)))
       (if (/= (i n) p) (status* p n-)
         (case (status* p n-)
               (:try (if (in-critical* n-) :try :critical))
               (:critical :idle)
               (t :try))))))

 (defun ok* (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) t
     (let ((n- (1- n)))
       (not (and (= (status* (a) n-) :critical)
                 (= (status* (b) n-) :critical)))))))

(defun ii-ok-for1 (n i)
  (iff (= (status* i n) :critical)
       (and (in-critical* n) (= (critical-id* n) i))))

(defun ii-ok (n)
  (and (ii-ok-for1 n (a)) (ii-ok-for1 n (b))))

(defthm bogus-linear
  (implies (integerp n)
           (equal (+ (- x) x n) n)))

(defthm ok-is-invariant
  (and (ii-ok 0) (ok* 0)
       (implies (and (natp n) (ii-ok n))
                (and (ok* (1+ n)) (ii-ok (1+ n)))))
  :hints (("Goal" :in-theory (disable (ii-ok) (ok*)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; a few auxiliary rules for the invariant prover ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; we will need if-lifting for equal rules in the invariant prover:
(if-lift-rules (equal x y))

; we also need to force a case-split on (i n) and (critical-id n)
; the need for a case-split on critical-id is unfortunate and is
; due to some weakness in the prover which needs to be resolved.
(finite-cases process-id :input (i n) ((a) (b)))
(finite-cases critical-id :state (critical-id n) ((a) (b)))

