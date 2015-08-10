(in-package "ACL2")


#|

  assertions.lisp
  ~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Tue Dec 21 05:27:21 2004

In this book, we provide the missing piece of symbolic simulation necessary to
do the partial (and total) correctness proof using symbolic simulation. In
particular, we provide two theorems, which are |nextt cutpoint for cutpoint|
and |nextt cutpoint for not cutpoint|. These two theorems allow us to do
efficient symbolic simulation based on reasoning about cutpoints.

|#

(include-book "ordinals/ordinals" :dir :system)
(include-book "misc/defpun" :dir :system)

;; Again I do have the functions nextt and run.

(defstub nextt (*) => *)
(defun run (s n) (if (zp n) s (run (nextt s) (1- n))))

;; I now encapsulate two functions default-state and cutpoint with the property
;; that the default state is not a cutpoint. This is all that I should need.

(encapsulate
 (((default-state) => *)
  ((cutpoint *) => *))

 (local (defun default-state () nil))
 (local (defun cutpoint (s) (equal s t)))

 (defthm |default is not a cutpoint|
   (not (cutpoint (default-state))))

)

;; I do the same definition of steps-to-cutpoint here. In other words it is the
;; same defpun as before.

(defpun steps-to-cutpoint-tail (s i)
  (if (cutpoint s)
      i
    (steps-to-cutpoint-tail (nextt s) (1+ i))))

;; (local (in-theory (disable natp)))

(defun steps-to-cutpoint (s)
  (let ((steps (steps-to-cutpoint-tail s 0)))
    (if (cutpoint (run s steps))
        steps
      (omega))))

(defun nextt-cutpoint (s)
   (let ((steps (steps-to-cutpoint s)))
     (if (natp steps)
         (run s steps)
       (default-state))))

(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (nextt s)))))

;;(local
 ;; (include-book "arithmetic/top-with-meta" :dir :system))

;; Also I copy and paste the same theorems as I had in the total and partial
;; correctness books. We should be able to just instantiate the theorems that I
;; had proved earlier to get this. This might be possible if we use either
;;  Rob's second order functions [1], or
;; Francisco's generic instantiation tool [2].
;;
;; [1] R. Sumners: Second Order Functions in ACL2.
;;     http://www.cs.utexas.edu/users/kaufmann/misc/sorta.lisp
;;
;; [2] F. J. Martin-Mateos, J. A. Alonso, M. J. Hidalgo, and
;;     J. L. Ruiz-Reina. A Generic Instantiation Tool and a Case Study: A Generic
;;     Multiset theory. In D. Borrione, M. Kaufmann, and J S. Moore, editors, Third
;;     International Workshop on the ACL2 Theorem Prover and Its Applications,
;;     Grenoble, France, April 2002.


 (local
  (defthmd steps-to-cutpoint-tail-inv
    (implies (and (cutpoint (run s k))
                  (natp steps))
             (let* ((result  (steps-to-cutpoint-tail s steps))
                    (cutpoint-steps (- result steps)))
               (and (natp result)
                    (natp cutpoint-steps)
                    (implies (natp k)
                             (<= cutpoint-steps k))
                    (cutpoint (run s cutpoint-steps)))))
    :hints (("Goal"
             :in-theory (enable natp)
             :induct (cutpoint-induction k steps s)))))

(local
 (defthm cutpoint-minimal
   (implies (and (natp k)
                 (cutpoint (run s k)))
            (<= (steps-to-cutpoint s)
                k))
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0)))))))

(local
 (defthm natp-implies-cutpoint
   (implies (natp (steps-to-cutpoint s))
            (cutpoint (run s (steps-to-cutpoint s))))
   :rule-classes :forward-chaining))

(local
 (defthm cutpoint-implies-steps-to-cutpoint-natp
   (implies (cutpoint (run s k))
            (natp (steps-to-cutpoint s)))
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0)))))))

(local (in-theory (disable steps-to-cutpoint)))

;; OK, now let us first prove that there is a relation between
;; steps-to-cutpoint of s and steps-to-cutpoint of (nextt s). To do this first
;; let us prove that if one is a natp then so is the other.

(local
 (defthm natp-steps-implies-natp-nextt
   (implies (and (natp (steps-to-cutpoint s))
                 (not (cutpoint s)))
            (natp (steps-to-cutpoint (nextt s))))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (disable cutpoint-implies-steps-to-cutpoint-natp)
            :use ((:instance natp-implies-cutpoint)
                  (:instance cutpoint-implies-steps-to-cutpoint-natp
                             (s (nextt s))
                             (k (1- (steps-to-cutpoint s)))))))))


;; Then of course we know that stepping from s is just 1 more than stepping
;; from (nextt s).

(local
 (defthm steps-to-cutpoint-nextt-is-1+
   (implies (and (not (cutpoint s))
                 (cutpoint (run s k)))
            (equal (steps-to-cutpoint s)
                   (1+ (steps-to-cutpoint (nextt s)))))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :cases ((< (steps-to-cutpoint s)
                       (1+ (steps-to-cutpoint (nextt s))))
                    (< (1+ (steps-to-cutpoint (nextt s)))
                       (steps-to-cutpoint s))
                    (= (1+ (steps-to-cutpoint (nextt s)))
                       (steps-to-cutpoint s))))
           ("Subgoal 2"
            :in-theory (disable cutpoint-minimal)
            :use ((:instance cutpoint-minimal
                             (s (nextt s))
                             (k (1- (steps-to-cutpoint s))))
                  (:instance natp-implies-cutpoint)))
           ("Subgoal 1"
            :in-theory (disable natp cutpoint-implies-steps-to-cutpoint-natp
                                cutpoint-minimal)
            :use ((:instance cutpoint-minimal
                             (k (1+ (steps-to-cutpoint (nextt s)))))
                  (:instance cutpoint-implies-steps-to-cutpoint-natp
                             (k (1- k))
                             (s (nextt s)))))
           ("[1]Goal"
            :in-theory (disable cutpoint-implies-steps-to-cutpoint-natp)
            :use ((:instance cutpoint-implies-steps-to-cutpoint-natp)
                  (:instance cutpoint-implies-steps-to-cutpoint-natp
                             (s (nextt s))
                             (k (1- k))))))))

;; I provide a version of this now which does not have a free variable.

(local
 (defthmd steps-=-1+-for-natp
   (implies (and (natp (steps-to-cutpoint s))
                 (not (cutpoint s)))
            (equal (steps-to-cutpoint s)
                   (1+ (steps-to-cutpoint (nextt s)))))
   :hints (("Goal"
            :in-theory (disable natp)
            :use ((:instance steps-to-cutpoint-nextt-is-1+
                             (k (steps-to-cutpoint s))))))))

;; For some reason the arithmetic books are coming in the way of proving the
;; theorem that I want. I need to investigate that later. For now I just prove
;; the inverse of the above theorem.

(local
 (defthm steps-=-1-for-natp
   (implies (and (natp (steps-to-cutpoint s))
                 (not (cutpoint s)))
            (equal (steps-to-cutpoint (nextt s))
                   (1- (steps-to-cutpoint s))))
   :hints (("Goal"
            :use steps-=-1+-for-natp))))

;; The following is a bad hack. It is also required to get the run function to
;; expand right.

(local
 (defthm run-expands
   (implies (and (equal n (1- k))
                 (natp k)
                 (natp n)
                 (syntaxp (symbolp s)))
            (equal (run s k)
                   (run (nextt s) n)))
   :hints (("Goal"
            :in-theory (enable natp)))))

;; So we are done with the natp case for (steps-to-cutpoint s). The other one
;; is trivial, by just showing that if (steps-to-cutpoint s) is not natp then
;; so is (steps-to-cutpoint (nextt s)).

(local
 (defthm natp-nextt-implies-natp
   (implies (natp (steps-to-cutpoint (nextt s)))
            (natp (steps-to-cutpoint s)))
   :hints (("Goal"
            :in-theory (disable cutpoint-implies-steps-to-cutpoint-natp)
            :use ((:instance natp-implies-cutpoint
                             (s (nextt s)))
                  (:instance cutpoint-implies-steps-to-cutpoint-natp
                             (k (1+ (steps-to-cutpoint (nextt s))))))))))

 ;; Now the final theorems. These provide the symbolic simulation rules.

(defthm |nextt cutpoint for not cutpoint|
  (implies (not (cutpoint s))
           (equal (nextt-cutpoint s)
                  (nextt-cutpoint (nextt s))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable natp)
           :do-not '(eliminate-destructors generalize fertilize)
           :cases ((natp (steps-to-cutpoint s))))
          ("Subgoal 1"
           :in-theory (disable steps-=-1-for-natp
                               natp
                               run)
           :use ((:instance steps-=-1-for-natp)
                 (:instance natp-steps-implies-natp-nextt)))))

(defthm |nextt cutpoint for cutpoint|
  (implies (cutpoint s)
           (equal (nextt-cutpoint s)
                  s))
  :hints (("Goal"
           :in-theory (enable steps-to-cutpoint))))
