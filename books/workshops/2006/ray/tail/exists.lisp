(in-package "ACL2")

#|

  inv-equations.lisp
  ~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Email:  sandip@cs.utexas.edu
Date:   07/23/2003

Here is another equation that we introduce. This one has the exists
quantifier. For other comments see the forall.lisp file.

|#


(set-match-free-default :all)

;; Here are the assumptions we make: namely we assume existence of functions
;; next, assertion, and cutpoint.

(defstub next (* *) => *)

(encapsulate
 (((assertion *) => *)
  ((cutpoint *) => *))

 (local (defun assertion (s) (declare (ignore s)) T))
 (local (defun cutpoint (s) (declare (ignore s)) T))

 (defthm assertion-is-boolean
   (booleanp (assertion s))
   :rule-classes :type-prescription)

 (defthm cutpoint-is-boolean
   (booleanp (cutpoint s))
   :rule-classes :type-prescription)

)


;; Let us now define the invariant inv, and the corresponding (quantified)
;; version next-inv for recursion purposes.

(defun run (s sched)
  (if (endp sched)
      s
    (run (next s (first sched))
         (rest sched))))

(defun no-cutpoint (p sched)
  (declare (xargs :measure (acl2-count sched)))
  (if (endp sched)
      (not (cutpoint p))
    (and (not (cutpoint p))
         (no-cutpoint (next p (first sched)) (rest sched)))))

(defun del-last (l)
  (if (endp l) nil
    (if (endp (rest l)) nil
      (cons (first l) (del-last (rest l))))))

(defun sched-to-cutpoint (p sched)
  (and (cutpoint (run p sched))
       (implies (consp sched)
                (no-cutpoint p (del-last sched)))))

(defun-sk inv (s)
  (exists sched
          (and (true-listp sched)
          (sched-to-cutpoint s sched)
          (assertion (run s sched)))))

(defun-sk next-inv (s)
  (exists i
          (inv (next s i))))

(in-theory (disable next-inv next-inv-suff))
(in-theory (disable inv inv-suff))

;; Now we start....

(local
 (defthm cutpoint-and-assertion-implies-inv
   (implies (and (cutpoint s)
                 (assertion s))
            (inv s))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable inv inv-suff)
            :use ((:instance inv-suff
                             (sched nil)))))))

(local
 (defthm inv-and-cutpoint-implies-assertion
   (implies (and (cutpoint s)
                 (inv s))
            (assertion s))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable inv)))))

(local
 (defthm cutpoint-implies-inv=assertion
   (implies (cutpoint s)
            (equal (inv s)
                   (assertion s)))
   :hints (("Goal"
            :use ((:instance inv-and-cutpoint-implies-assertion)
                  (:instance cutpoint-and-assertion-implies-inv))))))

(local
 (defthm not-cutpoint-and-sched-to-cutpoint-implies-cdr
   (implies (and (sched-to-cutpoint p sched)
                 (not (cutpoint p)))
            (sched-to-cutpoint (next p (car sched))
                               (cdr sched)))
  :rule-classes nil))

(local
 (defthm inv-implies-inv-next
   (implies (and (inv s)
                 (not (cutpoint s)))
            (inv (next s (car (inv-witness s)))))
   :hints (("Goal"
            :use ((:instance (:definition inv))
                  (:instance inv-suff
                             (s (next s (car (inv-witness s))))
                             (sched (cdr (inv-witness s))))
                  (:instance not-cutpoint-and-sched-to-cutpoint-implies-cdr
                             (sched (inv-witness s))))))))

(local
 (defthm inv-implies-next-inv
   (implies (and (inv s)
                 (not (cutpoint s)))
            (next-inv s))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance next-inv-suff
                             (i (car (inv-witness s)))))))))

(local
 (defthm sched-to-cutpoint-from-next
   (implies (and (sched-to-cutpoint (next s i) sched)
                 (not (cutpoint s)))
            (sched-to-cutpoint s (cons i sched)))))

(local
 (defthm inv-from-next-inv
   (implies (and (inv (next s i))
                 (not (cutpoint s)))
            (inv s))
   :hints (("Goal"
            :in-theory (disable sched-to-cutpoint)
            :use ((:instance (:definition inv)
                             (s (next s i)))
                  (:instance inv-suff
                             (sched (cons i (inv-witness (next s i))))))))))

(local
 (defthm next-inv-implies-inv
   (implies (and (next-inv s)
                 (not (cutpoint s)))
            (inv s))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable next-inv)))))

(DEFTHM inv-definition
  (equal (inv s)
         (if (cutpoint s)
             (assertion s)
           (next-inv s)))
  :hints (("Subgoal 1"
           :use ((:instance inv-implies-next-inv)
                 (:instance next-inv-implies-inv))))
  :rule-classes :definition)
