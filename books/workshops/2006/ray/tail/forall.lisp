(in-package "ACL2")

#|

  inv-equations.lisp
  ~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Email:  sandip@cs.utexas.edu
Date:   07/23/2003

This book attempts to answer a question I raised in J's talk on inductive
assertions and operational semantics at the ACL2 workshop. In particular, I was
asking myself the following question: Was J's method of "completion" of
invariants critically dependent on the fact that to him the step function was a
function of one argument, namely the state? What would happen if step took two
arguments, a state and input, and you want to define an invariant that holds
persists irrespective of the input? Could he define his invariant based on only
assertions at cutpoints?

How does such an invariant look like? It should look like:
(inv s) = (if (b s) (q s) (forall i (inv (step s i))))

It appeared to me then that for generic functions b, c, and step, such an
equation cannot be defined in general in ACL2. In particular, notice that the
defining equation requires recursion with quantification. So it was unclear to
me whether J's completion method works.

However, it turns out that given b, c, and step above, there always exists a
function inv that satisfies the above equation. This means that J's method can
be used for defining invariants even if the step function is a function of
state and input, and the invariant is required to be preserved for every
state. In particular, this means that if cutpoints can be defined on things
like concurrent algorithms, this invariant provides the same advantages as J's
does. Of course, in practice it does not, since ACL2 is not good at reasoning
about quantifiers. However, I was not interested in practical applications
here, I was just interested in answering the question that was bugging me.

As an aside, this book shows that tail-recursive equations with quantifiers can
be added to ACL2. (Notice that this equation uses forall in the recursive
equation. It is in fact easier to do exists, and I knew that before. I am happy
I can do forall. I believe that the technique is robust enough that I can
actually do any nesting of quantifiers, But I am not claiming anything there.)


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
  (forall sched
          (implies (sched-to-cutpoint s sched)
                   (assertion (run s sched)))))

(defun-sk next-inv (s)
  (forall i
          (inv (next s i))))

(in-theory (disable next-inv next-inv-necc))


;; Now we start....

(local
 (defthm cutpoint-implies-inv-=-assertion
   (implies (cutpoint s)
            (equal (inv s)
                   (assertion s)))
   :hints (("Goal"
            :in-theory (disable inv-necc)
            :use ((:instance inv-necc
                             (sched nil)))))))

(in-theory (disable inv))

(local
 (defthm no-cutpoint-next-reduction
   (implies (not (cutpoint p))
            (equal (no-cutpoint p (cons i sched))
                   (no-cutpoint (next p i) sched)))
   :rule-classes nil))

(local
 (defthm run-next-is-cons
   (equal (run (next s i) sched)
          (run s (cons i sched)))
   :rule-classes nil))

(local
 (defthm not-cutpoint-and-inv-implies-inv-next-aux
   (implies (and (inv s)
                 (not (cutpoint s))
                 (sched-to-cutpoint (next s i) sched))
            (assertion (run (next s i) sched)))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable inv inv-necc)
            :use ((:instance inv-necc
                             (sched (cons i sched))))))))

(local
 (defthm not-cutpoint-and-inv-implies-inv-next
   (implies (and (inv s)
                 (not (cutpoint s)))
            (inv (next s i)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance (:definition inv)
                             (s (next s i)))
                  (:instance inv-necc
                             (sched (list i)))
                  (:instance (:definition inv)
                             (s (next s i)))
                  (:instance not-cutpoint-and-inv-implies-inv-next-aux
                             (sched (inv-witness (next s i)))))))))

(local
 (defthm not-cutpoint-and-inv-implies-next-inv
   (implies (and (inv s)
                 (not (cutpoint s)))
            (next-inv s))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance not-cutpoint-and-inv-implies-inv-next
                             (i (next-inv-witness s)))
                  (:instance (:definition next-inv)))))))

(local
 (defthm not-consp-to-run
   (implies (not (consp sched))
            (equal (run s sched)
                   s))))

(local
 (defthm not-cutpoint-to-sched-next
   (implies (and (sched-to-cutpoint s sched)
                 (not (cutpoint s)))
            (sched-to-cutpoint (next s (car sched)) (cdr sched)))))

(local
 (defthm sched-to-cutpoint-implies-consp
   (implies (and (sched-to-cutpoint s sched)
                 (not (cutpoint s)))
            (consp sched))
   :rule-classes nil))

(local
 (in-theory (disable sched-to-cutpoint)))

(local
 (defthm not-inv-to-not-next-inv
   (implies (and (not (inv s))
                 (not (cutpoint s)))
            (not (next-inv s)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance (:definition inv))
                  (:instance sched-to-cutpoint-implies-consp
                             (sched (inv-witness s)))
                  (:instance next-inv-necc
                             (i (car (inv-witness s))))
                  (:instance inv-necc
                             (sched (cdr (inv-witness s)))
                             (s (next s (car (inv-witness s))))))))))

(local
 (defthm not-cutpoint-implies-inv=next-inv
   (implies (not (cutpoint s))
            (equal (inv s)
                   (next-inv s)))
   :hints (("Goal"
            :use ((:instance not-inv-to-not-next-inv)
                  (:instance not-cutpoint-and-inv-implies-next-inv))))))

;; And here is the final theorem. I of course need to package up this book, but
;; this is a rough draft.

(DEFTHM inv-definition
  (equal (inv s)
         (if (cutpoint s)
             (assertion s)
           (next-inv s)))
  :rule-classes :definition)
