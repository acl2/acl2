(in-package "ACL2")

#|

     fairenv.lisp
     ~~~~~~~~~~~~

Note from Sandip:  The original version of this fairness book was developed by
Rob Sumners.  This version makes several changes, in particular the use of
btm-measure and top-measure.  A cleaner collection of fairness books were later
derived by Rob and submitted to the ACl2 2003 workshop.

Fair environment assumptions for the bakery algorithm

OK, the following encapsulated functions define the properties of a fair
environment for the bakery. This environment is defined by the following three
functions:

   (fair-select env X)   -- returns the next input for the bakery algorithm
   (faie-step env X)     -- takes the current environment state, bakery state
                            and Xternal input and returns the next environment
                            state.
   (fair-measure env in) -- returns a lexicographic pair (i include some theory
                            below for well-founded ranks based on lexicographic
                            combinations of natural numbers) which is ensured
                            to decrease until the input in is selected.

We "install" the fair environment by redefining our step function to include
the functions fair-step and fair-select. Thus, with the  (bake+ st in) before,
we can now define the step function fair-bake+ as a step function using the
fair input. The precise definition will be given in programs.lisp.

|#

(include-book "measures")
(include-book "records")

(defun enqueue (e q)
  (if (endp q) (list e)
      (cons (first q)
            (enqueue e (rest q)))))

(defmacro select-ctr (x) `(<- ,x :select-ctr))
(defmacro select-que (x) `(<- ,x :select-que))
(defmacro env (x) `(<- ,x :env))

(defun add-que (x q)
  (if (memberp x q) q (enqueue x q)))

(defun rotate-que (x)
  (enqueue (first x) (rest x)))

(defun que-pos (x q)
  (if (or (endp q)
          (equal x (first q)))
      0
    (1+ (que-pos x (rest q)))))

(defthm enqueue-leaves-que-pos-unchanged
  (implies (memberp x q)
           (equal (que-pos x (enqueue e q))
                  (que-pos x q))))

(defthm memberp-holds-of-enqueue
  (memberp e (enqueue e q)))

(defthm memberp-preserved-by-enqueue
  (implies (memberp a q)
           (memberp a (enqueue e q))))

(encapsulate
 (((fair-select * *) => *)
  ((fair-step * *) => *)
  ((fair-measure * *) => *)
  ((btm-measure) => *)
  ((top-measure) => *))

 (local
  (defun fair-select (env X)
    (if (zp (select-ctr env))
        (first (select-que env))
      X)))

 (local
  (defun fair-step (env X)
    (let ((queue (select-que env)))
      (if (zp (select-ctr env))
          (update env
                  :select-ctr X
                  :select-que (rotate-que queue))
        (update env
                :select-ctr (1- (select-ctr env))
                :select-que (add-que X queue))))))

 (local
  (defun fair-measure (env in)
    (list 2
          (que-pos in (select-que env))
          (nfix (select-ctr env)))))

 (local
  (defun btm-measure ()
    (list 1 0 0)))

 (local
  (defun top-measure ()
    (list 3 0 0)))

 ;;;; exported theorem required to prove invariant with select-que

 (defthm fair-env-select-que-preserves
   (memberp (fair-select env X)
            (select-que (fair-step env X))))

 (defthm fair-step-preserves-membership
   (implies (memberp e (select-que env))
            (memberp e (select-que (fair-step env X)))))

 ;;;; exported properties of fair-measure

 (defthm fair-measure-is-measure
   (and (msrp (fair-measure env in))
        (nat-listp (fair-measure env in))))

 (defthm fair-measure-is-len-constant
   (len= (fair-measure (fair-step env in) in)
         (fair-measure env in)))

 (defthm input-selection-is-fair
   (implies (and (memberp in (select-que env))
                 (not (equal in (fair-select env X))))
            (msr< (fair-measure (fair-step env X) in)
                  (fair-measure env in))))

 ;;;; exported properties of btm-measure

 (defthm btm-measure-is-measure
   (and (msrp (btm-measure))
        (nat-listp (btm-measure))))

 (defthm btm-measure-is-len=0-fair-measure
   (len= (fair-measure env in)
         (btm-measure)))

 (defthm btm-measure-msr<-fair-measure
   (msr< (btm-measure)
         (fair-measure env in)))

 ;;;; exported properties of top-measure

 (defthm top-measure-is-measure
   (and (msrp (top-measure))
        (nat-listp (top-measure))))

 (defthm top-measure-is-len=0-fair-measure
   (len= (fair-measure env in)
         (top-measure)))

 (defthm fair-measure-msr<-top-measure
   (msr< (fair-measure env in)
         (top-measure)))

)





