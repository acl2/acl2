(in-package "ACL2")

#|

   bisimulation implies matching paths in ACL2
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

OK, the following book is an ACL2 formalization (i.e. hack) for demonstrating
that bisimilarity implies that any infinite path from one state can be matched
by an infinite path in the other state. Roughly, we would like to prove the
following:

(1)  (implies (bisimilar x y)
              (forall p : (path x)
                (exists p' : (path y)
                   (match p p'))))

But, this is a non-trivial higher-order theorem. First, the notion that x and y
are bisimilar is in fact a higher-order statement that there exists a relation
between states which can be proven to be a bisimulation. We "prove" this in
ACL2 by creating an encapsulation which constrains the set of universally
quantified functions in the above theorem and then show that we can construct
another function which is the witness for the (exists p' ..) and claim that we
have proven the intended theorem (1).

While this is not a closed-form theorem in ACL2, there is a reasonable argument
that the definitions and theorems in this book do demonstrate that any
application of the higher-order theorem (1) can be "simulated" by a series of
first-order definitions and theorems in ACL2 (which is about the best we could
hope for). Further, the events in this file could be wrapped up into a macro
which performed the necessary instantiation of (1) and generated the
corresponding definitions and theorems.

|# ; |

; The following two are now built-in (different variable name, though).

; (defun natp (n)
;   (and (integerp n)
;        (>= n 0))))

; (defthm natp-compound-recognizer
;   (iff (natp n)
;        (and (integerp n)
;             (>= n 0)))
;   :rule-classes :compound-recognizer)

(in-theory (disable natp))

; The following two are now built-in (different variable name, though).

; (local ; ACL2 primitive
;  (defun posp (n)
;    (and (integerp n)
;         (> n 0))))

; (defthm posp-compound-recognizer
;   (iff (posp n)
;        (and (integerp n)
;             (> n 0)))
;   :rule-classes :compound-recognizer)

(in-theory (disable posp))

(encapsulate
 (((transit * *) => *)  ;; a transition relation between states
  ((label *) => *)   ;; a labeling of atomic prop.s to states
  ((bisim * *) => *) ;; a bisimulation relation between states

  ;; we need a witnessing function for the choice in the bisimulation
  ;; we could use defun-sk, but choose to just go ahead and constrain
  ;; it here since the encapsulate is handy..
  ((bisim-witness * * *) => *)

  ;; an arbitrary path from a given initial state for the path
  ((path * *) => *))

  (local (defun transit (x y)
           (declare (ignore x y))
           t))

  (local (defun label (x)
           (declare (ignore x))
           t))

  (local (defun bisim (x y)
           (declare (ignore x y))
           t))
  
  (local (defun bisim-witness (x y z)
           (declare (ignore x y z))
           t))

  (defthm bisim-is-symmetric
    (implies (bisim x y)
             (bisim y x)))
  
  (defthm bisim-preserves-labels
    (implies (bisim x y)
             (equal (label x) (label y))))
  
  (defthm bisim-witness-is-always-step
    (implies (transit x z)
             (transit y (bisim-witness x y z))))
  
  (defthm bisim-states-can-match-transit
    (implies (and (bisim x y)
                  (transit x z))
             (bisim z (bisim-witness x y z))))

  (local (defun path (x n)
           (declare (ignore n))
           x))

  (defthm path-starts-at-x
    (equal (path x 0) x))

  (defthm path-takes-steps
    (implies (posp n)
             (transit (path x (1- n))
                      (path x n))))
)

;; We construct a "matching" path from some arbitrary y

(defun path+ (y i x)
  (if (zp i) y
    (bisim-witness (path x (1- i)) 
                   (path+ y (1- i) x)
                   (path x i))))

(defun matches (x y i)
  (equal (label (path x i))
         (label (path+ y i x))))

(defthm path+-starts-at-y
  (equal (path+ y 0 x) y))

(defthm path+-takes-steps
  (implies (posp i)
           (transit (path+ y (1- i) x)
                    (path+ y i x))))

(defthm bisim-implies-bisim-along-path
  (implies (and (natp i)
                (bisim x y))
           (bisim (path x i)
                  (path+ y i x)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((path+ y i x)))))

(defthm bisim-implies-matches
  (implies (and (natp i)
                (bisim x y))
           (matches x y i)))

