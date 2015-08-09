(in-package "ACL2")

#|

  initial-state.lisp
  ~~~~~~~~~~~~~~~~~~

In this book, we define an encapsulated function, initial-state, and show that
the invariant inv holds for that state. Thus our stuttering bisimulation will
claim that there exists an initial state such that if you run the program from
that state then the execution of the program matches the spec upto finite
stuttering.

|#

(include-book "programs")
(include-book "properties")


;; BEGIN Proofs of theorems.

(encapsulate
 (((initial-state-b) => *))

  (local
   (defun initial-state-b ()
     (>_ :procs nil
         :queue nil
         :bucket nil
         :maxval 0))
   )

  (local
   (defun initial-state-c ()
     nil)
   )

  (DEFTHM inv-b-c-initial-state->>
    (inv-b-c (initial-state-b))
    :rule-classes nil)

  (DEFTHM fair-inv-b-c-initial-state->>
    (fair-inv-b-c (initial-state-b))
    :rule-classes nil)

  (DEFTHM inv-c-s-rep-initial-state->>
    (inv-c-s (rep-c-s (initial-state-b)))
    :rule-classes nil)

)

