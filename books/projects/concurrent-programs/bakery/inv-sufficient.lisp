(in-package "ACL2")

#|

  inv-sufficient.lisp
  ~~~~~~~~~~~~~~~~~~~

In this book, we prove the theorem inv-sufficient->>. This will validate that
the proof of >>-stutter1 and >>-match that we achieve are indeed proofs of
stuttering bisimulation. With this theorem, we will be allowed to work with
suff, rather than inv. suff is a (possibly) simpler function than inv, since it
can use the current input as a parameter.

|#

(include-book "programs")
(include-book "properties")
(include-book "lexicographic-pos")
(include-book "properties-of-sets")

(local
(in-theory (enable memberp my-subsetp))
)

(local
(defthm inv-p-p-implies-suff-proc
  (implies (inv-p-p procs in bucket queue max)
           (suff-proc procs in bucket queue max)))
)

(local
(in-theory (disable pos=1+temp inv-p-p suff-proc))
)

(local
(defthm induct-on-keys
  (implies (and (inv-p-keys procs keys bucket queue max)
                (memberp in keys)
                (<- procs in))
           (suff-proc procs in bucket queue max)))
)

(local
(defthm inv-p-keys-to-car-queue-if-subset
  (implies (and (inv-p-keys procs keys bucket queue max)
                (my-subsetp queue keys)
                (consp queue))
           (inv-p-p procs (first queue) bucket queue max))
  :rule-classes :forward-chaining)
)

(DEFTHM inv-b-c-sufficient->>
  (implies (inv-b-c st)
           (suff-b-c st in))
  :rule-classes nil)

(DEFTHM fair-inv-b-c-sufficient->>
  (implies (fair-inv-b-c st)
           (fair-suff-b-c st X))
  :rule-classes nil)

(defthm inv-p-p-suff-proc-c-s
  (implies (inv-p-p-c-s procs in bucket queue go)
           (suff-proc-c-s procs in bucket queue go))
  :hints (("Goal"
           :do-not-induct t)))

(in-theory (disable inv-p-p-c-s suff-proc-c-s))

(defthm induct-on-keys-c-s
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys))
           (suff-proc-c-s procs in bucket queue go)))

(local
(defthm keys-not-nil-to-not-queue
  (implies (and (keys-not-nil keys)
                (my-subsetp queue keys)
                (memberp in queue))
           in)
  :rule-classes :forward-chaining)
)

(DEFTHM inv-c-s-sufficient
  (implies (and (inv-c-s st)
                (legal st in))
           (suff-c-s st in))
  :rule-classes nil)

