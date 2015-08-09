(in-package "ACL2")

#|

  final-theorems.lisp
  ~~~~~~~~~~~~~~~~~~~

In this book, we simply summarize all the final theorems that we have
proved in other books for the bakery. All the theorems should go thru
and say "redundant" in ACL2. I simply have this book, to make the task
easy for the reader of the proof. When all is said and done, these
will be the facts that we claim about the bakery algorithm.

|#

(include-book "labels")
(include-book "stutter1-match")
(include-book "stutter2")
(include-book "initial-state")
(include-book "inv-persists")
(include-book "inv-sufficient")

;; Labels of implementation and specification are equal

(DEFTHM labels-equal-b-c->>
  (implies (inv-b-c st)
	   (equal (label (rep-b-c st))
		  (label st)))
  :rule-classes nil)

(DEFTHM fair-labels-equal-b-c->>
  (implies (fair-inv-b-c st)
           (equal (label (rep-b-c st))
                  (label st)))
  :rule-classes nil)


;; A step of the implementation is a step of the specification upto
;; stuttering:

(DEFTHM >>-stutter1-b-c
  (implies (and (suff-b-c st in)
                (not (commit-b-c st in)))
           (equal (rep-b-c (bake+ st in))
                  (rep-b-c st)))
  :rule-classes nil)

(DEFTHM >>-fair-stutter1-b-c
  (implies (and (fair-suff-b-c st X)
                (not (commit-b-c st (fair-select (env st) X))))
           (equal (rep-b-c (fair-bake+ st X))
                  (rep-b-c st)))
  :rule-classes nil)

(DEFTHM >>-stutter1-c-s
  (implies (and (suff-c-s st in)
                (not (commit-c-s st in)))
              (equal (rep-c-s (cent st in))
                  (rep-c-s st)))
  :rule-classes nil)


(DEFTHM >>-match-b-c
  (implies (and (suff-b-c st in)
                (commit-b-c st in))
           (equal (rep-b-c (bake+ st in))
                  (cent (rep-b-c st) (pick-b-c st in))))
  :rule-classes nil)

(DEFTHM >>-fair-match-b-c
  (implies (and (fair-suff-b-c st X)
                (commit-b-c st (fair-select (env st) X)))
           (equal (rep-b-c (fair-bake+ st X))
                  (cent (rep-b-c st)
                        (fair-pick-b-c st X))))
  :rule-classes nil)

(DEFTHM match-c-s
  (implies (and (suff-c-s st in)
                (legal st in)
                (commit-c-s st in))
           (equal (rep-c-s (cent st in))
                  (spec (rep-c-s st) in)))
  :rule-classes nil)

;; Stuttering is finite:

(DEFTHM well-founded-b-c->>
  (msrp (rank-b-c st))
  :rule-classes nil)

(DEFTHM >>-stutter2-b-c
  (implies (and (fair-suff-b-c st X)
		(not (commit-b-c st (fair-select (env st) X))))
	   (msr< (rank-b-c (fair-bake+ st X))
		       (rank-b-c st)))
  :rule-classes nil)

;; There exists at least one state in which the invariant inv holds

(DEFTHM inv-b-c-initial-state->>
    (inv-b-c (initial-state-b))
    :rule-classes nil)

(DEFTHM fair-inv-b-c-initial-state->>
  (fair-inv-b-c (initial-state-b))
  :rule-classes nil)

(DEFTHM inv-c-s-rep-initial-state->>
  (inv-c-s (rep-c-s (initial-state-b)))
  :rule-classes nil)

;; "inv" is an invariant:

(DEFTHM inv-b-c-persists->>
  (implies (inv-b-c st)
	   (inv-b-c (bake+ st in)))
  :rule-classes nil)

(DEFTHM fair-inv-b-c-persists->>
  (implies (fair-inv-b-c st)
           (fair-inv-b-c (fair-bake+ st X)))
  :rule-classes nil)

(DEFTHM inv-c-s-persists->>
  (implies (and (inv-c-s st)
                (legal st in))
           (inv-c-s (cent st in)))
  :rule-classes nil)

;; "inv" is sufficient:

(DEFTHM inv-b-c-sufficient->>
  (implies (inv-b-c st)
           (suff-b-c st in))
  :rule-classes nil)

(DEFTHM fair-inv-b-c-sufficient->>
  (implies (fair-inv-b-c st)
           (fair-suff-b-c st X))
  :rule-classes nil)

(DEFTHM inv-c-s-sufficient
  (implies (and (inv-c-s st)
                (legal st in))
           (suff-c-s st in))
  :rule-classes nil)


