
(include-book "itest-cgen")
(include-book "itest-ithm")


(defunc id (x)
  :input-contract t
  :output-contract t
  x)


(defunc all-varp (xs)
  :input-contract (true-listp xs)
  :output-contract (booleanp (all-varp xs))
  (if (endp xs)
      t
    (and (varp (car xs))
         (all-varp (cdr xs)))))






(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (equal a (first X))
           (in a (rest X)))))
(definec subset (x :tl y :tl) :bool
; checks if every element in x is in y
  (or (endp x)
      (and (in (first x) y)
           (subset (rest x) y))))
(definec setequal (x :tl y :tl) :bool
; checks if x and y have exactly the same set of elements
  (and (subset x y)
       (subset y x)))
(definec aapp(x :tl y :tl):tl
  (if (endp x)
    y
    (cons (car x) (aapp (cdr x) y))))
(definec uunion (x :tl y :tl) :tl
; the union of x and y
  (aapp x y))
(defthm subset-part (implies (and (tlp x) (tlp y) (subset x y)) (subset x (cons a y))))
(defthm subset-self (implies (tlp x) (subset x x)))





:q

(load "prover.lisp")

(in-package :prover)
(define-theories)



(induction-proof-obligations '(acl2s::aapp acl2s::y acl2s::x) '(subset x (aapp y x)))
                             
(prover::check-file-proofs "tests/example.lisp")

