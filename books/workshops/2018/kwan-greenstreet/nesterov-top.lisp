; cert_param: (uses-acl2r)

;;
;; This book includes all the books included in "top.lisp"
;; and also Nesterov's theorem. To use them, ACL2(r) is 
;; required.
;; 
;; "nesterov-1.lisp" includes:
;; - the basic definitions and theorems involving the
;;   Lipschitz constant function "L" and the function "DIM"
;;   evaluating the the dimension of R^n
;; - the basic definitions and theorems involving convexity,
;;   continuity, and the derivatives/integrals of our convex
;;   function "mvfn" and its helper "phi-mvfn"
;; - ineq. 6 implies ineq. 1
;; - ineq. 5 implies ineq. 2
;;
;; "nesterov-2.lisp" includes:
;; - ineq. 0 implies ineq. 4
;; - ineq. 4 implies ineq. 1
;; - ineq. 1 implies ineq. 2
;; - ineq. 2 implies ineq. 3
;; - ineq. 3 implies ineq. 0
;;
;; "nesterov-3.lisp" includes:
;; - ineq. 1 implies ineq. 6
;; - ineq. 2 implies ineq. 5
;;
;; "nesterov-4.lisp" includes:
;; - the Skolem functions for all the inequalities
;; - the final form of Nesterov's theorem
;;
;; "ftc-2.lisp" is almost the same as "ftc-2.lisp" from the
;; integral book with some minor modifications. 
;;
;; The dependence between the .lisp files are as follows where
;; "->" denotes "depends on":
;;
;; nesterov-4 -> nesterov-3 -> nesterov-2 -> nesterov-1 -> ftc-2
;; 					     nesterov-1 -> convex -> ...
;;

(in-package "ACL2")
(include-book "nesterov-4")
