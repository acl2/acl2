(in-package "ACL2")

;; 
;; This book includes:
;;  - the vector space axioms contained in vectors.lisp
;;  - the inner product space axioms contained in 
;;    norm.lisp and partially in vectors.lisp
;;  - the proof of Cauchy-Schwarz contained in 
;;    cauchy-schwarz.lisp
;;  - the metric space axioms contained in metric.lisp
;;  - some examples of multivariate continuous functions
;;    contained in continuity.lisp
;;  - some theorems for reasoning about convex functions 
;;    contained in convex.lisp
;;
;; The dependences between the .lisp files are as follows 
;; where "->" denotes "depends on":
;;
;; convex -> metric -> cauchy-schwarz -> norm -> vectors
;;
;; continuity -> metric -> ...
;;

(include-book "convex")
(include-book "continuity")



