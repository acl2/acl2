;;; dag-unification-examples.lisp
;;; Examples of unification of terms represented as directed acyclic
;;; graphs (dags)
;;; ==========================================================================

#| This file is not a certifiable book.  To execute these tests:

(ld "dag-unification-examples.lisp" :ld-pre-eval-print t)

|#

(in-package "ACL2")

(include-book "dag-unification")


;;; EXAMPLES:
;;; =========
(reset-unif-problem 0 1023 terms-dag)

(dag-mgu '(f x (g (a) y)) '(f x (g y x)) terms-dag)
;;; ==> (((X A) (Y A)) <terms-dag>)

(dag-mgu '(h u) '(h (b)) terms-dag)
;;; ===> (((U B)) <terms-dag>)

(dag-mgu 1 1 terms-dag)
;;; ===> (NIL <terms-dag>)

(dag-unifiable 1 1 terms-dag)
;;; ===> (T <terms-dag>)

(dag-unifiable 1 '(f 1) terms-dag)
;;; ===> (NIL <terms-dag>)

(dag-mgu '(f (g x y) (g y x)) '(f u u) terms-dag)
;;; ===> (((Y . X) (U G X X)) <terms-dag>)

(dag-unifiable '(f (g x y) (g y x)) '(f x x) terms-dag)
;;; ===> (NIL <terms-dag>)

(dag-mgu '(f (h z) (h (h z))) '(f u (h (h (g v v)))) terms-dag)
;;; ===> (((Z G V V) (U H (G V V))) <terms-dag>)

(dag-mgu '(f x (g (a) y)) '(f x (g y x)) terms-dag)
;;; ===> (((X A) (Y A)) <terms-dag>)

(dag-mgu '(f x (g a y)) '(f x (g y x)) terms-dag)
;;; ===> (((Y . X) (A . X)) <terms-dag>)

(dag-mgu '(f x (g (a) y)) '(f x (g y x)) terms-dag)
;;; ===> (((X A) (Y A)) <terms-dag>)

(dag-mgu '(f x (g a y)) '(f x (g y x)) terms-dag)
;;; ===> (((Y . X) (A . X)) <terms-dag>)

(dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)) terms-dag)
;;; ===> (((V H (H Z)) (U H Z) (X H Z)) <terms-dag>)


;;; ---------------------
;;; Exponential problems
;;; ---------------------

;;; See pages 85 and 86 of "Term Rewriting and All That...", Baader &
;;; Nipkow. 

;;; See dag-unification.lisp for the definition of exp-unif-problem

;;; (exp-unif-problem 100 terms-dag)
;;; ===> (T <terms-dag>)
;;; Very fast!!!

;;; ------------------------------------------------------------------

;;; Nevertheless, the above algorithm is still exponential in time. The
;;; following unification problem reach that complexity.

;;; See dag-unification.lisp for the definition of exp-unif-problem-q


;;; ACL2 !>(exp-unif-problem-q 20 terms-dag)
;;; ===> (T <terms-dag>)
;;; For n>20, impractical...


;;; Analogue to the previous unification problem, but not unifiable. 

;;; See dag-unification.lisp for the definition of exp-unif-problem-qn


;;; ACL2 !>(exp-unif-problem-qn 20 terms-dag)
;;; (NIL <terms-dag>)
;;; For n>20, impractical...

