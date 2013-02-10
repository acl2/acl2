;; Exercise file to accompany 
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Startup file for exercise 3.
;;
;; Define a function cnf that converts negation normal form 
;; formulas to conjunctive normal form and a predicate cnfp 
;; that recognizes conjunctive normal form formulas.  Prove
;; correctness of the conversion function.

;; Note 1: See book nnf for the predicate nnfp, a recognizer of 
;; in negation normal form.

;; Note: to prove correctness in this case means to prove that cnf
;; 	(1) preserves the property wff
;;	(2) converts nnfp formulas to cnfp, and
;;	(3) is sound.

;; All neccesary definitions are in:
(include-book "../wfftype")

