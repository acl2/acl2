;; Exercise file to accompany 
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Startup file for exercise 6.
;;
;; We rely on the ability to generate a new symbol with respect to a
;; given symbol list in steps 2 and 3 of the search procedure.  In
;; variable renaming, step 2, we generate a new variable.  In
;; Skolemization, step 3, we generate a Skolem function name.  Common
;; Lisp has a function gensym, but it is state dependent and therefore 
;; not available in ACL2.  Define an ACL2 function that generates a 
;; symbol that is not in a given list of symbols, and prove its 
;; correctness.

;; Hint: ACL2 defines functions "coerce" and 
;; "intern-in-package-of-symbol."  See ACL2 documentation for more
;; information.
