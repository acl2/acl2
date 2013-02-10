;; Exercise file to accompany 
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Startup file for exercise 4.
;;
;; Define a resolution function that takes two formulas and
;; two specifications of subformulas within the formulas,
;; and computes a resolvent, if possible, of the two formulas
;; on the specified literals.
;;
;; Prove that the function is sound.

;; All neccesary definitions are in:
(include-book "../base")

;; Hint: the following lemma might be useful:
(encapsulate 
 nil
 (local (include-book "../close"))
 (defthm feval-alls-subset
   (implies (and (var-set a)
                 (var-set b)
                 (subsetp-equal a b)
                 (not (free-vars (alls a f))))
            (equal (feval (alls a f) i)
                   (feval (alls b f) i)))
   :rule-classes nil)
 )
