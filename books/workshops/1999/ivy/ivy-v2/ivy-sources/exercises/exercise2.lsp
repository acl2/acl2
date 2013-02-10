;; Exercise file to accompany 
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Startup file for exercise 2.
;;
;; Prove that if an interpretation contains a function func, 
;; and if a formula does not contain the corresponding function 
;; symbol, then evaluation of the formula in the interpretation is
;; independent of the occurrence of func.  Assume that func
;; is the first function in the interpretation.

;; Note 1: the intent of this exercise is to foster a
;; fuller understanding of the evaluation function. 
;; We spare the reader from the tedious task of
;; proving supporting lemmas by providing them in the
;; following book:

(include-book "../sk-misc-lemmas")

;; Note 2: funcs-in-formula (f) computes the list of functions
;; symbols that appear in f.  Its definition may be found in
;; book wfftype.

;; Hint: the following lemma might be useful:
(defthm not-member-union-forward-right
  (implies (not (member-equal x (union-equal a b)))
           (not (member-equal x b)))
  :rule-classes :forward-chaining)

;; The exercise asks the reader to prove the following conjecture
(defthm feval-with-useless-function
  (implies (not (member-equal func (funcs-in-formula f)))
	   (if flg
	       (equal (feval f (list* (domain i) (relations i)
				      (cons (cons func n) func)
				      (functions i)))
		      (feval f i ))
	     (implies (and (domain-term-list (fringe dom))
			   (wfquant f))
		      (equal (feval-d f dom (list* (domain i) (relations i)
						   (cons (cons func n) func)
						   (functions i)))
			     (feval-d f dom i))))) 
  :rule-classes nil)




