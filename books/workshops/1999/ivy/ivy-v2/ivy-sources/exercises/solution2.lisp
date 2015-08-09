;; Exercise file to accompany
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Solution for exercise 2.
;;
;; Prove that if an interpretation contains a function func,
;; and if a formula does not contain the corresponding function
;; symbol, then evaluation of the formula in the interpretation is
;; independent of the occurrence of func.  Assume that func
;; is the first function in the interpretation.

(in-package "ACL2")

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

;; ----------------------------------------------------------

(defthm eval-term-list-with-useless-function
  (implies (not (member-equal func (funcs-in-term-list l)))
           (equal (eval-term-list l (list* i1 i3
                                           (cons (cons func n) func)
                                           i4))
                  (eval-term-list l (list* i1 i3 i4))))
  :hints (("Goal"
           :in-theory (enable domain))))

(defthm not-member-funcs-a
  (implies (and (consp l)
                (not (member-equal func (funcs-in-term-list l))))
           (not (member-equal func (funcs-in-term-list (list (car l)))))))

(defthm not-member-funcs-b
  (implies (not (member-equal func (funcs-in-term-list (cons a l))))
           (not (member-equal func (funcs-in-term-list (list a)))))
  :hints (("Goal"
         :use ((:instance not-member-funcs-a (l (cons a l)))))))

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
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (enable eval-atomic)
	   :induct (feval-i flg f dom i)))
  :rule-classes nil)


