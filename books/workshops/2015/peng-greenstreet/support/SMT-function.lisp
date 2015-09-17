;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

;; SMT-function
(in-package "ACL2")
(include-book "std/strings/top" :dir :system)
(include-book "./helper")
(include-book "./SMT-extract")
(set-state-ok t)
(set-ignore-ok t)
(program)

;; create-name
(defun create-name (num)
  "create-name: creates a name for a new function"
  (let ((index (STR::natstr num)))
    (if (stringp index)
	(mv (intern-in-package-of-symbol
	     (concatenate 'string "var" index) 'ACL2)
	    (1+ num))
      (prog2$ (er hard? 'top-level "Error(function): create name failed: ~q0!" index)
	      (mv nil num)))))

;; replace-var
(defun replace-var (body var-pair)
  "replace-var: replace all appearance of a function symbol in the body with the var-pair"
  (if (atom body)
      (if (equal body (car var-pair))
	  (cadr var-pair)
	body)
    (cons (replace-var (car body) var-pair)
	  (replace-var (cdr body) var-pair))))

;; set-fn-body
(defun set-fn-body (body var-list)
  "set-fn-body: set the body for let expression"
  (if (endp var-list)
      body
    (set-fn-body
     (replace-var body (car var-list))
     (cdr var-list))))

;; make-var-list
(defun make-var-list (formal num)
  "make-var-list: make a list of expressions for replacement"
  (if (endp formal)
      (mv nil num)
    (mv-let (var-name res-num1)
	    (create-name num)
	    (mv-let (res-expr res-num2)
		    (make-var-list (cdr formal) res-num1)
		    (mv (cons (list (car formal) var-name) res-expr) res-num2)))))

;; assoc-fetch-key
(defun assoc-fetch-key (assoc-list)
  "assoc-fetch-key: fetching keys from an associate list"
  (if (endp assoc-list)
      nil
    (cons (caar assoc-list) (assoc-fetch-key (cdr assoc-list)))))

;; assoc-fetch-value
(defun assoc-fetch-value (assoc-list)
  "assoc-fetch-value: fetching values from an associate list"
  (if (endp assoc-list)
      nil
    (cons (cadr (car assoc-list)) (assoc-fetch-value (cdr assoc-list)))))

;; decrease-level-by-1
(defun decrease-level-by-1 (fn fn-level-lst)
  "decrease-level-by-1: decrease a function's expansion level by 1."
  (if (endp fn-level-lst)
      nil
      (if (equal (car (car fn-level-lst)) fn)
	  (cons (list fn (1- (cadr (car fn-level-lst))))
		(cdr fn-level-lst))
	  (cons (car fn-level-lst)
		(decrease-level-by-1 fn (cdr fn-level-lst))))))

;; expand-a-fn
;; e.g.(defun double (x y) (+ (* 2 x) y))
;;     (double a b) -> (let ((var1 a) (var2 b)) (+ (* 2 var1) var2))
;;     (double a b) -> ((lambda (var1 var2) (+ (* 2 var1) var2)) a b)
;; 2014-07-01
;; added code for decreasing level for function expanded
(defun expand-a-fn (fn fn-level-lst fn-waiting fn-extended num state)
  "expand-a-fn: expand an expression with a function definition, num should be accumulated by 1. fn should be stored as a symbol"
  (let ((formal (cdr (cadr (meta-extract-formula fn state))))
	;; the third element is the formalss
	(body (end (meta-extract-formula fn state)))
	;; the last element is the body
	)
    (if (endp formal)
	(mv body
	    (my-delete fn-waiting fn)
	    (cons fn fn-extended)
	    (decrease-level-by-1 fn fn-level-lst)
	    num)
	(mv-let (var-list num1)
		(make-var-list formal num)
		(mv (list 'lambda (assoc-fetch-value var-list)
			  (set-fn-body body var-list))
		    (my-delete fn-waiting fn)
		    (cons fn fn-extended)
		    (decrease-level-by-1 fn fn-level-lst)
		    num1)))))

;; lambdap
(defun lambdap (expr)
  "lambdap: check if a formula is a valid lambda expression"
  (if (not (equal (len expr) 3))
      nil
      (let ((lambdax (car expr))
	    (formals (cadr expr)))
	    ;;(body (caddr expr)))
	(if (and (equal lambdax 'lambda)
		 (listp formals)) ;; I can add a check for no
	                          ;; occurance of free variable in the future
	    t
	    nil))))

(skip-proofs
(mutual-recursion
 ;; expand-fn-help-list
 (defun expand-fn-help-list (expr fn-lst fn-level-lst fn-waiting fn-extended num state)
   "expand-fn-help-list"
   (declare (xargs :measure (list (acl2-count (len fn-waiting)) (acl2-count expr))))
   (if (endp expr)
       (mv nil num)
     (mv-let (res-expr1 res-num1)
	     (expand-fn-help (car expr) fn-lst fn-level-lst fn-waiting fn-extended num state)
	     (mv-let (res-expr2 res-num2)
		     (expand-fn-help-list (cdr expr) fn-lst fn-level-lst fn-waiting fn-extended res-num1 state)
		     (mv (cons res-expr1 res-expr2) res-num2)))))

 ;; expand-fn-help
 ;; This function should keep three lists of function names.
 ;   First one stores all functions possible for expansion.
 ;   Second one is for functions to be expanded
 ;   and the third one is for functions already expanded.
 ;; They should be updated accordingly:
 ;   when one function is expanded along a specific path
 ;   that function should be deleted from fn-waiting and added
 ;   into fn-expanded.
 ;; Resursion detection:
 ;   When one function call is encountered
 ;   we want to make sure that function is valid for expansion
 ;   by looking at fn-lst. Then we expand it, delete it from
 ;   fn-waiting and add it onto fn-expanded. The we want to make
 ;   sure that fn-waiting and fn-expaned is changing as we walk
 ;   through the tree of code.
 ;; Another way of recursion detection:
 ;   One might want to use this simpler way of handling recrusion
 ;   detection. We note the length of fn-lst, then we want to
 ;   count down the level of expansion. Any path exceeding this
 ;   length is a sign for recursive call. 
 (defun expand-fn-help (expr fn-lst fn-level-lst fn-waiting fn-extended num state)
   "expand-fn-help: expand an expression"
   (declare (xargs :measure (list (acl2-count (len fn-waiting)) (acl2-count expr))))
   (cond ((atom expr) ;; base case, when expr is an atom
 	  (mv expr num))
	 ((consp expr)
	  (let ((fn0 (car expr)) (params (cdr expr)))
	    (cond
	      ((and (atom fn0) (exist fn0 fn-lst)) ;; function exists in the list
	       (if (> (cadr (assoc fn0 fn-level-lst)) 0) ;; if fn0's level number is still larger than 0
		   (mv-let (res fn-w-1 fn-e-1 fn-l-l-1 num2)
			   (expand-a-fn fn0 fn-level-lst fn-waiting fn-extended num state) ;; expand a function
			   (mv-let (res2 num3)
				   (expand-fn-help res fn-lst fn-l-l-1 fn-w-1 fn-e-1 num2 state)
				   (if (endp params)
				       (mv res2 num3)
				       (mv-let (res3 num4)
					       (expand-fn-help-list params fn-lst fn-level-lst fn-waiting fn-extended num3 state)
					       (mv (cons res2 res3) num4)))))
		   (prog2$ (cw "Recursive function expansion level has reached 0: ~q0" fn0)
			   (mv expr num))))
	      ((atom fn0) ;; when expr is a un-expandable function
	       (mv-let (res num2)
		       (expand-fn-help-list (cdr expr) fn-lst fn-level-lst fn-waiting fn-extended num state)
		       (mv (cons (car expr) res) num2)))
	      ((lambdap fn0) ;; function is a lambda expression, expand the body
	       (let ((lambdax fn0) (params (cdr expr)))
		 (let ((formals (cadr lambdax)) (body (caddr lambdax)))
		   (mv-let (res num2)
			   (expand-fn-help body fn-lst fn-level-lst fn-waiting fn-extended num state)
			   (mv-let (res2 num3)
				   (expand-fn-help-list params fn-lst fn-level-lst fn-waiting fn-extended num2 state)
				   (mv (cons (list 'lambda formals res) res2)  num3))))))
	      ((and (not (lambdap fn0)) (consp fn0))
	       (mv-let (res num2)
		       (expand-fn-help fn0 fn-lst fn-level-lst fn-waiting fn-extended num state)
		       (mv-let (res2 num3)
			       (expand-fn-help-list params fn-lst fn-level-lst fn-waiting fn-extended num2 state)
			       (mv (cons res res2) num3))))
	      (t (prog2$ (er hard? 'top-level "Error(function): can not pattern match: ~q0" expr)
			 (mv expr num)))
	      )))
	 (t (prog2$ (er hard? 'top-level "Error(function): strange expression == ~q0" expr)
 		    (mv expr num)))))
)
)

(mutual-recursion

;; rewrite-formula-params
(defun rewrite-formula-params (expr let-expr)
  "rewrite-formula-params: a helper function for dealing with the param list of rewrite-formula function"
  (if (endp expr)
      nil
      (cons (rewrite-formula (car expr) let-expr)
	    (rewrite-formula-params (cdr expr) let-expr))))

;; rewrite-formula
;; rewrite the formula according to given hypothesis and let-expression
(defun rewrite-formula (expr let-expr)
  "rewrite-formula rewrites an expression by replacing corresponding terms in the let expression"
  (cond ((atom expr) ;; if expr is an atom
	 (let ((res-pair (assoc-equal expr let-expr)))
	   (if (equal res-pair nil)
	       expr
	       (cadr res-pair))))
      ;; if expr is a consp
	((consp expr)
	 (let ((fn (car expr))
	       (params (cdr expr)))
	   (if (listp fn)
	       ;; if first elem of expr is a list
	       (cond
		 ;; if it is a lambda expression
		 ((lambdap fn)
		  (let ((lambda-params (cadr fn))
			(lambda-body (caddr fn)))
		    (let ((res-pair (assoc-lambda
				     lambda-body
				     (create-assoc lambda-params params)
				     let-expr)))
		    (if (not (equal res-pair nil))
			(cadr res-pair)
			(cons (list 'lambda lambda-params (rewrite-formula lambda-body let-expr))
			      (rewrite-formula-params params let-expr))))))
		 ;; if it is a only a list, for handling nested list
		 (t
		  (cons (rewrite-formula fn let-expr)
			(rewrite-formula-params params let-expr))))
	       ;; if first elem of expr is an atom
	       (let ((res-pair (assoc-equal expr let-expr)))
		 (if (not (equal res-pair nil))
		     (cadr res-pair)
		     (cons fn (rewrite-formula-params params let-expr)))))))
	;; if expr is nil
	(t (er hard? 'top-level "Error(function): nil expression."))))
)

;; extract-orig-param
(defun extract-orig-param (expr)
  (get-orig-param (mv-nth 0 (mv-list 3 (SMT-extract expr))))) 

;; augment-formula
(defun augment-formula (expr let-type new-hypo)
  "augment-formula: for creating a new expression with hypothesis augmented with new-hypo, assuming new-hypo only adds to the hypo-list"
  (b* ( ((mv decl-list hypo-list concl) (SMT-extract expr)) )
      (list 'implies (and-list-logic (append decl-list let-type (list hypo-list) new-hypo))
            concl))
  )

;; reform-let
(defun reform-let (let-expr)
  "reform-let: reforms a let expression for convenient fetch"
  (let ((inverted-let-expr (invert-assoc let-expr)))
  (if (assoc-no-repeat inverted-let-expr)
      inverted-let-expr
      (er hard? 'top-level "Error(function): there's repetition in the associate list's values ~q0" let-expr))))

;; initial-level-help
(defun initial-level-help (fn-lst fn-level)
  "initial-level-help: binding a level to each function for expansion. fn-lst is a list of functions, fn-level is the number of levels we want to expand the functions."
  (if (endp fn-lst)
      nil
      (cons (list (car fn-lst) fn-level)
	    (initial-level-help (cdr fn-lst) fn-level))))

;; initial-level
(defun initial-level (fn-lst fn-level)
  "initial-level: binding a level to each function for expansion"
  (if (not (integerp fn-level))
      (initial-level-help fn-lst 1)
      (initial-level-help fn-lst fn-level)))

;; split-fn-from-type
(defun split-fn-from-type (fn-lst-with-type)
  ""
  (if (endp fn-lst-with-type)
      nil
      (cons (caar fn-lst-with-type)
	    (split-fn-from-type (cdr fn-lst-with-type)))))

;; replace-a-rec-fn
(defun replace-a-rec-fn (expr fn-lst-with-type fn-var-decl num)
  ""
  (mv-let (name res-num)
	  (create-name num)
	  (mv name
	      (cons (list name
			  expr
			  (cadr (assoc (car expr) fn-lst-with-type)))
		    fn-var-decl)
	      res-num)))

(mutual-recursion

 ;; replace-rec-fn-params
(defun replace-rec-fn-params (expr fn-lst-with-type fn-var-decl num)
  ""
  (if (endp expr)
       (mv expr fn-var-decl num)
     (mv-let (res-expr1 res-fn-var-decl1 res-num1)
	     (replace-rec-fn (car expr) fn-lst-with-type fn-var-decl num)
	     (mv-let (res-expr2 res-fn-var-decl2 res-num2)
		     (replace-rec-fn-params (cdr expr) fn-lst-with-type res-fn-var-decl1 res-num1)
		     (mv (cons res-expr1 res-expr2)
			 res-fn-var-decl2
			 res-num2)))))

;; replace-rec-fn
;; 2014-07-04
;; added function for postorder traversal
(defun replace-rec-fn (expr fn-lst-with-type fn-var-decl num)
  ""
  (cond ((atom expr)
	 (mv expr fn-var-decl num))
	((consp expr)
	 (let ((fn0 (car expr)) (params (cdr expr)))
	    (cond
	      ((and (atom fn0) (not (endp (assoc fn0 fn-lst-with-type)))) ;; function exists in the list
	       (mv-let (res fn-var-decl2 num2)
		       (replace-a-rec-fn expr fn-lst-with-type fn-var-decl num)
		       (mv res fn-var-decl2 num2)))
	      ((atom fn0) ;; when expr is a un-expandable function
	       (mv-let (res fn-var-decl2 num2)
		       (replace-rec-fn-params params fn-lst-with-type fn-var-decl num)
		       (mv (cons fn0 res) fn-var-decl2 num2)))
	      ((lambdap fn0) ;; function is a lambda expression, expand the body
	       (let ((lambdax fn0) (params (cdr expr)))
		 (let ((formals (cadr lambdax)) (body (caddr lambdax)))
		   (mv-let (res fn-var-decl2 num2)
			   (replace-rec-fn body fn-lst-with-type fn-var-decl num)
			   (mv-let (res2 fn-var-decl3 num3)
				   (replace-rec-fn-params params fn-lst-with-type fn-var-decl2 num2)
				   (mv (cons (list 'lambda formals res) res2)
				       fn-var-decl3
				       num3))))
		 ))
	      ((and (not (lambdap fn0)) (consp fn0))
	       (mv-let (res fn-var-decl2  num2)
		       (replace-rec-fn fn0 fn-lst-with-type fn-var-decl num)
		       (mv-let (res2 fn-var-decl3 num3)
			       (replace-rec-fn-params params fn-lst-with-type fn-var-decl2 num2)
			       (mv (cons res res2) fn-var-decl3 num3))))
	      (t (prog2$ (er hard 'top-level "Error(function): Can not pattern match, ~q0" expr)
			 (mv expr fn-var-decl  num)))
	      )))
	(t (prog2$ (er hard? 'top-level "Error(function): Strange expr, ~q0" expr)
		   (mv expr fn-var-decl  num)))))

)

;; create-let-decl
(defun create-let-decl (namelist typelist)
  (if (endp namelist)
      nil
    (cons (list (car typelist) (car namelist))
          (create-let-decl (cdr namelist) (cdr typelist))))
  )

;; expand-fn
(defun expand-fn (expr fn-lst-with-type fn-level let-expr let-type new-hypo state)
  "expand-fn: takes an expr and a list of functions, unroll the expression. fn-lst is a list of possible functions for unrolling."
  (let ((fn-lst (split-fn-from-type fn-lst-with-type)))
    (let ((reformed-let-expr (reform-let let-expr)))
      (let ((fn-level-lst (initial-level fn-lst fn-level)))
        (mv-let (res-expr1 res-num1)
                (expand-fn-help (rewrite-formula expr reformed-let-expr) fn-lst fn-level-lst fn-lst nil 0 state)
                (mv-let (res-expr res-fn-var-decl res-num)
                        (replace-rec-fn res-expr1 fn-lst-with-type nil res-num1)
                        (let ((rewritten-expr
                               (augment-formula (rewrite-formula res-expr reformed-let-expr)
                                                (create-let-decl (assoc-get-value reformed-let-expr) let-type)
                                                new-hypo)))
                          (let ((res (rewrite-formula res-expr1 reformed-let-expr)))
                            (let ((orig-param (extract-orig-param res)))
                              (mv rewritten-expr res res-num orig-param res-fn-var-decl))))))))))
