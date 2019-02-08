; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; default-hint.lisp
;;;
;;; This book contains the definition of several default hints we will
;;; be using to control nonlinear arithmetic.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dynamic-e-d")

; Matt K. mod, Jan. 2019: The following is needed for the #+acl2-devel build,
; since nonlinearp-default-hint defined below is a :logic mode function that
; calls observation-cw.
(include-book "system/observation1-cw" :dir :system)

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; When things have stabilized under simplification, enable non-linear
;;; arithmetic for one round (goal being simplified) only.

(defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)

; Guard change for tau after ACL2 Version 5.0 by J Moore:

; The hideous guard below is just the expected guard for

;  (access rewrite-constant
;          (access prove-spec-var pspv :rewrite-constant)
;          :nonlinearp)

; where, by ``expected,'' we mean to exclude the pathological cases allowing
; car and cdr to be applied to nil.  Unfortuantely, the guard must be changed
; every time the locations of the two fields change in their respective
; defrecs.  To get it, translate the access expression above and then write a
; consp of every subterm but the top-most.  In addition, you must also change
; the guard on the definition of this function where it is found -- twice! --
; in books/hints/basic-tests.lisp.

  (declare
   (xargs
    :guard
    (and (consp pspv)
         (consp (car pspv))
         (consp (car (car pspv)))
         (consp (cdr (car (car pspv))))
         (consp (cdr (cdr (car (car pspv)))))
         (consp (cdr (cdr (cdr (car (car pspv))))))
         (consp (cdr (cdr (cdr (cdr (car (car pspv)))))))
         (consp (cdr (cdr (cdr (cdr (cdr (car (car pspv))))))))
         (consp (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))
         (consp (car (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))))))

  (cond (stable-under-simplificationp
         (if (not (access rewrite-constant
			       (access prove-spec-var pspv :rewrite-constant)
			       :nonlinearp))
	   (prog2$
	    (observation-cw
             'nonlinearp-default-hint
             "We now enable non-linear arithmetic.")
	    '(:computed-hint-replacement t
					 :nonlinearp t))
           nil))
        ((access rewrite-constant
		      (access prove-spec-var pspv :rewrite-constant)
		      :nonlinearp)
         (if (and (consp hist)
		  (consp (car hist))
		  ;; Without this, we would loop forever.  But
		  ;; whenever I try to write an explanation, I get
		  ;; confused about why it works.  I stumbled across
		  ;; this by trial and error and observing the output
		  ;; of tracing.  Some day I should figure out what I
		  ;; am doing.
		  (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
	     (prog2$
              (observation-cw
               'nonlinearp-default-hint
               "We now disable non-linear arithmetic.")
              '(:computed-hint-replacement t
                                           :nonlinearp nil))
           nil))
        (t
         nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; I should document this better.

;;; Note: Consider leaving prefer-positive-exponents enabled.
;;; But, how do I ensure that this is not undone by some user-given
;;; :in-theory hint?

(defun arithmetic-default-hint (stable-under-simplificationp hist last-hint-used)
;  (declare (xargs :guard (and (consp pspv)
;			      (consp (car pspv))
;			      (consp (caar pspv))
;			      (consp (cdaar pspv))
;			      (consp (car (cdaar pspv)))
;			      (consp (caar (cdaar pspv)))
;			      (consp (cdaar (cdaar pspv)))
;			      (alistp (cddaar (cdaar pspv))))))
  (declare (xargs :mode :program))
  (cond (stable-under-simplificationp
	 (cond ((equal last-hint-used nil)
		(prog2$
		 (observation-cw
                  'arithmetic-default-hint
                  "We now enable prefer-positive-exponents.")
		 (let ((e/d '(((:REWRITE prefer-positive-exponents-scatter-exponents-equal)
			       (:REWRITE prefer-positive-exponents-scatter-exponents-<)
			       (:rewrite PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2)
			       (:REWRITE |(expt x (+ m n))|)
			       (:REWRITE |(expt x (+ m n)) non-zero (+ m n)|)
			       (:REWRITE |(expt x (+ m n)) non-zero x|)
			       ;;(:REWRITE |(expt x (+ m n)) non-pos m and n|)
			       ;;(:REWRITE |(expt x (+ m n))) non-neg m and n|)
			       (:REWRITE normalize-factors-scatter-exponents)
			       (:REWRITE simplify-products-scatter-exponents-equal)
			       (:REWRITE simplify-products-scatter-exponents-<))
			      ((:REWRITE normalize-factors-gather-exponents)
			       (:REWRITE simplify-products-gather-exponents-equal)
			       (:REWRITE simplify-products-gather-exponents-<)))))
		   `(:computed-hint-replacement ((arithmetic-default-hint
						  stable-under-simplificationp
						  hist
						  'prefer-positive-addends))
						;; I am surprised that a quote
						;; is not needed here, i.e.,
						;; :dynamic-e/d ',e/d
						:dynamic-e/d ,e/d
						:nonlinearp nil))))
	       ((equal last-hint-used 'prefer-positive-addends)
		(prog2$
                 (observation-cw
                  'arithmetic-default-hint
                  "We now enable non-linear arithmetic.")
		 `(:computed-hint-replacement ((arithmetic-default-hint
						stable-under-simplificationp
						hist 'non-linear-arithmetic))
					      :nonlinearp t)))
	       (t
		nil)))
        ((and (equal last-hint-used 'non-linear-arithmetic)
	      (consp hist)
	      (consp (car hist))
	      (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
	 (prog2$
          (observation-cw
           'arithmetic-default-hint
           "We now disable non-linear arithmetic and return to the earlier ~
            enabled theory.")
	  (let ((e/d '(((:REWRITE normalize-factors-gather-exponents)
			(:REWRITE simplify-products-gather-exponents-equal)
			(:REWRITE simplify-products-gather-exponents-<))
		       ((:REWRITE prefer-positive-exponents-scatter-exponents-equal)
			(:REWRITE prefer-positive-exponents-scatter-exponents-<)
			(:rewrite PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2)
			(:REWRITE |(expt x (+ m n))|)
			(:REWRITE |(expt x (+ m n)) non-zero (+ m n)|)
			(:REWRITE |(expt x (+ m n)) non-zero x|)
			;;(:REWRITE |(expt x (+ m n)) non-pos m and n|)
			;;(:REWRITE |(expt x (+ m n))) non-neg m and n|)
			(:REWRITE normalize-factors-scatter-exponents)
			(:REWRITE simplify-products-scatter-exponents-equal)
			(:REWRITE simplify-products-scatter-exponents-<)))))
	  `(:computed-hint-replacement ((arithmetic-default-hint
					 stable-under-simplificationp
					 hist nil))
				       ;; I am surprised that a quote
				       ;; is not needed here, i.e.,
				       ;; :dynamic-e/d ',e/d
				       :dynamic-e/d ,e/d
				       :nonlinearp nil))))
        (t
         nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; I would like to experiment with :or hints.  But I cannot use
;;; :computed-hint-replacement within an :or hint, so I need to use
;;; the same replacement on both branches.  Therefore, I need to keep
;;; track of where I am some other way than passing around extra
;;; flags.  Luckily, the goal spec gives it away.

(defun first-inductive-subgoal-p (id)
  (declare (xargs :guard (and (consp id)
			      (consp (cdr id)))))
  (and (< 1 (len (car id)))       ; We are inducting
       (equal 1 (len (cadr id)))  ; No splits
       (equal 0 (cddr id))))

(defun branch-taken1 (x ans)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x)
	 ans)
	((equal (car x) 'D1)
	 (branch-taken1 (cdr x) 1))
	((equal (car x) 'D2)
	 (branch-taken1 (cdr x) 2))
	(t
	 (branch-taken1 (cdr x) ans))))

(defun branch-taken (id)
  (declare (xargs :guard (and (consp id)
			      (consp (cdr id))
			      (true-listp (cadr id)))))
  (branch-taken1 (cadr id) nil))

(defun nonlinearp-default-hint++ (id stable-under-simplificationp hist last-hint-used)
;  (declare (xargs :guard (and (consp id)
;			      (consp (cdr id))
;			      (true-listp (cadr id))
;			      (consp pspv)
;			      (consp (car pspv))
;			      (consp (caar pspv))
;			      (consp (cdaar pspv))
;			      (consp (car (cdaar pspv)))
;			      (consp (caar (cdaar pspv)))
;			      (consp (cdaar (cdaar pspv)))
;			      (alistp (cddaar (cdaar pspv))))))
  (declare (xargs :mode :program))
  (cond	 ;;(first-inductive-subgoal-p id)
   ;;...)
   (stable-under-simplificationp
    (cond ((equal last-hint-used nil)
	   (prog2$
            (observation-cw
             'nonlinearp-default-hint++
             "Branch.")
	    (let ((e/d '(((:REWRITE prefer-positive-exponents-scatter-exponents-equal)
			  (:REWRITE prefer-positive-exponents-scatter-exponents-<)
			  (:rewrite PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2)
			  (:REWRITE |(expt x (+ m n))|)
			  (:REWRITE |(expt x (+ m n)) non-zero (+ m n)|)
			  (:REWRITE |(expt x (+ m n)) non-zero x|)
			  ;;(:REWRITE |(expt x (+ m n)) non-pos m and n|)
			  ;;(:REWRITE |(expt x (+ m n))) non-neg m and n|)
			  (:REWRITE normalize-factors-scatter-exponents)
			  (:REWRITE simplify-products-scatter-exponents-equal)
			  (:REWRITE simplify-products-scatter-exponents-<))
			 ((:REWRITE normalize-factors-gather-exponents)
			  (:REWRITE simplify-products-gather-exponents-equal)
			  (:REWRITE simplify-products-gather-exponents-<)))))
	    `(:computed-hint-replacement ((nonlinearp-default-hint++ id
								     stable-under-simplificationp
								     hist 'check-branch-taken))
					 ;; I am surprised that a quote
					 ;; is not needed here, i.e.,
					 ;; :dynamic-e/d ',e/d
					 :or ((:dynamic-e/d ,e/d
					       :nonlinearp nil)
					      (:nonlinearp t))))))
	  ((equal last-hint-used 'prefer-positive-exponents)
	   (prog2$
            (observation-cw
             'nonlinearp-default-hint++
             "Prefer-positive-exponents.")
	    `(:computed-hint-replacement ((nonlinearp-default-hint++ id
								     stable-under-simplificationp
								     hist 'non-linear-arithmetic))
					 :nonlinearp t)))
	  ((equal last-hint-used 'recycle)
	   (prog2$
            (observation-cw
             'nonlinearp-default-hint++
             "Recycle.")
	    `(:computed-hint-replacement ((nonlinearp-default-hint++ id
								     stable-under-simplificationp
								     hist 'non-linear-arithmetic))
					 :nonlinearp t)))
	  (t
	   nil)))
   ((equal last-hint-used 'check-branch-taken)
    (let ((branch-taken (branch-taken id)))
      (cond ((equal branch-taken 2)
	     (prog2$
              (observation-cw
               'nonlinearp-default-hint++
               "Check-branch-taken prefer-positive-exponents.")
	      `(:computed-hint-replacement ((nonlinearp-default-hint++ id
								       stable-under-simplificationp
								       hist 'prefer-positive-exponents))
					   :no-op t)))
	    ((equal branch-taken 1)
	     (prog2$
              (observation-cw
               'nonlinearp-default-hint++
               "Check-branch-taken non-linear-arithmetic.")
	      `(:computed-hint-replacement ((nonlinearp-default-hint++ id
								       stable-under-simplificationp
								       hist 'recycle))
					   :nonlinearp nil)))
	    (t
             (cw "~%~%~ [Note: Computed hint error --- seemingly impossible ~
                  case reached in nonlinearp-default-hint++.  Perhaps there ~
                  are two or more :OR hints interacting in unexpected ways.  ~
                  We do not know what to do here, and so are defaulting to ~
                  doing nothing.~%~%")))))
   ((and (equal last-hint-used 'non-linear-arithmetic)
	 (consp hist)
	 (consp (car hist))
	 (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
    (prog2$
     (observation-cw
      'nonlinearp-default-hint++
      "Non-linear-arithmetic.")
     `(:computed-hint-replacement ((nonlinearp-default-hint++ id
							      stable-under-simplificationp
							      hist 'recycle))
				  :nonlinearp nil)))
   (t
    nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The rest of this file is not used at the present.  I leave it here
;;; so I will not have to duplicate the work later, in case I ever decide
;;; to implement the strategies hinted at below.
#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Pieces of code for implementing a computed hint to rewrite equalities
;;; between boolean expressions to iff, e.g.,
;;; (equal (pred-1 ... ...)
;;;        (pred-2 ...))
;;; ==>
;;; (iff (pred-1 ... ...)
;;;      (pred-2 ...))

(defun boolean-fn-p (fn ens wrld)
  (declare (xargs :mode :program))
  (ts-booleanp (fcons-term fn (formals fn wrld)) ens wrld))

(defun equality-between-booleans-present-in-term (term ens wrld)
  (declare (xargs :mode :program))
  (and (equal (fn-symb term) 'EQUAL)
       (boolean-fn-p (car (cadr term)) ens wrld)
       (boolean-fn-p (car (caddr term)) ens wrld)))

(defun equality-between-booleans-present-in-goal-1 (goal ens wrld)
  (declare (xargs :mode :program))
  (if (endp goal)
      nil
    (or (equality-between-booleans-present-in-term (car goal) ens wrld)
	(equality-between-booleans-present-in-goal-1 (cdr goal) ens wrld))))

(defun equality-between-booleans-present-in-goal (goal pspv wrld)
  (declare (xargs :mode :program))
  (equality-between-booleans-present-in-goal-1 goal
					       (access rewrite-constant
						       (access prove-spec-var
							       pspv
							       :rewrite-constant)
						       :current-enabled-structure)
					       wrld))

|#

;; Put it up to eleven
