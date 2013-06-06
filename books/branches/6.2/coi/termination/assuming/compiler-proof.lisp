#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;; consider adding extra termination/measure functions to foo

;;
;; Prove Mcarthy's 91 function (?) assuming termination.
;;

;; For talk:
;;
;; 1) Present the generic theory of defxch and (possibly) defminterm.
;;
;; 2) Present an overview of continuation transformation.
;;
;; 3) Discuss generic interpreter
;;
;; 4) Challenge: new recursive scheme

(include-book "coi/defpun/defminterm" :dir :system)
(include-book "coi/defpun/ack" :dir :system)
(include-book "coi/nary/nary" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)

;; ===================================================================
;;
;; Generic continuation example (foo)
;;
;; ===================================================================

(encapsulate
    (
     ((foo-done *) => *)
     ((foo-tail *) => *)
     ((foo-base-step *) => *)
     ((foo-stk-step * *) => *)
     ((foo-step *) => *)
     ((foo-step-tail *) => *)
     ((foo-cont *) => *)
     ((foo-stk_measure * *) => *)
     ((foo-stk_terminates * *) => *)
     ;;((foo-x_terminates *) => *)
     ;;((foo-x_measure *) => *)

     )
  
  (local
   (encapsulate
       ()
     (defstub foo-done (arg) nil)
     (defstub foo-tail (arg) nil)
     (defstub foo-base-step (arg) nil)
     (defstub foo-stk-step (val cont) nil)
     (defstub foo-step (arg) nil)
     (defstub foo-step-tail (arg) nil)
     (defstub foo-cont (arg) nil)

     #+joe
     (defun foo-x_terminates (arg) 
       (declare (ignore arg))
       t)

     #+joe
     (defun foo-x_measure (arg)
       (declare (ignore arg))
       0)

     ;; With something like this definition ..
     
     (defminterm foo-stk (arg stk)
       (if (or (and (not (consp stk))
		    (foo-done arg)))
	   (foo-base-step arg)
	 (if (foo-done arg)
	     (let ((arg (foo-stk-step (foo-base-step arg) (car stk))))
	       (foo-stk arg (cdr stk)))
	   (if (foo-tail arg)
	       (foo-stk (foo-step-tail arg) stk)
	     (foo-stk (foo-step arg) (cons (foo-cont arg) stk))))))
     
     ))
  
  #+joe
  (defthm natp-foo-x_measure
    (<= 0 (foo-x_measure arg))
    :rule-classes (:linear))

  (defthm foo-stk_measure-definition
    (implies
     (foo-stk_terminates arg stk)
     (equal (foo-stk_measure arg stk)
	    (if (and (not (consp stk))
		     (foo-done arg))
		(o)
	      (if (foo-done arg)
		  (let ((arg (foo-stk-step (foo-base-step arg) (car stk))))
		    (+ 1 #+joe(foo-x_measure (foo-base-step arg))
		       (foo-stk_measure arg (cdr stk))))
		(if (foo-tail arg)
		    (1+ (foo-stk_measure (foo-step-tail arg) stk))
		  (1+ (foo-stk_measure (foo-step arg)
				       (cons (foo-cont arg) stk))))))))
    :rule-classes (:definition))

  (defthm natp-foo-stk_measure
    (natp (foo-stk_measure arg stk))
    :rule-classes ((:forward-chaining
		    :trigger-terms ((foo-stk_measure arg stk)))))

  (defthm foo-stk_terminates-definition
    (and
     (implies
      (and (foo-done arg) (not (consp stk)))
      (iff (foo-stk_terminates arg stk) t))
     (implies
      (and (syntaxp (symbolp arg))
	   (not (foo-done arg)))
      (iff (foo-stk_terminates arg stk)
	   (if (foo-tail arg) (foo-stk_terminates (foo-step-tail arg) stk)
	     (foo-stk_terminates (foo-step arg)
				 (cons (foo-cont arg) stk)))))
     (implies
      (and (syntaxp (symbolp arg))
	   (consp stk))
      (iff (foo-stk_terminates arg stk)
	   (if (foo-done arg)
	       (let ((arg (foo-stk-step (foo-base-step arg)
					(car stk))))
		 (and #+joe(foo-x_terminates (foo-base-step arg))
		      (foo-stk_terminates arg (cdr stk))))
	     (if (foo-tail arg)
		 (foo-stk_terminates (foo-step-tail arg) stk)
	       (foo-stk_terminates (foo-step arg)
				   (cons (foo-cont arg) stk))))))))
  
  )
	

(defun foo-stk (arg stk)
  (declare (xargs :verify-guards nil
		  :measure (foo-stk_measure arg stk)))
  (if (foo-stk_terminates arg stk)
      (if (and (not (consp stk))
	       (foo-done arg))
	  (foo-base-step arg)
	(if (foo-done arg)
	    (let ((arg (foo-stk-step (foo-base-step arg)
				     (car stk))))
	      (foo-stk arg (cdr stk)))
	  (if (foo-tail arg)
	      (foo-stk (foo-step-tail arg) stk)
	    (foo-stk (foo-step arg)
		     (cons (foo-cont arg) stk)))))
    (foo-base-step arg)))

(defun foo-stk_induction (arg stk1 stk2)
  (declare (xargs :measure (foo-stk_measure arg stk1)))
  (if (foo-stk_terminates arg stk1)
      (if (and (not (consp stk1))
	       (foo-done arg))
	  (list stk1 stk2)
	(if (foo-done arg)
	    (let ((arg (foo-stk-step (foo-base-step arg)
				     (car stk1))))
	      (foo-stk_induction arg (cdr stk1) (cdr stk2)))
	  (if (foo-tail arg)
	      (foo-stk_induction (foo-step-tail arg) stk1 stk2)
	    (foo-stk_induction
	     (foo-step arg)
	     (cons (foo-cont arg) stk1)
	     (cons (foo-cont arg) stk2)))))
    (list stk1 stk2)))
  
(defthm foo-stk_terminates_from_foo-stk_terminates
  (implies (and (foo-stk_terminates arg s)
		(head-equal r s)
		(<= (len r) (len s)))
	   (foo-stk_terminates arg r))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :induct (foo-stk_induction arg s r))))

(encapsulate
    ()
  
  (local
   (encapsulate
       ()
     
     (defthm foo-stk_terminates_list_equal
       (implies (and (foo-stk_terminates arg s)
		     (list-equal r s))
		(foo-stk_terminates arg r)))
     
     (defthm not_foo-stk_terminates_list_equal
       (implies (and (not (foo-stk_terminates arg r))
		     (list-equal r s))
		(not (foo-stk_terminates arg s))))
     
     ))
  
  (defcong list-equal iff (foo-stk_terminates arg r) 2)
  
  )

(defthm foo-stk_terminates_nil
  (implies (and (foo-stk_terminates arg s)
		(syntaxp (not (quotep s))))
	   (foo-stk_terminates arg nil))
  :rule-classes (:forward-chaining))
  
(defcong list-equal equal (foo-stk arg r) 2
  :hints (("goal" :induct (foo-stk_induction arg r r-equiv))))
  


(defthmd car-append
  (equal (car (append x y))
	 (if (consp x)
	     (car x)
	   (car y)))
  :hints (("Goal" :in-theory (enable append))))


(defthmd foo-stk_terminates_on_foo-stk
  (implies
   (consp r)
   (iff (foo-stk_terminates arg (append s r))
	(and
	 (foo-stk_terminates (foo-stk-step (foo-stk arg s) (car r))  (cdr r))
	 #+joe(foo-x_terminates (foo-stk-step (foo-stk arg s) (car r)))
	 (foo-stk_terminates arg s))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :do-not-induct t
	   :in-theory (enable car-append)
	   :induct (foo-stk arg s))))

(defthm foo-stk_termiantes_reduction
  (iff (foo-stk_terminates arg (cons a r))
       (and (foo-stk_terminates (foo-stk-step (foo-stk arg nil) a) r)
	    (foo-stk_terminates arg nil)))
  :hints (("goal" :in-theory '(car-cons cdr-cons append)
	   :use (:instance foo-stk_terminates_on_foo-stk
			   (s nil)
			   (r (cons a r))))))
  
(defthm foo-stk_measure_bound
  (implies
   (foo-stk_terminates arg stk)
   (< 0 (foo-stk_measure arg stk)))
  :rule-classes (:linear)
  :hints (("goal" :do-not '(eliminate-destructors generalize)
	   :do-not-induct t
	   :induct (foo-stk arg stk))))

(defthm foo-stk_measure_on_foo-stk
  (implies
   (and
    (consp r)
    (foo-stk_terminates arg (append s r)))
   (equal (foo-stk_measure arg (append s r))
	  (+ (foo-stk_measure arg s)
	     (foo-stk_measure (foo-stk-step (foo-stk arg s) (car r)) (cdr r)))))
  :rule-classes nil
  :hints (("goal" :do-not '(eliminate-destructors generalize)
	   :do-not-induct t
	   :induct (foo-stk arg s))))
  
(defthm foo-stk_measure_reduction
  (implies
   (foo-stk_terminates arg (cons a r))
   (equal (foo-stk_measure arg (cons a r))
	  (+ (foo-stk_measure arg nil)
	     (foo-stk_measure (foo-stk-step (foo-stk arg nil) a) r))))
  :hints (("goal" :use (:instance foo-stk_measure_on_foo-stk
				  (s nil)
				  (r (cons a r))))))

(defthm foo-stk_on_foo-stk
  (implies
   (and
    (consp r)
    (foo-stk_terminates arg (append s r)))
   (equal (foo-stk arg (append s r))
	  (foo-stk (foo-stk-step (foo-stk arg s) (car r)) (cdr r))))
  :rule-classes nil
  :hints (("goal" :induct (foo-stk arg s))))

(defthm foo-stk_reduction
  (implies
   (foo-stk_terminates arg (cons a r))
   (equal (foo-stk arg (cons a r))
	  (foo-stk (foo-stk-step (foo-stk arg nil) a) r)))
  :hints (("goal" :use (:instance foo-stk_on_foo-stk
				  (s nil)
				  (r (cons a r))))))

(defun foo (arg)
  (foo-stk arg nil))

(defun foo_terminates (arg)
  (foo-stk_terminates arg nil))

(defun foo_measure (arg)
  (foo-stk_measure arg nil))

(defthm foo_spec
  (implies
   (foo_terminates arg)
   (equal (foo arg)
	  (if (foo-done arg) (foo-base-step arg)
	    (if (foo-tail arg)
		(foo (foo-step-tail arg))
	      (foo (foo-stk-step (foo (foo-step arg)) (foo-cont arg)))))))
  :hints (("Goal" :expand (foo-stk arg nil)))
  :rule-classes (:definition))

(defthm foo_measure_spec
  (implies
   (foo_terminates arg)
   (equal (foo_measure arg)
	  (if (foo-done arg) (O)
	    (if (foo-tail arg)
		(1+ (foo_measure (foo-step-tail arg)))
	      (+ 1 (foo_measure (foo-step arg))
		 (foo_measure (foo-stk-step (foo (foo-step arg)) (foo-cont arg))))))))
  :hints (("Goal" :expand (FOO-STK_MEASURE arg nil)))
  :rule-classes (:definition))


(defthm foo_measure-bound
  (implies
   (foo_terminates arg)
   (< 0 (foo_measure arg)))
  :rule-classes (:linear))


(defthm foo_terminates_spec
  (and
   (implies
    (foo-done arg)
    (iff (foo_terminates arg) t))
   (implies
    (and
     (not (foo-done arg))
     (foo-tail arg))
    (iff (foo_terminates arg)
	 (foo_terminates (foo-step-tail arg))))
   (implies
    (and
     (not (foo-done arg))
     (not (foo-tail arg)))
    (iff (foo_terminates arg)
	 (and
	  (foo_terminates (foo-step arg))
	  (foo_terminates (foo-stk-step (foo (foo-step arg)) (foo-cont arg)))))))
  :hints (("Goal" :cases ((foo-done arg))
	   :expand (:free (x) (hide x))
	   :in-theory (e/d 
		       nil ;(foo_terminates)
		       (foo_measure_spec
			foo_spec))
	   :do-not `(preprocess))))

(in-theory (disable foo_terminates foo foo_measure))

(defun true (x)
  (declare (ignore x))
  t)

(defthmd foo_true
  (true (foo arg)))

(in-theory (disable true (true) (:type-prescription true)))

;; ===================================================================
;;
;; Generic spec interpreter (goo)
;;
;; ===================================================================

(SET-IRRELEVANT-FORMALS-OK t)
(set-ignore-ok t)

(defun rev (x) (revappend x nil))

(defun vstk-pop (stk)
  (let ((top (car stk))
	(stk (cdr stk)))
    (mv (car top)
	(cadr top)
	(caddr top)
	(cadddr top)
	stk)))

(defun vstk-push (args fn spec vals vstk)
  (cons (list args fn spec vals)
	vstk))

(defun spec-args (spec val)
  (list val (car spec) (cdr spec) nil nil))

(encapsulate
    (
     ((goo-spec) => *)
     ((goo-comp-step * * *) => *)
     ((goo-base-step *) => *)
     ((goo-done *) => *)
     ((goo-stk-1_terminates * *) => *)
     ((goo-stk-1_measure * *) => *)
     )

  (local
   (encapsulate
       ()

     (defund goo-spec ()
       `(a (b (c) (d)) (e)))
     
     (defund goo-comp-step (fn args vals)
       `(,fn ,args ,@vals))
     
     (defund goo-base-step (args)
       `(goo ,args))
     
     (defund goo-done (args)
       (consp args))
     
     (defminterm goo-stk-1 (list stk)
       (let ((args (car list))
	     (fn   (cadr list))
	     (spec (caddr list))
	     (vals (cadddr list))
	     (vstk (cadddr (cdr list))))
	 ;; base
	 (if (and 
	      (or (goo-done args)
		  (not (consp spec)))
	      (not (consp vstk))
	      (not (consp stk)))
	     ;; (foo-base-step arg)
	     (if (goo-done args)
		 (goo-base-step args)
	       (goo-comp-step fn args (rev vals)))
	   (if (and 
		(or (goo-done args)
		    (not (consp spec)))
		(not (consp vstk)))
	       (let ((arg (let ((val 
				 ;; (foo-base-step arg)
				 (if (goo-done args) (goo-base-step args)
				   (goo-comp-step fn args (rev vals)))))
			    ;; (foo-stk-step (foo-base-step arg) (car stk)
			    (let ((vstk (car stk)))
			      (met ((args fn spec vals vstk) (vstk-pop vstk))
				(list args fn spec (cons val vals) vstk))))))
		 (goo-stk-1 arg (cdr stk)))
	     (if ;; (not (foo-tail arg))
		 (or (goo-done args)
		     (not (consp spec)))
		 ;; (foo-step arg)
		 (let ((val (if (goo-done args) (goo-base-step args)
			      (goo-comp-step fn args (rev vals)))))
		   (let ((stk (cons vstk stk)))
		     (goo-stk-1 (spec-args (goo-spec) val) stk)))
	       ;; (foo-step-tail arg)
	       (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
		 (goo-stk-1 (list args (caar spec) (cdar spec) nil vstk) stk)))))))

     ))

  (defthm natp-goo-stk-1_measure
    (natp (goo-stk-1_measure arg stk))
    :rule-classes ((:forward-chaining
		    :trigger-terms ((goo-stk-1_measure arg stk)))))

  (defthm goo-stk-1_measure_definition
    (implies
     (goo-stk-1_terminates list stk)
     (equal (goo-stk-1_measure list stk)
	    (let ((args (car list))
		  (fn   (cadr list))
		  (spec (caddr list))
		  (vals (cadddr list))
		  (vstk (cadddr (cdr list))))
	      ;; base
	      (if (and 
		   (or (goo-done args)
		       (not (consp spec)))
		   (not (consp vstk))
		   (not (consp stk)))
		  ;; first
		  (o)
		(if (and 
		     (or (goo-done args)
			 (not (consp spec)))
		     (not (consp vstk)))
		    ;; second
		    (let ((arg (let ((val 
				      ;; (foo-base-step arg)
				      (if (goo-done args) (goo-base-step args)
					(goo-comp-step fn args (rev vals)))))
				 ;; (foo-stk-step (foo-base-step arg) (car stk)
				 (let ((vstk (car stk)))
				   (met ((args fn spec vals vstk) (vstk-pop vstk))
				     (list args fn spec (cons val vals) vstk))))))
		      (+ 1 (goo-stk-1_measure arg (cdr stk))))
		  (if ;; (not (foo-tail arg))
		      (or (goo-done args)
			  (not (consp spec)))
		      ;; (foo-step arg)
		      ;; third
		      (let ((val (if (goo-done args) (goo-base-step args)
				   (goo-comp-step fn args (rev vals)))))
			(let ((stk (cons vstk stk)))
			  (+ 1 (goo-stk-1_measure (spec-args (goo-spec) val) stk))))
		    ;; (foo-step-tail arg)
		    ;; fourth
		    (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
		      (+ 1 (goo-stk-1_measure (list args (caar spec) (cdar spec) nil vstk) stk)))))))))
    :rule-classes (:definition))

  (defthm goo-stk-1_terminates_defintion
    (and

     ;; Two base cases ..

     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(and 
	 (goo-done args)
	 (not (consp vstk))
	 (not (consp stk))))
      (goo-stk-1_terminates list stk))
     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(and 
	 (not (consp spec))
	 (not (consp vstk))
	 (not (consp stk))))
      (goo-stk-1_terminates list stk))

     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(AND (NOT (CONSP SPEC))
	     (NOT (CONSP VSTK))
	     (CONSP STK)))
      (iff (goo-stk-1_terminates list stk)
	   (let ((args (car list))
		 (fn   (cadr list))
		 (spec (caddr list))
		 (vals (cadddr list))
		 (vstk (cadddr (cdr list))))
	     (let ((arg (let ((val 
				      ;; (foo-base-step arg)
				      (if (goo-done args) (goo-base-step args)
					(goo-comp-step fn args (rev vals)))))
				 ;; (foo-stk-step (foo-base-step arg) (car stk)
				 (let ((vstk (car stk)))
				   (met ((args fn spec vals vstk) (vstk-pop vstk))
				     (list args fn spec (cons val vals) vstk))))))
	       (goo-stk-1_terminates arg (cdr stk))))))

     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(AND (GOO-DONE ARGS)
              (NOT (CONSP VSTK))
              (CONSP STK)))
      (iff (goo-stk-1_terminates list stk)
	   (let ((args (car list))
		 (fn   (cadr list))
		 (spec (caddr list))
		 (vals (cadddr list))
		 (vstk (cadddr (cdr list))))
	     (let ((arg (let ((val 
				      ;; (foo-base-step arg)
				      (if (goo-done args) (goo-base-step args)
					(goo-comp-step fn args (rev vals)))))
				 ;; (foo-stk-step (foo-base-step arg) (car stk)
				 (let ((vstk (car stk)))
				   (met ((args fn spec vals vstk) (vstk-pop vstk))
				     (list args fn spec (cons val vals) vstk))))))
	       (goo-stk-1_terminates arg (cdr stk))))))


     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(AND (NOT (CONSP SPEC)) (CONSP VSTK)))
      (iff (goo-stk-1_terminates list stk)
	   (let ((args (car list))
		 (fn   (cadr list))
		 (spec (caddr list))
		 (vals (cadddr list))
		 (vstk (cadddr (cdr list))))
	     (let ((val (if (goo-done args) (goo-base-step args)
				   (goo-comp-step fn args (rev vals)))))
			(let ((stk (cons vstk stk)))
			  (goo-stk-1_terminates (spec-args (goo-spec) val) stk))))))

     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(AND (GOO-DONE ARGS) (CONSP VSTK)))
      (iff (goo-stk-1_terminates list stk)
	   (let ((args (car list))
		 (fn   (cadr list))
		 (spec (caddr list))
		 (vals (cadddr list))
		 (vstk (cadddr (cdr list))))
	     (let ((val (if (goo-done args) (goo-base-step args)
				   (goo-comp-step fn args (rev vals)))))
			(let ((stk (cons vstk stk)))
			  (goo-stk-1_terminates (spec-args (goo-spec) val) stk))))))

     (implies
      (let ((args (car list))
	    (fn   (cadr list))
	    (spec (caddr list))
	    (vals (cadddr list))
	    (vstk (cadddr (cdr list))))
	(AND (NOT (GOO-DONE ARGS)) (CONSP SPEC)))
      (iff (goo-stk-1_terminates list stk)
	   (let ((args (car list))
		 (fn   (cadr list))
		 (spec (caddr list))
		 (vals (cadddr list))
		 (vstk (cadddr (cdr list))))
	     (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
	       (goo-stk-1_terminates (list args (caar spec) (cdar spec) nil vstk) stk)))))

     ))
      

  )

(defun goo-stk-1 (list stk)
  (declare (xargs :measure (goo-stk-1_measure list stk)))
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (if (goo-stk-1_terminates list stk)
	;; base
	(if (and 
	     (or (goo-done args)
		 (not (consp spec)))
	     (not (consp vstk))
	     (not (consp stk)))
	    ;; (foo-base-step arg)
	    (if (goo-done args)
		(goo-base-step args)
	      (goo-comp-step fn args (rev vals)))
	  (if (and 
	       (or (goo-done args)
		   (not (consp spec)))
	       (not (consp vstk)))
	      (let ((arg (let ((val 
				;; (foo-base-step arg)
				(if (goo-done args) (goo-base-step args)
				  (goo-comp-step fn args (rev vals)))))
			   ;; (foo-stk-step (foo-base-step arg) (car stk)
			   (let ((vstk (car stk)))
			     (met ((args fn spec vals vstk) (vstk-pop vstk))
			       (list args fn spec (cons val vals) vstk))))))
		(goo-stk-1 arg (cdr stk)))
	    (if ;; (not (foo-tail arg))
		(or (goo-done args)
		    (not (consp spec)))
		;; (foo-step arg)
		(let ((val (if (goo-done args) (goo-base-step args)
			     (goo-comp-step fn args (rev vals)))))
		  (let ((stk (cons vstk stk)))
		    (goo-stk-1 (spec-args (goo-spec) val) stk)))
	      ;; (foo-step-tail arg)
	      (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
		(goo-stk-1 (list args (caar spec) (cdar spec) nil vstk) stk)))))
      (if (goo-done args)
	  (goo-base-step args)
	(goo-comp-step fn args (rev vals))))))

(defun goo (args fn spec vals vstk)
  (goo-stk-1 (list args fn spec vals vstk) nil))

(defun goo_terminates (args fn spec vals vstk)
  (goo-stk-1_terminates (list args fn spec vals vstk) nil))

(defun goo_measure (args fn spec vals vstk)
  (goo-stk-1_measure (list args fn spec vals vstk) nil))

;; (foo-done arg)
(defund goo-done-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (and (or (goo-done args)
	     (not (consp spec)))
	 (not (consp vstk)))))

;; (foo-base-step arg)
(defund goo-base-step-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (if (goo-done args)
	(goo-base-step args)
      (goo-comp-step fn args (rev vals)))))

;; (foo-tail arg)
(defund goo-tail-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (not (or (goo-done args)
	     (not (consp spec))))))
  
;; (foo-stk-step val cont)
(defund goo-stk-step-1 (val cont)
  (let ((vstk cont))
    (met ((args fn spec vals vstk) (vstk-pop vstk))
	 (list args fn spec (cons val vals) vstk))))

;; (foo-step arg)
(defund goo-step-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (let ((val (if (goo-done args) (goo-base-step args)
		 (goo-comp-step fn args (rev vals)))))
      (spec-args (goo-spec) val))))

;; (foo-step-tail arg)
(defund goo-step-tail-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
      (list args (caar spec) (cdar spec) nil vstk))))

;; (foo-cont arg)
(defund goo-cont-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    vstk))

#+joe
(defund fn-spec-test (fn spec)
  (and fn (consp spec)))

(defun goo-call (val)
  (let ((spec (goo-spec)))
    (goo val (car spec) (cdr spec) nil nil)))

(defund goo-1-imp (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (if (or (not (goo_terminates args fn spec vals vstk))
	    (and (or (goo-done args) 
		     (not (consp spec)))
		 (not (consp vstk))))
	(if (goo-done args)
	    (goo-base-step args)
	  (goo-comp-step fn args (rev vals)))
      (if (or (goo-done args)
	      (not (consp spec)))
	  (let ((val (if (goo-done args) (goo-base-step args)
		       (goo-comp-step fn args (rev vals)))))
	    (let ((val (goo-call val)))
	      (met ((args fn spec vals vstk) (vstk-pop vstk))
		(goo args fn spec (cons val vals) vstk))))
	(let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
	  (goo args (caar spec) (cdar spec) nil vstk))))))

(defun goo-imp (args fn spec vals vstk)
  (goo-1-imp (list args fn spec vals vstk)))

(defun goo_terminates-1 (list)
  (goo-stk-1_terminates list nil))

(defun goo_measure-1 (list)
  (goo-stk-1_measure list nil))

(defun goo-1 (list)
  (goo-stk-1 list nil))

;; ===================================================================
;;
;; Unwinding proofs for (goo)
;;
;; ===================================================================

(defthm goo_true
  (true (goo args fn spec vals vstk))
  :hints (("Goal" :use (:functional-instance 
			(:instance foo_true
				   (arg (list args fn spec vals vstk)))
			(foo                goo-1)
			(foo_terminates     goo_terminates-1)
			(foo_measure        goo_measure-1)
			(foo-done           goo-done-1)
			(foo-base-step      goo-base-step-1)
			(foo-stk-step       goo-stk-step-1)
			(foo-step           goo-step-1)
			(foo-step-tail      goo-step-tail-1)
			(foo-cont           goo-cont-1)
			(foo-tail           goo-tail-1)
			(foo-stk            goo-stk-1)
			(foo-stk_terminates goo-stk-1_terminates)
			(foo-stk_measure    goo-stk-1_measure)
			)
	   :in-theory (enable goo-1-imp
			      GOO-DONE-1
			      GOO-BASE-STEP-1
			      GOO_TERMINATES
			      GOO-TAIL-1
			      GOO-STK-STEP-1
			      GOO-STEP-TAIL-1
			      GOO-STEP-1
			      GOO-CONT-1))))

(defthmd goo_definition
  (implies
   (syntaxp (symbolp args))
   (equal (goo args fn spec vals vstk)
	  (if (or (not (goo_terminates args fn spec vals vstk))
		  (and (or (goo-done args) 
			   (not (consp spec)))
		       (not (consp vstk))))
	      (if (goo-done args)
		  (goo-base-step args)
		(goo-comp-step fn args (rev vals)))
	    (if (or (goo-done args)
		    (not (consp spec)))
		(let ((val (if (goo-done args) (goo-base-step args)
			     (goo-comp-step fn args (rev vals)))))
		  (let ((val (goo-call val)))
		    (met ((args fn spec vals vstk) (vstk-pop vstk))
		      (goo args fn spec (cons val vals) vstk))))
	      (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
		(goo args (caar spec) (cdar spec) nil vstk))))))
  :hints (("Goal" :use (:functional-instance 
			(:instance foo_spec
				   (arg (list args fn spec vals vstk)))
			(foo                goo-1)
			(foo_terminates     goo_terminates-1)
			(foo_measure        goo_measure-1)
			(foo-done           goo-done-1)
			(foo-base-step      goo-base-step-1)
			(foo-stk-step       goo-stk-step-1)
			(foo-step           goo-step-1)
			(foo-step-tail      goo-step-tail-1)
			(foo-cont           goo-cont-1)
			(foo-tail           goo-tail-1)
			(foo-stk            goo-stk-1)
			(foo-stk_terminates goo-stk-1_terminates)
			(foo-stk_measure    goo-stk-1_measure)
			)
	   :in-theory (enable goo-1-imp
			      GOO-DONE-1
			      GOO-BASE-STEP-1
			      GOO_TERMINATES
			      GOO-TAIL-1
			      GOO-STK-STEP-1
			      GOO-STEP-TAIL-1
			      GOO-STEP-1
			      GOO-CONT-1))))

(defun goo_terminates-call (val)
  (let ((spec (goo-spec)))
    (goo_terminates val (car spec) (cdr spec) nil nil)))

(defthmd goo_terminates_definition
  (and
   (implies
    (and
     (goo-done args)
     (not (consp vstk)))
    (goo_terminates args fn spec vals vstk))
   (implies
    (and 
     (not (consp spec))
     (not (consp vstk)))
    (goo_terminates args fn spec vals vstk))
   (implies
    (and
     (syntaxp (symbolp args))
     (consp vstk)
     (goo-done args))
    (iff (goo_terminates args fn spec vals vstk)
	 (let ((val0 (goo-base-step args)))
	   (let ((val (goo-call val0)))
	     (met ((args fn spec vals vstk) (vstk-pop vstk))
	       (and (goo_terminates-call val0)
		    (goo_terminates args fn spec (cons val vals) vstk)))))))
   (implies
    (and
     (syntaxp (symbolp args))
     (consp vstk)
     (not (goo-done args))
     (not (consp spec)))
    (iff (goo_terminates args fn spec vals vstk)
	 (let ((val0 (goo-comp-step fn args (rev vals))))
	   (let ((val (goo-call val0)))
	     (met ((args fn spec vals vstk) (vstk-pop vstk))
	       (and (goo_terminates-call val0)
		    (goo_terminates args fn spec (cons val vals) vstk)))))))
   (implies
    (and
     (syntaxp (symbolp args))
     (not (goo-done args))
     (consp spec))
    (iff (goo_terminates args fn spec vals vstk)
	 (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
	   (goo_terminates args (caar spec) (cdar spec) nil vstk))))
   )

  :hints (("Goal" :use (:functional-instance 
			(:instance foo_terminates_spec
				   (arg (list args fn spec vals vstk)))
			(foo                goo-1)
			(foo_terminates     goo_terminates-1)
			(foo_measure        goo_measure-1)
			(foo-done           goo-done-1)
			(foo-base-step      goo-base-step-1)
			(foo-stk-step       goo-stk-step-1)
			(foo-step           goo-step-1)
			(foo-step-tail      goo-step-tail-1)
			(foo-cont           goo-cont-1)
			(foo-tail           goo-tail-1)
			(foo-stk            goo-stk-1)
			;;(foo-hyps           (lambda (list stk) t))
			(foo-stk_terminates goo-stk-1_terminates)
			(foo-stk_measure    goo-stk-1_measure)
			))
	  (and stable-under-simplificationp
	       '(:in-theory (enable goo-1-imp
				    GOO-DONE-1
				    GOO-BASE-STEP-1
				    GOO_TERMINATES
				    GOO-TAIL-1
				    GOO-STK-STEP-1
				    GOO-STEP-TAIL-1
				    GOO-STEP-1
				    GOO-CONT-1)))))

;; We probably could have retained a lot more of the structure here ..
;; we were just cut and pasting from the termination proof.

(defun goo_measure-call (val)
  (let ((spec (goo-spec)))
    (goo_measure val (car spec) (cdr spec) nil nil)))

(defthmd goo_measure_definition
  (implies
   (and
    (syntaxp (symbolp args))
    (goo_terminates args fn spec vals vstk))
   (equal (goo_measure args fn spec vals vstk)
	  (cond
	   ((and
	     (goo-done args)
	     (not (consp vstk))) (o))
	   ((and 
	     (not (consp spec))
	     (not (consp vstk))) (o))
	   ((and
	     (consp vstk)
	     (goo-done args))
	    (let ((val0 (goo-base-step args)))
	      (let ((val (goo-call val0)))
		(met ((args fn spec vals vstk) (vstk-pop vstk))
		  (+ 1 (goo_measure-call val0)
		     (goo_measure args fn spec (cons val vals) vstk))))))
	   ((and
	     (consp vstk)
	     (not (goo-done args))
	     (not (consp spec)))
	    (let ((val0 (goo-comp-step fn args (rev vals))))
	      (let ((val (goo-call val0)))
		(met ((args fn spec vals vstk) (vstk-pop vstk))
		  (+ 1 (goo_measure-call val0)
		     (goo_measure args fn spec (cons val vals) vstk))))))
	   (t
	    (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
	      (+ 1 (goo_measure args (caar spec) (cdar spec) nil vstk)))))))
  :hints (("Goal" :use (:functional-instance 
			(:instance foo_measure_spec
				   (arg (list args fn spec vals vstk)))
			(foo                goo-1)
			(foo_measure        goo_measure-1)
			(foo_terminates     goo_terminates-1)
			(foo-done           goo-done-1)
			(foo-base-step      goo-base-step-1)
			(foo-stk-step       goo-stk-step-1)
			(foo-step           goo-step-1)
			(foo-step-tail      goo-step-tail-1)
			(foo-cont           goo-cont-1)
			(foo-tail           goo-tail-1)
			(foo-stk            goo-stk-1)
			;;(foo-hyps           (lambda (list stk) t))
			(foo-stk_terminates goo-stk-1_terminates)
			(foo-stk_measure    goo-stk-1_measure)
			))
	  (and stable-under-simplificationp
	       '(:in-theory (enable goo-1-imp
				    GOO-DONE-1
				    GOO-BASE-STEP-1
				    GOO_TERMINATES
				    goo_measure
				    GOO-TAIL-1
				    GOO-STK-STEP-1
				    GOO-STEP-TAIL-1
				    GOO-STEP-1
				    GOO-CONT-1)))))

(defthm goo_measure_natp
  (natp (goo_measure args fn spec vals vstk))
  :rule-classes ((:forward-chaining 
		  :trigger-terms ((goo_measure args fn spec vals vstk))))
  :hints (("Goal" :in-theory (enable goo_measure))))

(defthm goo_measure_bound
  (implies
   (goo_terminates args fn spec vals vstk)
   (< 0 (goo_measure args fn spec vals vstk)))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable goo_measure goo_terminates)
	   :use (:functional-instance 
			(:instance foo_measure-bound
				   (arg (list args fn spec vals vstk)))
			(foo                goo-1)
			(foo_measure        goo_measure-1)
			(foo_terminates     goo_terminates-1)
			(foo-done           goo-done-1)
			(foo-base-step      goo-base-step-1)
			(foo-stk-step       goo-stk-step-1)
			(foo-step           goo-step-1)
			(foo-step-tail      goo-step-tail-1)
			(foo-cont           goo-cont-1)
			(foo-tail           goo-tail-1)
			(foo-stk            goo-stk-1)
			(foo-stk_terminates goo-stk-1_terminates)
			(foo-stk_measure    goo-stk-1_measure)
			))))

;;
;; I think this process would be simplified if we didn't push "args"
;; onto vstk .. then vstk would always be constant :)
;;

(in-theory (disable goo-call))
(in-theory (disable goo_terminates-call))
(in-theory (disable goo_measure-call))
(in-theory (disable goo))
(in-theory (disable goo_terminates))
(in-theory (disable goo_measure))
;; In the "real world" we want these enabled.
(in-theory (disable goo_definition))
(in-theory (disable goo_terminates_definition))
(in-theory (disable goo_measure_definition))

;; ===================================================================
;;
;; Now the stage is set to instantiate thse (goo) theorems for
;; specific functions generated by the compiler.
;;
;; ===================================================================

;; The result will be proofs similar to the following:

(defstub pred (x) nil)

#+joe
(defthm open-goo
  (pred (goo args 'a '((b (c) (d)) (e)) nil nil))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
	   :do-not '(generalize eliminate-destructors)
	   :in-theory (e/d (GOO-1-IMP)))))

#|
;; DAG :: What if we wanted to unwind it again?  This seems not to
;; work quite right.  Note in particular that the "hidden" call
;; to foo manifests itself (at least) in the termination conditions.

(defun goo-top_stk (list vstk)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list)))
    (goo args fn spec vals vstk)))

(defund goo-top_stk_terminates (list vstk)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list)))
    (goo_terminates args fn spec vals vstk)))

(defund goo-top_stk_measure (list vstk)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list)))
    (goo_measure args fn spec vals vstk)))

(defun goo-top-1 (list)
  (goo-top_stk list nil))

(defun goo-top_terminates-1 (list)
  (goo-top_stk_terminates list nil))

(defun goo-top_measure-1 (list)
  (goo-top_stk_measure list nil))

;; (foo-done arg)
(defund goo-top-done-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (or (goo-done args)
	(not (consp spec)))))

;; (foo-base-step arg)
(defund goo-top-base-step-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list))
	(vstk (cadddr (cdr list))))
    (if (goo-done args)
	(goo-base-step args)
      (goo-comp-step fn args (rev vals)))))

;; (foo-stk-step val cont)
(defund goo-top-stk-step-1 (val cont)
  (let ((val (goo-call val)))
    (let ((args (car cont))
	  (fn   (cadr cont))
	  (spec (caddr cont))
	  (vals (cadddr cont)))
      (list args fn spec (cons val vals)))))

;; (foo-step arg)
(defund goo-top-step-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list)))
    (list args (caar spec) (cdar spec) nil)))

;; (foo-tail arg)
(defund goo-top-tail-1 (list)
  nil)

;; (foo-step-tail arg)
(defund goo-top-step-tail-1 (list)
  list)

;; (foo-cont arg)
(defund goo-top-cont-1 (list)
  (let ((args (car list))
	(fn   (cadr list))
	(spec (caddr list))
	(vals (cadddr list)))
    (list args fn (cdr spec) vals)))

(defun goo-top-imp-1 (arg)
  (if (goo-top-done-1 arg) (goo-top-base-step-1 arg)
    (goo-top-1 (goo-top-stk-step-1 (goo-top-1 (goo-top-step-1 arg)) (goo-top-cont-1 arg)))))
  
(defun goo-top-imp (args fn spec vals)
  (let ((arg (list args fn spec vals)))
    (goo-top-imp-1 arg)))

(defun goo-top (args fn spec vals)
  (let ((arg (list args fn spec vals)))
    (goo-top-1 arg)))

(defun goo-top_terminates (args fn spec vals)
  (goo-top_terminates-1 (list args fn spec vals)))

(defthm goo-top-reduction
  (implies
   (goo-top_terminates-1 arg)
   (equal (goo-top-1 arg)
	  (goo-top-imp-1 arg)))
  :hints (("Goal" :use (:functional-instance 
			foo_spec
			#+joe(:instance foo_spec (arg (list args fn spec vals)))
			(foo                goo-top-1)
			(foo_terminates     goo-top_terminates-1)
			(foo_measure        goo-top_measure-1)
			(foo-done           goo-top-done-1)
			(foo-base-step      goo-top-base-step-1)
			(foo-stk-step       goo-top-stk-step-1)
			(foo-step           goo-top-step-1)
			(foo-step-tail      goo-top-step-tail-1)
			(foo-cont           goo-top-cont-1)
			(foo-tail           goo-top-tail-1)
			(foo-stk            goo-top_stk)
			(foo-stk_terminates goo-top_stk_terminates)
			(foo-stk_measure    goo-top_stk_measure)
			))
	  (and stable-under-simplificationp
	       '(:in-theory (enable
			     GOO-TOP-DONE-1
			     GOO-STK-1
			     GOO-TOP-BASE-STEP-1
			     GOO-TOP-STK-STEP-1
			     GOO-TOP-CONT-1
			     GOO-TOP-STEP-1
			     GOO-TOP_STK_TERMINATES
			     )
		 :restrict ((OPEN_GOO-STK-1_TERMINATES! ((list (LIST (CAR ARG)
								     (CADR ARG)
								     (CADDR ARG)
								     (CADDDR ARG)
								     STK)))))))))
(in-theory (disable goo-comp-step goo-call))

(mutual-recursion 
 
 
 (defun spec-interpreter (args spec)
   (declare (xargs :measure (acl2-count spec)))
   (if (consp spec)
       (let ((key (car spec)))
	 (let ((vals (spec-list-interpreter args (cdr spec))))
	   (goo-comp-step key args vals)))
     nil))
 
 (defun spec-list-interpreter (args spec)
   (declare (xargs :measure (acl2-count spec)))
   (if (consp spec)
       (cons (let ((args (spec-interpreter args (car spec))))
	       (goo-call (car args)))
	     (spec-list-interpreter args (cdr spec)))
     nil))

 )
 
(defthm
  (equal (goo-1-imp args fn spec vals vstk)
	 
|#

;;
;; Yay.
;;

;;
;; Here is a proof of the essential property of McCarthy's 91 function ..
;;

#+joe
(encapsulate
    ()


(defminterm mc-stk (n stk)
  (if (and (> n 100) (not (consp stk))) (- n 10)
    (if (> n 100)
	(let ((value (- n 10)))
	  (mc-stk value (cdr stk)))
      (mc-stk (+ n 11) (cons nil stk)))))

(defund mc91-terminates (n)
  (mc-stk_terminates n nil))

(defund mc91 (n)
  (mc-stk n nil))

(defund mc91-measure (n)
  (mc-stk_measure n nil))

#+joe
(skip-proofs
 (encapsulate
     ()

   (defthmd mc91-definition
     (equal (mc91 n)
	    (if (mc91-terminates n)
		(if (> n 100) (- n 10)
		  (mc91 (mc91 (+ n 11))))
	      (- n 10)))
     :rule-classes (:definition)
     :hints (("Goal" :in-theory (enable mc91))))
   
   (defthmd mc91-terminates-definition
     (and
      (implies
       (> n 100)
       (mc91-terminates n))
      (implies
       (not (> n 100))
       (iff (mc91-terminates n)
	    (and (mc91-terminates (+ n 11))
		 (mc91-terminates (mc91 (+ n 11)))))))
     :hints (("Goal" :in-theory (enable mc91-terminates))))

   (defthmd mc91-measure-definition
     (implies
      (mc91-terminates n)
      (equal (mc91-measure n)
	     (if (> n 100) (o)
	       (+ (mc91-measure (+ n 11))
		  (mc91-measure (mc91 (+ n 11)))))))
     :rule-classes (:definition)
     :hints (("Goal" :in-theory (enable mc91-measure))))
   
   (defthm mc91-measure-bound
     (implies
      (mc91-terminates n)
      (< 0 (mc91-measure n)))
     :rule-classes (:linear))

   (in-theory (enable mc91-terminates-definition mc91-definition mc91-measure-definition))

   ))
   
(defun mc91-induction (n)
  (declare (xargs :measure (mc91-measure n)))
  (if (mc91-terminates n)
      (if (> n 100) (- n 10)
	(list (mc91-induction (+ n 11))
	      (mc91-induction (mc91 (+ n 11)))))
    (- n 10)))

(in-theory (disable (mc91-terminates) (mc91)))

(defthm mc91-proof
  (implies
   (and
    (integerp n)
    (mc91-terminates n))
   (equal (mc91 n)
	  (if (< n 101) 91 (- n 10))))
  :hints (("Goal" :induct (mc91-induction n)
	   :expand (mc91 n))))

)
