#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|      Copyright © 2005-7 Rockwell Collins, Inc.  All Rights Reserved.      |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "defxch")
(include-book "defpun")

(defun o () 1)
(defun inx (x m)
  (declare (ignore x))
  (+ 1 (nfix m)))

(defmacro defminterm-1-arg (fn fn-test fn-base fn-step)

  (let ((fn-minterm      (packn-pos (list fn "_MINTERM")      fn))
	(fn-minterm-term (packn-pos (list fn "_MINTERM_TERM") fn))
	(fn-measure      (packn-pos (list fn "_MEASURE")      fn))
	(fn-terminates   (packn-pos (list fn "_TERMINATES")   fn))
	)

    `(encapsulate
      ()

      (set-ignore-ok t)
      (set-irrelevant-formals-ok t)

      (defxch-aux ,fn-minterm inx o natp ,fn-test ,fn-base ,fn-step)

      (defun ,fn-measure (x)
	(nfix (,fn-minterm x)))

      (defun ,fn-terminates (x)
	(,fn-minterm-term x))

      (in-theory
       (disable
	(,fn-terminates)
	(,fn-measure)
	))

      (defthm ,(packn-pos (list "OPEN_" fn "_MEASURE") fn)
	(implies (,fn-terminates kst)
		 (and
		  (implies
		   (not (,fn-test kst))
		   (equal (,fn-measure kst)
			  (+ 1 (,fn-measure (,fn-step kst)))))
		  (implies
		   (,fn-test kst)
		   (equal (,fn-measure kst) (o)))))
	:hints (("Goal" :in-theory (disable ,(packn-pos (list fn-minterm "_TERM_PROP") fn-minterm)))))

      (defthm ,(packn-pos (list "OPEN_" fn "_TERMINATES") fn)
	(and (implies (not (,fn-test kst))
		      (iff (,fn-terminates kst)
			   (,fn-terminates (,fn-step kst))))
	     (implies (,fn-test kst)
		      (,fn-terminates kst)))
	:hints (("Goal" :in-theory '(,(packn-pos (list fn-minterm "_TERM_PROP") fn-minterm)
				     ,fn-terminates))))

      (in-theory (disable ,fn-measure ,fn-terminates))

      )
    ))

(defmacro minterm (fn type &rest args)
  (declare (ignore type args)
	   (xargs :guard (equal (len args) 1)))
  (let ((fn-test (packn-pos (list fn "_TEST") fn))
	(fn-base (packn-pos (list fn "_BASE") fn))
	(fn-step (packn-pos (list fn "_STEP1") fn)))
    `(defminterm-1-arg ,fn ,fn-test ,fn-base ,fn-step)))

(defun unbundle (args list)
  (if (consp args)
      (cons `(,(car args) (car ,list))
	    (unbundle (cdr args) `(cdr ,list)))
    nil))

(defun args-syntax-guard (args)
  (if (consp args)
      (cons `(or (symbolp ,(car args)) (quotep ,(car args)))
	    (args-syntax-guard (cdr args)))
    nil))

(defun generate-open-theorems (fn fn-test fn-terminates fn-step-1 args head tail)
  (declare (xargs :mode :program))
  (if (consp head)
      (let ((arg (car head)))
	(cons
	 `(defthmd ,(packn-pos (list "OPEN_" fn "_TERMINATES_" arg) fn)
	    (implies
	     (syntaxp (and ,@(args-syntax-guard (append (cdr head) tail))))
	     (and (implies (not (,fn-test ,@args))
			   (iff (,fn-terminates ,@args)
				(let ,(unbundle args `(,fn-step-1 (list ,@args)))
				  (,fn-terminates ,@args))))
		  (implies (,fn-test ,@args)
			   (,fn-terminates ,@args)))))
	 (generate-open-theorems fn fn-test fn-terminates fn-step-1 args (cdr head) (cons arg tail))))
    nil))

(defmacro defminterm-n-args (fn args test base step)

  (let* ((fn-test         (packn-pos (list fn "TEST_BODY")     fn))
	 (fn-base         (packn-pos (list fn "BASE_BODY")     fn))
	 (fn-step         (packn-pos (list fn "STEP_BODY")     fn))
	 (fn-1            (packn-pos (list fn      "_1")       fn))
	 (fn-test-1       (packn-pos (list fn-test "_1")       fn))
	 (fn-base-1       (packn-pos (list fn-base "_1")       fn))
	 (fn-step-1       (packn-pos (list fn-step "_1")       fn))
	 (fn-measure      (packn-pos (list fn "_MEASURE")      fn))
	 (fn-1-measure    (packn-pos (list fn "_1_MEASURE")    fn))
	 (fn-terminates   (packn-pos (list fn "_TERMINATES")   fn))
	 (fn-1-terminates (packn-pos (list fn "_1_TERMINATES") fn))
	 )

    `(encapsulate
      ()

      (set-ignore-ok t)
      (set-irrelevant-formals-ok t)

      (defun ,fn-base-1 (list)
	(let ,(unbundle args 'list)
	  ,base))

      (defun ,fn-test-1 (list)
	(let ,(unbundle args 'list)
	  ,test))

      (defun ,fn-step-1 (list)
	(let ,(unbundle args 'list)
	  ,step))

      (defun ,fn-base (,@args)
	(,fn-base-1 (list ,@args)))

      (defun ,fn-test (,@args)
	(,fn-test-1 (list ,@args)))

      (defun ,fn-step (,@args)
	(,fn-step-1 (list ,@args)))

      (defminterm-1-arg ,fn-1 ,fn-test-1 ,fn-base-1 ,fn-step-1)

      (defun ,fn-measure (,@args)
	(,fn-1-measure (list ,@args)))

      (defun ,fn-terminates (,@args)
	(,fn-1-terminates (list ,@args)))

      (defthm ,(packn-pos (list "OPEN_" fn "_MEASURE") fn)
	(implies (,fn-terminates ,@args)
		 (and
		  (implies
		   (not (,fn-test ,@args))
		   (equal (,fn-measure ,@args)
			  (let ,(unbundle args `(,fn-step-1 (list ,@args)))
			    (+ 1 (,fn-measure ,@args)))))
		  (implies
		   (,fn-test ,@args)
		   (equal (,fn-measure ,@args) (o))))))

      (defthm ,(packn-pos (list "OPEN_" fn "_TERMINATES") fn)
	(implies
	 (syntaxp (and ,@(args-syntax-guard args)))
	 (and (implies (not (,fn-test ,@args))
		       (iff (,fn-terminates ,@args)
			    (let ,(unbundle args `(,fn-step-1 (list ,@args)))
			      (,fn-terminates ,@args))))
	      (implies (,fn-test ,@args)
		       (,fn-terminates ,@args)))))

      ,@(if (< 1 (len args))
	    (generate-open-theorems fn fn-test fn-terminates fn-step-1 args args nil)
	  nil)

      (defthmd ,(packn-pos (list "OPEN_" fn "_TERMINATES!") fn)
	(and (implies (not (,fn-test ,@args))
		      (iff (,fn-terminates ,@args)
			   (let ,(unbundle args `(,fn-step-1 (list ,@args)))
			     (,fn-terminates ,@args))))
	     (implies (,fn-test ,@args)
		      (,fn-terminates ,@args))))

      (in-theory (disable ,fn-measure ,fn-terminates))

      )))

(defun if-formp (form)
  (declare (type t form))
  (if (consp form)
      (if (equal (car form) 'if)
	  (and (consp (cdr form))
	       (consp (cddr form))
	       (consp (cdddr form))
	       (null  (cddddr form)))
	(if (equal (car form) 'let)
	    (and (consp (cdr form))
		 (consp (cddr form))
		 (null  (cdddr form))
		 (if-formp (caddr form)))
	  t))
    nil))

;;
;; Some number of let's followed by an "if"
;;

(defun if-test (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
	  (cadr form)
	(if (equal (car form) 'let)
	    `(let ,(cadr form)
	       ,(if-test (caddr form)))
	  nil))
    nil))

(defun if-base (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
	  (caddr form)
	(if (equal (car form) 'let)
	    `(let ,(cadr form)
	       ,(if-base (caddr form)))
	  nil))
    nil))

(defun if-body (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
	  (cadddr form)
	(if (equal (car form) 'let)
	    `(let ,(cadr form)
	       ,(if-body (caddr form)))
	  nil))
    nil))

(defun contains-fapp-rec (fn args form)
  (declare (type t form))
  (if (consp form)
      (if args
      	  (or (contains-fapp-rec fn nil (car form))
	      (contains-fapp-rec fn   t (cdr form)))
	(or (equal fn (car form))
	    (contains-fapp-rec fn t (cdr form))))
    nil))

(defmacro contains-fapp (fn form)
  `(contains-fapp-rec ,fn nil ,form))

(defun wf-measure-body (fn form)
  (declare (type t form))
  (and (if-formp form)
       (not (iff (contains-fapp fn (if-base form))
		 (contains-fapp fn (if-body form))))))

(defun remap-fn-rec (fn fn* args form)
  (declare (type (satisfies true-listp) fn*))
  (if (consp form)
      (if args
	  (cons (remap-fn-rec fn fn* nil (car form))
		(remap-fn-rec fn fn* t (cdr form)))
	(if (equal fn (car form))
	    (append fn* (remap-fn-rec fn fn* t (cdr form)))
	  (cons (car form) (remap-fn-rec fn fn* t (cdr form)))))
    form))

(defmacro remap-fn (fn fn* form)
  `(remap-fn-rec ,fn ,fn* nil ,form))

(defun replace-fn-rec (fn term args form)
  (declare (type t form))
  (if (consp form)
      (if args
	  (cons (replace-fn-rec fn term nil (car form))
		(replace-fn-rec fn term t (cdr form)))
	(if (equal fn (car form))
	    term
	  (cons (car form) (replace-fn-rec fn term t (cdr form)))))
    form))

(defmacro replace-fn (fn term form)
  `(replace-fn-rec ,fn ,term nil ,form))

(defun map-replace-fn (fn list body)
  (declare (type t fn list body))
  (if (consp list)
      (cons
       (replace-fn fn (car list) body)
       (map-replace-fn fn (cdr list) body))
    nil))

(defthm true-listp-map-replace-fn
  (true-listp (map-replace-fn fn list body)))

(defun extract-fn (fn args form)
  (declare (type t form))
  (if (consp form)
      (if args
	  (or (extract-fn fn nil (car form))
	      (extract-fn fn t (cdr form)))
	(if (equal fn (car form)) form
	  (extract-fn fn t (cdr form))))
    form))

(defun push-lets (fn body)
  (declare (type t fn body))
  (let ((fcall (extract-fn fn nil body)))
    (if (consp fcall)
	`(,fn ,@(map-replace-fn fn (cdr fcall) body))
      `(,fn))))

(defun test-base-body (fn form)
  (declare (type (satisfies if-formp) form))
  (let ((body (if-body form)))
    (if (contains-fapp fn body)
	(mv (if-test form) (if-base form) body)
      (mv `(not ,(if-test form)) body (if-base form)))))

(defun pun-form (fn form)
  (declare (type (satisfies if-formp) form))
  (let ((body (if-body form)))
    (if (contains-fapp fn body)
	(let ((test (if-test form))
	      (base (if-base form))
	      (body (push-lets fn body)))
	  `(if ,test ,base ,body))
      (let ((test `(not ,(if-test form)))
	    (base body)
	    (body (push-lets fn (if-base form))))
	`(if ,test ,base ,body)))))

(defun first-list (list)
  (declare (type t list))
  (if (consp list)
      (if (consp (cdr list))
	  (cons (car list) (first-list (cdr list)))
	nil)
    nil))

;    (declare (xargs :guard (wf-measure-body fn form)))

(defun contains-guard-declaration-rec (decl)
  (declare (type t decl))
  (if (consp decl)
      (if (consp (car decl))
	  (or (equal (caar decl) 'type)
	      (contains-guard-declaration-rec (cdr decl)))
	(contains-guard-declaration-rec (cdr decl)))
    nil))

(defun contains-guard-declaration (decl)
  (declare (type t decl))
  (and (consp decl)
       (equal (car decl) 'declare)
       (contains-guard-declaration-rec (cdr decl))))

(defun contain-guard-declarations (decls)
  (declare (type t decls))
  (if (consp decls)
      (or (contains-guard-declaration (car decls))
	  (contain-guard-declarations (cdr decls)))
    nil))

(defmacro defminterm (fn args &rest term)
  (let ((form  (car (last term)))
	(decls (first-list term)))
    (let ((guards (contain-guard-declarations decls)))
      (mv-let (test base body) (test-base-body fn form)
	      (let ((step (remap-fn fn `(list) body)))
		(let ((fn-terminates (packn-pos (list fn "_TERMINATES") fn))
		      (fn-measure    (packn-pos (list fn "_MEASURE") fn))
		      ;(fn-step-1     (packn-pos (list fn "STEP_BODY_1") fn))
		      (fn-x          (packn-pos (list fn "_EXECUTION") fn))
		      (fn-x-nt       (packn-pos (list fn "_EXECUTION_NON_TERMINATING") fn))
		      (fn-x-to-fn    (packn-pos (list fn "_EXECUTION_TO_" fn) fn))
		      (open-fn-terminates (packn-pos (list "OPEN_" fn "_TERMINATES") fn))
		      (open-fn-rec-term   (packn-pos (list "OPEN_" fn "_REC_TERM") fn))
		      )
		  (let ((body-x (remap-fn fn `(,fn-x _base_case_) body)))
		    `(encapsulate
			 ()

		       (set-ignore-ok t)
		       (set-irrelevant-formals-ok t)

		       (defminterm-n-args ,fn ,args ,test ,base ,step)

		       ,@(and
			  guards
			  `(
			    (defun ,fn-x (_base_case_ ,@args)
			      ,@decls
			      (declare (xargs :verify-guards nil
					      :measure (,fn-measure ,@args)))
			      (mbe :logic (if (,fn-terminates ,@args)
					      (if ,test ,base ,body-x)
					    _base_case_)
				   :exec (if ,test ,base ,body-x)))

			    (defthm ,fn-x-nt
			      (implies
			       (not (,fn-terminates ,@args))
			       (equal (,fn-x _base_case_ ,@args) _base_case_)))

			    (verify-guards
			     ,fn-x
			     :hints (("goal" :in-theory (disable ,open-fn-terminates))
				     (and acl2::stable-under-simplificationp
					  `(:in-theory (current-theory :here)))))))

		       (defun ,fn (,@args)
			 ,@decls
			 (declare (xargs :verify-guards nil
					 :measure (,fn-measure ,@args)))
			 ,(let ((logic `(if (and (,fn-terminates ,@args) (not ,test))
					    ,body
					  ,base)))
			    (if guards
				`(mbe :logic ,logic
				      :exec (,fn-x ,base ,@args))
			      logic)))

		       (defthmd ,open-fn-rec-term
			 (implies (and (,fn-terminates ,@args) (not ,test))
				  (equal (,fn ,@args) ,body)))

		       ,@(if guards
			     `(
			       (defthm ,fn-x-to-fn
				 (implies
				  (,fn-terminates ,@args)
				  (equal (,fn-x _base_case_ ,@args)
					 (,fn ,@args))))

			       (verify-guards
				,fn
				:hints (("goal" :in-theory (disable ,open-fn-terminates))))
			       )
			   `(
			     (in-theory
			      (disable
			       (,fn)
			       ))))

		       )
		    )))))))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defund inca (a) (1+ (ifix a)))

   (defstub some-test (a) nil)
   (defund test-a (a) (some-test a))

   (defminterm foo (a)
     (let ((a (inca a)))
       (if (test-a a) (inca a)
	 (foo (inca a)))))

   (defthm integerp-foo
     (integerp (foo a))
     :hints (("Subgoal *1/2" :expand (inca a))))

   (defthm foo-prop
     (implies
      (integerp a)
      (< a (foo a)))
     :hints (("Goal" :induct (foo a))
	     (and acl2::stable-under-simplificationp
		  '(:in-theory (enable inca)))))

   )))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defund foo_test  (x) x)
   (defund foo_base  (x) x)
   (defund foo_step1 (x) x)

   (minterm foo state (x state))

   )))

(encapsulate
    (
     (defxch_measure    (x)   t)
     (defxch_terminates (x)   t)
     (defxch_test       (x)   t)
     (defxch_base       (r x) t)
     (defxch_r0         ()    t)
     (defxch_steps      (x)   t)
     (defxch_fn_pun     (r x) t)
     (defxch_inc        (x r) t)
     (defxch_hyps       (x)   t)
     (defxch_type       (x)   t)
     (defxch_default    ()    t)
     )

  (local
   (encapsulate ()

     (defstub defxch_r0      () nil)
     (defstub defxch_default () nil)
     (defstub defxch_test    (x)   nil)
     (defund defxch_steps   (x)  x)

     (defun defxch_hyps (x)
       (declare (ignore x)) t)

     (defun defxch_type (x)
       (declare (ignore x)) t)

     (defun   defxch_inc     (x r)
       (declare (ignore x)) r)

     (defun defxch_base (r x)
       (declare (ignore x)) r)

     (defminterm defxch (x)
       (if (defxch_test x) x
	 (defxch (defxch_steps x))))

     (defpun defxch_fn_pun (r x)
       (if (defxch_test x) (defxch_base r x)
	 (defxch_fn_pun (defxch_inc x r) (defxch_steps x))))

     ))

  (defthm defxch_base_defxch_inc_commute
    (equal (defxch_base (defxch_inc a r) x)
	   (defxch_inc a (defxch_base r x))))

  (defthm defxch_type_defxch_r0
    (defxch_type (defxch_r0)))

  (defthm defxch_type_defxch_base
    (implies
     (and
      (defxch_hyps x)
      (defxch_type r))
     (defxch_type (defxch_base r x))))

  (defthm defxch_type_defxch_default
    (defxch_type (defxch_default)))

  (defthm defxch_inc_preserves_type
    (implies
     (and
      (defxch_hyps x)
      (defxch_type r))
     (defxch_type (defxch_inc x r))))

  (defthm defxch_steps_preserves_hyps
    (implies
     (defxch_hyps x)
     (defxch_hyps (defxch_steps x)))
    :hints (("Goal" :in-theory (enable defxch_steps))))

  (defthm natp-defxch_measure
     (natp (defxch_measure x))
     :rule-classes (:rewrite :type-prescription))

  (defthm defxch_measure_property
    (implies
     (and
      (defxch_terminates x)
      (not (defxch_test x)))
     (< (defxch_measure (defxch_steps x)) (defxch_measure x)))
    :rule-classes (:rewrite :linear))

  (defthm defxch_terminates_property
    (and
     (implies
      (and
       (defxch_hyps x)
       (defxch_test x))
      (iff (defxch_terminates x) t))
     (implies
      (and
       (defxch_hyps x)
       (not (defxch_test x)))
      (iff (defxch_terminates x) (defxch_terminates (defxch_steps x))))))

  (defthm defxch_fn_pun_prop
    (implies
     (and
      (defxch_hyps x)
      (defxch_type r))
     (equal (defxch_fn_pun r x)
	    (if (defxch_test x) (defxch_base r x)
	      (defxch_fn_pun (defxch_inc x r) (defxch_steps x)))))
    :rule-classes (:definition))

  (defthm defxch_inc_of-inc
    (implies
     (and
      (defxch_hyps x)
      (defxch_hyps a)
      (defxch_type r))
     (equal (defxch_inc a (defxch_inc x r))
	    (defxch_inc x (defxch_inc a r)))))

  )

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defun defxch_inductshun (r x)
       (declare (xargs :measure (defxch_measure x)))
       (if (or (not (defxch_hyps x)) (not (defxch_type r)) (defxch_test x) (not (defxch_terminates x))) r
	 (defxch_inductshun (defxch_inc x r) (defxch_steps x))))

     (defthm open_defxch_fn_pun
       (and
	(implies
	 (and
	  (defxch_hyps x)
	  (defxch_type r)
	  (defxch_test x))
	 (equal (defxch_fn_pun r x) (defxch_base r x)))
	(implies
	 (and
	  (defxch_hyps x)
	  (defxch_type r)
	  (not (defxch_test x)))
	 (equal (defxch_fn_pun r x)
		(defxch_fn_pun (defxch_inc x r) (defxch_steps x))))))

     (defthm foo-over-defxch_inc
       (implies
	(and
	  (defxch_hyps x)
	  (defxch_type r)
	  (defxch_hyps a)
	  (defxch_terminates x))
	(equal (defxch_fn_pun (defxch_inc a r) x)
	       (defxch_inc a (defxch_fn_pun r x))))
       :hints (("goal" :induct (defxch_inductshun r x))
	       ("Subgoal *1/1" :cases ((defxch_test x)))))

     (defthm terminal_prop
       (implies
	(and
	 (defxch_hyps x)
	 (defxch_type r)
	 (defxch_terminates x))
	(equal (defxch_fn_pun r x)
	       (if (defxch_test x) (defxch_base r x)
		 (defxch_inc x (defxch_fn_pun r (defxch_steps x))))))
       :rule-classes nil
       :hints (("Goal" :induct (defxch_inductshun r x))))

     ))

  (defun defxch_fn (x)
    (declare (xargs :measure (defxch_measure x)))
    (if (defxch_terminates x)
	(if (defxch_test x) (defxch_base (defxch_r0) x)
	  (defxch_inc x (defxch_fn (defxch_steps x))))
      (defxch_default)))

  (local
   (encapsulate
       ()

     (defun defxch_aux (x)
       (defxch_fn_pun (defxch_r0) x))

     (defthm open_defxch_aux
       (implies
	(and
	 (defxch_hyps x)
	 (defxch_terminates x))
	(equal (defxch_aux x)
	       (if (defxch_test x) (defxch_base (defxch_r0) x)
		 (defxch_inc x (defxch_aux (defxch_steps x))))))
       :hints (("Goal" :use (:instance terminal_prop (r (defxch_r0))))))

     (defthm defxch_fn_to_aux
       (implies
	(and
	 (defxch_hyps x)
	 (defxch_terminates x))
	(equal (defxch_fn x) (defxch_aux x)))
       :hints (("Goal" :induct (defxch_fn x))))

     ))

  (defthm defxch_fn_to_fn_pun
    (implies
     (and
      (defxch_hyps x)
      (defxch_terminates x))
     (equal (defxch_fn x) (defxch_fn_pun (defxch_r0) x))))

  )

(local
 (encapsulate
     ()

   (defstub test (x) nil)
   (defstub steq (x) nil)

   (defminterm foo_induction (x)
     (if (test x) x
       (foo_induction (steq x))))

   ;;
   ;; Here is a template for how to use this theorem ..
   ;;

   (defpun foo_pun (r x)
     (if (test x) r
       (foo_pun (+ 1 r) (steq x))))

   #+joe
   (defthm open_foo_pun
     (implies
      (in-conclusion (foo_pun r x))
      (equal (foo_pun r x)
	     (if (test x) r
	       (foo_pun (+ 1 r) (steq x)))))
     :hints (("Goal" :in-theory (enable open-foo_pun))))

   (defun foo (x)
     (declare (xargs :measure (foo_induction_measure x)))
     (if (foo_induction_terminates x)
	 (if (test x) 0
	   (+ 1 (foo (steq x))))
       0))

   (defthm foo_to_foo_pun
     (implies
      (foo_induction_terminates x)
      (equal (foo x) (foo_pun 0 x)))
     :hints (("Goal" :use (:functional-instance defxch_fn_to_fn_pun
						(defxch_type       (lambda (r) t))
						(defxch_hyps       (lambda (x) t))
						(defxch_fn         foo)
						(defxch_fn_pun     foo_pun)
						(defxch_test       test)
						(defxch_r0         (lambda () 0))
						(defxch_base       (lambda (r x) r))
						(defxch_default    (lambda () 0))
						(defxch_steps      steq)
						(defxch_measure    foo_induction_measure)
						(defxch_terminates foo_induction_terminates)
						(defxch_inc        (lambda (x r) (+ 1 r)))
						))))


   ))

(defmacro defxch-1 (fn fn_test r0 fn_base fn_step fn_inc &key (measure 'nil) (terminates 'nil))
  (declare (xargs :guard (iff measure terminates)))
  (let ((fn_induction            (packn-pos (list fn "_INDUCTION") fn))
	(fn_induction_measure    (or measure    (packn-pos (list fn "_INDUCTION_MEASURE") fn)))
	(fn_induction_terminates (or terminates (packn-pos (list fn "_INDUCTION_TERMINATES") fn)))
	(measure-required (not measure))
	(fn_pun        (packn-pos (list fn "_PUN") fn))
	(open-fn_pun   (packn-pos (list "OPEN-" fn "_PUN") fn))
	(fn_to_fn_pun  (packn-pos (list fn "_TO_" fn "_PUN") fn))
	)

    `(encapsulate
	 ()

       ,@(and measure-required
	      `((defminterm ,fn_induction (x)
		  (if (,fn_test x) x
		    (,fn_induction (,fn_step x))))))

       (defpun ,fn_pun (r x)
	 (if (,fn_test x) (,fn_base r x)
	   (,fn_pun (,fn_inc x r) (,fn_step x))))

       (in-theory (enable ,open-fn_pun))

       (defun ,fn (x)
	 (declare (xargs :measure (,fn_induction_measure x)))
	 (if (,fn_induction_terminates x)
	     (if (,fn_test x) (,fn_base ,r0 x)
	       (,fn_inc x (,fn (,fn_step x))))
	   ,r0))

       (defthmd ,fn_to_fn_pun
	 (implies
	  (,fn_induction_terminates x)
	  (equal (,fn x) (,fn_pun ,r0 x)))
	 :hints (("Goal" :use (:functional-instance defxch_fn_to_fn_pun
						    (defxch_type       (lambda (r) t))
						    (defxch_hyps       (lambda (x) t))
						    (defxch_test       ,fn_test)
						    (defxch_r0         (lambda () ,r0))
						    (defxch_base       ,fn_base)
						    (defxch_default    (lambda () ,r0))
						    (defxch_steps      ,fn_step)
						    (defxch_fn         ,fn)
						    (defxch_fn_pun     ,fn_pun)
						    (defxch_measure    ,fn_induction_measure)
						    (defxch_terminates ,fn_induction_terminates)
						    (defxch_inc        ,fn_inc)
						    ))))


       )))

(local
 (encapsulate
     ()
   (defstub goo_test (x) nil)
   (defstub goo_step (x) nil)
   (defstub goo_pred (x) nil)

   (defun goo_base (r x)
     (declare (ignore x))
     r)

   (defun goo_inc (x r)
     (and (goo_pred x) r))

   (defxch-1 goo goo_test 't goo_base goo_step goo_inc)

   ))

(defun just-body (fn term)
  (declare (type t fn term))
  (if (consp term)
      (if (consp (car term))
	  (if (equal (caar term) fn)
	      (car term)
	    (just-body fn (cdr term)))
	(just-body fn (cdr term)))
    nil))

(defun tail-body (fn form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'let)
	  `(let ,(cadr form)
	     ,(tail-body fn (caddr form)))
	(just-body fn form))
    nil))

;; For efficiency we may want to witness a 2 argument example that we can
;; functionally instantiate over and over in vfaat .. rather than doing a
;; complete defxch each time.

(defmacro defxch (fn args form &key (defpun 'nil) (measure 'nil) (terminates 'nil) (induction 'nil))
  (declare (xargs :guard (and (iff measure terminates) (implies defpun measure))))
  (let ((fn_pun       (or defpun (packn-pos (list fn "_PUN") fn)))
	(fn_pun_induction  (packn-pos (list fn "_PUN_INDUCTION") fn))
	(fn_induction (or induction (if measure fn (packn-pos (list fn "_INDUCTION") fn))))
	(fn_induction_terminates (or terminates (packn-pos (list fn "_INDUCTION_TERMINATES") fn)))
	(fn_induction_measure    (or measure (packn-pos (list fn "_INDUCTION_MEASURE") fn)))
	(defmeasure   (not measure))
	(open-fn_pun  (packn-pos (list "OPEN-" fn "_PUN") fn))
	(fn-1         (packn-pos (list fn "-1") fn))
	(fn-1-pun     (packn-pos (list fn "-1_PUN") fn))
	(fn-inc-1     (packn-pos (list fn "-inc-1") fn))
	(fn-test-1    (packn-pos (list fn "-test-1") fn))
	(fn-step-1    (packn-pos (list fn "-step-1") fn))
	(fn-measure-1 (packn-pos (list fn "-measure-1") fn))
	(fn-terminates-1 (packn-pos (list fn "-terminates-1") fn))
	(fn-1-reduction  (packn-pos (list fn "-1-reduction") fn))
	(fn-1-pun-reduction  (packn-pos (list fn "-1-pun-reduction") fn))
	(fn-to-fn-pun        (packn-pos (list fn "_to_" fn "_pun") fn))
	(fn-1-to-fn-1-pun    (packn-pos (list fn "-1_TO_" fn "-1_PUN") fn))
	)
  (mv-let (test base body) (test-base-body fn form)
    (let ((tbody (tail-body fn body)))
      (let ((fn-inc (replace-fn fn `xarg body)))
	(let ((pun-body (remap-fn fn `(,fn_pun ,fn-inc) (push-lets fn tbody))))
	  `(encapsulate
	       ()

	     (set-ignore-ok t)
	     (set-irrelevant-formals-ok t)

	     ,@(and defmeasure
		    `((defminterm ,fn_induction ,args
			(if ,test (list ,@args) ,(remap-fn fn `(,fn_induction) tbody)))))

	     ,@(and (not defpun)
		    `(
		      (defpun ,fn_pun (xarg ,@args)
			(if ,test xarg ,pun-body))

		      (in-theory (enable ,open-fn_pun))

		      (defun ,fn ,args
			(declare (xargs :measure (,fn_induction_measure ,@args)))
			(if (,fn_induction_terminates ,@args)
			    ,form
			  ,base))
		      ))

	     (local
	      (encapsulate
		  ()

		(defun ,fn-test-1 (list)
		  (let ,(unbundle args 'list)
		    ,test))

		(defun ,fn-step-1 (list)
		  (let ,(unbundle args 'list)
		    ,(remap-fn fn `(list) tbody)))

		(defun ,fn-inc-1 (list xarg)
		  (let ,(unbundle args 'list)
		    ,fn-inc))

		(defun ,fn-measure-1 (list)
		  (let ,(unbundle args 'list)
		    (,fn_induction_measure ,@args)))

		(defun ,fn-terminates-1 (list)
		  (let ,(unbundle args 'list)
		    (,fn_induction_terminates ,@args)))

		(defxch-1 ,fn-1 ,fn-test-1 ,base (lambda (r x) r) ,fn-step-1 ,fn-inc-1
		  :measure    ,fn-measure-1
		  :terminates ,fn-terminates-1
		  )

		(defthm ,fn-1-reduction
		  (equal (,fn ,@args)
			 (,fn-1 (list ,@args)))
		  :hints (("Goal" :induct (,fn_induction ,@args))))

		(defun ,fn_pun_induction (xarg ,@args)
		  (declare (xargs :measure (,fn_induction_measure ,@args)))
		  (if (,fn_induction_terminates ,@args)
		      (if ,test xarg ,(remap-fn fn_pun `(,fn_pun_induction) pun-body))
		    xarg))

		(defthm ,fn-1-pun-reduction
		  (implies
		   (,fn_induction_terminates ,@args)
		   (equal (,fn_pun xarg ,@args)
			  (,fn-1-pun xarg (list ,@args))))
		  :hints (("Goal" :induct (,fn_pun_induction xarg ,@args))))

		))

	     (defthmd ,fn-to-fn-pun
	       (implies
		(,fn_induction_terminates ,@args)
		(equal (,fn ,@args) (,fn_pun ,base ,@args)))
	       :hints (("Goal" :in-theory (enable ,fn-1-to-fn-1-pun))))

	     )))))))

(encapsulate
 ()
 (local
  (encapsulate
   ()

   (SET-IGNORE-OK T)
   (SET-IRRELEVANT-FORMALS-OK T)
   (defstub text (x y) nil)
   (defstub hoot (x y) nil)
   (defstub stx (x y) nil)
   (defstub sty (x y) nil)
   (defun inxx  (x r) (+ 1 r))
   (defxch goop (x y)
     (if (text x y) (r0)
       (inxx x (goop (stx x y) (sty x y)))))

   ))
 )

(encapsulate
 ()
 (local
  (encapsulate
   ()

   (SET-IGNORE-OK T)
   (SET-IRRELEVANT-FORMALS-OK T)
   (defstub text (x y) nil)
   (defstub hoot (x y) nil)
   (defstub stx (x y) nil)
   (defstub sty (x y) nil)
   (defun inxx  (x r) (+ 1 r))
   (defminterm goop_induction (x y)
     (if (text x y) (list x y)
       (goop_induction (stx x y) (sty x y))))
   (defxch goop (x y)
     (if (text x y) (r0)
       (inxx x (goop (stx x y) (sty x y))))
     :measure goop_induction_measure
     :terminates goop_induction_terminates)

   ))
 )

(encapsulate
 ()
 (local
  (encapsulate
   ()

   (SET-IGNORE-OK T)
   (SET-IRRELEVANT-FORMALS-OK T)
   (defstub text (x y) nil)
   (defstub hoot (x y) nil)
   (defstub stx (x y) nil)
   (defstub sty (x y) nil)
   (defun inxx  (x r) (+ 1 r))
   (defminterm goop_induction (x y)
     (if (text x y) (list x y)
       (goop_induction (stx x y) (sty x y))))
   (defun goop (x y)
     (declare (xargs :measure (goop_induction_measure x y)))
     (if (goop_induction_terminates x y)
	 (if (text x y) (r0)
	   (inxx x (goop (stx x y) (sty x y))))
       (r0)))
   (defpun goop_pun (xarg x y)
     (if (text x y) xarg
       (goop_pun (inxx x xarg) (stx x y) (sty x y))))
   (in-theory (enable open-goop_pun))
   (defxch goop (x y)
     (if (text x y) (r0)
       (inxx x (goop (stx x y) (sty x y))))
     :defpun  goop_pun
     :measure goop_induction_measure
     :terminates goop_induction_terminates)

   ))
 )

(defmacro vfaat_fn_hyps (k st)
  `(and (vfaat_fn_hyp1 ,k)
	(vfaat_fn_hyp2 ,st)))

(encapsulate
    (
     (vfaat_fn_hyp1       (k)      t)
     (vfaat_fn_hyp2       (st)     t)
     (vfaat_fn_type       (r)      t)
     (vfaat_fn            (k st)   t)
     (vfaat_fn_pun        (r k st) t)
     (vfaat_fn_induction_measure    (k st)   t)
     (vfaat_fn_induction_terminates (k st)   t)
     (vfaat_fn_test       (k)      t)
     (vfaat_fn_base       ()       t)
     (vfaat_fn_default    ()       t)
     (vfaat_fn_branch     (k st)   t)
     (vfaat_fn_comp       (k st)   t)
     (vfaat_fn_inc        (k st r) t)
     )

  (local
   (encapsulate ()

     (defstub vfaat_fn_test    (k)      nil)
     (defstub vfaat_fn_base    () nil)
     (defstub vfaat_fn_default () nil)
     (defstub vfaat_fn_branch  (k st)   nil)
     (defstub vfaat_fn_comp    (k st)   nil)

     (defun vfaat_fn_hyp1 (k)
       (declare (ignore k))
       t)

     (defun vfaat_fn_hyp2 (st)
       (declare (ignore st))
       t)

     (defun vfaat_fn_type (r)
       (declare (ignore r))
       t)

     (defun vfaat_fn_inc (k st r)
       (declare (ignore k st)) r)

     (defminterm vfaat_fn_induction (k st)
       (if (vfaat_fn_test k) (list k st)
	 (vfaat_fn_induction (vfaat_fn_branch k st) (vfaat_fn_comp k st))))

     (defun vfaat_fn (k st)
       (declare (xargs :measure (vfaat_fn_induction_measure k st)))
       (if (vfaat_fn_induction_terminates k st)
	   (if (vfaat_fn_test k) (vfaat_fn_base)
	     (vfaat_fn_inc k st (vfaat_fn (vfaat_fn_branch k st) (vfaat_fn_comp k st))))
	 (vfaat_fn_default)))

     (defpun vfaat_fn_pun (r k st)
       (if (vfaat_fn_test k) r
	 (vfaat_fn_pun (vfaat_fn_inc k st r) (vfaat_fn_branch k st) (vfaat_fn_comp k st))))

     ))

  (defthm vfaat_fn_step_preserves_vfaat_fn_hyps
    (implies
     (and
      (vfaat_fn_hyp1 k)
      (vfaat_fn_hyp2 st))
     (and (vfaat_fn_hyp1 (vfaat_fn_branch k st))
	  (vfaat_fn_hyp2 (vfaat_fn_comp k st)))))

  (defthm vfaat_fn_type_vfaat_fn_base
    (vfaat_fn_type (vfaat_fn_base)))

  (defthm vfaat_fn_type_vfaat_fn_default
    (vfaat_fn_type (vfaat_fn_default)))

  (defthm vfaat_fn_type_vfaat_fn_inc
    (implies
     (and
      (vfaat_fn_hyp1 k)
      (vfaat_fn_hyp2 st)
      (vfaat_fn_type r))
     (vfaat_fn_type (vfaat_fn_inc k st r))))

  (defthm natp-vfaat_fn_induction_measure
    (natp (vfaat_fn_induction_measure k st))
    :rule-classes (:rewrite :type-prescription))

  (defthm vfaat_fn_induction_measure_property
    (implies
     (and
      (vfaat_fn_induction_terminates k st)
      (not (vfaat_fn_test k)))
     (< (vfaat_fn_induction_measure (vfaat_fn_branch k st) (vfaat_fn_comp k st)) (vfaat_fn_induction_measure k st)))
    :rule-classes (:rewrite :linear))

  (defthm vfaat_fn_induction_terminates_property
    (and
     (implies
      (and
       (vfaat_fn_hyps k st)
       (vfaat_fn_test k))
      (iff (vfaat_fn_induction_terminates k st) t))
     (implies
      (and
       (vfaat_fn_hyps k st)
       (not (vfaat_fn_test k)))
      (iff (vfaat_fn_induction_terminates k st) (vfaat_fn_induction_terminates (vfaat_fn_branch k st) (vfaat_fn_comp k st))))))

  (defthm vfaat_fn_pun_prop
    (implies
     (and
      (vfaat_fn_hyps k st)
      (vfaat_fn_type r))
     (equal (vfaat_fn_pun r k st)
	    (if (vfaat_fn_test k) r ;; (vfaat_fn_base r)
	      (vfaat_fn_pun (vfaat_fn_inc k st r) (vfaat_fn_branch k st) (vfaat_fn_comp k st)))))
    :rule-classes (:definition))

  (defthm vfaat_fn_inc_of-inc
    (implies
     (and
      (vfaat_fn_type r)
      (vfaat_fn_hyps a b)
      (vfaat_fn_hyps k st))
     (equal (vfaat_fn_inc a b (vfaat_fn_inc k st r))
	    (vfaat_fn_inc k st (vfaat_fn_inc a b r)))))

  (defthm vfaat_fn_property
    (equal (vfaat_fn k st)
	   (if (vfaat_fn_induction_terminates k st)
	       (if (vfaat_fn_test k) (vfaat_fn_base)
		 (vfaat_fn_inc k st (vfaat_fn (vfaat_fn_branch k st) (vfaat_fn_comp k st))))
	     (vfaat_fn_default)))
    :rule-classes (:definition))

  )

(defthm vfaat_fn_to_fn_pun
  (implies
   (and
    (vfaat_fn_hyps k st)
    (vfaat_fn_induction_terminates k st))
   (equal (vfaat_fn k st)
	  (vfaat_fn_pun (vfaat_fn_base) k st)))
  :rule-classes nil
  :hints (("Goal" :use (:functional-instance
			(:instance defxch_fn_to_fn_pun (x (list k st)))
			(defxch_hyps       (lambda (list) (vfaat_fn_hyps (car list) (cadr list))))
			(defxch_type       vfaat_fn_type)
			(defxch_fn         (lambda (list) (vfaat_fn (car list) (cadr list))))
			(defxch_fn_pun     (lambda (x list) (vfaat_fn_pun x (car list) (cadr list))))
			(defxch_test       (lambda (list) (vfaat_fn_test (car list))))
			(defxch_base       (lambda (r x) r))
			(defxch_r0         vfaat_fn_base)
			(defxch_default    vfaat_fn_default)
			(defxch_steps      (lambda (list) (list (vfaat_fn_branch (car list) (cadr list))
								(vfaat_fn_comp (car list) (cadr list)))))
			(defxch_measure    (lambda (list) (vfaat_fn_induction_measure (car list) (cadr list))))
			(defxch_terminates (lambda (list) (vfaat_fn_induction_terminates (car list) (cadr list))))
			(defxch_inc        (lambda (list r) (vfaat_fn_inc (car list) (cadr list) r)))
			))))

(defmacro vfaat_fnx_hyps (k st)
  `(and (vfaat_fnx_hyp1 ,k)
	(vfaat_fnx_hyp2 ,st)))

(encapsulate
    (
     (vfaat_fnx_hyp1       (k)      t)
     (vfaat_fnx_hyp2       (st)     t)
     (vfaat_fnx_type       (r)      t)
     (vfaat_fnx            (k st)   t)
     (vfaat_fnx_pun        (r k st) t)
     (vfaat_fnx_induction_measure    (k st)   t)
     (vfaat_fnx_induction_terminates (k st)   t)
     (vfaat_fnx_test       (k)      t)
     (vfaat_fnx_r0         ()       t)
     (vfaat_fnx_base       (r k st) t)
     (vfaat_fnx_default    ()       t)
     (vfaat_fnx_branch     (k st)   t)
     (vfaat_fnx_comp       (k st)   t)
     (vfaat_fnx_inc        (k st r) t)
     )

  (local
   (encapsulate ()

     (defstub vfaat_fnx_test    (k)      nil)
     (defstub vfaat_fnx_r0      () nil)
     (defstub vfaat_fnx_default () nil)
     (defstub vfaat_fnx_branch  (k st)   nil)
     (defstub vfaat_fnx_comp    (k st)   nil)

     (defun vfaat_fnx_base (r k st)
       (declare (ignore k st))
       r)

     (defun vfaat_fnx_hyp1 (k)
       (declare (ignore k))
       t)

     (defun vfaat_fnx_hyp2 (st)
       (declare (ignore st))
       t)

     (defun vfaat_fnx_type (r)
       (declare (ignore r))
       t)

     (defun vfaat_fnx_inc (k st r)
       (declare (ignore k st)) r)

     (defminterm vfaat_fnx_induction (k st)
       (if (vfaat_fnx_test k) (list k st)
	 (vfaat_fnx_induction (vfaat_fnx_branch k st) (vfaat_fnx_comp k st))))

     (defun vfaat_fnx (k st)
       (declare (xargs :measure (vfaat_fnx_induction_measure k st)))
       (if (vfaat_fnx_induction_terminates k st)
	   (if (vfaat_fnx_test k) (vfaat_fnx_base (vfaat_fnx_r0) k st)
	     (vfaat_fnx_inc k st (vfaat_fnx (vfaat_fnx_branch k st) (vfaat_fnx_comp k st))))
	 (vfaat_fnx_default)))

     (defpun vfaat_fnx_pun (r k st)
       (if (vfaat_fnx_test k) (vfaat_fnx_base r k st)
	 (vfaat_fnx_pun (vfaat_fnx_inc k st r) (vfaat_fnx_branch k st) (vfaat_fnx_comp k st))))

     ))

  (defthm vfaat_fnx_step_preserves_vfaat_fnx_hyps
    (implies
     (and
      (vfaat_fnx_hyp1 k)
      (vfaat_fnx_hyp2 st))
     (and (vfaat_fnx_hyp1 (vfaat_fnx_branch k st))
	  (vfaat_fnx_hyp2 (vfaat_fnx_comp k st)))))

  (defthm vfaat_fnx_type_vfaat_fnx_base
    (implies
     (and
      (vfaat_fnx_hyp1 k)
      (vfaat_fnx_hyp2 st)
      (vfaat_fnx_type r))
     (vfaat_fnx_type (vfaat_fnx_base r k st))))

  (defthm vfaat_fnx_base_vfaat_fnx_inc_commute
    (equal (vfaat_fnx_base (vfaat_fnx_inc k1 st1 r) k2 st2)
	   (vfaat_fnx_inc k1 st1 (vfaat_fnx_base r k2 st2))))

  (defthm vfaat_fnx_type_vfaat_fnx_r0
    (vfaat_fnx_type (vfaat_fnx_r0)))

  (defthm vfaat_fnx_type_vfaat_fnx_default
    (vfaat_fnx_type (vfaat_fnx_default)))

  (defthm vfaat_fnx_type_vfaat_fnx_inc
    (implies
     (and
      (vfaat_fnx_hyp1 k)
      (vfaat_fnx_hyp2 st)
      (vfaat_fnx_type r))
     (vfaat_fnx_type (vfaat_fnx_inc k st r))))

  (defthm natp-vfaat_fnx_induction_measure
    (natp (vfaat_fnx_induction_measure k st))
    :rule-classes (:rewrite :type-prescription))

  (defthm vfaat_fnx_induction_measure_property
    (implies
     (and
      (vfaat_fnx_induction_terminates k st)
      (not (vfaat_fnx_test k)))
     (< (vfaat_fnx_induction_measure (vfaat_fnx_branch k st) (vfaat_fnx_comp k st)) (vfaat_fnx_induction_measure k st)))
    :rule-classes (:rewrite :linear))

  (defthm vfaat_fnx_induction_terminates_property
    (and
     (implies
      (and
       (vfaat_fnx_hyp1 k)
       (vfaat_fnx_hyp2 st)
       (vfaat_fnx_test k))
      (iff (vfaat_fnx_induction_terminates k st) t))
     (implies
      (and
       (vfaat_fnx_hyp1 k)
       (vfaat_fnx_hyp2 st)
       (not (vfaat_fnx_test k)))
      (iff (vfaat_fnx_induction_terminates k st) (vfaat_fnx_induction_terminates (vfaat_fnx_branch k st) (vfaat_fnx_comp k st))))))

  (defthm vfaat_fnx_pun_prop
    (implies
     (and
      (vfaat_fnx_hyp1 k)
      (vfaat_fnx_hyp2 st)
      (vfaat_fnx_type r))
     (equal (vfaat_fnx_pun r k st)
	    (if (vfaat_fnx_test k) (vfaat_fnx_base r k st)
	      (vfaat_fnx_pun (vfaat_fnx_inc k st r) (vfaat_fnx_branch k st) (vfaat_fnx_comp k st)))))
    :rule-classes (:definition))

  (defthm vfaat_fnx_inc_of-inc
    (implies
     (and
      (vfaat_fnx_type r)
      (vfaat_fnx_hyps a b)
      (vfaat_fnx_hyps k st))
     (equal (vfaat_fnx_inc a b (vfaat_fnx_inc k st r))
	    (vfaat_fnx_inc k st (vfaat_fnx_inc a b r)))))

  (defthm vfaat_fnx_property
    (equal (vfaat_fnx k st)
	   (if (vfaat_fnx_induction_terminates k st)
	       (if (vfaat_fnx_test k) (vfaat_fnx_base (vfaat_fnx_r0) k st)
		 (vfaat_fnx_inc k st (vfaat_fnx (vfaat_fnx_branch k st) (vfaat_fnx_comp k st))))
	     (vfaat_fnx_default)))
    :rule-classes (:definition))

  )

(defthm vfaat_fnx_to_fn_pun
  (implies
   (and
    (vfaat_fnx_hyps k st)
    (vfaat_fnx_induction_terminates k st))
   (equal (vfaat_fnx k st)
	  (vfaat_fnx_pun (vfaat_fnx_r0) k st)))
  :rule-classes nil
  :hints (("Goal" :use (:functional-instance
			(:instance defxch_fn_to_fn_pun (x (list k st)))
			(defxch_hyps       (lambda (list) (vfaat_fnx_hyps (car list) (cadr list))))
			(defxch_type       vfaat_fnx_type)
			(defxch_fn         (lambda (list) (vfaat_fnx (car list) (cadr list))))
			(defxch_fn_pun     (lambda (x list) (vfaat_fnx_pun x (car list) (cadr list))))
			(defxch_test       (lambda (list) (vfaat_fnx_test (car list))))
			(defxch_base       (lambda (r list) (vfaat_fnx_base r (car list) (cadr list))))
			(defxch_r0         vfaat_fnx_r0)
			(defxch_default    vfaat_fnx_default)
			(defxch_steps      (lambda (list) (list (vfaat_fnx_branch (car list) (cadr list))
								(vfaat_fnx_comp (car list) (cadr list)))))
			(defxch_measure    (lambda (list) (vfaat_fnx_induction_measure (car list) (cadr list))))
			(defxch_terminates (lambda (list) (vfaat_fnx_induction_terminates (car list) (cadr list))))
			(defxch_inc        (lambda (list r) (vfaat_fnx_inc (car list) (cadr list) r)))
			))))

#|
ACL2:

(defthm <NAME>_to_<NAME>_pun
  (implies
   (<TERMINATES> k st)
   (equal (<NAME> k st)
	  (<NAME>_pun <BASE> k st)))
  :hints (("Goal" :use (:functional-instance
			vfaat_fn_to_fn_pun
			(vfaat_fn_hyp1                 kstate-p)
			(vfaat_fn_hyp2                 st-p)
			(vfaat_fn_type                 <TYPE3>)
			(vfaat_fn                      <NAME>)
			(vfaat_fn_pun                  <NAME>_pun)
			(vfaat_fn_induction_measure    <MEASURE>)
			(vfaat_fn_induction_terminates <TERMINATES>)
			(vfaat_fn_test                 <EXIT>)
			(vfaat_fn_base                 (lambda () <BASE>))
			(vfaat_fn_default              (lambda () <DEFAULT>))
			(vfaat_fn_branch               <BRANCH>)
			(vfaat_fn_comp                 <COMP>)
			(vfaat_fn_inc                  <NAME>_inc)
			))))

PVS:

  IMPORTING defxch[
	  <TYPE1>, <TYPE2>, <TYPE3>,
	  <NAME>,
	  <NAME>_pun,
	  <NAME>_inc,
          <EXIT>,
          <BASE>,
          <DEFAULT>,
          <BRANCH>,
          <COMP>,
          <MEASURE>,
          <TERMINATES>
	  ] as <NAME>_xch

  <NAME>_to_<NAME>_pun: LEMMA
    FORALL (k: <TYPE1>, st:<TYPE2>):
      <TERMINATES> =>
        <NAME>(k,st) =
          <NAME>_pun(<BASE>,k,st)
%|- <NAME>_to_<NAME>_pun: PROOF
%|-   (auto-rewrite "<NAME>_xch.fn_to_fn_pun") (skosimp) (assert)
%|- QED


|#
