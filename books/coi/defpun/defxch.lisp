#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;; [Jared] switched this to use arithmetic-3 instead of 2
(local (include-book "arithmetic-3/bind-free/top" :dir :system))

;; (encapsulate
;;  (
;;   ((inc *)  -> *)
;;   ((test *) -> *)
;;   ((base *) -> *)
;;   ((step *) -> *)
;;   )

(defstub steq (x) nil)

;; DAG : We might want to further constrain this so that the tesq is
;; boolean.  Alternately, we could have another predicate over test
;; that we later functionally instantiate over terminates.  ie: if
;; test satisfies some predicate, so does terminates.

(defstub tesq (x) nil)
(defstub basq (x) nil)

(encapsulate
 (
  ((inc * *) => *)
  ((inc-pred *) => *)
  ((r0) => *)
  )

 (local
  (defun r0 () 0))

 (local
  (defun inc (a b)
    (+ (nfix a) (nfix b))))

 (local
  (defun inc-pred (a) (natp a)))

 (defthm inc_commutes
   (equal (inc v1 (inc v2 r))
	  (inc v2 (inc v1 r))))

 (defthm inc-pred-inc
   (inc-pred (inc a b)))

 (defthm inc-pred-ro
   (inc-pred (r0)))

 )

;; Generate this stuff ..

(DEFUN pun-stn (X N)
  (if (ZP N) x
    (pun-stn (steq X)
	     (1- N))))

(defthm open-pun-stn
  (implies
   (not (zp n))
   (equal  (pun-stn x n) (pun-stn (steq x) (1- n)))))

(DEFCHOOSE pun-fch (N)
  (X)
  (tesq (pun-stn X n)))



(defthm pun-fch-prop
  (IMPLIES
   (TESQ (PUN-STN x n))
   (TESQ (PUN-STN x (PUN-FCH x))))
  :hints (("goal" :use (:instance pun-fch))))

(defthm test-non-existence
  (implies
   (and
    (not (tesq a))
    (zp (pun-fch a)))
   (not (tesq (pun-stn a n))))
  :rule-classes nil
  :hints (("goal" :induct (pun-stn a n))
	  ("Subgoal *1/2" :use (:instance pun-fch-prop (x a)))))

(defthm test-non-existence-instance
  (implies
   (and
    (not (tesq a))
    (zp (pun-fch a)))
   (not (tesq (pun-stn (steq a) n))))
  :hints (("goal" :use (:instance test-non-existence (n (1+ (nfix n)))))))

(defthm generalized-test-non-existence
  (implies
   (and
    (not (tesq a))
    (not (tesq (pun-stn a (pun-fch a)))))
   (not (tesq (pun-stn a n))))
  :rule-classes nil
  :hints (("goal" :induct (pun-stn a n))))

(defthm generalized-test-non-existence-instance
  (implies
   (and
    (not (tesq a))
    (not (tesq (pun-stn a (pun-fch a)))))
   (not (tesq (pun-stn (steq a) n))))
  :hints (("goal" :use (:instance generalized-test-non-existence (n (1+ (nfix n)))))))

(defthm  tesq_step_from_tesq
  (implies
   (not (tesq a))
   (iff (tesq (pun-stn a (pun-fch a)))
        (tesq (pun-stn (steq a) (pun-fch (steq a))))))
  :hints (("Goal''" :expand (PUN-STN A (pun-fch a)))))

(defun fch-term(a) (tesq (pun-stn a (pun-fch a))))

(defthm fch-term_step_from_fch-term
  (and
   (implies
    (not (tesq a))
    (iff (fch-term a)
	 (fch-term (steq a))))
   (implies
    (tesq a)
    (fch-term a)))
  :hints (("goal" :use (:instance pun-fch-prop (n 0) (x a)))))

(defun xtesq (args) (tesq (car args)))
(defun xbasq (args) (cdr args))
(defun xsteq (args) (cons (steq (car args)) (inc (car args) (cdr args))))

;; (encapsulate
;;  (
;;   ((xun *) => *)
;;   )

;;  (local
;;   (encapsulate
;;    ()

(LOCAL
 (IN-THEORY (DISABLE xtesq xbasq xsteq)))

(DEFUN xun-stn (X N)
  (IF (ZP N) X
      (xun-stn (xsteq X) (1- N))))

(defthm xunstn_to_punstn
  (equal (car (xun-stn x n))
	 (pun-stn (car x) n))
  :hints (("goal" :in-theory (enable xsteq)
	   :do-not '(eliminate-destructors))))

(defun xun-fch-fn (x)
  (pun-fch (car x)))

(defthm xun-fch
  (IMPLIES (XTESQ (XUN-STN X N))
	   (LET ((N (XUN-FCH-fn X)))
		(XTESQ (XUN-STN X N))))
  :hints (("goal" :in-theory (enable xtesq))))

(DEFUN xun-fn (X N)
  (DECLARE (XARGS :MEASURE (NFIX N)))
  (IF (OR (ZP N) (xtesq X))
      (xbasq X)
      (xun-fn (xsteq X)
	      (1- N))))

(DEFUN
  xun (X)
  (IF (xtesq (xun-stn X (xun-fch-fn X)))
      (xun-fn X (xun-fch-fn X))
      nil))

(defthm push_inc_into_fn
  (equal (inc v (xun-fn a n))
	 (xun-fn (cons (car a) (inc v (cdr a))) n))
  :hints (("goal" :in-theory (enable xbasq xsteq xtesq))))

;;   ))

(defthm push_inc_into_xun
  (implies
   (tesq (pun-stn (car a) n))
   (equal (inc v (xun a))
	  (xun (cons (car a) (inc v (cdr a)) ))))
  :hints (("goal" :in-theory (enable xun xtesq))))

(encapsulate
 ()

 (local
  (include-book "misc/defpun" :dir :system)
  )

 (DEFTHM xun-def
   (EQUAL (xun X)
	  (IF (xtesq X)
	      (xbasq X)
	      (xun (xsteq X))))
   :HINTS
   (("Goal"
     :in-theory '(xun xtesq
		      xbasq xsteq
		      xun-stn xun-fn
		      (:TYPE-PRESCRIPTION xun-fn))
     :USE
     (:FUNCTIONAL-INSTANCE GENERIC-TAIL-RECURSIVE-DEFPUN-F
			   (DEFPUN-F xun)
			   (DEFPUN-TEST xtesq)
			   (DEFPUN-BASE xbasq)
			   (DEFPUN-ST xsteq)
			   (DEFPUN-STN xun-stn)
			   (FCH xun-fch-fn)
			   (DEFPUN-FN xun-fn)))
    ("Subgoal 2" :in-theory '(xun xtesq
				  xbasq xsteq
				  xun-stn xun-fn
				  (:TYPE-PRESCRIPTION xun-fn))
     :USE xun-fch))
   :RULE-CLASSES :DEFINITION)
  )

(in-theory
 (disable
  xun
  ))

;; )

(defun xch-pun (r x) (xun (cons x r)))

(defthm xch-pun-def
  (equal (xch-pun r x)
	 (if (tesq x) r
	   (xch-pun (inc x r) (steq x))))
  :rule-classes (:definition)
  :hints (("goal" :in-theory (enable XSTEQ xbasq xtesq))))

(defun xch (a)
  (xun (cons a (r0))))

(defthm open-xun
  (and
   (implies
    (not (xtesq x))
    (equal (xun x) (xun (xsteq x))))
   (implies
    (xtesq x)
    (equal (xun x) (xbasq x)))))

(defthm xch_prop
  (implies
   (fch-term a)
   (equal (xch a)
	  (if (tesq a) (r0)
	    (inc a (xch (steq a))))))
  :hints (("goal" :in-theory (enable xsteq xbasq xtesq))
	  (and acl2::stable-under-simplificationp
	       `(:use ((:instance PUSH_INC_INTO_XUN
				  (v a)
				  (n (pun-fch (steq a)))
				  (a (cons (steq a) (r0)))))))))

(defthm xch-pun-prop
  (implies
   (fch-term a)
   (equal (xch-pun (r0) a)
	  (if (tesq a) (r0)
	    (inc a (xch-pun (r0) (steq a))))))
  :hints (("goal" :use (:instance xch_prop))))

(defthm xch-xch-pun-reduction
  (equal (xch a) (xch-pun (r0) a)))

(defthm inc-pred-xch
  (implies
   (fch-term a)
   (inc-pred (xch a)))
  :hints (("goal" :in-theory '(xch_prop inc-pred-inc inc-pred-ro))))

(defmacro defxch-aux (xch inc r0 inc-pred tesq basq steq)

; Execution of this function produces an encapsulation that introduces
; a constrained tail recursive f with the constraint
; (equal (f x) (if (tesq x) (basq x) (f (st x)))),
; where tesq, basq and st are previously defined functions of arity 1.

  (let ((pun-stn    (packn-pos (list xch "-pun-stn")      xch))
        (pun-fch    (packn-pos (list xch "-pun-fch")      xch))
	(xtesq      (packn-pos (list xch "-xtesq")        xch))
	(xbasq      (packn-pos (list xch "-xbasq")        xch))
	(xsteq      (packn-pos (list xch "-xsteq")        xch))
	(xun-fn     (packn-pos (list xch "-xun-fn")       xch))
	(xun-stn    (packn-pos (list xch "-xun-stn")      xch))
	(xun-fch-fn (packn-pos (list xch "-xun-fch-fn")   xch))
	(xun        (packn-pos (list xch "-xun")          xch))
	(fch-term   (packn-pos (list xch "_TERM")         xch))
	(fch-term-type (packn-pos (list xch "_TERM_TYPE") xch))
	(open-xch   (packn-pos (list "OPEN-" xch)         xch))
	(xch-prop   (packn-pos (list xch "_PROP")         xch))
	(xch-term-prop (packn-pos (list xch "_TERM_PROP") xch))
	(inc-pred-xch  (packn-pos (list inc-pred "_" xch) xch))
	(xch-pun       (packn-pos (list xch "_pun")       xch))
	(xch-pun-def   (packn-pos (list xch "_pun_def")   xch))
	(xch-xch-pun-reduction (packn-pos (list xch "_" xch "_pun_reduction")   xch))
	)

    `(encapsulate
      ((,xch (x) t)
       (,xch-pun (r x) t)
       (,fch-term (x) t))

      (set-ignore-ok t)
      (set-irrelevant-formals-ok t)

      (local (in-theory (disable ,tesq ,basq ,steq)))

      (local
       (defun ,pun-stn (x n)
	 (if (zp n)
	     x
	   (,pun-stn (,steq x) (1- n)))))

      (local
       (defchoose ,pun-fch (n) (x)
	 (,tesq (,pun-stn x n))))

      (local
       (defthm ,(packn-pos (list xch "-pun-fch-prop") xch)
	 (implies
	  (,tesq (,pun-stn x n))
	  (,tesq (,pun-stn x (,pun-fch x))))
	 :hints (("goal" :use ,pun-fch))))

      (local (defun ,fch-term (x) (,tesq (,pun-stn x (,pun-fch x)))))

      (defthm ,fch-term-type
	(booleanp (,fch-term x)))

      (local (defun ,xtesq (args) (,tesq (car args))))
      (local (defun ,xbasq (args) (cdr args)))
      (local (defun ,xsteq (args) (cons (,steq (car args))
					(,inc (car args) (cdr args)))))

      #+joe
      (LOCAL
       (IN-THEORY (DISABLE ,xtesq ,xbasq ,xsteq)))

      (local
       (DEFUN ,xun-stn (X N)
	 (IF (ZP N) X
	     (,xun-stn (,xsteq X) (1- N)))))

      (local
       (defun ,xun-fch-fn (x)
	 (,pun-fch (car x))))

      (local
       (DEFUN ,xun-fn (X N)
	 (DECLARE (XARGS :MEASURE (NFIX N)))
	 (IF (OR (ZP N) (,xtesq X))
	     (,xbasq X)
	     (,xun-fn (,xsteq X)
		      (1- N)))))

      (local
       (DEFUN ,xun (X)
	 (IF (,xtesq (,xun-stn X (,xun-fch-fn X)))
	     (,xun-fn X (,xun-fch-fn X))
	     nil)))

      (local
       (defun ,xch-pun (r args) (,xun (cons args r))))


      (local
       (defun ,xch (a) (,xun (cons a (,r0)))))

      (defthmd ,xch-xch-pun-reduction
	(equal (,xch a) (,xch-pun (,r0) a))
	:hints (;; This kind of proof hackery is killing me!
		;; "heuristically unattractive", my foot!
		(and stable-under-simplificationp
		     '(:expand (,pun-stn x n)))
		("goal"
		 :use (:functional-instance xch-pun-def
					    (xch-pun    ,xch-pun)
					    (inc-pred   ,inc-pred)
					    (fch-term   ,fch-term)
					    (r0         ,r0)
					    (inc        ,inc)
					    (xch        ,xch)
					    (xun        ,xun)
					    (xun-fch-fn ,xun-fch-fn)
					    (xun-stn    ,xun-stn)
					    (xun-fn     ,xun-fn)
					    (xsteq      ,xsteq)
					    (xbasq      ,xbasq)
					    (xtesq      ,xtesq)
					    (tesq       ,tesq)
					    (basq       ,basq)
					    (steq       ,steq)
					    (pun-stn    ,pun-stn)
					    (pun-fch    ,pun-fch)
					    ))))

      (defthmd ,xch-pun-def
	(equal (,xch-pun r x)
	       (if (,tesq x) r
		 (,xch-pun (,inc x r) (,steq x))))
	:rule-classes (:definition)
	:hints (("goal" :use (:functional-instance xch-pun-def
						   (xch-pun    ,xch-pun)
						   (inc-pred   ,inc-pred)
						   (fch-term   ,fch-term)
						   (r0         ,r0)
						   (inc        ,inc)
						   (xch        ,xch)
						   (xun        ,xun)
						   (xun-fch-fn ,xun-fch-fn)
						   (xun-stn    ,xun-stn)
						   (xun-fn     ,xun-fn)
						   (xsteq      ,xsteq)
						   (xbasq      ,xbasq)
						   (xtesq      ,xtesq)
						   (tesq       ,tesq)
						   (basq       ,basq)
						   (steq       ,steq)
						   (pun-stn    ,pun-stn)
						   (pun-fch    ,pun-fch)
						   ))))
      (defthmd ,xch-prop
	(implies
	 (,fch-term a)
	 (equal (,xch a)
		(if (,tesq a) (,r0)
		  (,inc a (,xch (,steq a))))))
	:hints (("goal" :use (:functional-instance xch_prop
						   (inc-pred   ,inc-pred)
						   (fch-term   ,fch-term)
						   (r0         ,r0)
						   (inc        ,inc)
						   (xch        ,xch)
						   (xun        ,xun)
						   (xun-fch-fn ,xun-fch-fn)
						   (xun-stn    ,xun-stn)
						   (xun-fn     ,xun-fn)
						   (xsteq      ,xsteq)
						   (xbasq      ,xbasq)
						   (xtesq      ,xtesq)
						   (tesq       ,tesq)
						   (basq       ,basq)
						   (steq       ,steq)
						   (pun-stn    ,pun-stn)
						   (pun-fch    ,pun-fch)
						   ))))
      (defthm ,open-xch
	(implies
	 (,fch-term a)
	 (and (implies (,tesq a) (equal (,xch a) (,r0)))
	      (implies (not (,tesq a))
		       (equal (,xch a)
			      (,inc a (,xch (,steq a)))))))
	:hints (("goal" :in-theory '(,xch-prop))))

      (defthm ,inc-pred-xch
	(implies
	 (,fch-term a)
	 (,inc-pred (,xch a)))
	:hints (("goal" :use (:functional-instance inc-pred-xch
						   (inc-pred   ,inc-pred)
						   (fch-term   ,fch-term)
						   (r0         ,r0)
						   (inc        ,inc)
						   (xch        ,xch)
						   (xun        ,xun)
						   (xun-fch-fn ,xun-fch-fn)
						   (xun-stn    ,xun-stn)
						   (xun-fn     ,xun-fn)
						   (xsteq      ,xsteq)
						   (xbasq      ,xbasq)
						   (xtesq      ,xtesq)
						   (tesq       ,tesq)
						   (basq       ,basq)
						   (steq       ,steq)
						   (pun-stn    ,pun-stn)
						   (pun-fch    ,pun-fch)
						   ))))

      (defthm ,xch-term-prop
	(and
	 (implies
	  (not (,tesq a))
	  (iff (,fch-term a)
	       (,fch-term (,steq a))))
	 (implies
	  (,tesq a)
	  (,fch-term a)))
	:hints (("goal" :use (:functional-instance fch-term_step_from_fch-term
						   (inc-pred   ,inc-pred)
						   (fch-term   ,fch-term)
						   (r0         ,r0)
						   (inc        ,inc)
						   (xch        ,xch)
						   (xun        ,xun)
						   (xun-fch-fn ,xun-fch-fn)
						   (xun-stn    ,xun-stn)
						   (xun-fn     ,xun-fn)
						   (xsteq      ,xsteq)
						   (xbasq      ,xbasq)
						   (xtesq      ,xtesq)
						   (tesq       ,tesq)
						   (basq       ,basq)
						   (steq       ,steq)
						   (pun-stn    ,pun-stn)
						   (pun-fch    ,pun-fch)
						   ))))


      )
    ))
