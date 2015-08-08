(in-package "ACL2")

(include-book "stepprocess")

;;---------------------------------------------
;; Here is the simulator

;; The oracle for the simulator tells what type of operation and
;; which operation of that type to do next.  It is a list of
;; pairs in which the cars are a (random) type and the cdrs are
;; (random) nonnegative integers.

(defun oraclep (o)
  (declare (xargs :guard t))
  (cond ((atom o) (null o))
	(t (and (consp (car o))
		(or (equal (caar o) 'step)
		    (equal (caar o) 'deliver))
		(integerp (cdar o))
		(>= (cdar o) 0)
		(oraclep (cdr o))))))

;; There is a built-in (mod x y) for rationals, but the version for
;; nonnegative integers in book mod-gcd seems easier to work with.

(include-book "../../../../arithmetic/mod-gcd")

;; count -- counts the number of oracle members we go through.
;; trace -- keeps track of what we do.  If the oracle says to do
;;          something that can't be done, nothing is added to the trace.
;;

(defun sim (oracle count trace ms)
  (declare (xargs :guard (and (oraclep oracle)
			      (naturalp count)
			      (true-listp trace)
                              (mstatep ms))
                  :verify-guards nil))

  (let ((np (active-pstates (pstates ms) (cstates ms) (lstates ms)))
	(nc (active-cstates (cstates ms))))

    (cond ((atom oracle) (list 'timeout count trace ms))
	  ((and (equal np 0)
		(equal nc 0)) (list (if (> (waiting-pstates (pstates ms)
							    (cstates ms)
							    (lstates ms))
					   0)
					'someone-is-waiting
				        'nothing-to-do)
				    'count count
				    'trace trace
				    'final-mstate ms))

	  ((and (equal (caar oracle) 'step)
		(> np 0))
	   (let ((ps (ith-active-pstate
		      (+ 1 (nonneg-int-mod (cdar oracle) np))
		      (pstates ms)
		      (cstates ms)
		      (lstates ms))))
	     (sim (cdr oracle) (1+ count) (append trace
						  (list (list 'step (car ps)
							      (cc ps))))
		  (step-process ms ps))))

	  ((and (equal (caar oracle) 'deliver)
		(> nc 0))
	   (let ((cs (ith-active-cstate
		      (+ 1 (nonneg-int-mod (cdar oracle) nc))
		      (cstates ms))))
	     (sim (cdr oracle) (1+ count) (append
					   trace
					   (list (list 'deliver (car cs))))
		  (deliver-message ms cs ))))

	  ;; If there is no operation of the given type to perform,
	  ;; just go to the next member of the oracle.

	  (t (sim (cdr oracle) (1+ count) trace ms)))))

;;--------------------
;; lemmas to help verify sim guards

(defthm mstatep-properties
  (implies (mstatep ms)
	   (and (pstate-listp (car ms))
		(cstate-listp (cadr ms)))))

(defthm sim-guard-helper-1
  (implies (and (cstate-listp css)
		(ith-active-cstate n css))
	   (consp (ith-active-cstate n css))))

(defthm sim-guard-helper-2
  (implies (and (pstate-listp pss)
		(cstate-listp css)
		(lstate-listp lss)
		(ith-active-pstate n pss css lss))
	   (consp (ith-active-pstate n pss css lss))))

(defthm sim-guard-helper-3
  (implies (and (pstate-listp pss)
		(cstate-listp css)
		(lstate-listp lss)
		(not (consp (cddr (ith-active-pstate n pss css lss)))))
	   (not (cddr (ith-active-pstate n pss css lss)))))

(defthm sim-guard-helper-4
  (implies (and (pstate-listp pss)
		(cstate-listp css)
		(lstate-listp lss)
		(not (consp (cdr (ith-active-pstate n pss css lss)))))
	   (not (cdr (ith-active-pstate n pss css lss)))))

(verify-guards sim
  :hints (("Goal"
	   :in-theory (disable deliver-message
			       step-process
			       cstatep pstatep
			       )))
  :otf-flg t)
