#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "defung")

;; A more efficient executable that combines the domain check with the
;; computation.  Primary issue: it requires efficient multi-value
;; returns and potentially substantial reworking of function bodies.

(def::ung Lack (x y)
  (declare (xargs :non-executable t
		  :signature ((integerp integerp) integerp)
		  :default-value '0))
  (if (= x 0) (1+ y)
    (if (= y 0) (Lack (1- x) 1)
      (Lack (1- x) (Lack x (1- y))))))

;; The executable

(defun ack-default (x y)
  (declare (type integer y)
	   (ignore x))
  (1+ y))

(defun xack (dom def x y)
  (declare (type integer x y def)
	   (xargs :verify-guards nil))
  (mbe :logic (met ((dom1 val) (mv (Lack-domain x y) (Lack x y)))
		(let ((dom (and dom dom1)))
		  (mv dom (if dom val def))))
       :exec (if (defung::true (not dom)) (mv dom def)
	       (if (defung::true (= x 0)) (mv t (1+ y))
		 (if (defung::true (= y 0)) (xack dom def (1- x) 1)
		   (met ((dom0 xack0) (xack dom def x (1- y)))
		     (xack dom0 def (1- x) xack0)))))))

(verify-guards xack
	       :hints (("Goal" :in-theory (disable defung::open-true)
			:expand (Lack-domain x y))))

;; The logical interface

(defun ack-domain (x y)
  (declare (type integer x y))
  (met ((dom val) (xack t (ack-default x y) x y))
    (declare (ignore val))
    dom))

(defun ack (x y)
  (declare (type integer x y))
  (met ((dom val) (xack t (ack-default x y) x y))
    (declare (ignore dom))
    val))

(defun ack-measure (x y)
  (Lack-measure x y))

(encapsulate
    ()

  (defthm ack-definition
    (equal (ack x y)
	   (if (not (ack-domain x y)) (ack-default x y)
	     (if (defung::true (= x 0)) (1+ y)
	       (if (defung::true (= y 0)) (ack (1- x) 1)
		 (ack (1- x) (ack x (1- y)))))))
    :rule-classes ((:definition :controller-alist ((ack t t))))
    :hints (("Goal" :in-theory (disable defung::open-true)
	     :expand (Lack-domain x y))))

  (local (in-theory (disable ack-definition)))

  (defthm ack-domain-definition
    (equal (ack-domain x y)
	   (if (defung::true (= x 0)) t
	     (if (defung::true (= y 0)) (ack-domain (1- x) 1)
	       (and (ack-domain x (1- y))
		    (ack-domain (1- x) (ack x (1- y)))))))
    :rule-classes ((:definition :controller-alist ((ack-domain t t))))
    :hints (("Goal" :in-theory (disable defung::open-true)
	     :expand (Lack-domain x y))))

  (local (in-theory (disable ack-domain-definition)))

  (defthm ack-measure-definition
    (equal (ack-measure x y)
	   (if (not (ack-domain x y)) 0
	     (if (defung::true (= x 0)) 0
	       (if (defung::true (= y 0)) (1+ (ack-measure (1- x) 1))
		 (max (1+ (ack-measure x (1- y)))
		      (1+ (ack-measure (1- x) (ack x (1- y)))))))))
    :rule-classes ((:definition :controller-alist ((ack-measure t t))))
    :hints (("Goal" :in-theory (disable defung::open-true)
	     :expand ((Lack-domain x y)
		      (Lack-measure x y)))))
  
  (in-theory (disable (:definition ack)
		      (:definition ack-domain)
		      (:definition ack-measure)))
  

  )

(defun ack-induction (x y)
  (declare (xargs :measure (ack-measure x y)
		  :hints ((and stable-under-simplificationp 
			       '(:expand (ack-measure x y))))))
  (if (not (ack-domain x y)) nil
    (if (defung::true (= x 0)) t
      (if (defung::true (= y 0)) (ack-induction (1- x) 1)
	(and (ack-induction x (1- y))
	     (ack-induction (1- x) (ack x (1- y))))))))

(defthm ack-induction-reduction
  (equal (ack-induction x y)
	 (ack-domain x y))
  :hints (("Goal" :induct (ack-induction x y))))

;; Note that execution time is better than indexed computation (ack3
;; in ack-variants.lisp)
#|
ACL2 !>(time$ (ack 3 11))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 1.02 seconds realtime, 1.02 seconds runtime
; (1,120 bytes allocated).
16381
ACL2 !>(time$ (ack3 3 11))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 1.25 seconds realtime, 1.25 seconds runtime
; (1,120 bytes allocated).
16381
|#
