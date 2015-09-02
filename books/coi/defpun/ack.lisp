#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "defminterm")
;;(xxclude-book "../lists/basic")

(defun natural-listp (list)
  (declare (type t list))
  (if (consp list)
      (and (natp (car list))
	   (natural-listp (cdr list)))
    (null list)))

(defthm true-listp-from-natural-listp
  (implies (natural-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defminterm ack (x y xargs)
  (declare (xargs :verify-guards nil)
	   (type (integer 0 *) x y)
	   (type (satisfies natural-listp) xargs))
  (if (and (not (consp xargs)) (zp x)) (+ y 1)
    (if (zp x) (ack (car xargs) (+ y 1) (cdr xargs))
      (if (zp y) (ack (1- x) 1 xargs)
	(ack x (1- y) (cons (1- x) xargs))))))

(defun ack_induction (x y r s)
  (declare (xargs :measure (ack_measure x y r)))
  (if (ack_terminates x y r)
      (if (and (not (consp r)) (zp x)) (+ y 1)
	(if (zp x) (ack_induction (car r) (+ y 1) (cdr r) (cdr s))
	  (if (zp y) (ack_induction (1- x) 1 r s)
	    (ack_induction x (1- y) (cons (1- x) r) (cons (1- x) s)))))
    (cons s (+ y 1))))

;;
;;
;;

(defun head-equal (s r)
  (if (consp s)
      (and (consp r)
	   (equal (car s) (car r))
	   (head-equal (cdr s) (cdr r)))
    t))

;; jcd - Removing list-equal -- use list::equiv instead, it is provably
;; equal and already has lots of nice rules.

(defun list-equal (x y)
  (if (consp x)
      (and (consp y)
	   (equal (car x) (car y))
	   (list-equal (cdr x) (cdr y)))
    (not (consp y))))

(DEFTHM OPEN-list-equal
  (IMPLIES (AND (CONSP X) (CONSP Y))
	   (EQUAL (LIST-EQUAL X Y)
		  (AND (EQUAL (CAR X) (CAR Y))
		       (LIST-EQUAL (CDR X) (CDR Y)))))
  :HINTS (("Goal" :IN-THEORY (ENABLE LIST-EQUAL))))

(defequiv list-equal)

(defcong list-equal equal (consp x) 1)
(defcong list-equal list-equal (cons a b) 2)
(defcong list-equal equal (car x) 1)
(defcong list-equal list-equal (cdr x) 1)

(in-theory (disable list-equal))

;;

(DEFTHM CDR-APPEND-CONSP
  (IMPLIES (CONSP X)
	   (EQUAL (CDR (APPEND X Y))
		  (APPEND (CDR X) Y)))
  :HINTS (("goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM CAR-APPEND-CONSP
  (IMPLIES (CONSP X)
	   (EQUAL (CAR (APPEND X Y)) (CAR X)))
  :HINTS (("goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM LEN-APPEND
  (EQUAL (LEN (APPEND X Y))
	 (+ (LEN X) (LEN Y)))
  :HINTS (("Goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM LEN-CONS
  (EQUAL (LEN (CONS A X)) (+ 1 (LEN X)))
  :HINTS (("Goal" :IN-THEORY (ENABLE LEN))))

(DEFTHM APPEND-CONSP-TYPE-TWO
  (IMPLIES (CONSP Y) (CONSP (APPEND X Y)))
  :RULE-CLASSES ((:TYPE-PRESCRIPTION)))

(DEFTHM APPEND-OF-CONS
  (EQUAL (APPEND (CONS A X) Y)
	 (CONS A (APPEND X Y))))

(DEFTHM APPEND-OF-NON-CONSP-ONE
  (IMPLIES (NOT (CONSP X))
	   (EQUAL (APPEND X Y) Y))
  :HINTS (("Goal" :IN-THEORY (ENABLE APPEND))))

;;

(defthm list-equal-implication
  (implies (list-equal r s)
           (and (head-equal r s)
                (<= (len r) (len s))))
   :rule-classes (:forward-chaining))

(defthm not-consp-implication
  (implies (not (consp r))
           (and (head-equal r s)
                (<= (len r) (len s)))))

(defthm head-equal-append
  (head-equal x (append x y)))

(in-theory (disable append))

;; we get this from lists
;; (defthm len-append
;;   (<= (len x) (len (append x y))))

(defthm ack_terminates_from_ack_terminates
  (implies (and (ack_terminates x y s)
                (head-equal r s)
                (<= (len r) (len s)))
           (ack_terminates x y r))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :induct (ack_induction x y s r))))


(encapsulate
    ()

  (local
   (encapsulate
       ()

       ;; jcd - note, if you can prove that ack_terminates returns a
       ;; boolean, then you can instead immediately prove

     (defthm ack_terminates_list_equal
       (implies (and (ack_terminates x y s)
                     (list-equal r s))
                (ack_terminates x y r)))

     (defthm not_ack_terminates_list_equal
       (implies (and (not (ack_terminates x y r))
                     (list-equal r s))
                (not (ack_terminates x y s))))

     ))

  (defcong list-equal iff (ack_terminates x y r) 3)

  )

(defthm ack_terminates_nil
  (implies (and (ack_terminates x y s)
                (syntaxp (not (quotep s))))
           (ack_terminates x y nil))
  :rule-classes (:forward-chaining))

(defcong list-equal equal (ack x y r) 3
  :hints (("goal" :induct (ack_induction x y r r-equiv))))

;; jcd - removing this, it seems redundant with the congruence rule
;; above.
;; (defthm ack_reduction_free
;;   (implies (and (ack_terminates x y r)
;;                 (syntaxp (not (acl2::term-order r s)))
;;                 (list-equal s r))
;;            (equal (ack x y s)
;;                   (ack x y r))))

(defthmd open_ack_terminates-1
  (implies
   (syntaxp (and (or (symbolp x) (quotep x))
		 (or (symbolp y) (quotep y))))
   (and
    (implies
     (not (acktest_body x y xargs))
     (iff
      (ack_terminates x y xargs)
      (let
       ((x (car (ackstep_body_1 (list x y xargs))))
	(y (car (cdr (ackstep_body_1 (list x y xargs)))))
	(xargs
	 (car (cdr (cdr (ackstep_body_1 (list x y xargs)))))))
       (ack_terminates x y xargs))))
    (implies (acktest_body x y xargs)
	     (ack_terminates x y xargs)))))

(defthm ack_termiantes_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (ack_terminates (car r) (ack x y s) (cdr r)))
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
	   :induct (ack x y s))))


(defthm ack_measure_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (equal (ack_measure x y (append s r))
	  (+ (ack_measure x y s)
	     (ack_measure (car r) (ack x y s) (cdr r)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
	   :induct (ack x y s))))


(defthm ack_measure_reduction
  (implies
   (ack_terminates x y (cons a r))
   (equal (ack_measure x y (cons a r))
	  (+ (ack_measure x y nil)
	     (ack_measure a (ack x y nil) r))))
  :hints (("goal" :in-theory (disable OPEN_ACK_MEASURE)
	   :use (:instance ack_measure_on_ack
			   (s nil)
			   (r (cons a r))))))

(defthm ack_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (equal (ack x y (append s r))
	  (ack (car r) (ack x y s) (cdr r))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
	   :induct (ack x y s))))


(defthm ack_reduction
  (implies
   (ack_terminates x y (cons a r))
   (equal (ack x y (cons a r))
	  (ack a (ack x y nil) r)))
  :hints (("goal" :use (:instance ack_on_ack
				  (s nil)
				  (r (cons a r))))))

(defun ak (x y)
  (ack x y nil))

(defun ak_terminates (x y)
  (ack_terminates x y nil))

(defun ak_measure (x y)
  (ack_measure x y nil))

(defthm ak_spec
  (equal (ak x y)
	 (if (ak_terminates x y)
	     (if (zp x) (+ y 1)
	       (if (zp y) (ak (1- x) 1)
		 (ak (1- x) (ak x (1- y)))))
	   (+ y 1)))
  :rule-classes nil)

(defthm ak_measure_spec
  (implies
   (ak_terminates x y)
   (equal (ak_measure x y)
	  (if (zp x) (o)
	    (if (zp y) (1+ (ak_measure (1- x) 1))
	      (+ 1 (ak_measure x (1- y))
		 (ak_measure (1- x) (ak x (1- y))))))))
  :hints (("goal" :in-theory (disable OPEN_ACK_TERMINATES-1))))

(in-theory
 (disable
  ak
  ak_measure
  ak_terminates
  ))

