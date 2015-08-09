(in-package "ACL2")

;; Conjunctions and disjunctions in wffs must be binary.  But it's not
;; fair to ask users (i.e., us) to write formulas like that.
;;
;; We define a recognizer SWEET-WFF and functions UNSWEETEN
;; and SWEETEN to translate between SWEET-WFF and WFF.
;; I expect that sweet formulas will be used only for I/O.
;; In order to prove that the translations give "equivalent" formulas
;; we would have to define evaluation for sweet formulas;
;; I don't see any other use for sweet-feval, so why bother?
;;
;; Sweetness is only for conjunctions and disjunctions.  Maybe we
;; should sweeten quantified formulas as well, so we could write things
;; like (all x y z (f)), (all x y exists z u all v (f)).
;;
;;  1. Define recognizer sweet-wff,
;;  2. define functions sweeten and unsweeten,
;;  3. prove that sweeten gives a sweet-wff,
;;  4. prove that unsweeten gives a wff,
;;  5. prove one of the invertibility statements:
;;     (EQUAL (UNSWEETEN (SWEETEN F)) F)
;;     (The other one won't hold.)
;;  6. prove that sweetening a sweet-wff formula doesn't change it,
;;  7. prove that unsweetening a wff doesn't change it.

(include-book "base")

(set-well-founded-relation e0-ord-<)

;;------------------------------------------------------------
;; A sweet-wff is like a wff, except that conjunctions and
;; disjunctions can have any number (including 0 or 1) of arguments.
;; The last argument of AND cannot be an AND formula.  However,
;; other arguments of AND can be AND formulas.  When we sweeten
;; formulas below, only the right branches will be sweetened.
;; For example, (AND (AND a b) (AND c d)) becomes (AND (AND a b) c d).
;;
;; If you want more, you can use function right-assoc first.
;;
;; There is a tradeoff here.  I think the cleanest sweetening would
;; change 'FALSE to '(OR) and 'TRUE to '(AND).  But 'FALSE
;; is nicer than '(OR), and we have made it nice instead of clean.
;;
;; This means that (EQUAL (SWEETEN (UNSWEETEN F)) F) won't be a theorem,
;; because (SWEETEN (UNSWEETEN '(OR))) will be 'FALSE.
;;
;; Even if 'FALSE sweetens to '(OR), there will be a problem with
;; (EQUAL (SWEETEN (UNSWEETEN F)) F), because some simplification may
;; occur.  For example, '(OR (A) FALSE) would sweeten to '(A).
;; I think there is a theorem there if F is simplified in some ways.

(defun swfand (p)  ;; sweet version of wfand
  (declare (xargs :guard t))
  (and (consp p) (equal (car p) 'and)))

(defun swfor (p)  ;; sweet version of wfor
  (declare (xargs :guard t))
  (and (consp p) (equal (car p) 'or)))

(mutual-recursion

 (defun sweet-wff (f)
   (declare (xargs :guard t))
   (cond ((equal f 'true) t)
	 ((equal f 'false) t)
	 ((wfatom f) t)
	 ((wfnot f) (sweet-wff (a1 f)))
	 ((wfiff f) (and (sweet-wff (a1 f)) (sweet-wff (a2 f))))
	 ((wfimp f) (and (sweet-wff (a1 f)) (sweet-wff (a2 f))))
	 ((wfquant f) (sweet-wff (a2 f)))
	 ((swfand f) (sweet-wff-list-and (cdr f)))
	 ((swfor f)  (sweet-wff-list-or (cdr f)))
	 (t nil)))

 (defun sweet-wff-list-and (lst)  ;; last cannot be swfand
   (declare (xargs :guard t))
   (cond ((atom lst) (null lst))
	 ((atom (cdr lst)) (and (null (cdr lst))
				(not (swfand (car lst)))
				(sweet-wff (car lst))))
	 (t (and (sweet-wff (car lst))
		 (sweet-wff-list-and (cdr lst))))))

 (defun sweet-wff-list-or (lst)  ;; last cannot be swfor
   (declare (xargs :guard t))
   (cond ((atom lst) (null lst))
	 ((atom (cdr lst)) (and (null (cdr lst))
				(not (swfor (car lst)))
				(sweet-wff (car lst))))
	 (t (and (sweet-wff (car lst))
		 (sweet-wff-list-or (cdr lst))))))
 )

;;--------------------------------------------------------------------
;; Unsweeten takes a sweet-wff and returns a wff.

(mutual-recursion

 (defun unsweeten (f)
   (declare (xargs :guard (sweet-wff f)
		   :measure (acl2-count f)))
   (cond ((wfnot f) (list 'not (unsweeten (a1 f))))
	 ((wfbinary f) (list (car f) (unsweeten (a1 f)) (unsweeten (a2 f))))
	 ((wfquant f) (list (car f) (a1 f) (unsweeten (a2 f))))
	 ((swfand f) (unsweeten-and (cdr f)))
	 ((swfor f)  (unsweeten-or  (cdr f)))
	 (t f)))

 (defun unsweeten-and (lst)
   (declare (xargs :guard (sweet-wff-list-and lst)
		   :measure (acl2-count lst)))
   (cond ((atom lst) 'true)  ;; empty conjunction is 'true
	 ((atom (cdr lst)) (unsweeten (car lst)))
	 (t (list 'and
		  (unsweeten (car lst))
		  (unsweeten-and (cdr lst))))))

 (defun unsweeten-or (lst)
   (declare (xargs :guard (sweet-wff-list-or lst)
		   :measure (acl2-count lst)))
   (cond ((atom lst) 'false)  ;; empty disjunction is 'false
	 ((atom (cdr lst)) (unsweeten (car lst)))
	 (t (list 'or
		  (unsweeten (car lst))
		  (unsweeten-or (cdr lst))))))
 )

;;---------------------------------------------------------------
;; This is an induction scheme that corresponds to sweet-wff and unsweeten.

(defun unsweeten-i (flg x)
  (declare (xargs :guard t))
  (cond ((equal flg 'and) (cond ((atom x) 'junk)
				((atom (cdr x)) (unsweeten-i 'wff (car x)))
				(t (cons (unsweeten-i 'wff (car x))
					 (unsweeten-i 'and (cdr x))))))
	((equal flg 'or)  (cond ((atom x) 'junk)
				((atom (cdr x)) (unsweeten-i 'wff (car x)))
				(t (cons (unsweeten-i 'wff (car x))
					 (unsweeten-i 'or (cdr x))))))
	(t (cond ((wfnot x) (unsweeten-i t (a1 x)))
		 ((wfbinary x) (cons (unsweeten-i t (a1 x))
				     (unsweeten-i t (a2 x))))
		 ((wfquant x) (unsweeten-i t (a2 x)))
		 ((swfand x) (unsweeten-i 'and (cdr x)))
		 ((swfor x)  (unsweeten-i 'or  (cdr x)))
		 (t nil)))))

;;------------------------------------------------------------------
;; Prove that unsweetening a sweet-wff gives a wff.

(defthm unsweeten-wff-flg
  (cond ((equal flg 'and) (implies (sweet-wff-list-and x)
				   (wff (unsweeten-and x))))
	((equal flg 'or)  (implies (sweet-wff-list-or x)
				   (wff (unsweeten-or x))))
	(t (implies (sweet-wff x)
		    (wff (unsweeten x)))))
  :hints (("Goal"
	   :induct (unsweeten-i flg x)))
  :rule-classes nil)

(defthm unsweeten-wff
  (implies (sweet-wff x)
	   (wff (unsweeten x)))
  :hints (("Goal"
	   :by (:instance unsweeten-wff-flg (flg 'junk)))))

;;---------------------------------------------------------------
;; Now, we sweeten formulas.  As far as I can see now, this will
;; only be used for printing formulas.  (The measure is complicated,
;; because sometimes the argument doesn't get smaller.)
;;
;; Note that only right associated conjunctions and disjunctions
;; are sweetened.  If you want more, you can use function
;; right-assoc first.

(mutual-recursion

 (defun sweeten (f)
   (declare (xargs :guard (wff f)
		   :measure (cons (1+ (acl2-count f)) 0)))
   (cond ;; ((equal f 'true)  (list 'and))
	 ;; ((equal f 'false) (list 'or))
         ((wfnot f) (list 'not (sweeten (a1 f))))
	 ((wfquant f) (list (car f) (a1 f) (sweeten (a2 f))))
	 ((wfand f) (list* 'and (sweeten (a1 f)) (sweeten-and (a2 f))))
	 ((wfor f) (list* 'or (sweeten (a1 f)) (sweeten-or (a2 f))))
	 ((wfbinary f) (list (car f) (sweeten (a1 f)) (sweeten (a2 f))))
	 (t f)))

 (defun sweeten-and (f)
   (declare (xargs :guard (wff f)
		   :measure (cons (1+ (acl2-count f)) 1)))
   (cond ;; ((equal f 'true) nil)
         ((not (wfand f)) (list (sweeten f)))
	 (t (cons (sweeten (a1 f)) (sweeten-and (a2 f))))))

 (defun sweeten-or (f)
   (declare (xargs :guard (wff f)
		   :measure (cons (1+ (acl2-count f)) 1)))
   (cond ;; ((equal f 'false) nil)
         ((not (wfor f)) (list (sweeten f)))
	 (t (cons (sweeten (a1 f)) (sweeten-or (a2 f))))))
 )

;;------------------------------------------------------------
;; Now prove that sweeten gives a sweet formula.
;;
;; First, another induction scheme, corresponding to
;; sweeten/sweeten-and/sweeten-or.

(defun sweeten-i (flg f)
   (declare (xargs :guard (wff f)
		   :measure (cons (1+ (acl2-count f))
				  (if (or (equal flg 'and)
					  (equal flg 'or)) 1 0))))
   (cond ((equal flg 'and) (cond ;; ((equal f 'true) 'junk)
				 ((not (wfand f)) (sweeten-i 'wff f))
				 (t (cons (sweeten-i 'wff (a1 f))
					  (sweeten-i 'and (a2 f))))))
	 ((equal flg 'or)  (cond ;; ((equal f 'false) 'junk)
				 ((not (wfor f)) (sweeten-i 'wff f))
				 (t (cons (sweeten-i 'wff (a1 f))
					  (sweeten-i 'or (a2 f))))))
	 (t (cond ((wfnot f) (sweeten-i 'wff (a1 f)))
		  ((wfquant f) (sweeten-i 'wff (a2 f)))
		  ((wfand f) (cons (sweeten-i 'wff (a1 f))
				   (sweeten-i 'and (a2 f))))
		  ((wfor f)  (cons (sweeten-i 'wff (a1 f))
				   (sweeten-i 'or (a2 f))))
		  ((wfbinary f) (cons (sweeten-i 'wff (a1 f))
				      (sweeten-i 'wff (a2 f))))
		  (t 'junk)))))

;;----------------------------------------------------------------------
;; Prove that sweetening a wff gives a sweet-wff.

(defthm sweeten-car-flg
  (equal (car (sweeten f)) (car f))
  :hints (("Goal"
	   :induct (sweeten-i flg f))))

(defthm sweeten-wff-flg
  (cond ((equal flg 'and) (implies (wff x)
				   (sweet-wff-list-and (sweeten-and x))))
	((equal flg 'or)  (implies (wff x)
				   (sweet-wff-list-or (sweeten-or x))))
	(t (implies (wff x)
		    (sweet-wff (sweeten x)))))
  :hints (("Goal"
	   :induct (sweeten-i flg x)))
  :rule-classes nil)

(defthm sweeten-wff
  (implies (wff x)
	   (sweet-wff (sweeten x)))
  :hints (("Goal"
	   :by (:instance sweeten-wff-flg (flg 'junk)))))

;;----------------------------------------------------------
;; An invertibility theorem.

(defthm unsweeten-sweeten-flg
  (implies (wff f)
	   (cond ((equal flg 'and) (equal (unsweeten-and (sweeten-and f)) f))
		 ((equal flg 'or)  (equal (unsweeten-or (sweeten-or f)) f))
		 (t (equal (unsweeten (sweeten f)) f))))
  :hints (("Goal"
	   :induct (sweeten-i flg f)))
  :rule-classes nil)

(defthm unsweeten-sweeten
  (implies (wff f)
	   (equal (unsweeten (sweeten f)) f))
  :hints (("Goal"
           :by (:instance unsweeten-sweeten-flg (flg 'junk)))))

;;----------------------------------------------------------
;; The other invertibility statement
;;
;; (defthm sweeten-unsweeten
;;   (implies (sweet-wff f)
;;            (equal (sweeten (unsweeten f)) f)))
;;
;; is not a theorem.  See comments at the beginning.

;;---------------------------------------------------------------
;; What happens if we unsweeten an ordinary wff?

(defthm unsweeten-ordinary-wff
  (implies (wff f)
	   (equal (unsweeten f) f)))

;; What if we sweeten a sweet formula?

(defthm sweeten-sweet-wff-flg
  (cond ((equal flg 'and) (implies (and (sweet-wff x)
					(not (wfand x)))
				   (equal (sweeten-and x) (list x))))
	((equal flg 'or)  (implies (and (sweet-wff x)
					(not (wfor x)))
				   (equal (sweeten-or x) (list x))))
	(t (implies (sweet-wff x)
		    (equal (sweeten x) x))))
  :hints (("Goal"
	   :induct (sweeten-i flg x)))
  :rule-classes nil)

(defthm sweeten-sweet-wff
  (implies (sweet-wff x)
	   (equal (sweeten x) x))
  :hints (("Goal"
	   :by (:instance sweeten-sweet-wff-flg (flg 'junk)))))

;; The following idempotence theorems are now trivial consequences.

(defthm sweeten-idempotent
  (implies (wff f)
	   (equal (sweeten (sweeten f))
		  (sweeten f))))

(defthm unsweeten-idempotent
  (implies (sweet-wff f)
	   (equal (unsweeten (unsweeten f))
		  (unsweeten f))))

