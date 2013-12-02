#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;; (set-evisc-tuple nil :iprint :same :sites :all)

(include-book "defung")
;;(include-book "trivial-ancestors-check")
;;(local (use-trivial-ancestors-check))

;; ==================================================================

(defstub intersect-path (key path) nil)
(defstub get-transitions (key alist) nil)

(defmacro find-loop-macro (path key alist)
  `(let ((path ,path)
	 (key ,key)
	 (alist ,alist))
     (let ((loop (intersect-path key path)))
       (if (not (null loop)) loop
	 (let ((vals (get-transitions key alist)))
	   (find-loop-rec (cons key path) vals alist))))))

(def::ung find-loop-rec (path vals alist)
  (if (endp vals) nil
    (or (find-loop-macro path (car vals) alist)
	(find-loop-rec path (cdr vals) alist))))

;; ==================================================================
;;
;; A simple counting function to help us test the computational
;; features of defung.
;;
;; (big-depth) is the maximum "free" recursion provided by the
;; library.  Since it is a fixnum, it should be quite fast.
;;
;; ==================================================================

(def::ung inc-dec (n m)
  (declare (xargs :signature ((natp natp) natp)))
  (if (zp n) m
    (inc-dec (1- n) (1+ m))))

;; ;; We could also do (trace$ INC-DEC-COMPUTE) as most of the work
;; ;; happens there .. but it makes for a rather large trace.
;;
;; ACL2 !>(trace$ inc-dec inc-dec-compute-mbe INC-DEC-DOMAIN-COMPUTE-MBE)
;;  ((INC-DEC)
;;   (INC-DEC-COMPUTE-MBE)
;;   (INC-DEC-DOMAIN-COMPUTE-MBE))
;; ACL2 !>(inc-dec (+ 2 (big-depth)) 0)
;; 1> (ACL2_*1*_ACL2::INC-DEC 536870913 0)
;;   2> (INC-DEC 536870913 0)
;;     3> (INC-DEC-DOMAIN-COMPUTE-MBE 2 536870911)
;;       4> (INC-DEC-DOMAIN-COMPUTE-MBE 1 536870912)
;;         5> (INC-DEC-DOMAIN-COMPUTE-MBE 0 536870913)
;;         <5 (INC-DEC-DOMAIN-COMPUTE-MBE T)
;;       <4 (INC-DEC-DOMAIN-COMPUTE-MBE T)
;;     <3 (INC-DEC-DOMAIN-COMPUTE-MBE T)
;;     3> (INC-DEC-COMPUTE-MBE 2 536870911)
;;       4> (INC-DEC-COMPUTE-MBE 1 536870912)
;;         5> (INC-DEC-COMPUTE-MBE 0 536870913)
;;         <5 (INC-DEC-COMPUTE-MBE 536870913)
;;       <4 (INC-DEC-COMPUTE-MBE 536870913)
;;     <3 (INC-DEC-COMPUTE-MBE 536870913)
;;   <2 (INC-DEC 536870913)
;; <1 (ACL2_*1*_ACL2::INC-DEC 536870913)
;; 536870913

;;
;; Proof by execution. Odd that it seems to execute inc-dec 3 times ?
;;
(defthm test-inc-dec
  (equal (inc-dec (+ 2 (defung::big-depth)) 0)
	 (+ 2 (defung::big-depth)))
  :hints (("Goal" :in-theory (enable (defung::big-depth-fn)))))

(defthm inc-dec-works
  (implies
   (and
    (natp n)
    (natp m)
    (inc-dec-domain n m))
   (equal (inc-dec n m) (+ n m))))

(defun alt-inc-dec-induction (n m)
  (if (zp n) m
    (alt-inc-dec-induction (1- n) (1+ m))))

(defthm inc-dec-always-terminates
  (inc-dec-domain n m)
  :hints (("Goal" :induct (alt-inc-dec-induction n m))))

;; ==================================================================
;;
;; A test of recursive calls as recursion guards.
;;
;; ==================================================================

(def::ung rectest (x)
  (if (zp x) 3
    (if (equal x 1) (1+ (rectest (1- x)))
      (if (oddp (rectest (- x 2)))
	  (1+ (rectest (1- x)))
	7))))

;; =================================================================
;;
;; A test of mixed recursion w/in lambda
;;
;; ==================================================================

(def::ung mixed-rec (x)
  (declare (xargs :signature ((integerp) integerp)
		  :verify-guards nil
		  :default-value '0))
  (if (zp x) 0
    (let ((v (mixed-rec (1- x))))
      (+ v (mixed-rec v)))))

(defthm mixed-rec-is-zero
  (equal (mixed-rec x) 0))

;; ==================================================================
;;
;; ackermann's
;;
;; ==================================================================

(def::ung ack (x y)
  (declare (xargs :signature ((integer integer) integer)))
  (if (<= x 0) (1+ y)
    (if (<= y 0) (ack (1- x) 1)
      (ack (1- x) (ack x (1- y))))))

;; Package check - looking for symbol conflicts w/ acl2::ack
(def::ung def::ack (n m)
  (declare (xargs :signature ((integerp integer) integerp)))
  (if (= n 0) m
    (def::ack (def::ack (1- n) m) m)))

(def::ung acker (x y)
  (declare (xargs :signature ((integer integer) integer)))
  (if (= x 0) (1+ y)
    (if (= y 0) (acker (1- x) 1)
      (acker (1- x) (acker x (1- y))))))

;; No guards .. will execute using ec-call
(def::ung slacker (x y)
  (if (= x 0) (1+ y)
    (if (= y 0) (slacker (1- x) 1)
      (slacker (1- x) (slacker x (1- y))))))

;; ==================================================================
;;
;; factorial
;;
;; ==================================================================

(def::ung rfact (n r)
  (declare (type integer n r))
  (if (= n 0) r 
    (rfact (1- n) (* n r))))

(def::ung fact (n)
  (declare (xargs :signature ((integer) integer)))
  (if (= n 0) 1
    (* n (fact (1- n)))))

;; ==================================================================
;;
;; zero
;;
;; ==================================================================

(def::ung zero-fn (n)
  (declare (xargs :signature ((integerp) integerp)
		  :verify-guards nil))
  (if (zp n) 0
    (zero-fn (zero-fn (1- n)))))

(defthm zero-fn-unwinding
  (implies
   (zero-fn-domain n)
   (equal (zero-fn n)
	  0)))

;; ==================================================================
;;
;; quad zero
;;
;; ==================================================================

(def::ung zero4 (n)
  (declare (xargs :signature ((natp) natp)))
  (if (zp n) 0
    (zero4 (zero4 (zero4 (zero4 (1- n)))))))

(defthm zero4-reduction
  (equal (zero4 n) 0))

;; ==================================================================
;;
;; one
;;
;; ==================================================================

(def::ung one (n) 
  (declare (type (satisfies natp) n))
  (if (zp n) 1 (one (1- n))))

(def::ung one-2 (n) 
  (declare (xargs :signature ((natp) natp)))
  (if (zp n) 1 (one-2 (one-2 (1- n)))))

(def::ung one-let (n) 
  (declare (xargs :signature ((natp) natp)))
  (if (zp n) 1 
    (let ((n (1- n)))
      (let ((res (one-let n))) 
	res))))

(def::ung one-3 (n)
  (declare (xargs :non-executable t
		  :signature ((natp) natp)))
  (if (zp n) 1 
    (let ((n (1- n)))
      (let ((n (one-3 n)))
	(let ((n (one-3 n)))
	  (let ((n (one-3 n)))
	    n))))))

;; ==================================================================
;;
;; fib
;;
;; ==================================================================

(def::ung fibc (n)
  (cond 
   ((zp n) 1)
   ((<= n 1) 1)
   (t (+ (fibc (- n 1)) (fibc (- n 2))))))

;; ==================================================================
;;
;; Mc91
;;
;; Note that we need the :default-value in order to prove the type
;; condition.  It is also necessary for the out of domain proof.
;;
;; ==================================================================

(def::ung f91 (x)
  (declare (xargs :signature ((natp) natp)
		  :default-value (if (> x '100) (- x '10) '91)))
  (if (> x 100) (- x 10)
    (f91 (f91 (+ x 11)))))

(defthm f91-unwinding-1
  (implies
   (and
    (f91-domain x)
    (> x 100))
   (equal (f91 x) (- x 10)))
  :hints (("Goal" :induct (f91 x))))

(defthm f91-unwinding-2
  (implies
   (and
    (integerp x)
    (f91-domain x)
    (not (> x 100)))
   (equal (f91 x) 91))
  :hints (("Goal" :induct (f91 x))))

;;
;; Out of domain reasoning ..
;;

(defthm f91-unwinding
  (implies
   (integerp x)
   (equal (f91 x) (if (> x 100) (- x 10) 91))))

;; ==================================================================
;;
;; Takeuti's fn
;;
;; ==================================================================

(def::ung tarai (x y z)
  (declare (xargs :signature ((integer integer integer) integer)))
  (if (<= x y) y
    (tarai (tarai (1- x) y z)
	   (tarai (1- y) z x)
	   (tarai (1- z) x y))))

(defthm natp-tarai
  (implies
   (and
    (natp x)
    (natp y)
    (natp z)
    (tarai-domain x y z))
   (natp (tarai x y z))))

(defthm tarai-unwinding
  (implies
   (tarai-domain x y z)
   (equal (tarai x y z)
	  (if (<= x y) y
            (if (<= y z) z
              x))))
  :hints (("Goal" :in-theory (disable open-tarai-domain))))

;; ==================================================================
;;
;; An example from a mutually recursive clique ..
;;
;; ==================================================================


(defun num-list-guard (key a list)
  (declare (type symbol key)
	   (xargs :verify-guards t))
  (case key
	(list-2-nat (let ((a a) (list list))
			 (and (and (integerp a)
				   (integer-listp list)))))
	(list-2-list (let ((zed a))
			  (and (and (integer-listp zed)))))
	(t (let ((a a) (list list))
		(and (and (integerp a)
			  (integer-listp list)))))))

(defthm num-list-guard-rule-1
  (implies
   (and
    (num-list-guard key a list)
    (equal key 'list-2-nat))
   (and (integerp a)
	(integer-listp list)))
  :rule-classes (:forward-chaining))

(defthm num-list-guard-rule-1-type
  (implies
   (and
    (equal key 'list-2-nat)
    (integerp a)
    (integer-listp list))
   (num-list-guard key a list))
  :rule-classes (:rewrite :type-prescription))

(defthm num-list-guard-rule-2
  (implies
   (and
    (num-list-guard key a list)
    (equal key 'list-2-list))
   (integer-listp a))
  :rule-classes (:forward-chaining))

(defthm num-list-guard-rule-2-type
  (implies
   (and
    (equal key 'list-2-list)
    (integer-listp a))
   (num-list-guard key a list))
  :rule-classes (:rewrite :type-prescription))

(defthm num-list-guard-rule-3
  (implies
   (and
    (num-list-guard key a list)
    (not (equal key 'list-2-list))
    (not (equal key 'list-2-nat)))
   (and (integerp a)
	(integer-listp list)))
  :rule-classes (:forward-chaining))

(defthm num-list-guard-rule-3-type
  (implies
   (and
    (not (equal key 'list-2-list))
    (not (equal key 'list-2-nat))
    (integerp a)
    (integer-listp list))
   (num-list-guard key a list))
  :rule-classes (:rewrite :type-prescription))

(defun num-list-postcondition (key a list v)
  (declare (ignore a list))
  (case key
	(list-2-nat (integerp v))
	(list-2-list (integer-listp v))
	(t (booleanp v))))
  
;; Why were these failing as :forward-chaining rules?
;; - it said unreleaved hyps (?)

(defthm num-list-postcondition-rule-1
  (implies
   (and
    (num-list-postcondition key a list v)
    (equal key 'list-2-nat))
   (integerp v))
  :rule-classes (:forward-chaining))

(defthm num-list-postcondition-rule-2
  (implies
   (and
    (num-list-postcondition key a list v)
    (equal key 'list-2-list))
   (integer-listp v))
  :rule-classes (:forward-chaining))

(defthm num-list-postcondition-rule-3
  (implies
   (and
    (num-list-postcondition key a list v)
    (not (equal key 'list-2-list))
    (not (equal key 'list-2-nat)))
   (booleanp v))
  :rule-classes (:forward-chaining))

(defmacro list-2-nat-num-list-macro (a list)
       (cons 'let
             (cons (cons (list 'a a)
                         (cons (list 'list list) 'nil))
                   (cons (cons 'num-list
                               (cons (cons 'quote (cons 'list-2-nat 'nil))
                                     (append '(a list) 'nil)))
                         'nil))))

(defmacro list-2-list-num-list-macro (zed)
  (cons 'let
	(cons (cons (list 'a zed)
		    (cons (list 'list *nil*) 'nil))
	      (cons (cons 'num-list
			  (cons (cons 'quote (cons 'list-2-list 'nil))
				(append '(a list) 'nil)))
		    'nil))))

(defmacro list-to-bool-num-list-macro (a list)
  (cons 'let
	(cons (cons (list 'a a)
		    (cons (list 'list list) 'nil))
	      (cons (cons 'num-list
			  (cons (cons 'quote (cons 'list-to-bool 'nil))
				(append '(a list) 'nil)))
		    'nil))))

(def::ung num-list (key a list)
  (declare (type symbol key)
	   (xargs :verify-guards nil
		  :signature-hints ((and stable-under-simplificationp
					 '(:expand (:free (key) (num-list-0-domain key a list)))))
		  :signature ((symbolp t (lambda (list) (num-list-guard key a list)))
			      (lambda (v) (num-list-postcondition key a list v)))))
  (case
   key
   (list-2-nat
    (let ((a a) (list list))
	 (if (consp list)
	     (binary-* (if (list-to-bool-num-list-macro a (cdr list))
			   '1
			   a)
		       (list-2-nat-num-list-macro (car list)
						  (cdr list)))
	     a)))
   (list-2-list (let ((zed a))
		     (if (consp zed)
			 (cons (list-2-nat-num-list-macro (car zed)
							  (cdr zed))
			       (list-2-list-num-list-macro (cdr zed)))
			 'nil)))
   (t
    (let
     ((a a) (list list))
     (if
      (evenp (len list))
      (oddp (list-2-nat-num-list-macro a (list-2-list-num-list-macro list)))
      (evenp (list-2-nat-num-list-macro a (cdr list))))))))

;;
;; Here we demonstrate how to use the type theorem generated by the
;; defung macro to verify the guards after function admission.
;;

(defthm integerp-implies-acl2-numberp
  (implies
   (integerp x) 
   (acl2-numberp x))
  :rule-classes (:forward-chaining))

(def::signature binary-* (integerp integerp) integerp)

(verify-guards NUM-LIST-POSTCONDITION)

(def::signature fix (integerp) integerp)

(IN-THEORY (DISABLE FIX oddp evenp))

(in-theory (disable NUM-LIST-GUARD NUM-LIST-POSTCONDITION))

(def::signature cdr (integer-listp) integer-listp)
(def::signature car ((lambda (x) (and (consp x) (integer-listp x)))) integerp)

(verify-guards NUM-LIST-DEFAULT)

(verify-guards NUM-LIST-MONADIC
	       :hints (("Goal" :do-not-induct t
			:expand ((:Free (key) (num-list-0-domain key a list))))))

(verify-guards num-list)

;; ==================================================================
