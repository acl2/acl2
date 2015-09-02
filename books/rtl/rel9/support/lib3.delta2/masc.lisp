; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "misc/total-order" :dir :system)

(encapsulate ()

(local (INCLUDE-BOOK "../lib3/rtl"))
(local (INCLUDE-BOOK "../lib3/rtlarr"))

(defund fl (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))


;;CAT (concatenation):

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(defun formal-+ (x y)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun cat-size (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

;Allows things like (in-theory (disable cat)) to refer to binary-cat.
(add-macro-alias cat binary-cat)

;;Equality comparison:

;Leaving this enabled caused a stack overflow in simple-loops when building one of our models.
;However, we have very few lemmas about log=, so you may want to enable this for your proofs.
(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defund log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))


;;Unsigned inequalities:

(defund log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defund log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defund log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defund log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))


(defthm log<-nonnegative-integer-type
  (and (integerp (log< x y))
       (<= 0 (log< x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<)))

(defthm log<=-nonnegative-integer-type
  (and (integerp (log<= x y))
       (<= 0 (log<= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<=)))

(defthm log>-nonnegative-integer-type
  (and (integerp (log> x y))
       (<= 0 (log> x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>)))

(defthm log>=-nonnegative-integer-type
  (and (integerp (log>= x y))
       (<= 0 (log>= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>=)))

(defthm log=-nonnegative-integer-type
  (and (integerp (log= x y))
       (<= 0 (log= x y)))
  :rule-classes (:type-prescription))

(defthm log=-commutative
       (equal (log= x y)
              (log= y x))
       :hints (("Goal" :in-theory (enable log=))))

;;This rule is no better than log=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log=)))

(defthm log<>-nonnegative-integer-type
  (and (integerp (log<> x y))
       (<= 0 (log<> x y)))
  :rule-classes (:type-prescription))

(defthm log<>-commutative
  (equal (log<> x y)
	 (log<> y x)))

;;This rule is no better than log<>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<>)))

(defmacro default-get-valu () 0)

(defun rcdp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (rcdp (cdr x))
           (not (equal (cdar x)
                       (default-get-valu)))
           (or (null (cdr x))
               (acl2::<< (caar x) (caadr x))))))

(defthm rcdp-implies-alistp
  (implies (rcdp x) (alistp x)))

(defmacro ifrp-tag ()
  ''unlikely-to-ever-occur-in-an-executable-counterpart)

(defun ifrp (x) ;; ill-formed rcdp
  (declare (xargs :guard t))
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (equal (cdar x) (ifrp-tag))
           (ifrp (caar x)))))

(defun acl2->rcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifrp x) (list (cons x (ifrp-tag))) x))

(defun rcd->acl2 (r)  ;; inverse of acl2->rcd.
  (declare (xargs :guard (rcdp r)))
  (if (ifrp r) (caar r) r))

(defun ag-aux (a r) ;; record g(et) when r is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (acl2::<< a (caar r)))
         (default-get-valu))
        ((equal a (caar r))
         (cdar r))
        (t
         (ag-aux a (cdr r)))))

(defun ag (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (ag-aux a (acl2->rcd x)))

(defun acons-if (a v r)
  (declare (xargs :guard (rcdp r)))
  (if (equal v (default-get-valu)) r (acons a v r)))

(defun as-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (acl2::<< a (caar r)))
         (acons-if a v r))
        ((equal a (caar r))
         (acons-if a v (cdr r)))
        (t
         (cons (car r) (as-aux a v (cdr r))))))

(defun as (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (as-aux a v (acl2->rcd x))))


;;Basic properties of arrays:

(defthm ag-same-as
  (equal (ag a (as a v r))
         v))

(defthm ag-diff-as
  (implies (not (equal a b))
           (equal (ag a (as b v r))
                  (ag a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm ag-of-as-redux
  (equal (ag a (as b v r))
         (if (equal a b) v (ag a r))))

(in-theory (disable ag-of-as-redux))

(defthm as-same-ag
  (equal (as a (ag a r) r)
         r))

(defthm as-same-as
  (equal (as a y (as a x r))
         (as a y r)))

(defthm as-diff-as
  (implies (not (equal a b))
           (equal (as b y (as a x r))
                  (as a x (as b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a as)))))

;; the following theorems are less relevant but have been useful in dealing
;; with a default record of NIL.

(defthm ag-of-nil-is-default
  (equal (ag a nil) (default-get-valu)))

(defthm as-non-default-cannot-be-nil
  (implies (not (equal v (default-get-valu)))
           (as a v r)))

(defthm non-nil-if-ag-not-default
  (implies (not (equal (ag a r)
                       (default-get-valu)))
           r)
  :rule-classes :forward-chaining)

;;We disable as and ag, assuming the rules proved in this book are
;;sufficient to manipulate any record terms that are encountered.

(in-theory (disable as ag))

)

(encapsulate ()

(local (INCLUDE-BOOK "bits"))
(local (include-book "arithmetic-5/top" :dir :system))

; We have decided to allow setbits to open up in terms of cat.  So, we leave it
; enabled.

(defun setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (integerp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))))
  (mbe :logic (cat (bits x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat (bits y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits y (+ i (- j)) 0))
                           (t
                            (cat (bits x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat (bits y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits x (1- j) 0)
                          j))
                    (t
                     (cat (bits x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat (bits y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits x (1- j) 0)
                               j)
                          (1+ i))))))

(defun setbitn (x w n y)
  (declare (xargs :guard (and (natp x)
                              (integerp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))))
  (setbits x w n n y))

)

(defun intval (w x)
  (if (= (bitn x (1- w)) 1)
      (- x (expt 2 w))
    x))

(defun logior1 (x y)
  (if (and (equal x 0) (equal y 0)) 0 1))

(defun logand1 (x y)
  (if (or (equal x 0) (equal y 0)) 0 1))

(defun lognot1 (x)
  (if (equal x 0) 1 0))

(defun true () 1)

(defun false () 0)

(defmacro if1 (x y z) `(if (eql ,x 0) ,z ,y))

(defmacro in-function (fn term)
  `(if ,term () (er hard ',fn "Assertion ~x0 failed" ',term)))
