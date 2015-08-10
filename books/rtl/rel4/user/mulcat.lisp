(in-package "ACL2")

(local (include-book "../support/mulcat"))
(local (include-book "../support/guards"))

;;Necessary defuns:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp m) (< 0 m)
                              (integerp n) (< 0 n))))
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

;; New stuff:


(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

;this rule is no better than mulcat-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription mulcat)))

(defthm mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x)
		    (bits x (1- l) 0))))

(defthm mulcat-bvecp-simple
  (implies (and (= p (* l n))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p))
  :rule-classes ())

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
                (case-split (integerp p))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p)))

(defthm mulcat-0
  (equal (mulcat l n 0)
         0))

(defthm mulcat-0-two
  (equal (mulcat l 0 x)
         0))

(defthm bvecp-mulcat-1
    (implies (natp n)
	     (bvecp (mulcat 1 n 1) n))
  :rule-classes ())

(defthm mulcat-n-1
    (implies (case-split (<= 0 n))
	     (equal (mulcat 1 n 1)
		    (1- (expt 2 n)))))

(defun mulcat-induct (n n2)
  (if (and (integerp n) (> n 0) (integerp n2) (> n2 0))
      (mulcat-induct (1- n) (1- n2))
      0))

;BOZO prove a bits-mulcat? could be used to prove-bitn-mulcat

;BOZO generalize to bits of mulcat when x is larger than 1?
;not general (note the 1 for the l parameter)
;and to when (<= n m)
;add to lib/ ?
(defthm bitn-mulcat-1
  (implies (and (< m n)
                (case-split (bvecp x 1))
                (case-split (natp m))
                (case-split (integerp n)) ;(case-split (natp n))
                )
           (equal (bitn (mulcat 1 n x) m)
                  x)))

(defthm bitn-mulcat-2
  (implies (and (<= (* l n) n2)
                (natp n)
                (natp l)
                (natp n2)
                (case-split (bvecp x l))
                )
           (equal (bitn (mulcat l n x) n2)
                  0)))
