(in-package "ACL2")

(local (include-book "../support/setbitn"))
(local (include-book "../support/guards"))

;; Necessary defuns:

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

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

(defund setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
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

;;
;; New stuff:
;;

(defund setbitn (x w n y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))))
  (setbits x w n n y))

(defthm setbitn-nonnegative-integer-type
  (and (integerp (setbitn x w n y))
       (<= 0 (setbitn x w n y)))
  :rule-classes (:type-prescription))

;this rule is no better than setbits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription setbitn)))

(defthm setbitn-natp
  (natp (setbitn x w n y)))

;add setbitn-bvecp-simple?

(defthm setbitn-bvecp
  (implies (and (<= w k)
                (case-split (integerp k)))
           (bvecp (setbitn x w n y) k)))

(defthm setbitn-rewrite
  (implies (syntaxp (quotep n))
           (equal (setbitn x w n y)
                  (setbits x w n n y))))

;gen?
(defthm bitn-setbitn
  (implies (and (case-split (bvecp y 1))
                (case-split (< 0 w))
                (case-split (< n w))
                (case-split (< k w))
                (case-split (<= 0 k))
                (case-split (integerp w))
                (case-split (integerp n))
                (<= 0 n)
                (case-split (integerp k))
                )
           (equal (bitn (setbitn x w n y) k)
                  (if (equal n k)
                      y
                    (bitn x k)))))

(defthm setbitn-setbitn
  (implies (and (case-split (<= 0 n))
                (case-split (< n w))
                (case-split (integerp w))
                (case-split (integerp n))
                )
           (equal (setbitn (setbitn x w n y) w n y2)
                  (setbitn x w n y2))))

(defthm setbitn-does-nothing
  (implies (and (case-split (<= 0 n))
                (case-split (< n w))
                (case-split (integerp w))
                (case-split (integerp n))
                )
           (equal (setbitn x w n (bitn x n))
                  (bits x (+ -1 w) 0))))

