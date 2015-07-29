(in-package "RTL")

(include-book "definitions")
(local (include-book "basic"))
(local (include-book "bits"))

(local (include-book "arithmetic-5/top" :dir :system))

;Allows things like (in-theory (disable cat)) to refer to binary-cat.
(add-macro-alias cat binary-cat)

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


;;;**********************************************************************
;;;                      Boolean Functions
;;;**********************************************************************

(defun log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defun log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))

(defun log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defun log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defun log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defun log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))

(defun logior1 (x y)
  (if (and (equal x 0) (equal y 0)) 0 1))

(defun logand1 (x y)
  (if (or (equal x 0) (equal y 0)) 0 1))

(defun lognot1 (x)
  (if (equal x 0) 1 0))

(defun true$ () 1)

(defun false$ () 0)

(defmacro if1 (x y z) `(if (eql ,x 0) ,z ,y))

(defmacro in-function (fn term)
  `(if1 ,term () (er hard ',fn "Assertion ~x0 failed" ',term)))


;;;**********************************************************************
;;;                           Arrays
;;;**********************************************************************

; Matt K. edit: Commenting out the rest, because rcdp here conflicts with the
; definition in misc/records.lisp, and both are included when building the
; ACL2+books manual.

#||

(INCLUDE-BOOK "misc/total-order" :dir :system)

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

||#

;;;**********************************************************************
;;;                      Fixed-Point Registers
;;;**********************************************************************

(defund ui (r) r)

(defund si (r n)
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defund uf (r n m)
  (* (expt 2 (- m n)) (ui r)))

(defund sf (r n m)
  (* (expt 2 (- m n)) (si r n)))

(defthmd bits-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i))))))))
  :hints (("Goal" :in-theory (enable uf ui chop)
                  :use (:instance bits-fl-diff (x r) (i (1+ i))))))

(defthmd bits-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i)
                  (< i n))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i))))))))
  :hints (("Goal" :in-theory (enable sf si chop)
                  :use ((:instance bits-fl-diff (x r) (i (1+ i)))
                        (:instance bits-fl-diff (x (- r (expt 2 n))) (i (1+ i)))
                        (:instance bits-plus-mult-2 (x r) (k n) (y -1) (n i) (m j))))))

(defthm chop-uf-1
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (= (* (expt 2 f) (- x (chop x k)))
                (bits r (1- (- f k)) 0))))
  :hints (("Goal" :in-theory (enable uf ui chop)
                  :use ((:instance bits-uf (i (- n (+ m k 1))) (j 0)))))
  :rule-classes ())

(defthm chop-uf-2
  (implies (and (integerp f)
                (rationalp x))
           (iff (= x 0) (= (* (expt 2 f) x) 0)))
  :rule-classes ())

(defthm chop-uf-3
  (implies (and (integerp f)
                (rationalp x)
                (rationalp y)
                (rationalp z)
                (= z (* (expt 2 f) (- x y))))
           (iff (= x y) (= z 0)))
  :hints (("Goal" :use ((:instance chop-uf-2 (x (- x y))))))
  :rule-classes ())

(defthm chop-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :hints (("Goal" :use (chop-uf-1
                        (:instance chop-uf-3 (f (- n m)) (x (uf r n m)) (y (chop (uf r n m) k)) (z (bits r (- n (+ m k 1)) 0))))))
  :rule-classes ())

(defthm chop-sf-1
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (= (* (expt 2 f) (- x (chop x k)))
                (bits r (1- (- f k)) 0))))
  :hints (("Goal" :in-theory (enable sf si chop)
                  :use ((:instance bits-sf (i (- n (+ m k 1))) (j 0)))))
  :rule-classes ())

(defthm chop-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :hints (("Goal" :use (chop-sf-1
                        (:instance chop-uf-3 (f (- n m)) (x (sf r n m)) (y (chop (sf r n m) k)) (z (bits r (- n (+ m k 1)) 0))))))
  :rule-classes ())

(local (include-book "bits"))

(defthmd sf-val
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (bvecp r n)
                (integerp y)
                (= (mod y (expt 2 n)) r)
                (<= (- (expt 2 (1- n))) y)
                (< y (expt 2 (1- n))))
            (equal (sf r n m) (* (expt 2 (- m n)) y)))
  :hints (("Goal" :use ((:instance si-bits (x y)))
                  :in-theory (enable bits-mod sf))))
