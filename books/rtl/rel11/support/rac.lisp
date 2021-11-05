(in-package "RTL")

(include-book "verify-guards")
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

;;;**********************************************************************
;;;                        Miscellaneous Macros
;;;**********************************************************************

(defmacro in-function (fn term)
  `(if1 ,term () (er hard ',fn "Assertion ~x0 failed" ',term)))

;;;**********************************************************************
;;;                           Arrays
;;;**********************************************************************

(include-book "misc/total-order" :dir :system)

(defmacro default-get-valu () 0)

(defun arcdp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (arcdp (cdr x))
           (not (equal (cdar x)
                       (default-get-valu)))
           (or (null (cdr x))
               (acl2::<< (caar x) (caadr x))))))

(defthm arcdp-implies-alistp
  (implies (arcdp x) (alistp x)))

(defmacro aifrp-tag ()
  ''unlikely-to-ever-occur-in-an-executable-counterpart)

(defun aifrp (x) ;; ill-formed arcdp
  (declare (xargs :guard t))
  (or (not (arcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (equal (cdar x) (aifrp-tag))
           (aifrp (caar x)))))

(defun acl2->arcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (aifrp x) (list (cons x (aifrp-tag))) x))

(defun arcd->acl2 (r)  ;; inverse of acl2->arcd.
  (declare (xargs :guard (arcdp r)))
  (if (aifrp r) (caar r) r))

(defun ag-aux (a r) ;; record g(et) when r is a well-formed record.
  (declare (xargs :guard (arcdp r)))
  (cond ((or (endp r)
             (acl2::<< a (caar r)))
         (default-get-valu))
        ((equal a (caar r))
         (cdar r))
        (t
         (ag-aux a (cdr r)))))

(defun ag (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (ag-aux a (acl2->arcd x)))

(defun acons-if (a v r)
  (declare (xargs :guard (arcdp r)))
  (if (equal v (default-get-valu)) r (acons a v r)))

(defun as-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (arcdp r)))
  (cond ((or (endp r)
             (acl2::<< a (caar r)))
         (acons-if a v r))
        ((equal a (caar r))
         (acons-if a v (cdr r)))
        (t
         (cons (car r) (as-aux a v (cdr r))))))

;; we need the following theorems in order to get the guard for s to verify.

(local
(defthm as-aux-is-bounded
  (implies (and (arcdp r)
                (as-aux a v r)
                (acl2::<< e a)
                (acl2::<< e (caar r)))
           (acl2::<< e (caar (as-aux a v r))))))

(local
(defthm as-aux-preserves-arcdp
  (implies (arcdp r)
           (arcdp (as-aux a v r)))))

(defun as (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (arcd->acl2 (as-aux a v (acl2->arcd x))))


;;;; basic property of records ;;;;

(local
(defthm arcdp-implies-true-listp
  (implies (arcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm ag-aux-same-as-aux
  (implies (arcdp r)
           (equal (ag-aux a (as-aux a v r))
                  v))))

(local
(defthm ag-aux-diff-as-aux
  (implies (and (arcdp r)
                (not (equal a b)))
           (equal (ag-aux a (as-aux b v r))
                  (ag-aux a r)))))

(local
(defthm as-aux-same-ag-aux
  (implies (arcdp r)
           (equal (as-aux a (ag-aux a r) r)
                  r))))

(local
(defthm as-aux-same-as-aux
  (implies (arcdp r)
           (equal (as-aux a y (as-aux a x r))
                  (as-aux a y r)))))

(local
(defthm as-aux-diff-as-aux
  (implies (and (arcdp r)
                (not (equal a b)))
           (equal (as-aux b y (as-aux a x r))
                  (as-aux a x (as-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a as))))))

(local
(defthm as-aux-non-nil-cannot-be-nil
  (implies (and (not (equal v (default-get-valu)))
                (arcdp r))
           (as-aux a v r))))

(local
(defthm ag-aux-is-nil-for-<<
  (implies (and (arcdp r)
                (acl2::<< a (caar r)))
           (equal (ag-aux a r)
                  (default-get-valu)))))


;;;; properties of acl2->arcd and arcd->acl2 ;;;;

(local
(defthm acl2->arcd-arcd->acl2-of-arcdp
  (implies (arcdp x)
           (equal (acl2->arcd (arcd->acl2 x))
                  x))))

(local
(defthm acl2->arcd-returns-arcdp
  (arcdp (acl2->arcd x))))

(local
(defthm acl2->arcd-preserves-equality
  (iff (equal (acl2->arcd x) (acl2->arcd y))
       (equal x y))))

(local
(defthm arcd->acl2-acl2->arcd-inverse
  (equal (arcd->acl2 (acl2->arcd x)) x)))

(local
(defthm arcd->acl2-of-record-non-nil
  (implies (and r (arcdp r))
           (arcd->acl2 r))))

(in-theory (disable acl2->arcd arcd->acl2))


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

(defthm ash-rewrite
  (equal (ash i c)
         (fl (* (ifix i) (expt 2 c))))
  :hints (("Goal" :in-theory (enable floor fl ash))))

(defthm rem-mod
  (implies (and (natp m) (posp n))
	   (equal (rem m n) (mod m n))))
