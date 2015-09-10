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

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "rtlarr-new"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)

;;We define generic record accessing and updating functions to be used
;;with RTL arrays.  The basic functions are (ag a r) and (as a v r)
;;where a is an array index, v is a value, r is an "array" or record.
;;(ag a r) returns the value at index a in array r, and (as a v r) returns
;;a new array with index a set to value v in array r.

(include-book "misc/total-order" :dir :system)

(include-book "rtl")

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

;; OK, we add here some properties for typing the records and the values which
;; are stored in the records. This "typing" is pretty generic, but we choose the
;; "bvecp" types for record values because it suits AMD's RTL modeling needs.

(defun bv-arrp (x k)
  (declare (xargs :guard (integerp k)))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (bv-arrp (cdr x) k)
           (not (equal (cdar x)
                       (default-get-valu)))
           (bvecp (cdar x) k)
           (or (null (cdr x))
               (acl2::<< (caar x) (caadr x))))))

(defthm as-maps-bv-arr-to-bv-arr
  (implies (and (bv-arrp r k)
                (bvecp v k))
           (bv-arrp (as a v r) k)))

(defthm ag-maps-bv-arr-to-bvecp
  (implies (bv-arrp r k)
           (bvecp (ag a r) k)))

(defun mk-bvarr (r k)
  (declare (xargs :guard (integerp k)))
  (if (bv-arrp r k) r ()))

(defthm mk-bvarr-is-bv-arrp
  (bv-arrp (mk-bvarr r k) k))

(defthm mk-bvarr-identity
  (implies (bv-arrp r k)
           (equal (mk-bvarr r k) r)))

(in-theory (disable bv-arrp mk-bvarr))

;;We also define as2 and ag2 for 2-dimensional arrays but these simply
;;macro-expand into appropriate as and ag calls.

(defmacro ag2 (a b r)
  `(ag (cons ,a ,b) ,r))

(defmacro as2 (a b v r)
  `(as (cons ,a ,b) ,v ,r))


;;We disable as and ag, assuming the rules proved in this book are
;;sufficient to manipulate any record terms that are encountered.

(in-theory (disable as ag))

(defun positive-integer-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (equal l nil))
        (t (and (integerp (car l))
                (< 0 (car l))
                (positive-integer-listp (cdr l))))))

(defmacro arr0 (&rest dims)
  (declare (ignore dims)
           (xargs :guard (positive-integer-listp dims)))
  nil)

;;Functions representing bit vectors of determined length but undetermined value:

(encapsulate
 ((reset2 (key size) t))
 (local (defun reset2 (key size) (declare (ignore key size)) nil))
 (defthm bv-arrp-reset2
   (bv-arrp (reset2 key size) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))))

(encapsulate
 ((unknown2 (key size n) t))
 (local (defun unknown2 (key size n) (declare (ignore key size n)) nil))
 (defthm bv-arrp-unknown2
   (bv-arrp (unknown2 key size n) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))))

;BOZO where in lib/ should this go?
(defthm bv-arrp-if1
  (equal (bv-arrp (if1 x y z) n)
         (if1 x (bv-arrp y n) (bv-arrp z n))))



