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

; Rob Sumners

(in-package "ACL2")

#|

We define properties of a generic record accessor function and updater function
we will use for RTL arrays.  The basic functions are (ag a r) and (as a v r)
where a is an array index, v is a value, r is an "array" or record, and
(ag a r) returns the value set to index a in array r, and (as a v r) returns
a new array with index a set to value v in array r.

The following main lemmas are "exported" about record (ag)et and (as)et:

(defthm ag-same-as
  (equal (ag a (as a v r))
         v))

(defthm ag-diff-as
  (implies (not (equal a b))
           (equal (ag a (as b v r))
                  (ag a r))))

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


We also include some auxiliary lemmas which have proven useful.

(defthm ag-of-nil-is-default
  (equal (ag a nil) (default-get-valu)))

(defthm as-non-default-cannot-be-nil
  (implies (not (equal v (default-get-valu)))
           (as a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (as-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-ag-not-default
  (implies (not (equal (ag a r)
                       (default-get-valu)))
           r)
  :rule-classes :forward-chaining)


We also include some "type" lemmas for accesses and updates of rtl arrays.

(defthm as-maps-bv-arr-to-bv-arr
  (implies (and (bv-arrp r k)
                (bvecp v k))
           (bv-arrp (as a v r) k)))

(defthm ag-maps-bv-arr-to-bvecp
  (implies (bv-arrp r k)
           (bvecp (ag a r) k)))


Note we also define as2 and ag2 for 2-dimensional arrays but these simply
macro-expand into appropriate as and ag calls.

We normalize the array structures (which allows the 'equal-ity based rewrite
rules) as alists where the keys (cars) are ordered using the total-order added
to ACL2 and defined in the included book. We define a set of "-aux" functions
which assume well-formed records -- defined by rcdp -- and then prove the
desired properties using hypothesis assuming well-formed records.

We then remove these well-formed record hypothesis by defining an invertible
mapping (acl2->rcd) taking any ACL2 object and returning a well-formed
record. We then prove the desired properties using the proper translations of
the -aux functions to the acl2 objects, and subsequently remove the
well-formed record hypothesis.

|#

(include-book "misc/total-order" :dir :system)

;; BEGIN records definitions.

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

;; we need the following theorems in order to get the guard for s to verify.

(local
(defthm as-aux-is-bounded
  (implies (and (rcdp r)
                (as-aux a v r)
                (acl2::<< e a)
                (acl2::<< e (caar r)))
           (acl2::<< e (caar (as-aux a v r))))))

(local
(defthm as-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (as-aux a v r)))))

(defun as (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (as-aux a v (acl2->rcd x))))


;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm ag-aux-same-as-aux
  (implies (rcdp r)
           (equal (ag-aux a (as-aux a v r))
                  v))))

(local
(defthm ag-aux-diff-as-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (ag-aux a (as-aux b v r))
                  (ag-aux a r)))))

(local
(defthm as-aux-same-ag-aux
  (implies (rcdp r)
           (equal (as-aux a (ag-aux a r) r)
                  r))))

(local
(defthm as-aux-same-as-aux
  (implies (rcdp r)
           (equal (as-aux a y (as-aux a x r))
                  (as-aux a y r)))))

(local
(defthm as-aux-diff-as-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (as-aux b y (as-aux a x r))
                  (as-aux a x (as-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a as))))))

(local
(defthm as-aux-non-nil-cannot-be-nil
  (implies (and (not (equal v (default-get-valu)))
                (rcdp r))
           (as-aux a v r))))

(local
(defthm ag-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (acl2::<< a (caar r)))
           (equal (ag-aux a r)
                  (default-get-valu)))))


;;;; properties of acl2->rcd and rcd->acl2 ;;;;

(local
(defthm acl2->rcd-rcd->acl2-of-rcdp
  (implies (rcdp x)
           (equal (acl2->rcd (rcd->acl2 x))
                  x))))

(local
(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x))))

(local
(defthm acl2->rcd-preserves-equality
  (iff (equal (acl2->rcd x) (acl2->rcd y))
       (equal x y))))

(local
(defthm rcd->acl2-acl2->rcd-inverse
  (equal (rcd->acl2 (acl2->rcd x)) x)))

(local
(defthm rcd->acl2-of-record-non-nil
  (implies (and r (rcdp r))
           (rcd->acl2 r))))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final (exported) properties of record g(et) and s(et) ;;;;

;; NOTE that these theorems basically follow from the "equivalent" properties
;; for s-aux and g-aux with rcdp hypothesis, and the lemmas about the acl2->rcd
;; and its inverse rcd->acl2. If the user wanted to add to the following set of
;; exported theorems, they should add the corresponding lemma about s-aux and
;; g-aux using rcdp hypothesis and then add the theorem here about the generic
;; s(et) and g(et) they wish to export from the book.

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
           (as a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (as-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-ag-not-default
  (implies (not (equal (ag a r)
                       (default-get-valu)))
           r)
  :rule-classes :forward-chaining)

;; OK, we add here some properties for typing the records and the values which
;; are stored in the records. This "typing" is pretty generic, but we choose the
;; "bvecp" types for record values because it suits AMD's RTL modeling needs.

(defun bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

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

(local
(defthm bvecp-of-default-get-valu-is-true
  (bvecp (default-get-valu) k)))

(local
(defthm bvecp-of-ifrp-tag-is-false
  (not (bvecp (ifrp-tag) k))))

(in-theory (disable bvecp))

(local
(defthm bv-arrp-implies-rcdp
  (implies (bv-arrp r k)
           (rcdp r))))

(local
(defthm as-aux-maps-bv-rcd-to-bv-rcd
  (implies (and (bv-arrp r k)
                (bvecp v k))
           (bv-arrp (as-aux a v r) k))))

(local
(defthm ag-aux-maps-bv-rcd-to-bvecp
  (implies (bv-arrp r k)
           (bvecp (ag-aux a r) k))))

(local
(defthm bv-arrp-implies-not-ifrp
  (implies (bv-arrp x k)
           (not (ifrp x)))))

(local
(defthm bv-arrp-acl2->rcd-transfers
  (implies (bv-arrp x k)
           (bv-arrp (acl2->rcd x) k))
  :hints (("Goal" :in-theory (enable acl2->rcd)))))

(local
(defthm bv-arrp-rcd->acl2-transfers
  (implies (bv-arrp r k)
           (bv-arrp (rcd->acl2 r) k))
  :hints (("Goal" :in-theory (enable rcd->acl2)))))

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

;; finally we define some "2D" array accessors.

(defmacro ag2 (a b r)
  `(ag (cons ,a ,b) ,r))

(defmacro as2 (a b v r)
  `(as (cons ,a ,b) ,v ,r))


;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable as ag))

; Begin events added March 2005 when it was discovered that they are in
; ../lib/rtlarr.lisp but not in this file.

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
   (("goal" :in-theory (enable bv-arrp)))
   ))

(encapsulate
 ((unknown2 (key size n) t))
 (local (defun unknown2 (key size n) (declare (ignore key size n)) nil))
 (defthm bv-arrp-unknown2
   (bv-arrp (unknown2 key size n) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))
   ))

(defun if1 (x y z)
  (declare (xargs :guard (integerp x)))
  (if (eql x 0) z y))

;BOZO where in lib/ should this go?
(defthm bv-arrp-if1
  (equal (bv-arrp (if1 x y z) n)
         (if1 x (bv-arrp y n) (bv-arrp z n))))

; End events added March 2005 when it was discovered that they are in
; ../lib/rtlarr.lisp but not in this file.
