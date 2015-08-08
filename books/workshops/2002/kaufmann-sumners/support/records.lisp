; Rob Sumners

(in-package "ACL2")

#|

We define properties of a generic record accessor function and updater
function.  The basic functions are (g a r) and (s a v r) where a is an
address/key, v is a value, r is a record, and (g a r) returns the value set to
address a in record r, and (s a v r) returns a new record with address a set to
value v in record r.

The following main lemmas are "exported" about record (g)et and (s)et:

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

We also include some auxiliary lemmas which have proven useful.

(defthm access-of-nil-is-nil
  (not (g a nil)))

(defthm record-set-cannot-be-nil
  (implies v (s a v r)))

(defthm record-get-non-nil-cannot-be-nil
  (implies (g a r) r))

We normalize the record structures (which allows the 'equal-ity based rewrite
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

(include-book "../../../../misc/total-order")

;; BEGIN records definitions.

(defun rcdp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (rcdp (cdr x))
           (cdar x)
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defthm rcdp-implies-alistp
  (implies (rcdp x) (alistp x)))

(defun ifrp (x) ;; ill-formed rcdp
  (declare (xargs :guard t))
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifrp x) (list (cons nil x)) x))

(defun rcd->acl2 (x)  ;; inverse of acl2->rcd.
  (declare (xargs :guard (rcdp x)))
  (if (ifrp x) (cdar x) x))

(defun g-aux (a x) ;; record g(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp x)))
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

;; we use the name g-aux in this book, but used rcd-access in the paper for
;; presentation reasons. Here we simply document their equivalence using the
;; following macro.
(defmacro rcd-access (a r)
  `(g-aux ,a ,r))

(defun g (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (g-aux a (acl2->rcd x)))

(defun acons-if (a v x)
  (declare (xargs :guard (rcdp x)))
  (if v (acons a v x) x))

(defun s-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (<< a (caar r)))
         (acons-if a v r))
        ((equal a (caar r))
         (acons-if a v (cdr r)))
        (t
         (cons (car r) (s-aux a v (cdr r))))))

;; we use the name s-aux in this book, but used rcd-update in the paper for
;; presentation reasons. Here we simply document their equivalence using the
;; following macro.
(defmacro rcd-update (a v r)
  `(s-aux ,a ,v ,r))

;; we need the following theorems in order to get the guard for s to verify.

(local
(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r))))))

(local
(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r)))))

(defun s (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (rcd-update a v (acl2->rcd x))))


;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm g-aux-same-s-aux
  (implies (rcdp r)
           (equal (g-aux a (s-aux a v r))
                  v))))

(local
(defthm g-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (g-aux a (s-aux b v r))
                  (g-aux a r)))))

(local
(defthm s-aux-same-g-aux
  (implies (rcdp r)
           (equal (s-aux a (g-aux a r) r)
                  r))))

(local
(defthm s-aux-same-s-aux
  (implies (rcdp r)
           (equal (s-aux a y (s-aux a x r))
                  (s-aux a y r)))))

(local
(defthm s-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s))))))

(local
(defthm s-aux-non-nil-cannot-be-nil
  (implies (and v (rcdp r))
           (s-aux a v r))))

(local
(defthm g-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (<< a (caar r)))
           (equal (g-aux a r) nil))))


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

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm g-of-s-redux
  (equal (g a (s b v r))
         (if (equal a b) v (g a r))))

(in-theory (disable g-of-s-redux))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

;; the following theorems are less relevant but have been useful in dealing
;; with a default record of NIL.

(defthm g-of-nil-is-nil
  (not (g a nil)))

(defthm s-non-nil-cannot-be-nil
  (implies v (s a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (s-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-g-non-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)

;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable s g))
