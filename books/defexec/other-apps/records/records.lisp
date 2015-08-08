; Rob Sumners
; Modified to be slightly more extensible by David Rager in 2012

(in-package "ACL2")

#|

This version of records.lisp is based on the usual one, in
books/misc/records.lisp, but supports fast execution via mbe.

We define properties of a generic record accessor function and updater
function.  The basic functions are (mget a r) and (mset a v r) where a is an
address/key, v is a value, r is a record, and (mget a r) returns the value set to
address a in record r, and (mset a v r) returns a new record with address a set to
value v in record r.

The following main lemmas are "exported" about record (mget)et and (s)et:

(defthm mget-same-mset
  (equal (mget a (mset a v r))
         v))

(defthm mget-diff-mset
  (implies (not (equal a b))
           (equal (mget a (mset b v r))
                  (mget a r))))

(defthm mset-same-mget
  (equal (mset a (mget a r) r)
         r))

(defthm mset-same-mset
  (equal (mset a y (mset a x r))
         (mset a y r)))

(defthm mset-diff-mset
  (implies (not (equal a b))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

We also include some auxiliary lemmas which have proven useful.

(defthm access-of-nil-is-nil
  (not (mget a nil)))

(defthm record-mset-cannot-be-nil
  (implies v (mset a v r)))

(defthm record-mget-non-nil-cannot-be-nil
  (implies (mget a r) r))

Furthermore, in an attempt to make this version of records extensible (by this,
we mean that a user can define a new record-like object that uses mset and
mget), we provide a theory event that labels the lemmas we needed when
extending this record in our own work.  To understand why this is helpful,
first see the theory event extensible-records below for a list of the lemmas we
deemed necessary.  Then, after commenting out the form that enables that theory
in file books/demos/modeling/memories.lisp, try to certify that
book (memories.lisp).  Notice that it fails with three subgoals (as of ACL2
5.0).  The memory model needs the lemmas that theory extensible-records
provides.

We normalize the record structures (which allows the 'equal-ity based rewrite
rules) as alists where the keys (cars) are ordered using the total-order added
to ACL2 and defined in the included book. We define a set of "-aux" functions
which assume well-formed records -- defined by well-formed-map -- and then prove the
desired properties using hypothesis assuming well-formed records.

We then remove these well-formed record hypothesis by defining an invertible
mapping (acl2->map) taking any ACL2 object and returning a well-formed
record. We then prove the desired properties using the proper translations of
the -aux functions to the acl2 objects, and subsequently remove the
well-formed record hypothesis.

|#

(include-book "misc/total-order" :dir :system)

;; BEGIN records definitions.

(defun ill-formed-key ()
  (declare (xargs :guard t))
  "unlikely-we-should-ever-encounter-this-particular-string-as-a-key!?!?!?!")

(defun wf-keyp (x)
  (declare (xargs :guard t))
  (not (equal x (ill-formed-key))))

(defun well-formed-map (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (well-formed-map (cdr x))
           (cdar x)
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defun ifmp (x) ;; ill-formed well-formed-map
  (declare (xargs :guard t))
  (or (not (well-formed-map x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (equal (caar x) (ill-formed-key))
           (ifmp (cdar x)))))

(defun acl2->map (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifmp x) (list (cons (ill-formed-key) x)) x))

(defun map->acl2 (x)  ;; inverse of acl2->map.
  (declare (xargs :guard (well-formed-map x)))
  (if (ifmp x) (cdar x) x))

(defun mget-wf (a x) ;; record g(et) when x is a well-formed record.
  (declare (xargs :guard (well-formed-map x)))
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (mget-wf a (cdr x)))))

(defun good-map (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (good-map (cdr x))
           (cdar x)
           (wf-keyp (caar x))
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defthmd good-map-implies-well-formed-map
  (implies (good-map x)
           (well-formed-map x)))
(local (in-theory (enable good-map-implies-well-formed-map)))

(local
(defthm good-map-implies-not-ifmp
  (implies (good-map x)
           (not (ifmp x)))))

(defun mget-fast (a x)
  (declare (xargs :guard (good-map x)))
  (cond ((endp x) nil)
        ((equal a (caar x)) (cdar x))
        (t (mget-fast a (cdr x)))))

(local
(defthm mget-fast-equals-mget-wf
  (implies (good-map x)
           (equal (mget-fast a x)
                  (mget-wf a x)))))

(defun mget (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard (good-map x)))
  (mbe :logic (mget-wf a (acl2->map x))
       :exec (mget-fast a x)))


(defun mset-wf (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (well-formed-map r)))
  (cond ((or (endp r)
             (<< a (caar r)))
         (if v (cons (cons a v) r) r))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        (t
         (cons (car r) (mset-wf a v (cdr r))))))

;; we need the following theorems in order to get the guard for s to verify.

(defthmd mset-wf-is-bounded
  (implies (and (well-formed-map r)
                (mset-wf a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (mset-wf a v r)))))
(local (in-theory (enable mset-wf-is-bounded)))

(local
(defthm mset-wf-preserves-well-formed-map
  (implies (well-formed-map r)
           (well-formed-map (mset-wf a v r)))))

(defthmd mset-wf-preserves-good-map
  (implies (and (good-map r)
                (wf-keyp a))
           (good-map (mset-wf a v r))))
(local (in-theory (enable mset-wf-preserves-good-map)))

(defun mset-fast (a v r)
  (declare (xargs :guard (good-map r)))
  (cond ((endp r)
         (if v (cons (cons a v) r) ()))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        ((<< a (caar r))
         (if v (cons (cons a v) r) r))
        (t
         (cons (car r) (mset-fast a v (cdr r))))))

(local
(defthm mset-fast-equals-mset-wf
  (implies (good-map r)
           (equal (mset-fast a v r)
                  (mset-wf a v r)))))

(defun mset (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard (and (wf-keyp a) (good-map x))))
  (mbe :logic (map->acl2 (mset-wf a v (acl2->map x)))
       :exec (mset-fast a v x)))

;; We need the following property in order to do guard verification of
;; functions which use records:

(defthm mset-preserves-good-map
  (implies (and (good-map x) (wf-keyp a))
           (good-map (mset a v x))))


;;;; basic property of records ;;;;

(local
(defthm well-formed-map-implies-true-listp
  (implies (well-formed-map x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of mset-wf and mget-wf ;;;;

(local
(defthm mget-wf-same-mset-wf
  (implies (well-formed-map r)
           (equal (mget-wf a (mset-wf a v r))
                  v))))

(local
(defthm mget-wf-diff-mset-wf
  (implies (and (well-formed-map r)
                (not (equal a b)))
           (equal (mget-wf a (mset-wf b v r))
                  (mget-wf a r)))))

(local
(defthm mset-wf-same-mget-wf
  (implies (well-formed-map r)
           (equal (mset-wf a (mget-wf a r) r)
                  r))))

(local
(defthm mset-wf-same-mset-wf
  (implies (well-formed-map r)
           (equal (mset-wf a y (mset-wf a x r))
                  (mset-wf a y r)))))

(local
(defthm mset-wf-diff-mset-wf
  (implies (and (well-formed-map r)
                (not (equal a b)))
           (equal (mset-wf b y (mset-wf a x r))
                  (mset-wf a x (mset-wf b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a mset-wf))))))

(local
(defthm mset-wf-non-nil-cannot-be-nil
  (implies (and v (well-formed-map r))
           (mset-wf a v r))))

(local
(defthm mget-wf-is-nil-for-<<
  (implies (and (well-formed-map r)
                (<< a (caar r)))
           (equal (mget-wf a r) nil))))


;;;; properties of acl2->map and map->acl2 ;;;;

(local
(defthm acl2->map-map->acl2-of-well-formed-map
  (implies (well-formed-map x)
           (equal (acl2->map (map->acl2 x))
                  x))))

(local
(defthm acl2->map-returns-well-formed-map
  (well-formed-map (acl2->map x))))

(local
(defthm acl2->map-preserves-equality
  (iff (equal (acl2->map x) (acl2->map y))
       (equal x y))))

(local
(defthm map->acl2-acl2->map-inverse
  (equal (map->acl2 (acl2->map x)) x)))

(local
(defthm map->acl2-of-record-non-nil
  (implies (and r (well-formed-map r))
           (map->acl2 r))))

; The following two theorems are useful when using this implementation of
; records to provide set/get functionality to an interface.

(defthmd good-map-implies-equal-map->acl2-to-x
  (implies (good-map x)
           (equal (map->acl2 x)
                  x)))

(defthmd good-map-implies-equal-acl2->map-to-x
  (implies (good-map x)
           (equal (acl2->map x)
                  x)))

(in-theory (disable acl2->map map->acl2))

;;;; final (exported) properties of record g(et) and s(et) ;;;;

;; NOTE that these theorems basically follow from the "equivalent" properties
;; for mset-wf and mget-wf with well-formed-map hypothesis, and the lemmas about the acl2->map
;; and its inverse map->acl2. If the user wanted to add to the following set of
;; exported theorems, they should add the corresponding lemma about mset-wf and
;; mget-wf using well-formed-map hypothesis and then add the theorem here about the generic
;; s(et) and g(et) they wish to export from the book.

(defthm mget-same-mset
  (equal (mget a (mset a v r))
         v))

(defthm mget-diff-mset
  (implies (not (equal a b))
           (equal (mget a (mset b v r))
                  (mget a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm mget-of-mset-redux
  (equal (mget a (mset b v r))
         (if (equal a b) v (mget a r))))

(in-theory (disable mget-of-mset-redux))

(defthm mset-same-mget
  (equal (mset a (mget a r) r)
         r))

(defthm mset-same-mset
  (equal (mset a y (mset a x r))
         (mset a y r)))

(defthm mset-diff-mset
  (implies (not (equal a b))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a mset)))))

;; the following theorems are less relevant but have been useful in dealing
;; with a default record of NIL.

(defthm mget-of-nil-is-nil
  (not (mget a nil)))

(defthm mset-non-nil-cannot-be-nil
  (implies v (mset a v r))
  :hints (("Goal"
           :in-theory (disable map->acl2-of-record-non-nil)
           :use (:instance map->acl2-of-record-non-nil
                           (r (mset-wf a v (acl2->map r)))))))

(defthm non-nil-if-mget-non-nil
  (implies (mget a r) r)
  :rule-classes :forward-chaining)

;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable mset mget))

(deftheory extensible-records

; Theory useful for extending records.

  '(good-map-implies-equal-map->acl2-to-x
    good-map-implies-equal-acl2->map-to-x

    good-map wf-keyp good-map-implies-well-formed-map mset-wf-is-bounded
    mset-wf-preserves-good-map mset mset-wf))
