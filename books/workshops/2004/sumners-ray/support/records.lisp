;; maps.lisp

(in-package "ACL2")

(set-match-free-default :all)

#|

We define properties of a generic map or record accessor function and updater
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

We also include some additional functions and lemmas for defining functions
which recur through a record. The function 'dom takes a record and returns the
set of "keys" or "fields" in the record. We prove the following properties of
'dom with respect 's and 'g.

(defthm dom-of-s
  (equal (dom (s a v r))
         (if v
             (sadd a (dom r))
           (sdrop a (dom r)))))

(defthm in-dom-iff-g
  (iff (in a (dom r))
       (g a r)))

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

(include-book "sets")

;; BEGIN records definitions.

(verify-guards <<)

(defun ill-formed-key ()
  (declare (xargs :guard t))
  "unlikely-we-should-ever-encounter-this-particular-string-as-a-key!?!?!?!")

(defun wf-keyp (x)
  (declare (xargs :guard t))
  (not (equal x (ill-formed-key))))

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
           (equal (caar x) (ill-formed-key))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifrp x) (list (cons (ill-formed-key) x)) x))

(defun rcd->acl2 (x)  ;; inverse of acl2->rcd.
  (declare (xargs :guard t))
  (if (ifrp x) (and (consp x) (consp (car x)) (cdar x)) x))

(defun g-aux (a x) ;; record g(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp x)))
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

(defun g (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (g-aux a (acl2->rcd x)))

(defabbrev acons-if (a v x)
  (if v (cons (cons a v) x) x))

(defun s-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (<< a (caar r)))
         (acons-if a v r))
        ((equal a (caar r))
         (acons-if a v (cdr r)))
        (t
         (cons (car r) (s-aux a v (cdr r))))))

(defun s (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (s-aux a v (acl2->rcd x))))

(defun dom-aux (x)
;;  (declare (xargs :guard (rcdp x)))
  (if (endp x) ()
    (sadd (caar x) (dom-aux (cdr x)))))

(defun dom (x)
  (dom-aux (acl2->rcd x)))


;; We now provide "faster" versions of the above record operations. The bodies
;; of these "f" functions should rewrite immediately to the nicer logic
;; functions.

(defun wf-rcdp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (wf-rcdp (cdr x))
           (cdar x)
           (wf-keyp (caar x))
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(local
(defthm wf-rcdp-implies-rcdp
  (implies (wf-rcdp x)
           (rcdp x))))

(local
(defthm wf-rcdp-implies-not-ifrp
  (implies (wf-rcdp x)
           (not (ifrp x)))))

(defun fast-g (a r)
  (declare (xargs :guard (wf-rcdp r)))
  (cond ((endp r) nil)
        ((equal a (caar r)) (cdar r))
        (t (fast-g a (cdr r)))))

(local
(defthm fast-g-equals-g-aux
  (implies (wf-rcdp r)
           (equal (fast-g a r)
                  (g-aux a r)))))

(defun fg (a r)
  (declare (xargs :guard (wf-rcdp r)))
  (mbe :logic (g a r)
       :exec (fast-g a r)))

(local
(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r))))))

(local
(defthm s-aux-preserves-wf-rcdp
  (implies (and (wf-rcdp r)
                (wf-keyp a))
           (wf-rcdp (s-aux a v r)))))

(defun fast-s (a v r)
  (declare (xargs :guard (wf-rcdp r)))
  (cond ((endp r)
         (acons-if a v ()))
        ((equal a (caar r))
         (acons-if a v (cdr r)))
        ((<< a (caar r))
         (acons-if a v r))
        (t
         (cons (car r) (fast-s a v (cdr r))))))

(local
(defthm fast-s-equals-s-aux
  (implies (wf-rcdp r)
           (equal (fast-s a v r)
                  (s-aux a v r)))))

(defun fs (a v r)
  (declare (xargs :guard (and (wf-keyp a) (wf-rcdp r))))
  (mbe :logic (s a v r)
       :exec (fast-s a v r)))

;; we will need the following theorem in order to prove guards in functions
;; which use fs:

(defthm s-preserves-wf-rcdp
  (implies (and (wf-rcdp r)
                (wf-keyp a))
           (wf-rcdp (s a v r))))


;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r)))))

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
           (not (g-aux a r)))))

(local
(defthm dom-aux-of-s-aux
  (implies (rcdp r)
           (equal (dom-aux (s-aux a v r))
                  (if v
                      (sadd a (dom-aux r))
                    (sdrop a (dom-aux r)))))))

(local
(defthm in-dom-aux-iff-g-aux
  (implies (rcdp r)
           (iff (g-aux a r)
                (in a (dom-aux r))))))

(defun induct-two-records (r1 r2)
  (declare (xargs :measure (+ (len r1) (len r2))))
  (cond ((endp r1) r2)
        ((endp r2) r1)
        ((<< (caar r1) (caar r2))
         (induct-two-records (cdr r1) r2))
        ((<< (caar r2) (caar r1))
         (induct-two-records r1 (cdr r2)))
        ((equal (caar r1) (caar r2))
         (induct-two-records (cdr r1) (cdr r2)))
        (t nil)))

;;;; The output from the following theorems is voluminous,
;;;; and it is pretty impressive that ACL2 can get through
;;;; this proof without any help other than the induction
;;;; scheme. Cool.

(local
(defthm equal-s-aux-redux-1
  (implies (and (rcdp r1)
                (rcdp r2)
                (equal (s-aux a v1 r1) (s-aux a v2 r2)))
           (equal (equal v1 v2) t))
  :hints (("Goal" :induct (induct-two-records r1 r2)))))

(local
(defthm equal-s-aux-redux-2
  (implies (and (rcdp r1)
                (rcdp r2)
                (equal (s-aux a v1 r1) (s-aux a v2 r2)))
           (equal (equal (s-aux a v r1) (s-aux a v r2))
                  t))
  :hints (("Goal" :induct (induct-two-records r1 r2)))))

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

(local
(defthm rcd->acl2-preserves-equality-on-rcds
  (implies (and (rcdp x) (rcdp y))
           (iff (equal (rcd->acl2 x) (rcd->acl2 y))
                (equal x y)))))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final (exported) properties of record g(et) and s(et) ;;;;

(defthm dom-of-s
  (equal (dom (s a v r))
         (if v
             (sadd a (dom r))
           (sdrop a (dom r)))))

(defthm in-dom-iff-g
  (iff (g a r)
       (in a (dom r))))

;; We disable this rule because it may introduce "dom" into contexts where it
;; is not wanted.
(in-theory (disable in-dom-iff-g))

(local
(defthm dom-aux-empty-iff-empty
  (implies (rcdp r)
           (iff (dom-aux r) r))))

(defthm dom-empty-iff-empty
  (iff (dom x) x))

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

(defthm equal-s-redux-1
  (implies (equal (s a v1 r1) (s a v2 r2))
           (equal (equal v1 v2) t))
  :hints (("Goal"
           :use ((:instance equal-s-aux-redux-1
                            (r1 (acl2->rcd r1))
                            (r2 (acl2->rcd r2))))
           :in-theory (disable equal-s-aux-redux-1))))

(defthm equal-s-redux-2
  (implies (equal (s a v1 r1) (s a v2 r2))
           (equal (equal (s a v r1) (s a v r2)) t)))

;; Finally, we prove some "constructive" properties about records. In
;; particular, we want to show the following property:
;;
;;     (not (equal (g a x) x))
;;
;; unfortunately, the above is not true when x is NIL, and may not be true when
;; a is NIL, so we will have a weaker form of the above property:
;;
;;     (implies (and x a) (not (equal (g a x) x)))
;;
;; further, we would like to generalize this to any nesting of g(et)s Well,
;; what we can show is the following property:
;;
;;     (implies (and x a) (< (rcd-count (g a x)) (rcd-count x)))
;;
;; where rcd-count is a natural number measure function.

(defun rcount-msr (r)
  (cond ((null r) 0)
        ((endp r) 1)
        (t (+ 1
              (rcount-msr (car r))
              (rcount-msr (cdr r))))))

(defun rcount (r)
  (declare (xargs :measure (rcount-msr r)))
  (if (null r) 0
    (+ 1
       (rcount (cdar r))
       (rcount (cdr r)))))

(defthm rcount-g-aux-<
  (implies r
           (< (rcount (g-aux a r))
              (rcount r))))

(defthm rcount-g-<
  (implies (and x (wf-keyp a))
           (< (rcount (g a x))
              (rcount x)))
  :hints (("Goal" :in-theory (enable acl2->rcd))))

;; We disable s, g, and dom assuming the rules proven in this book are
;; sufficient to manipulate record terms which are encountered.

(in-theory (disable s g dom))

;; in order to facilitate debugging of proofs which involve (equal (s .) (s .))
;; terms, we include some additional definitions and rules in terms of s and g.

(defun s-clr (a r) (s a nil r))

(defthm equal-s-destruct
  (equal (equal (s a v1 r1) (s a v2 r2))
         (and (equal v1 v2)
              (equal (s-clr a r1) (s-clr a r2)))))

;; we no longer desire to have the parent theorems enabled
(in-theory (disable equal-s-redux-1 equal-s-redux-2))

(defthm g-same-s-clr
  (equal (g a (s-clr a r))
         nil))

(defthm g-diff-s-clr
  (implies (not (equal a b))
           (equal (g a (s-clr b r))
                  (g a r))))

(defthm s-same-s-clr
  (equal (s-clr a (s a v r))
         (s-clr a r)))

(defthm s-diff-s-clr
  (implies (not (equal a b))
           (equal (s-clr b (s a v r))
                  (s a v (s-clr b r)))))

(defthm dom-s-clr
  (equal (dom (s-clr a r))
         (sdrop a (dom r))))

;; we add some rules for dealing with the case where records are collapsed as
;; quoted constants. Some normalization may not occur in this case unless one
;; "cleans" up the quoted constant records.

(defun quoted-rcd-with-non-nil-field (a r)
  (or (and (quotep r)
           (g a (second r)))
      (and (consp r)
           (eq (first r) 's)
           (quoted-rcd-with-non-nil-field a (fourth r)))))

(defthm s-clean-up-rcd
  (implies (syntaxp (and (quotep a)
                         (quoted-rcd-with-non-nil-field (second a) r)))
           (equal (s a v r)
                  (s a v (s-clr a r)))))

(in-theory (disable s-clr))

;; equal-s-destruct may be too aggressive and possibly, the following rules are
;; more appropriate candidates for use (maybe together):

(defthm equal-s-key
  (equal (equal (s a v1 r) (s a v2 r))
         (equal v1 v2)))

(defthm equal-s-rcd
  (equal (equal (s a v r1) (s a v r2))
         (equal (s-clr a r1) (s-clr a r2))))

(in-theory (disable equal-s-destruct equal-s-key equal-s-rcd))

;; we conclude with some useful macros for defining functions which recur
;; through records (for functions of this ilk, use (xargs :measure (rmsr r)) on
;; the record parameter)

(defmacro rempty (r)
  `(not (dom ,r)))

(defmacro rcar (r)
  `(scar (dom ,r)))

(defmacro rcdr (r)
  `(s-clr (rcar ,r) ,r))

(defmacro rmsr (r)
  `(card (dom ,r)))

(in-theory (disable s g))

(defun rts (n r)
  (declare (xargs :guard (and (integerp n) (>= n 0)
                              (wf-rcdp r))))
  (if (zp n) r
    (let ((k (- (nfix (g :b r))
                (nfix (g :b r)))))
      (rts (1- n) (s :b (1+ k) r)))))

(defun frts (n r)
  (declare (xargs :guard (and (integerp n) (>= n 0)
                              (wf-rcdp r))))
  (if (zp n) r
    (let ((k (- (nfix (fg :b r))
                (nfix (fg :b r)))))
      (frts (1- n) (fs :b (1+ k) r)))))

(defun arts (n r)
  (declare (xargs :guard (and (integerp n) (>= n 0)
                              (alistp r))))
  (if (zp n) r
    (let ((k (nfix (cdr (assoc-eq :a r)))))
      (arts (1- n) (acons :a (1+ k) r)))))

