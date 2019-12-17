; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Author: Sol Swords <sswords@centtech.com>
; Based on previous work by Jared Davis -- see ../defrstobj/typed-records.lisp.

(in-package "RSTOBJ2")
(include-book "misc/total-order" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "centaur/misc/introduce-var" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(set-verify-guards-eagerness 2)


; This book develops a generic theory for multi-typed records.


; -----------------------------------------------------------------------------
;
;                    GENERIC DEFINITION OF MULTI-TYPED RECORDS
;
; -----------------------------------------------------------------------------

(encapsulate
  (((mtr-elem-p * *) => *
    :formals (key x))
   ((mtr-elem-default *) => *
    :formals (key))
   ((mtr-elem-fix * *) => *
    :formals (key x)))

  (local (defun mtr-elem-p (key x)
           (declare (ignore key))
           (natp x)))
  (local (defun mtr-elem-default (key)
           (declare (ignore key))
           0))
  (local (defun mtr-elem-fix (key x)
           (declare (ignore key))
           (if (natp x) x 0)))

  (defthm booleanp-of-mtr-elem-p
    (booleanp (mtr-elem-p key x))
    :rule-classes :type-prescription)

  (defthm mtr-elem-p-of-mtr-elem-default
    (mtr-elem-p key (mtr-elem-default key)))

  (defthm mtr-elem-p-of-mtr-elem-fix
    (mtr-elem-p key (mtr-elem-fix key x)))

  (defthm mtr-elem-fix-idempotent
    (implies (mtr-elem-p key x)
             (equal (mtr-elem-fix key x) x))))
;; (defun elem-fix (x)
;;   ;; Standard fixing function.
;;   (if (elem-p x)
;;       x
;;     (elem-default)))

(defun mtr-p1 (x)
  ;; Main typed-record predicate (ordered alist where every key is bound
  ;; to a non-default value).
  (or (null x)
      (and (consp x)
           (consp (car x))
           (mtr-p1 (cdr x))
           (mtr-elem-p (caar x) (cdar x))
           (not (equal (cdar x) (mtr-elem-default (caar x))))
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defun mtr-p (x)
  ;; Full typed-record predicate.  (GOOD-PART . BAD-PART) where the good part
  ;; is the ordred alist of good values, and the bad-part is where we put any
  ;; non-good initial record so we can get the set-of-get theorem.
  (and (consp x)
       (mtr-p1 (car x))
       (car x)
       (not (mtr-p (cdr x)))))

(defun to-mtr (x)
  ;; Interpret any ACL2 object as a typed record.  If it's already a MTR-P,
  ;; we're good.  Otherwise, interpret it as having an empty good part and
  ;; itself as the bad part.
  (if (mtr-p x)
      x
    (cons nil x)))

(defun mtr-bad-part (r)
  ;; Get the bad part from the typed record interpretation of x.  Mainly of
  ;; use for EQUAL-BY-TR-GET.
  (if (mtr-p r)
      (cdr r)
    r))

(defun mtr-get1 (k r)
  ;; Lookup a key in the good part.
  (declare (xargs :guard (mtr-p1 r)))
  (cond ((or (endp r)
             (<< k (caar r)))
         (mtr-elem-default k))
        ((equal k (caar r))
         (cdar r))
        (t
         (mtr-get1 k (cdr r)))))

(defun mtr-set1 (k v r)
  ;; Set a key to a (good) value in the good part.
  (declare (xargs :guard (mtr-p1 r)))
  (cond ((or (endp r)
             (<< k (caar r)))
         (if (equal v (mtr-elem-default k))
             r
           (cons (cons k v) r)))
        ((equal k (caar r))
         (if (equal v (mtr-elem-default k))
             (cdr r)
           (cons (cons k v) (cdr r))))
        (t
         (cons (car r) (mtr-set1 k v (cdr r))))))

(defun mtr-get (k r)
  ;; Main typed record lookup function.
  (mtr-get1 k (car (to-mtr r))))

(defun mtr-set (k v r)
  ;; Main typed record update function.
  (let* ((rec  (to-mtr r))
         (rec1 (car rec))
         (bad  (cdr rec))
         (new-rec1 (mtr-set1 k (mtr-elem-fix k v) rec1)))
    (if new-rec1
        (cons new-rec1 bad)
      bad)))


; Basic supporting theorems about mtr-get1 and mtr-set1.

(defthm mtr-elem-p-of-mtr-get1
  (implies (mtr-p1 r)
           (mtr-elem-p k (mtr-get1 k r))))

(defthm mtr-get1-of-mtr-set1-same
  (implies (and (mtr-p1 r)
                (mtr-elem-p a v))
           (equal (mtr-get1 a (mtr-set1 a v r))
                  v)))

(defthm mtr-get1-of-mtr-set1-diff
  (implies (and (mtr-p1 r)
                (not (equal a b)))
           (equal (mtr-get1 a (mtr-set1 b v r))
                  (mtr-get1 a r))))

(defthm mtr-set1-of-mtr-get1-same
  (implies (mtr-p1 r)
           (equal (mtr-set1 a (mtr-get1 a r) r)
                  r)))

(defthm mtr-set1-of-mtr-set1-same
  (implies (mtr-p1 r)
           (equal (mtr-set1 a y (mtr-set1 a x r))
                  (mtr-set1 a y r))))

(defthm mtr-set1-of-mtr-set1-diff
  (implies (and (mtr-p1 r)
                (not (equal a b)))
           (equal (mtr-set1 b y (mtr-set1 a x r))
                  (mtr-set1 a x (mtr-set1 b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))


; Additional, technical lemmas about mtr-get1 and mtr-set1.

(defthm mtr-set1-is-bounded
  (implies (and (mtr-p1 r)
                (mtr-set1 a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (mtr-set1 a v r)))))

(defthm mtr-set1-preserves-mtr-p
  (implies (and (mtr-p1 r)
                (mtr-elem-p a v))
           (mtr-p1 (mtr-set1 a v r))))

(defthm mtr-set1-under-iff
  (implies (and (mtr-p1 r)
                (mtr-elem-p a v))
           (iff (mtr-set1 a v r)
                (not (and (equal v (mtr-elem-default a))
                          (or (atom r)
                              (and (equal (cdr r) nil)
                                   (equal (caar r) a))))))))


; Main theorems of interest.

(defthm mtr-elem-p-of-mtr-get
  (mtr-elem-p a (mtr-get a x)))

(defthm mtr-get-of-mtr-set-same
  (equal (mtr-get a (mtr-set a v r))
         (mtr-elem-fix a v)))

(defthm mtr-get-of-mtr-set-diff
  (implies (not (equal a b))
           (equal (mtr-get a (mtr-set b v r))
                  (mtr-get a r))))

(defthm mtr-set-of-mtr-get-same
  (equal (mtr-set a (mtr-get a r) r)
         r))

(defthm mtr-set-of-mtr-set-same
  (equal (mtr-set a y (mtr-set a x r))
         (mtr-set a y r)))

(defthm mtr-set-of-mtr-set-diff
  (implies (not (equal a b))
           (equal (mtr-set b y (mtr-set a x r))
                  (mtr-set a x (mtr-set b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))

; The case-splitting rule isn't necessarily a good idea, and originally I
; didn't even introduce it.  But now it seems most convenient to just prove it,
; leave it enabled, and let the user turn it off when it becomes too expensive.

(defthm mtr-get-of-mtr-set-strong
  (equal (mtr-get a (mtr-set b v r))
         (if (equal a b)
             (mtr-elem-fix a v)
           (mtr-get a r))))


; Some additional, occasionally useful theorems.

(defthm mtr-get-of-nil
  ;; May be useful for using NIL as the default typed record
  (equal (mtr-get a nil)
         (mtr-elem-default a)))

(defthm mtr-bad-part-of-mtr-set
  ;; May be useful when trying to use EQUAL-BY-MTR-GET.
  (equal (mtr-bad-part (mtr-set k v r))
         (mtr-bad-part r)))

(in-theory (disable mtr-set mtr-get mtr-bad-part))




; -----------------------------------------------------------------------------
;
;                PICK-A-POINT PROOFS OF TYPED-RECORD EQUALITY
;
; -----------------------------------------------------------------------------

; This is basically copied and pasted from the misc/equal-by-g.lisp book, which
; dealt with ordinary records.  The only twist is that we have to also assume
; that the bad parts are equal.  The reason for this twist: in misc/records,
; the "bad part" is just the value of the key NIL. In our case we can't assume
; the value for NIL can be just anything, because it has to satisfy (mtr-elem-p
; nil x).  So we have the "bad part" be a separate field that isn't accessed by
; a regular key but by a separate function, mtr-bad-part.

; I leave the badguy and the main theorems about it visible, because it seems
; like it may sometimes be useful.

(defund mtr-badguy1 (x y)
  (declare (xargs :verify-guards nil))
  (cond ((atom x)
         (if (atom y)
             nil
           (cons :extra-in-y (car y))))
        ((atom y)
         (cons :extra-in-x (car x)))
        ((equal (car x) (car y))
         (mtr-badguy1 (cdr x) (cdr y)))
        ((<< (caar x) (caar y))
         (cons :extra-in-x (car x)))
        ((equal (caar x) (caar y))
         (cons :mismatch (car x)))
        (t
         (cons :extra-in-y (car y)))))

(local (in-theory (enable mtr-badguy1)))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (mtr-badguy1 x y)) a)
                          (equal (car (mtr-badguy1 x y)) :extra-in-x)
                          (mtr-p1 x)
                          (<< b (caar x)))
                     (not (<< a b)))))

   (defthm lookup-in-x-when-extra-in-x
     (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-x)
                   (mtr-p1 x)
                   (mtr-p1 y))
              (not (equal (mtr-get1 (cadr (mtr-badguy1 x y)) x)
                          (mtr-elem-default (cadr (mtr-badguy1 x y)))))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-x)
                          (<< a (caar x))
                          (<< (cadr (mtr-badguy1 x y)) a)
                          (mtr-p1 x))
                     (not (<< a (caar y))))))

   (defthm lookup-in-y-when-extra-in-x
     (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-x)
                   (mtr-p1 x)
                   (mtr-p1 y))
              (and (equal (mtr-get1 (cadr (mtr-badguy1 x y)) y)
                          (mtr-elem-default (cadr (mtr-badguy1 x y)))))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (mtr-badguy1 x y)) a)
                          (equal (car (mtr-badguy1 x y)) :extra-in-y)
                          (<< b (caar x))
                          (mtr-p1 y)
                          (<< b (caar y)))
                     (not (<< a b)))))

   (defthm lookup-in-y-when-extra-in-y
     (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-y)
                   (mtr-p1 x)
                   (mtr-p1 y))
              (not (equal (mtr-get1 (cadr (mtr-badguy1 x y)) y)
                          (mtr-elem-default (cadr (mtr-badguy1 x y)))))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-y)
                          (<< a (caar x))
                          (<< (cadr (mtr-badguy1 x y)) a)
                          (mtr-p1 y))
                     (not (<< a (caar y))))))

   (defthm lookup-in-x-when-extra-in-y
     (implies (and (equal (car (mtr-badguy1 x y)) :extra-in-y)
                   (mtr-p1 x)
                   (mtr-p1 y))
              (equal (mtr-get1 (cadr (mtr-badguy1 x y)) x)
                     (mtr-elem-default (cadr (mtr-badguy1 x y))))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (mtr-badguy1 x y)) a)
                          (equal (car (mtr-badguy1 x y)) :mismatch)
                          (mtr-p1 x)
                          (mtr-p1 y)
                          (<< b (caar x))
                          (<< b (caar y)))
                     (not (<< a b)))))

   (local (defthm l1
            (implies (and (equal (car (mtr-badguy1 x y)) :mismatch)
                          (mtr-p1 x)
                          (mtr-p1 y)
                          (<< a (caar x))
                          (<< (cadr (mtr-badguy1 x y)) a))
                     (not (<< a (caar y))))))

   (defthm mismatch-when-mismatch
     (implies (and (equal (car (mtr-badguy1 x y)) :mismatch)
                   (mtr-p1 x)
                   (mtr-p1 y))
              (equal (equal (mtr-get1 (cadr (mtr-badguy1 x y)) x)
                            (mtr-get1 (cadr (mtr-badguy1 x y)) y))
                     nil)))))



; It's easy to see that these are the only cases, and hence it is clear that
; the mtr-badguy1 works and if it reports a mismatch, it really is a mismatch.

(local (defthm mtr-badguy1-cases
         (or (not (mtr-badguy1 x y))
             (equal (car (mtr-badguy1 x y)) :mismatch)
             (equal (car (mtr-badguy1 x y)) :extra-in-x)
             (equal (car (mtr-badguy1 x y)) :extra-in-y))
         :rule-classes nil))

(local (defthm mtr-get1-of-mtr-badguy1
         (implies (and (mtr-badguy1 x y)
                       (mtr-p1 x)
                       (mtr-p1 y))
                  (not (equal (mtr-get1 (cadr (mtr-badguy1 x y)) x)
                              (mtr-get1 (cadr (mtr-badguy1 x y)) y))))
         :hints(("Goal" :use ((:instance mtr-badguy1-cases))))))

(local (defthm mtr-badguy1-unless-equal
         (implies (and (not (equal x y))
                       (mtr-p1 x)
                       (mtr-p1 y))
                  (mtr-badguy1 x y))))

(defund mtr-badguy (x y)
  (declare (xargs :verify-guards nil))
  (mtr-badguy1 (car (to-mtr x))
              (car (to-mtr y))))

(defthm mtr-badguy-finds-counterexample
  (implies (mtr-badguy x y)
           (not (equal (mtr-get (cadr (mtr-badguy x y)) x)
                       (mtr-get (cadr (mtr-badguy x y)) y))))
  :hints(("Goal" :in-theory (enable mtr-get
                                    mtr-badguy))))

(defthm mtr-badguy-unless-equal
  (implies (and (not (equal x y))
                (equal (mtr-bad-part x) (mtr-bad-part y)))
           (mtr-badguy x y))
  :hints(("Goal" :in-theory (enable to-mtr
                                    mtr-bad-part
                                    mtr-badguy))))


; The theorem EQUAL-BY-MTR-GET lets us show that two typed records are equal by
; showing (1) that their every key is bound to the same value, and (2) that
; their badparts are the same.

(encapsulate
  (((equal-by-mtr-get-hyp) => *)
   ((equal-by-mtr-get-lhs) => *)
   ((equal-by-mtr-get-rhs) => *))

  (local (defun equal-by-mtr-get-hyp () nil))
  (local (defun equal-by-mtr-get-lhs () nil))
  (local (defun equal-by-mtr-get-rhs () nil))

  (defthm equal-by-mtr-get-constraint
    (implies (equal-by-mtr-get-hyp)
             (and (equal (mtr-get arbitrary-key (equal-by-mtr-get-lhs))
                         (mtr-get arbitrary-key (equal-by-mtr-get-rhs)))
                  (equal (mtr-bad-part (equal-by-mtr-get-lhs))
                         (mtr-bad-part (equal-by-mtr-get-rhs)))))))

(defthm equal-by-mtr-get
  (implies (equal-by-mtr-get-hyp)
           (equal (equal-by-mtr-get-lhs)
                  (equal-by-mtr-get-rhs)))
  :hints(("Goal"
          :in-theory (disable mtr-badguy-finds-counterexample mtr-badguy)
          :use ((:instance mtr-badguy-finds-counterexample
                           (x (equal-by-mtr-get-lhs))
                           (y (equal-by-mtr-get-rhs)))))))




; -----------------------------------------------------------------------------
;
;                   ALMOST-EQUALITIES BETWEEN NESTS OF SETS
;
; -----------------------------------------------------------------------------
;
; The theorem we now prove is something that Jared, Sol, and Anna came up with
; after experimenting with a toy machine model.  The problem we ran into was
; that we sometimes encountered goals of the form:
;
;   (implies ...
;            (equal (s :key1 val1 (s :key2 val2 (s :key3 val3 st)))
;                   (s :key1 val1' (s :key2 val2' (s :key3 val3' st)))))
;
; Where usually we had, e.g., VAL1 = VAL1', but there was *some* mistake that
; meant some particular VALi was not equal to VALi'.  Because of this mistake,
; the EQUAL could obviously not be resolved by ordinary (EQUAL X X) reduction.
;
; The problem is that these terms can be large, making it hard to figure out
; which VALi and VALi' are not equal.
;
; The idea of this theorem is that if we want to prove an equality like this,
; we will reduce it to proving that for some arbitrary key ARB,
;
;    (= (g ARB (s :key1 val1 .......))
;       (g ARB (s :key1 val1' .......)))
;
; As long as the strong form of the G-over-S rule is enabled, then the G can
; march through each side of the equality and split the goal into cases.  The
; first case is that G is :key1 and we need to show VAL1==VAL1'.  If that's
; easy we proceed to the next case and so on.  This process should result in
; reducing the goal down to just (= VALi VALi') for the values that don't
; obviously have this property.
;
; The rule has some tricky syntaxp hypotheses to prevent it from firing unless
; we're really trying to show an equality between s-nests.  For instance, if we
; have a hyp that is (equal (s :key1 val1 ...) (s :key1 val1' ...)), then we'll
; want to do something that doesn't reduce the equality to an arbitrary key.

(defthm equal-of-mtr-set
  (implies
   (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (mtr-set ,a ,v ,x) ,y) mfc state)
                (acl2::rewriting-positive-literal-fn `(equal ,y (mtr-set ,a ,v ,x)) mfc state)))
   (equal (equal (mtr-set a v x) y)
          (and (equal (mtr-bad-part (mtr-set a v x))
                      (mtr-bad-part y))
               (let ((key (acl2::introduce-var 'arbitrary-key
                                               (hide (cadr (mtr-badguy (mtr-set a v x) y))))))
                 (and (equal (mtr-get key (mtr-set a v x))
                             (mtr-get key y)))))))
  :hints(("Goal"
          :expand (:free (x) (hide x))
          :in-theory (enable acl2::introduce-var)
          :use ((:instance mtr-badguy-finds-counterexample
                           (x (mtr-set a v x))
                           (y y))
                (:instance mtr-badguy-unless-equal
                           (x (mtr-set a v x))
                           (y y))))))


; This commented out stuff was an earlier attempt to solve the same problem.
; We think the rule above is much nicer, though.

;; (defsection tr-decompose-with-key

;;   (local (defthm help0
;;            (implies (not (equal (mtr-elem-fix a) (mtr-elem-fix b)))
;;                     (equal (EQUAL (MTR-SET K A X) (MTR-SET K B Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable MTR-GET-OF-MTR-SET-SAME)
;;                    :use ((:instance MTR-GET-OF-MTR-SET-SAME
;;                                     (a k)
;;                                     (v a)
;;                                     (r x))
;;                          (:instance MTR-GET-OF-MTR-SET-SAME
;;                                     (a k)
;;                                     (v b)
;;                                     (r y)))))))

;;   (local (defthm help1
;;            (implies (not (EQUAL (MTR-BAD-PART X) (MTR-BAD-PART Y)))
;;                     (equal (EQUAL (MTR-SET K v1 X)
;;                                   (MTR-SET K v2 Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable MTR-BAD-PART-OF-MTR-SET)
;;                    :use ((:instance MTR-BAD-PART-OF-MTR-SET
;;                                     (v v1) (r x))
;;                          (:instance MTR-BAD-PART-OF-MTR-SET
;;                                     (v v2) (r y)))))))

;;   (local (defthm help2
;;            (implies (and (not (equal k nonk))
;;                          (not (EQUAL (mtr-get nonk X) (mtr-get nonk Y))))
;;                     (equal (EQUAL (MTR-SET K v1 X)
;;                                   (MTR-SET K v2 Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable MTR-GET-OF-MTR-SET-diff)
;;                    :use ((:instance MTR-GET-OF-MTR-SET-diff
;;                                     (a nonk) (b k) (v v1) (r x))
;;                          (:instance MTR-GET-OF-MTR-SET-diff
;;                                     (a nonk) (b k) (v v2) (r y)))))))

;;   (local (defthmd part1
;;            (implies (equal (mtr-set k v1 x)
;;                            (mtr-set k v2 y))
;;                     (and (equal (mtr-elem-fix v1) (mtr-elem-fix v2))
;;                          (equal (mtr-set k (mtr-elem-default) x)
;;                                 (mtr-set k (mtr-elem-default) y))))
;;            :hints(("Goal" :use ((:functional-instance
;;                                  equal-by-mtr-get
;;                                  (equal-by-mtr-get-lhs (lambda () (mtr-set k (mtr-elem-default) x)))
;;                                  (equal-by-mtr-get-rhs (lambda () (mtr-set k (mtr-elem-default) y)))
;;                                  (equal-by-mtr-get-hyp (lambda ()
;;                                                         (equal (mtr-set k v1 x)
;;                                                                (mtr-set k v2 y)))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((equal arbitrary-key k)))))))

;;   (local (defthmd part2
;;            (implies (and (equal (mtr-elem-fix v1) (mtr-elem-fix v2))
;;                          (equal (mtr-set k (mtr-elem-default) x)
;;                                 (mtr-set k (mtr-elem-default) y)))
;;                     (equal (mtr-set k v1 x)
;;                            (mtr-set k v2 y)))
;;            :hints(("Goal"
;;                    :use ((:functional-instance
;;                           equal-by-mtr-get
;;                           (equal-by-mtr-get-lhs (lambda () (mtr-set k v1 x)))
;;                           (equal-by-mtr-get-rhs (lambda () (mtr-set k v2 y)))
;;                           (equal-by-mtr-get-hyp (lambda ()
;;                                                  (and (equal (mtr-elem-fix v1) (mtr-elem-fix v2))
;;                                                       (equal (mtr-set k (mtr-elem-default) x)
;;                                                              (mtr-set k (mtr-elem-default) y))))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((equal arbitrary-key k)))))))

;;   (defthm tr-decompose-with-key
;;     (implies (syntaxp (or (not (equal v1 (list 'quote (mtr-elem-default))))
;;                           (not (equal v2 (list 'quote (mtr-elem-default))))))
;;              (equal (equal (mtr-set k v1 x)
;;                            (mtr-set k v2 y))
;;                     (and (equal (mtr-elem-fix v1) (mtr-elem-fix v2))
;;                          (equal (mtr-set k (mtr-elem-default) x)
;;                                 (mtr-set k (mtr-elem-default) y)))))
;;     :hints(("Goal"
;;             :use ((:instance part1)
;;                   (:instance part2))))))







; -----------------------------------------------------------------------------
;
;                   GENERIC ARRAY/TYPED RECORD SUPPORT
;
; -----------------------------------------------------------------------------

; We now adapt the definitions we used to implement untyped array/record pairs
; so that they deal with typed arrays and records.  These functions are useful
; in converting between records and arrays (by which we mean true-listp's of a
; certain length that are read and written by position, in the logical sense of
; STOBJ arrays).

(defun mtr-array-p1 (n x)
  (declare (xargs :measure (len x)
                  :guard (natp n)))
  (if (atom x)
      (eq x nil)
    (and (mtr-elem-p (nfix n) (car x))
         (mtr-array-p1 (+ 1 (nfix n)) (cdr x)))))

(defthm true-listp-when-mtr-array-p1
  (implies (mtr-array-p1 n x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm mtr-array-p1-of-update-nth
  (implies (and (mtr-array-p1 m arr)
                (mtr-elem-p (+ (nfix m) (nfix n)) val)
                (< (nfix n) (len arr)))
           (mtr-array-p1 m (update-nth n val arr)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm mtr-elem-p-of-nth-when-mtr-array-p1
  (implies (and (mtr-array-p1 m arr)
                (< (nfix n) (len arr)))
           (mtr-elem-p (+ (nfix m) (nfix n)) (nth n arr)))
  :hints(("Goal" :in-theory (enable nth))))

(defun mtr-array-p (x)
  (mtr-array-p1 0 x))

(defthm true-listp-when-mtr-array-p
  (implies (mtr-array-p x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(defthm mtr-array-p-of-update-nth
  (implies (and (mtr-array-p arr)
                (mtr-elem-p (nfix n) val)
                (< (nfix n) (len arr)))
           (mtr-array-p (update-nth n val arr))))

(defthm mtr-elem-p-of-nth-when-mtr-array-p
  (implies (and (mtr-array-p arr)
                (equal nn (nfix n))
                (< nn (len arr)))
           (mtr-elem-p nn (nth n arr)))
  :hints (("goal" :use ((:instance mtr-elem-p-of-nth-when-mtr-array-p1
                         (m 0)))
           :in-theory (disable mtr-elem-p-of-nth-when-mtr-array-p1))))




(defun array-to-mtr (n arr rec)
  ;; Store arr[0]...arr[n] into rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      rec
    (let ((n (- n 1)))
      (array-to-mtr n arr (mtr-set n (nth n arr) rec)))))

(defun mtr-to-array (n rec arr)
  ;; Load arr[0]...arr[n] from rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      arr
    (let ((n (- n 1)))
      (mtr-to-array n rec (update-nth n (mtr-get n rec) arr)))))

(defun mtr-delete-indices (n rec)
  ;; Delete rec[0]...rec[n] from rec
  (declare (xargs :guard (natp n)))
  (if (zp n)
      rec
    (let ((n (- n 1)))
      (mtr-delete-indices n (mtr-set n (mtr-elem-default n) rec)))))

(defun array-mtr-pair-p (arr rec len)
  ;; Recognize array/record pairs where the array has size LEN and the record
  ;; has nothing in keys 0...LEN-1.
  (declare (xargs :guard (natp len)))
  (and (mtr-array-p arr)
       (= (len arr) len)
       (equal rec (mtr-delete-indices len rec))))



(defthm mtr-get-of-array-to-mtr
  (equal (mtr-get key (array-to-mtr n arr rec))
         (if (and (natp key)
                  (< key (nfix n)))
             (mtr-elem-fix key (nth key arr))
           (mtr-get key rec))))

(defthm mtr-bad-part-of-array-to-mtr
  (equal (mtr-bad-part (array-to-mtr n arr rec))
         (mtr-bad-part rec)))


(defthm true-listp-of-mtr-to-array
  (implies (true-listp arr)
           (true-listp (mtr-to-array n rec arr))))

(defthm len-of-mtr-to-array
  (equal (len (mtr-to-array n rec arr))
         (max  (nfix n) (len arr))))

(defthm mtr-array-p1-of-nthcdr
  (implies (mtr-array-p1 n x)
           (mtr-array-p1 (+ (nfix n) (nfix m)) (nthcdr m x))))

(local (defthm nthcdr-of-update-nth
         (equal (nthcdr n (update-nth n v x))
                (update-nth 0 v (nthcdr n x)))))

(local (defthm cdr-of-nthcdr-nminus1
         (implies (posp n)
                  (equal (cdr (nthcdr (+ -1 n) x))
                         (nthcdr n x)))))

(defthm mtr-array-p-of-mtr-to-array-when-mtr-array-p1
  (implies (and (mtr-array-p1 n (nthcdr n arr))
                (<= (nfix n) (len arr)))
           (mtr-array-p (mtr-to-array n rec arr))))

(defthm mtr-array-p-of-mtr-to-array
  (implies (and (mtr-array-p arr)
                (<= (nfix n) (len arr)))
           (mtr-array-p (mtr-to-array n rec arr)))
  :hints (("goal" :use ((:instance mtr-array-p-of-mtr-to-array-when-mtr-array-p1)
                        (:instance mtr-array-p1-of-nthcdr (n 0) (m n) (x arr))))))

(local (in-theory (disable mtr-array-p)))

(defthm nth-of-mtr-to-array
  (equal (nth key (mtr-to-array n rec arr))
         (cond ((< (nfix key) (nfix n))
                (mtr-get (nfix key) rec))
               (t
                (nth key arr)))))

(defthm nth-of-mtr-to-array-of-array-to-mtr
  (implies (and (natp key)
                (natp n)
                (< key n)
                (<= n (len arr1))
                (equal (len arr1) (len arr2))
                (mtr-array-p arr1))
           (equal (nth key (mtr-to-array n (array-to-mtr n arr1 rec) arr2))
                  (nth key arr1))))

(defthm mtr-to-array-of-array-to-mtr
  (implies (and (force (equal (len arr1) (len arr2)))
                (force (equal n (len arr1)))
                (force (natp (len arr1)))
                (force (mtr-array-p arr1))
                (force (mtr-array-p arr2)))
           (equal (mtr-to-array n (array-to-mtr n arr1 rec) arr2)
                  arr1))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (equal (len arr1) (len arr2))
                                           (equal n (len arr1))
                                           (mtr-array-p arr1)
                                           (mtr-array-p arr2))))
                 (equal-by-nths-lhs (lambda ()
                                      (mtr-to-array n (array-to-mtr n arr1 rec) arr2)))
                 (equal-by-nths-rhs (lambda ()
                                      arr1)))))))

(defthm mtr-to-array-idempotent
  (implies (and (force (natp (len arr1)))
                (force (mtr-array-p arr1)))
           (equal (mtr-to-array n rec1 (mtr-to-array n rec2 arr1))
                  (mtr-to-array n rec1 arr1)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (natp (len arr1))
                                           (mtr-array-p arr1))))
                 (equal-by-nths-lhs (lambda ()
                                      (mtr-to-array n rec1 (mtr-to-array n rec2 arr1))))
                 (equal-by-nths-rhs (lambda ()
                                      (mtr-to-array n rec1 arr1))))))))

(defthm mtr-to-array-of-mtr-set
  (implies (and (natp n)
                (natp i)
                (< i n)
                (mtr-elem-p i val)
                (mtr-array-p arr))
           (equal (mtr-to-array n (mtr-set i val rec) arr)
                  (update-nth i val (mtr-to-array n rec arr))))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (natp n)
                                           (natp i)
                                           (< i n)
                                           (mtr-elem-p i val)
                                           (mtr-array-p arr))))
                 (equal-by-nths-lhs (lambda ()
                                      (mtr-to-array n (mtr-set i val rec) arr)))
                 (equal-by-nths-rhs (lambda ()
                                      (update-nth i val (mtr-to-array n rec arr)))))))))



(defthm mtr-delete-indices-of-nil
  (equal (mtr-delete-indices n nil)
         nil)
  ;; I need this yucky hint because this is breaking the typed-record abstraction
  ;; and looking at its actual representation.
  :hints(("Goal" :in-theory (enable mtr-set))))

(defthm mtr-bad-part-of-mtr-delete-indices
  (equal (mtr-bad-part (mtr-delete-indices n rec))
         (mtr-bad-part rec)))

(defthm mtr-get-of-mtr-delete-indices
  (equal (mtr-get key (mtr-delete-indices n rec))
         (if (and (natp key)
                  (< key (nfix n)))
             (mtr-elem-default key)
           (mtr-get key rec))))

(defthm mtr-delete-indices-of-array-to-mtr
  (equal (mtr-delete-indices n (array-to-mtr n arr rec))
         (mtr-delete-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-mtr-get
                 (equal-by-mtr-get-hyp (lambda () t))
                 (equal-by-mtr-get-lhs (lambda ()
                                        (mtr-delete-indices n (array-to-mtr n arr rec))))
                 (equal-by-mtr-get-rhs (lambda ()
                                        (mtr-delete-indices n rec))))))))

(defthm mtr-delete-indices-of-mtr-set
  (implies (and (natp n)
                (natp i)
                (< i n))
           (equal (mtr-delete-indices n (mtr-set i val rec))
                  (mtr-delete-indices n rec)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-mtr-get
                 (equal-by-mtr-get-hyp (lambda ()
                                   (and (natp n)
                                        (natp i)
                                        (< i n))))
                 (equal-by-mtr-get-lhs (lambda ()
                                   (mtr-delete-indices n (mtr-set i val rec))))
                 (equal-by-mtr-get-rhs (lambda ()
                                   (mtr-delete-indices n rec))))))))


(defthm array-to-mtr-inverse-lemma
  (equal (mtr-get key (array-to-mtr n
                                  (mtr-to-array n rec arr)
                                  (mtr-delete-indices n rec)))
         (mtr-get key rec)))

(defthm array-to-mtr-inverse
  (equal (array-to-mtr n
                      (mtr-to-array n rec arr)
                      (mtr-delete-indices n rec))
         rec)
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-mtr-get
                 (equal-by-mtr-get-hyp (lambda () t))
                 (equal-by-mtr-get-lhs (lambda ()
                                        (array-to-mtr n
                                                     (mtr-to-array n rec arr)
                                                     (mtr-delete-indices n rec))))
                 (equal-by-mtr-get-rhs (lambda () rec)))))))

(defthm mtr-delete-indices-idempotent
  (equal (mtr-delete-indices n (mtr-delete-indices n rec))
         (mtr-delete-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-mtr-get
                 (equal-by-mtr-get-hyp (lambda () t))
                 (equal-by-mtr-get-lhs (lambda ()
                                        (mtr-delete-indices n (mtr-delete-indices n rec))))
                 (equal-by-mtr-get-rhs (lambda ()
                                        (mtr-delete-indices n rec))))))))






(defthm array-mtr-pair-p-of-nil
  (implies (and (mtr-array-p arr)
                (equal (len arr) n))
           (array-mtr-pair-p arr nil n)))

(defthm array-mtr-pair-p-of-update-nth
  (implies (and (array-mtr-pair-p arr rec len)
                (force (natp n))
                (force (natp len))
                (force (< n len))
                (force (mtr-elem-p n val)))
           (array-mtr-pair-p (update-nth n val arr) rec len)))

(defthm array-mtr-pair-p-of-mtr-delete-indices
  (implies (array-mtr-pair-p arr rec len)
           (array-mtr-pair-p arr (mtr-delete-indices len rec) len)))




; We now show that whenever either the ARR or REC part of an array/record pair
; are different, then the "logical record" obtained by array-to-mtr is
; different.

(local
 (defsection equal-of-array-to-mtr-part1

; First we show that if the ARRs are well-formed but differ, then there is some
; key that ends up with a different value and hence the logical records are
; different.

   (local (defun nth-badguy (x y)
            (cond ((or (not (consp x))
                       (not (consp y)))
                   0)
                  ((equal (car x) (car y))
                   (+ 1 (nth-badguy (cdr x) (cdr y))))
                  (t
                   0))))

   (local (defthm nth-badguy-bounded
            (<= (nth-badguy x y) (len x))
            :rule-classes :linear))

   (local (defthm nth-badguy-is-bad
            (implies (and (equal (len x) (len y))
                          (not (equal (nth-badguy x y) (len x))))
                     (not (equal (nth (nth-badguy x y) x)
                                 (nth (nth-badguy x y) y))))))

   (local (defthm nth-badguy-is-equality
            (implies (and (equal (len x) (len y))
                          (true-listp x)
                          (true-listp y))
                     (equal (equal (nth-badguy x y) (len x))
                            (equal x y)))))

   (local (defthm mtr-elem-p-of-nth-when-mtr-array-p-split
            (implies (and (equal nn (nfix n))
                          (mtr-array-p arr))
                     (equal (mtr-elem-p nn (nth n arr))
                            (if (< (nfix n) (len arr))
                                t
                              (mtr-elem-p nn nil))))
            :hints(("Goal" :in-theory (disable nth acl2::nth-when-zp)
                    :do-not-induct t))))

   (local (defthmd main-lemma
            (implies (and (not (equal arr1 arr2))
                          (equal (len arr1) (len arr2))
                          (natp (len arr1))
                          (mtr-array-p arr1)
                          (mtr-array-p arr2))
                     (let ((key (nth-badguy arr1 arr2)))
                       (not (equal (mtr-get key (array-to-mtr (len arr1) arr1 rec1))
                                   (mtr-get key (array-to-mtr (len arr1) arr2 rec2))))))
            :hints(("Goal"
                    :do-not '(generalize fertilize)
                    :do-not-induct t))))

   (defthm equal-of-array-to-mtr-part1
     (implies (and (not (equal arr1 arr2))
                   (equal (len arr1) (len arr2))
                   (natp (len arr1))
                   (mtr-array-p arr1)
                   (mtr-array-p arr2))
              (not (equal (array-to-mtr (len arr1) arr1 rec1)
                          (array-to-mtr (len arr1) arr2 rec2))))
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :do-not-induct t
             :use ((:instance main-lemma)))))))


; Now we turn our attention to the record.  There are two ways for the records
; to be different: they can have different badparts or some different key.  The
; badpart case is trivial:

(local
 (defthm equal-of-array-to-mtr-part2
   (implies (case-split (not (equal (mtr-bad-part rec1) (mtr-bad-part rec2))))
            (not (equal (array-to-mtr n arr1 rec1)
                        (array-to-mtr n arr2 rec2))))
   :hints(("Goal"
           :do-not '(generalize fertilize)
           :do-not-induct t
           :in-theory (disable mtr-bad-part-of-array-to-mtr)
           :use ((:instance mtr-bad-part-of-array-to-mtr (arr arr1) (rec rec1))
                 (:instance mtr-bad-part-of-array-to-mtr (arr arr2) (rec rec2)))))))


(local
 (defsection equal-of-array-to-mtr-part3

   (local
    (defthm gross

; This is horrible.  We basically are arguing that the mtr-badguy can't give us
; an index that's going to lead us to the array, because we know that the
; records each bind those keys to NIL.

      (let ((key (cadr (mtr-badguy rec1 rec2))))
        (implies (and (not (equal rec1 rec2))
                      (equal (mtr-bad-part rec1) (mtr-bad-part rec2))
                      (equal rec1 (mtr-delete-indices n rec1))
                      (equal rec2 (mtr-delete-indices n rec2))
                      (natp n)
                      (natp key))
                 (<= n key)))
      :hints(("Goal"
              :do-not '(generalize fertilize)
              :do-not-induct t
              :in-theory (disable mtr-get-of-mtr-delete-indices
                                  mtr-delete-indices
                                  mtr-badguy
                                  mtr-badguy-finds-counterexample)
              :use ((:instance mtr-get-of-mtr-delete-indices
                               (key (cadr (mtr-badguy rec1 rec2)))
                               (n n)
                               (rec rec1))
                    (:instance mtr-get-of-mtr-delete-indices
                               (key (cadr (mtr-badguy rec1 rec2)))
                               (n n)
                               (rec rec2))
                    (:instance mtr-badguy-finds-counterexample
                               (x rec1)
                               (y rec2)))))))

   (local
    (defthm main-lemma
      (implies (and (not (equal rec1 rec2))
                    (equal (mtr-bad-part rec1) (mtr-bad-part rec2))
                    (equal rec1 (mtr-delete-indices len rec1))
                    (equal rec2 (mtr-delete-indices len rec2)))
               (let ((key (cadr (mtr-badguy rec1 rec2))))
                 (not (equal (mtr-get key (array-to-mtr len arr1 rec1))
                             (mtr-get key (array-to-mtr len arr2 rec2))))))
      :hints(("Goal"
              :in-theory (disable mtr-badguy mtr-get-of-array-to-mtr gross)
              :do-not '(generalize fertilize)
              :do-not-induct t
              :use ((:instance mtr-get-of-array-to-mtr
                               (key (cadr (mtr-badguy rec1 rec2)))
                               (n len)
                               (arr arr1)
                               (rec rec1))
                    (:instance mtr-get-of-array-to-mtr
                               (key (cadr (mtr-badguy rec1 rec2)))
                               (n len)
                               (arr arr2)
                               (rec rec2))
                    (:instance gross
                               (n (nfix len))))))))

   (defthm equal-of-array-to-mtr-part3
     (implies (and (not (equal rec1 rec2))
                   (case-split (equal (mtr-bad-part rec1) (mtr-bad-part rec2)))
                   (equal rec1 (mtr-delete-indices len rec1))
                   (equal rec2 (mtr-delete-indices len rec2)))
              (not (equal (array-to-mtr len arr1 rec1)
                          (array-to-mtr len arr2 rec2))))
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :do-not-induct t
             :in-theory (disable mtr-delete-indices main-lemma mtr-badguy)
             :use ((:instance main-lemma)))))))

(local (defthmd equal-of-array-to-mtr-orig
         ;; This is the original version I proved.  But, it turns out to be difficult
         ;; to unify with this and apply this rule.  The rule below is better.
         (implies (and (array-mtr-pair-p arr1 rec1 len)
                       (array-mtr-pair-p arr2 rec2 len)
                       (natp len))
                  (equal (equal (array-to-mtr len arr1 rec1)
                                (array-to-mtr len arr2 rec2))
                         (and (equal arr1 arr2)
                              (equal rec1 rec2))))
         :hints(("Goal"
                 :do-not '(generalize fertilize)
                 :do-not-induct t
                 :in-theory (e/d (array-mtr-pair-p)
                                 (mtr-delete-indices))
                 :cases ((equal rec1 rec2))))))

(defthm equal-of-array-to-mtr
  (implies (and (array-mtr-pair-p arr1 rec1 len1)
                (array-mtr-pair-p arr2 rec2 len2)
                (equal len1 len)
                (equal len2 len)
                (natp len))
           (equal (equal (array-to-mtr len arr1 rec1)
                         (array-to-mtr len arr2 rec2))
                  (and (equal arr1 arr2)
                       (equal rec1 rec2))))
  :hints(("Goal"
          :in-theory (disable mtr-delete-indices
                              array-to-mtr
                              array-mtr-pair-p)
          :use ((:instance equal-of-array-to-mtr-orig)))))









