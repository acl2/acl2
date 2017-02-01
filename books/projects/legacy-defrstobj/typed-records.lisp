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
; Original author: Jared Davis <jared@centtech.com>

(in-package "RSTOBJ")
(include-book "misc/total-order" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "centaur/misc/introduce-var" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "array-lemmas"))
(set-verify-guards-eagerness 2)


; typed-records.lisp
;
; This file is similar in spirit to coi/records/defrecord.lisp, which was
; described in the following paper.
;
;   David Greve and Matthew Wilding.  Typed ACL2 Records. ACL2 Workshop 2003.
;
; Loosely speaking, our goal here is to develop a record-like structure where
; the values always have a particular type.  The resulting structure satisfies
; almost the same theorems as in the misc/records book, but the g-same-s
; theorem becomes
;
;   (g a (s a v r)) = (foo-fix v)      ; instead of just being v
;
; And we gain the theorem (foop (g a r)).
;
; Greve and Wilding accomplish this by starting with an ordinary record, but
; instead of just storing values or fixed values into its slots, they instead
; store ENTRIES of the form (FOO . NON-ENTRY), where the FOO must be a foop
; that is not the default foop.  I started with this, but when I tried to
; extend it to be able to view a STOBJ array as a typed record, I ran into
; trouble.  I didn't see a good way to prove something akin to EQUAL-BY-G, and
; without that it didn't seem easy to adapt the basic approach I'd developed
; for untyped records to typed records.
;
; I went to Sol's office to gripe about this, and we started to try to more
; precisely understand what was problematic.  In a short time, we had come up
; with a different way to implement typed records that seems to be much more
; suitable.  In short, instead of using a misc/record with some kind of special
; entries, we directly develop a new kind of typed record where the well-formed
; records are only allowed to have values of the proper type.  This lets us
; nicely separate the bad part of the record (if any) from the good part, and
; obtain a theorem in the spirit of EQUAL-BY-G.
;
; This book develops a generic theory for typed records.  By itself this
; generic theory is not very useful, so you will want to also be aware of:
;
;  - def-typed-record.lisp
;       Provides the DEF-TYPED-RECORD macro for automatically instantiating
;       the typed records theory for a new, specific kind of type, and
;
;  - typed-record-tests.lisp
;       Several examples of using DEF-TYPED-RECORDS to introduce different
;       kinds of typed records.



; -----------------------------------------------------------------------------
;
;                    GENERIC DEFINITION OF TYPED RECORDS
;
; -----------------------------------------------------------------------------

(encapsulate
  (((elem-p *) => *)
   ((elem-default) => *))

  (local (defun elem-p (x) (natp x)))
  (local (defun elem-default () 0))

  (defthm booleanp-of-elem-p
    (booleanp (elem-p x))
    :rule-classes :type-prescription)

  (defthm elem-p-of-elem-default
    (elem-p (elem-default))))

(defun elem-fix (x)
  ;; Standard fixing function.
  (if (elem-p x)
      x
    (elem-default)))

(defun tr-p1 (x)
  ;; Main typed-record predicate (ordered alist where every key is bound
  ;; to a non-default value).
  (or (null x)
      (and (consp x)
           (consp (car x))
           (tr-p1 (cdr x))
           (elem-p (cdar x))
           (not (equal (cdar x) (elem-default)))
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defun tr-p (x)
  ;; Full typed-record predicate.  (GOOD-PART . BAD-PART) where the good part
  ;; is the ordred alist of good values, and the bad-part is where we put any
  ;; non-good initial record so we can get the set-of-get theorem.
  (and (consp x)
       (tr-p1 (car x))
       (car x)
       (not (tr-p (cdr x)))))

(defun to-tr (x)
  ;; Interpret any ACL2 object as a typed record.  If it's already a TR-P,
  ;; we're good.  Otherwise, interpret it as having an empty good part and
  ;; itself as the bad part.
  (if (tr-p x)
      x
    (cons nil x)))

(defun tr-bad-part (r)
  ;; Get the bad part from the typed record interpretation of x.  Mainly of
  ;; use for EQUAL-BY-TR-GET.
  (if (tr-p r)
      (cdr r)
    r))

(defun tr-get1 (k r)
  ;; Lookup a key in the good part.
  (declare (xargs :guard (tr-p1 r)))
  (cond ((or (endp r)
             (<< k (caar r)))
         (elem-default))
        ((equal k (caar r))
         (cdar r))
        (t
         (tr-get1 k (cdr r)))))

(defun tr-set1 (k v r)
  ;; Set a key to a (good) value in the good part.
  (declare (xargs :guard (tr-p1 r)))
  (cond ((or (endp r)
             (<< k (caar r)))
         (if (equal v (elem-default))
             r
           (cons (cons k v) r)))
        ((equal k (caar r))
         (if (equal v (elem-default))
             (cdr r)
           (cons (cons k v) (cdr r))))
        (t
         (cons (car r) (tr-set1 k v (cdr r))))))

(defun tr-get (k r)
  ;; Main typed record lookup function.
  (tr-get1 k (car (to-tr r))))

(defun tr-set (k v r)
  ;; Main typed record update function.
  (let* ((rec  (to-tr r))
         (rec1 (car rec))
         (bad  (cdr rec))
         (new-rec1 (tr-set1 k (elem-fix v) rec1)))
    (if new-rec1
        (cons new-rec1 bad)
      bad)))


; Basic supporting theorems about tr-get1 and tr-set1.

(defthm elem-p-of-tr-get1
  (implies (tr-p1 r)
           (elem-p (tr-get1 k r))))

(defthm tr-get1-of-tr-set1-same
  (implies (and (tr-p1 r)
                (elem-p v))
           (equal (tr-get1 a (tr-set1 a v r))
                  v)))

(defthm tr-get1-of-tr-set1-diff
  (implies (and (tr-p1 r)
                (not (equal a b)))
           (equal (tr-get1 a (tr-set1 b v r))
                  (tr-get1 a r))))

(defthm tr-set1-of-tr-get1-same
  (implies (tr-p1 r)
           (equal (tr-set1 a (tr-get1 a r) r)
                  r)))

(defthm tr-set1-of-tr-set1-same
  (implies (tr-p1 r)
           (equal (tr-set1 a y (tr-set1 a x r))
                  (tr-set1 a y r))))

(defthm tr-set1-of-tr-set1-diff
  (implies (and (tr-p1 r)
                (not (equal a b)))
           (equal (tr-set1 b y (tr-set1 a x r))
                  (tr-set1 a x (tr-set1 b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))


; Additional, technical lemmas about tr-get1 and tr-set1.

(defthm tr-set1-is-bounded
  (implies (and (tr-p1 r)
                (tr-set1 a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (tr-set1 a v r)))))

(defthm tr-set1-preserves-tr-p
  (implies (and (tr-p1 r)
                (elem-p v))
           (tr-p1 (tr-set1 a v r))))

(defthm tr-set1-under-iff
  (implies (and (tr-p1 r)
                (elem-p v))
           (iff (tr-set1 a v r)
                (not (and (equal v (elem-default))
                          (or (atom r)
                              (and (equal (cdr r) nil)
                                   (equal (caar r) a))))))))


; Main theorems of interest.

(defthm elem-p-of-tr-get
  (elem-p (tr-get a x)))

(defthm tr-get-of-tr-set-same
  (equal (tr-get a (tr-set a v r))
         (elem-fix v)))

(defthm tr-get-of-tr-set-diff
  (implies (not (equal a b))
           (equal (tr-get a (tr-set b v r))
                  (tr-get a r))))

(defthm tr-set-of-tr-get-same
  (equal (tr-set a (tr-get a r) r)
         r))

(defthm tr-set-of-tr-set-same
  (equal (tr-set a y (tr-set a x r))
         (tr-set a y r)))

(defthm tr-set-of-tr-set-diff
  (implies (not (equal a b))
           (equal (tr-set b y (tr-set a x r))
                  (tr-set a x (tr-set b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))

; The case-splitting rule isn't necessarily a good idea, and originally I
; didn't even introduce it.  But now it seems most convenient to just prove it,
; leave it enabled, and let the user turn it off when it becomes too expensive.

(defthm tr-get-of-tr-set-strong
  (equal (tr-get a (tr-set b v r))
         (if (equal a b)
             (elem-fix v)
           (tr-get a r))))


; Some additional, occasionally useful theorems.

(defthm tr-get-of-nil
  ;; May be useful for using NIL as the default typed record
  (equal (tr-get a nil)
         (elem-default)))

(defthm tr-bad-part-of-tr-set
  ;; May be useful when trying to use EQUAL-BY-TR-GET.
  (equal (tr-bad-part (tr-set k v r))
         (tr-bad-part r)))

(in-theory (disable tr-set tr-get tr-bad-part))




; -----------------------------------------------------------------------------
;
;                PICK-A-POINT PROOFS OF TYPED-RECORD EQUALITY
;
; -----------------------------------------------------------------------------

; This is basically copied and pasted from the misc/equal-by-g.lisp book, which
; dealt with ordinary records.  The only twist is that we have to also assume
; that the bad parts are equal.

; I leave the badguy and the main theorems about it visible, because it seems
; like it may sometimes be useful.

(defund tr-badguy1 (x y)
  (declare (xargs :verify-guards nil))
  (cond ((atom x)
         (if (atom y)
             nil
           (cons :extra-in-y (car y))))
        ((atom y)
         (cons :extra-in-x (car x)))
        ((equal (car x) (car y))
         (tr-badguy1 (cdr x) (cdr y)))
        ((<< (caar x) (caar y))
         (cons :extra-in-x (car x)))
        ((equal (caar x) (caar y))
         (cons :mismatch (car x)))
        (t
         (cons :extra-in-y (car y)))))

(local (in-theory (enable tr-badguy1)))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (tr-badguy1 x y)) a)
                          (equal (car (tr-badguy1 x y)) :extra-in-x)
                          (tr-p1 x)
                          (<< b (caar x)))
                     (not (<< a b)))))

   (defthm lookup-in-x-when-extra-in-x
     (implies (and (equal (car (tr-badguy1 x y)) :extra-in-x)
                   (tr-p1 x)
                   (tr-p1 y))
              (not (equal (tr-get1 (cadr (tr-badguy1 x y)) x)
                          (elem-default)))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (tr-badguy1 x y)) :extra-in-x)
                          (<< a (caar x))
                          (<< (cadr (tr-badguy1 x y)) a)
                          (tr-p1 x))
                     (not (<< a (caar y))))))

   (defthm lookup-in-y-when-extra-in-x
     (implies (and (equal (car (tr-badguy1 x y)) :extra-in-x)
                   (tr-p1 x)
                   (tr-p1 y))
              (and (equal (tr-get1 (cadr (tr-badguy1 x y)) y)
                          (elem-default)))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (tr-badguy1 x y)) a)
                          (equal (car (tr-badguy1 x y)) :extra-in-y)
                          (<< b (caar x))
                          (tr-p1 y)
                          (<< b (caar y)))
                     (not (<< a b)))))

   (defthm lookup-in-y-when-extra-in-y
     (implies (and (equal (car (tr-badguy1 x y)) :extra-in-y)
                   (tr-p1 x)
                   (tr-p1 y))
              (not (equal (tr-get1 (cadr (tr-badguy1 x y)) y)
                          (elem-default)))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (tr-badguy1 x y)) :extra-in-y)
                          (<< a (caar x))
                          (<< (cadr (tr-badguy1 x y)) a)
                          (tr-p1 y))
                     (not (<< a (caar y))))))

   (defthm lookup-in-x-when-extra-in-y
     (implies (and (equal (car (tr-badguy1 x y)) :extra-in-y)
                   (tr-p1 x)
                   (tr-p1 y))
              (equal (tr-get1 (cadr (tr-badguy1 x y)) x)
                     (elem-default))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (tr-badguy1 x y)) a)
                          (equal (car (tr-badguy1 x y)) :mismatch)
                          (tr-p1 x)
                          (tr-p1 y)
                          (<< b (caar x))
                          (<< b (caar y)))
                     (not (<< a b)))))

   (local (defthm l1
            (implies (and (equal (car (tr-badguy1 x y)) :mismatch)
                          (tr-p1 x)
                          (tr-p1 y)
                          (<< a (caar x))
                          (<< (cadr (tr-badguy1 x y)) a))
                     (not (<< a (caar y))))))

   (defthm mismatch-when-mismatch
     (implies (and (equal (car (tr-badguy1 x y)) :mismatch)
                   (tr-p1 x)
                   (tr-p1 y))
              (equal (equal (tr-get1 (cadr (tr-badguy1 x y)) x)
                            (tr-get1 (cadr (tr-badguy1 x y)) y))
                     nil)))))



; It's easy to see that these are the only cases, and hence it is clear that
; the tr-badguy1 works and if it reports a mismatch, it really is a mismatch.

(local (defthm tr-badguy1-cases
         (or (not (tr-badguy1 x y))
             (equal (car (tr-badguy1 x y)) :mismatch)
             (equal (car (tr-badguy1 x y)) :extra-in-x)
             (equal (car (tr-badguy1 x y)) :extra-in-y))
         :rule-classes nil))

(local (defthm tr-get1-of-tr-badguy1
         (implies (and (tr-badguy1 x y)
                       (tr-p1 x)
                       (tr-p1 y))
                  (not (equal (tr-get1 (cadr (tr-badguy1 x y)) x)
                              (tr-get1 (cadr (tr-badguy1 x y)) y))))
         :hints(("Goal" :use ((:instance tr-badguy1-cases))))))

(local (defthm tr-badguy1-unless-equal
         (implies (and (not (equal x y))
                       (tr-p1 x)
                       (tr-p1 y))
                  (tr-badguy1 x y))))

(defund tr-badguy (x y)
  (declare (xargs :verify-guards nil))
  (tr-badguy1 (car (to-tr x))
              (car (to-tr y))))

(defthm tr-badguy-finds-counterexample
  (implies (tr-badguy x y)
           (not (equal (tr-get (cadr (tr-badguy x y)) x)
                       (tr-get (cadr (tr-badguy x y)) y))))
  :hints(("Goal" :in-theory (enable tr-get
                                    tr-badguy))))

(defthm tr-badguy-unless-equal
  (implies (and (not (equal x y))
                (equal (tr-bad-part x) (tr-bad-part y)))
           (tr-badguy x y))
  :hints(("Goal" :in-theory (enable to-tr
                                    tr-bad-part
                                    tr-badguy))))


; The theorem EQUAL-BY-TR-GET lets us show that two typed records are equal by
; showing (1) that their every key is bound to the same value, and (2) that
; their badparts are the same.

(encapsulate
  (((equal-by-tr-get-hyp) => *)
   ((equal-by-tr-get-lhs) => *)
   ((equal-by-tr-get-rhs) => *))

  (local (defun equal-by-tr-get-hyp () nil))
  (local (defun equal-by-tr-get-lhs () nil))
  (local (defun equal-by-tr-get-rhs () nil))

  (defthm equal-by-tr-get-constraint
    (implies (equal-by-tr-get-hyp)
             (and (equal (tr-get arbitrary-key (equal-by-tr-get-lhs))
                         (tr-get arbitrary-key (equal-by-tr-get-rhs)))
                  (equal (tr-bad-part (equal-by-tr-get-lhs))
                         (tr-bad-part (equal-by-tr-get-rhs)))))))

(defthm equal-by-tr-get
  (implies (equal-by-tr-get-hyp)
           (equal (equal-by-tr-get-lhs)
                  (equal-by-tr-get-rhs)))
  :hints(("Goal"
          :in-theory (disable tr-badguy-finds-counterexample tr-badguy)
          :use ((:instance tr-badguy-finds-counterexample
                           (x (equal-by-tr-get-lhs))
                           (y (equal-by-tr-get-rhs)))))))




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

(defthm equal-of-tr-set
  (implies
   (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (tr-set ,a ,v ,x) ,y) mfc state)
                (acl2::rewriting-positive-literal-fn `(equal ,y (tr-set ,a ,v ,x)) mfc state)))
   (equal (equal (tr-set a v x) y)
          (and (equal (tr-bad-part (tr-set a v x))
                      (tr-bad-part y))
               (let ((key (acl2::introduce-var 'arbitrary-key
                                               (hide (cadr (tr-badguy (tr-set a v x) y))))))
                 (and (equal (tr-get key (tr-set a v x))
                             (tr-get key y)))))))
  :hints(("Goal"
          :expand (:free (x) (hide x))
          :in-theory (enable acl2::introduce-var)
          :use ((:instance tr-badguy-finds-counterexample
                           (x (tr-set a v x))
                           (y y))
                (:instance tr-badguy-unless-equal
                           (x (tr-set a v x))
                           (y y))))))


; This commented out stuff was an earlier attempt to solve the same problem.
; We think the rule above is much nicer, though.

;; (defsection tr-decompose-with-key

;;   (local (defthm help0
;;            (implies (not (equal (elem-fix a) (elem-fix b)))
;;                     (equal (EQUAL (TR-SET K A X) (TR-SET K B Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable TR-GET-OF-TR-SET-SAME)
;;                    :use ((:instance TR-GET-OF-TR-SET-SAME
;;                                     (a k)
;;                                     (v a)
;;                                     (r x))
;;                          (:instance TR-GET-OF-TR-SET-SAME
;;                                     (a k)
;;                                     (v b)
;;                                     (r y)))))))

;;   (local (defthm help1
;;            (implies (not (EQUAL (TR-BAD-PART X) (TR-BAD-PART Y)))
;;                     (equal (EQUAL (TR-SET K v1 X)
;;                                   (TR-SET K v2 Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable TR-BAD-PART-OF-TR-SET)
;;                    :use ((:instance TR-BAD-PART-OF-TR-SET
;;                                     (v v1) (r x))
;;                          (:instance TR-BAD-PART-OF-TR-SET
;;                                     (v v2) (r y)))))))

;;   (local (defthm help2
;;            (implies (and (not (equal k nonk))
;;                          (not (EQUAL (TR-get nonk X) (tr-get nonk Y))))
;;                     (equal (EQUAL (TR-SET K v1 X)
;;                                   (TR-SET K v2 Y))
;;                            nil))
;;            :hints(("Goal"
;;                    :in-theory (disable TR-GET-OF-TR-SET-diff)
;;                    :use ((:instance TR-GET-OF-TR-SET-diff
;;                                     (a nonk) (b k) (v v1) (r x))
;;                          (:instance TR-GET-OF-TR-SET-diff
;;                                     (a nonk) (b k) (v v2) (r y)))))))

;;   (local (defthmd part1
;;            (implies (equal (tr-set k v1 x)
;;                            (tr-set k v2 y))
;;                     (and (equal (elem-fix v1) (elem-fix v2))
;;                          (equal (tr-set k (elem-default) x)
;;                                 (tr-set k (elem-default) y))))
;;            :hints(("Goal" :use ((:functional-instance
;;                                  equal-by-tr-get
;;                                  (equal-by-tr-get-lhs (lambda () (tr-set k (elem-default) x)))
;;                                  (equal-by-tr-get-rhs (lambda () (tr-set k (elem-default) y)))
;;                                  (equal-by-tr-get-hyp (lambda ()
;;                                                         (equal (tr-set k v1 x)
;;                                                                (tr-set k v2 y)))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((equal arbitrary-key k)))))))

;;   (local (defthmd part2
;;            (implies (and (equal (elem-fix v1) (elem-fix v2))
;;                          (equal (tr-set k (elem-default) x)
;;                                 (tr-set k (elem-default) y)))
;;                     (equal (tr-set k v1 x)
;;                            (tr-set k v2 y)))
;;            :hints(("Goal"
;;                    :use ((:functional-instance
;;                           equal-by-tr-get
;;                           (equal-by-tr-get-lhs (lambda () (tr-set k v1 x)))
;;                           (equal-by-tr-get-rhs (lambda () (tr-set k v2 y)))
;;                           (equal-by-tr-get-hyp (lambda ()
;;                                                  (and (equal (elem-fix v1) (elem-fix v2))
;;                                                       (equal (tr-set k (elem-default) x)
;;                                                              (tr-set k (elem-default) y))))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((equal arbitrary-key k)))))))

;;   (defthm tr-decompose-with-key
;;     (implies (syntaxp (or (not (equal v1 (list 'quote (elem-default))))
;;                           (not (equal v2 (list 'quote (elem-default))))))
;;              (equal (equal (tr-set k v1 x)
;;                            (tr-set k v2 y))
;;                     (and (equal (elem-fix v1) (elem-fix v2))
;;                          (equal (tr-set k (elem-default) x)
;;                                 (tr-set k (elem-default) y)))))
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

(defun elem-list-p (x)
  (if (atom x)
      (eq x nil)
    (and (elem-p (car x))
         (elem-list-p (cdr x)))))

(defthm true-listp-when-elem-list-p
  (implies (elem-list-p x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(defthm elem-list-p-of-update-nth
  (implies (and (elem-list-p arr)
                (elem-p val)
                (< (nfix n) (len arr)))
           (elem-list-p (update-nth n val arr)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm elem-p-of-nth
  (implies (and (elem-list-p arr)
                (< (nfix n) (len arr)))
           (elem-p (nth n arr)))
  :hints(("Goal" :in-theory (enable nth))))




(defun array-to-tr (n arr rec)
  ;; Store arr[0]...arr[n] into rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      rec
    (let ((n (- n 1)))
      (array-to-tr n arr (tr-set n (nth n arr) rec)))))

(defun tr-to-array (n rec arr)
  ;; Load arr[0]...arr[n] from rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      arr
    (let ((n (- n 1)))
      (tr-to-array n rec (update-nth n (tr-get n rec) arr)))))

(defun tr-delete-indices (n rec)
  ;; Delete rec[0]...rec[n] from rec
  (declare (xargs :guard (natp n)))
  (if (zp n)
      rec
    (let ((n (- n 1)))
      (tr-delete-indices n (tr-set n (elem-default) rec)))))

(defun array-rec-pair-p (arr rec len)
  ;; Recognize array/record pairs where the array has size LEN and the record
  ;; has nothing in keys 0...LEN-1.
  (declare (xargs :guard (natp len)))
  (and (elem-list-p arr)
       (= (len arr) len)
       (equal rec (tr-delete-indices len rec))))



(defthm tr-get-of-array-to-tr
  (equal (tr-get key (array-to-tr n arr rec))
         (if (and (natp key)
                  (< key (nfix n)))
             (elem-fix (nth key arr))
           (tr-get key rec))))

(defthm tr-bad-part-of-array-to-tr
  (equal (tr-bad-part (array-to-tr n arr rec))
         (tr-bad-part rec)))


(defthm true-listp-of-tr-to-array
  (implies (true-listp arr)
           (true-listp (tr-to-array n rec arr))))

(defthm len-of-tr-to-array
  (equal (len (tr-to-array n rec arr))
         (max (nfix n) (len arr))))

(defthm elem-list-p-of-tr-to-array
  (implies (and (elem-list-p arr)
                (<= (nfix n) (len arr)))
           (elem-list-p (tr-to-array n rec arr))))


(defthm nth-of-tr-to-array
  (equal (nth key (tr-to-array n rec arr))
         (cond ((< (nfix key) (nfix n))
                (tr-get (nfix key) rec))
               (t
                (nth key arr)))))

(defthm nth-of-tr-to-array-of-array-to-tr
  (implies (and (natp key)
                (natp n)
                (< key n)
                (<= n (len arr1))
                (equal (len arr1) (len arr2))
                (elem-list-p arr1))
           (equal (nth key (tr-to-array n (array-to-tr n arr1 rec) arr2))
                  (nth key arr1))))

; sswords note, 1/30/2017: The following note pertains to a previous version;
; see git revisions dated prior to this note.  The (fixed) theorem is below the note.

; Matt K. note, 1/28/2017, regarding fix for soundness bug in functional
; instantiation: The next lemma, tr-to-array-of-array-to-tr, is not a theorem!
; This directory is being excluded with cert_pl_exclude because of this lemma.
; Here is a demonstration that it is not a theorem.

#||
cd books/projects/legacy-defrstobj/
acl2
(rebuild "typed-records.lisp" 'nth-of-tr-to-array-of-array-to-tr)

(defun naught () 0)
(defun naught-p (x) (equal x 0))
(defattach (elem-p naught-p) (elem-default naught))

; And then:

RSTOBJ !>(with-guard-checking
          nil
          (let ((arr2 nil) (arr1 nil) (n 0) (n2 -1) (rec nil))
            (IMPLIES (AND (EQUAL (LEN ARR1) (LEN ARR2))
                          (EQUAL N2 (+ -1 (LEN ARR1)))
                          (ELEM-LIST-P ARR1)
                          (ELEM-LIST-P ARR2)
                          (INTEGERP N)
                          (<= 0 N)
                          (< N (MAX (+ 1 (NFIX N2)) (LEN ARR2))))
                     (EQUAL (NTH N
                                 (TR-TO-ARRAY N2 (ARRAY-TO-TR N2 ARR1 REC)
                                              ARR2))
                            (NTH N ARR1)))))
NIL
RSTOBJ !>
||#

;;; NOT A THEOREM (see above)!
#||
(defthm tr-to-array-of-array-to-tr
  (implies (and (force (equal (len arr1) (len arr2)))
                (force (equal n (- (len arr1) 1)))
                (force (posp (len arr1)))
                (force (elem-list-p arr1))
                (force (elem-list-p arr2)))
           (equal (tr-to-array n (array-to-tr n arr1 rec) arr2)
                  arr1))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (equal (len arr1) (len arr2))
                                           (equal n (- (len arr1) 1))
                                           (elem-list-p arr1)
                                           (elem-list-p arr2))))
                 (equal-by-nths-lhs (lambda ()
                                      (tr-to-array n (array-to-tr n arr1 rec) arr2)))
                 (equal-by-nths-rhs (lambda ()
                                      arr1)))))))
||#

(defthm tr-to-array-of-array-to-tr
  (implies (and (force (equal (len arr1) (len arr2)))
                (force (equal n (len arr1)))
                (force (elem-list-p arr1))
                (force (elem-list-p arr2)))
           (equal (tr-to-array n (array-to-tr n arr1 rec) arr2)
                  arr1))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (equal (len arr1) (len arr2))
                                           (equal n (len arr1))
                                           (elem-list-p arr1)
                                           (elem-list-p arr2))))
                 (equal-by-nths-lhs (lambda ()
                                      (tr-to-array n (array-to-tr n arr1 rec) arr2)))
                 (equal-by-nths-rhs (lambda ()
                                      arr1)))))))

(defthm tr-to-array-idempotent
  (implies (force (elem-list-p arr1))
           (equal (tr-to-array n rec1 (tr-to-array n rec2 arr1))
                  (tr-to-array n rec1 arr1)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (elem-list-p arr1)))
                 (equal-by-nths-lhs (lambda ()
                                      (tr-to-array n rec1 (tr-to-array n rec2 arr1))))
                 (equal-by-nths-rhs (lambda ()
                                      (tr-to-array n rec1 arr1))))))))

(defthm tr-to-array-of-tr-set
  (implies (and (natp n)
                (natp i)
                (< i n)
                (elem-p val)
                (elem-list-p arr))
           (equal (tr-to-array n (tr-set i val rec) arr)
                  (update-nth i val (tr-to-array n rec arr))))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (natp n)
                                           (natp i)
                                           (< i n)
                                           (elem-p val)
                                           (elem-list-p arr))))
                 (equal-by-nths-lhs (lambda ()
                                      (tr-to-array n (tr-set i val rec) arr)))
                 (equal-by-nths-rhs (lambda ()
                                      (update-nth i val (tr-to-array n rec arr)))))))))



(defthm tr-delete-indices-of-nil
  (equal (tr-delete-indices n nil)
         nil)
  ;; I need this yucky hint because this is breaking the typed-record abstraction
  ;; and looking at its actual representation.
  :hints(("Goal" :in-theory (enable tr-set))))

(defthm tr-bad-part-of-tr-delete-indices
  (equal (tr-bad-part (tr-delete-indices n rec))
         (tr-bad-part rec)))

(defthm tr-get-of-tr-delete-indices
  (equal (tr-get key (tr-delete-indices n rec))
         (if (and (natp key)
                  (< key (nfix n)))
             (elem-default)
           (tr-get key rec))))

(defthm tr-delete-indices-of-array-to-tr
  (equal (tr-delete-indices n (array-to-tr n arr rec))
         (tr-delete-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-tr-get
                 (equal-by-tr-get-hyp (lambda () t))
                 (equal-by-tr-get-lhs (lambda ()
                                        (tr-delete-indices n (array-to-tr n arr rec))))
                 (equal-by-tr-get-rhs (lambda ()
                                        (tr-delete-indices n rec))))))))

(defthm tr-delete-indices-of-tr-set
  (implies (and (natp n)
                (natp i)
                (< i n))
           (equal (tr-delete-indices n (tr-set i val rec))
                  (tr-delete-indices n rec)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-tr-get
                 (equal-by-tr-get-hyp (lambda ()
                                   (and (natp n)
                                        (natp i)
                                        (< i n))))
                 (equal-by-tr-get-lhs (lambda ()
                                   (tr-delete-indices n (tr-set i val rec))))
                 (equal-by-tr-get-rhs (lambda ()
                                   (tr-delete-indices n rec))))))))


(defthm array-to-tr-inverse-lemma
  (equal (tr-get key (array-to-tr n
                                  (tr-to-array n rec arr)
                                  (tr-delete-indices n rec)))
         (tr-get key rec)))

(defthm array-to-tr-inverse
  (equal (array-to-tr n
                      (tr-to-array n rec arr)
                      (tr-delete-indices n rec))
         rec)
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-tr-get
                 (equal-by-tr-get-hyp (lambda () t))
                 (equal-by-tr-get-lhs (lambda ()
                                        (array-to-tr n
                                                     (tr-to-array n rec arr)
                                                     (tr-delete-indices n rec))))
                 (equal-by-tr-get-rhs (lambda () rec)))))))

(defthm tr-delete-indices-idempotent
  (equal (tr-delete-indices n (tr-delete-indices n rec))
         (tr-delete-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-tr-get
                 (equal-by-tr-get-hyp (lambda () t))
                 (equal-by-tr-get-lhs (lambda ()
                                        (tr-delete-indices n (tr-delete-indices n rec))))
                 (equal-by-tr-get-rhs (lambda ()
                                        (tr-delete-indices n rec))))))))






(defthm array-rec-pair-p-of-nil
  (implies (and (elem-list-p arr)
                (equal (len arr) n))
           (array-rec-pair-p arr nil n)))

(defthm array-rec-pair-p-of-update-nth
  (implies (and (array-rec-pair-p arr rec len)
                (force (natp n))
                (force (< n len))
                (force (elem-p val)))
           (array-rec-pair-p (update-nth n val arr) rec len)))

(defthm array-rec-pair-p-of-tr-delete-indices
  (implies (array-rec-pair-p arr rec len)
           (array-rec-pair-p arr (tr-delete-indices len rec) len)))




; We now show that whenever either the ARR or REC part of an array/record pair
; are different, then the "logical record" obtained by array-to-tr is
; different.

(local
 (defsection equal-of-array-to-tr-part1

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

   (local (defthm elem-p-of-nth-when-elem-listp
            (implies (elem-list-p arr)
                     (equal (elem-p (nth n arr))
                            (if (< (nfix n) (len arr))
                                t
                              (elem-p nil))))))

   (local (defthmd main-lemma
            (implies (and (not (equal arr1 arr2))
                          (equal (len arr1) (len arr2))
                          (elem-list-p arr1)
                          (elem-list-p arr2))
                     (let ((key (nth-badguy arr1 arr2)))
                       (not (equal (tr-get key (array-to-tr (len arr1) arr1 rec1))
                                   (tr-get key (array-to-tr (len arr1) arr2 rec2))))))
            :hints(("Goal"
                    :do-not '(generalize fertilize)
                    :do-not-induct t))))

   (defthm equal-of-array-to-tr-part1
     (implies (and (not (equal arr1 arr2))
                   (equal (len arr1) (len arr2))
                   (elem-list-p arr1)
                   (elem-list-p arr2))
              (not (equal (array-to-tr (len arr1) arr1 rec1)
                          (array-to-tr (len arr1) arr2 rec2))))
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :do-not-induct t
             :use ((:instance main-lemma)))))))


; Now we turn our attention to the record.  There are two ways for the records
; to be different: they can have different badparts or some different key.  The
; badpart case is trivial:

(local
 (defthm equal-of-array-to-tr-part2
   (implies (case-split (not (equal (tr-bad-part rec1) (tr-bad-part rec2))))
            (not (equal (array-to-tr n arr1 rec1)
                        (array-to-tr n arr2 rec2))))
   :hints(("Goal"
           :do-not '(generalize fertilize)
           :do-not-induct t
           :in-theory (disable tr-bad-part-of-array-to-tr)
           :use ((:instance tr-bad-part-of-array-to-tr (arr arr1) (rec rec1))
                 (:instance tr-bad-part-of-array-to-tr (arr arr2) (rec rec2)))))))


(local
 (defsection equal-of-array-to-tr-part3

   (local
    (defthm gross

; This is horrible.  We basically are arguing that the tr-badguy can't give us
; an index that's going to lead us to the array, because we know that the
; records each bind those keys to NIL.

      (let ((key (cadr (tr-badguy rec1 rec2))))
        (implies (and (not (equal rec1 rec2))
                      (equal (tr-bad-part rec1) (tr-bad-part rec2))
                      (equal rec1 (tr-delete-indices n rec1))
                      (equal rec2 (tr-delete-indices n rec2))
                      (natp n)
                      (natp key))
                 (<= n key)))
      :hints(("Goal"
              :do-not '(generalize fertilize)
              :do-not-induct t
              :in-theory (disable tr-get-of-tr-delete-indices
                                  tr-delete-indices
                                  tr-badguy
                                  tr-badguy-finds-counterexample)
              :use ((:instance tr-get-of-tr-delete-indices
                               (key (cadr (tr-badguy rec1 rec2)))
                               (n n)
                               (rec rec1))
                    (:instance tr-get-of-tr-delete-indices
                               (key (cadr (tr-badguy rec1 rec2)))
                               (n n)
                               (rec rec2))
                    (:instance tr-badguy-finds-counterexample
                               (x rec1)
                               (y rec2)))))))

   (local
    (defthm main-lemma
      (implies (and (not (equal rec1 rec2))
                    (equal (tr-bad-part rec1) (tr-bad-part rec2))
                    (equal rec1 (tr-delete-indices len rec1))
                    (equal rec2 (tr-delete-indices len rec2)))
               (let ((key (cadr (tr-badguy rec1 rec2))))
                 (not (equal (tr-get key (array-to-tr len arr1 rec1))
                             (tr-get key (array-to-tr len arr2 rec2))))))
      :hints(("Goal"
              :in-theory (disable tr-badguy tr-get-of-array-to-tr gross)
              :do-not '(generalize fertilize)
              :do-not-induct t
              :use ((:instance tr-get-of-array-to-tr
                               (key (cadr (tr-badguy rec1 rec2)))
                               (n len)
                               (arr arr1)
                               (rec rec1))
                    (:instance tr-get-of-array-to-tr
                               (key (cadr (tr-badguy rec1 rec2)))
                               (n len)
                               (arr arr2)
                               (rec rec2))
                    (:instance gross
                               (n (nfix len))))))))

   (defthm equal-of-array-to-tr-part3
     (implies (and (not (equal rec1 rec2))
                   (case-split (equal (tr-bad-part rec1) (tr-bad-part rec2)))
                   (equal rec1 (tr-delete-indices len rec1))
                   (equal rec2 (tr-delete-indices len rec2)))
              (not (equal (array-to-tr len arr1 rec1)
                          (array-to-tr len arr2 rec2))))
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :do-not-induct t
             :in-theory (disable tr-delete-indices main-lemma tr-badguy)
             :use ((:instance main-lemma)))))))

(local (defthmd equal-of-array-to-tr-orig
         ;; This is the original version I proved.  But, it turns out to be difficult
         ;; to unify with this and apply this rule.  The rule below is better.
         (implies (and (array-rec-pair-p arr1 rec1 len)
                       (array-rec-pair-p arr2 rec2 len)
                       (natp len))
                  (equal (equal (array-to-tr len arr1 rec1)
                                (array-to-tr len arr2 rec2))
                         (and (equal arr1 arr2)
                              (equal rec1 rec2))))
         :hints(("Goal"
                 :do-not '(generalize fertilize)
                 :do-not-induct t
                 :in-theory (e/d (array-rec-pair-p)
                                 (tr-delete-indices))))))

(defthm equal-of-array-to-tr
  (implies (and (array-rec-pair-p arr1 rec1 len1)
                (array-rec-pair-p arr2 rec2 len2)
                (equal len1 len)
                (equal len2 len)
                (natp len))
           (equal (equal (array-to-tr len arr1 rec1)
                         (array-to-tr len arr2 rec2))
                  (and (equal arr1 arr2)
                       (equal rec1 rec2))))
  :hints(("Goal"
          :in-theory (disable tr-delete-indices
                              array-to-tr
                              array-rec-pair-p
                              equal-of-array-to-tr-orig
                              equal-of-array-to-tr-part2)
          :use ((:instance equal-of-array-to-tr-orig (len len))))))









