; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

(include-book "base")

; (i-am-here) The following include-book is thought to be necessary for the
; acl2-devel run but not for normal certification.  But we have not checked
; whether the devel run will succeed without this include-book!
#+acl2-devel
(include-book "system/apply/loop-scions" :dir :system)

; Lemmas for Relieving Routine Loop$ Guards

; Preservation of true-list-listp

(defthm true-list-listp-tails
  (implies (true-listp lst)
           (true-list-listp (tails lst))))

(defthm true-list-listp-until$
  (implies (true-list-listp lst)
           (true-list-listp (until$ fn lst))))

(defthm true-list-listp-until$+
  (implies (true-list-listp lst)
           (true-list-listp (until$+ fn globals lst))))

(defthm true-list-listp-when$
  (implies (true-list-listp lst)
           (true-list-listp (when$ fn lst))))

(defthm true-list-listp-when$+
  (implies (true-list-listp lst)
           (true-list-listp (when$+ fn globals lst))))

(defthm true-listp-car-loop$-as-tuple
  (implies (true-list-listp tuple)
           (true-listp (car-loop$-as-tuple tuple))))

(defthm len-car-loop$-as-tuple
  (equal (len (car-loop$-as-tuple tuple))
         (len tuple)))

(defthm len-cdr-loop$-as-tuple
  (equal (len (cdr-loop$-as-tuple tuple))
         (len tuple)))

(defthm true-list-listp-cdr-loop$-as-tuple
  (implies (true-list-listp tuple)
           (true-list-listp (cdr-loop$-as-tuple tuple))))

(defthm true-list-listp-loop$-as
  (implies (true-list-listp tuple)
           (true-list-listp (loop$-as tuple))))

(defthm len-member-equal-loop$-as
  (implies (member-equal newv (loop$-as tuple))
           (equal (len newv) (len tuple)))
  :hints (("Goal" :induct (loop$-as tuple))))

; Preservation of integer-listp

(defthm integer-listp-from-to-by
  (implies (and (integerp i)
                (integerp k))
           (integer-listp (from-to-by i j k))))

(defthm integer-listp-until$
  (implies (integer-listp lst)
           (integer-listp (until$ fn lst))))

(defthm integer-listp-when$
  (implies (integer-listp lst)
           (integer-listp (when$ fn lst))))

; Lemmas needed for Special Conjecture c2

(encapsulate
  nil
  ;; (local (include-book "arithmetic-5/top" :dir :system))
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (include-book "centaur/bitops/floor-mod" :dir :system))
  (local (in-theory (disable floor mod)))

  (defthm member-equal-from-to-by-exact
    (implies (and (integerp i)
                  (integerp j)
                  (integerp k)
                  (< 0 k))
             (iff (member-equal newv (from-to-by i j k))
                  (and (integerp newv)
                       (<= i newv)
                       (<= newv j)
                       (equal (mod (- newv i) k) 0))))
    :hints (("goal" :induct (from-to-by i j k)
             :expand ((MOD (+ (- I) NEWV) K)
                      (mod 0 k))))
    ;; :hints (("Goal" :in-theory (disable |(integerp (- x))|)))
    )

  (defthm integerp==>numerator-=-x
    (implies (integerp x)
             (equal (numerator x)
                    x)))

  (defthm integerp==>denominator-=-1
    (implies (integerp x)
             (equal (denominator x)
                    1))))

; Preservation of member-posship
#||

(defthm member-pos-until$
  (implies (not (member-pos newv lst))
           (not (member-pos newv (until$ fn lst)))))

(defthm member-pos-until$+
  (implies (not (member-pos newv lst))
           (not (member-pos newv (until$+ fn globals lst)))))

(defthm member-pos-when$
  (implies (not (member-pos newv lst))
           (not (member-pos newv (when$ fn lst)))))

(defthm member-pos-when$+
  (implies (not (member-pos newv lst))
           (not (member-pos newv (when$+ fn globals lst)))))

(encapsulate
  nil
  (local (include-book
          "arithmetic-5/top" :dir :system))

  (defthm member-pos-from-to-by-exact
    (implies (and (integerp i)
                  (integerp j)
                  (integerp k)
                  (< 0 k))
             (iff (member-pos newv (from-to-by i j k))
                  (and (integerp newv)
                       (<= i newv)
                       (<= newv j)
                       (equal (mod (- newv i) k) 0)))))

  (in-theory (disable member-pos-from-to-by-exact)))

(defthm member-pos-from-to-by-weak
  (and
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (not (integerp newv)))
            (not (member-pos newv (from-to-by i j k))))
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (< newv i))
            (not (member-pos newv (from-to-by i j k))))
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (< j newv))
            (not (member-pos newv (from-to-by i j k))))))

(defthm member-pos-from-to-by-1
  (implies (and (integerp i)
                (integerp j))
           (iff (member-pos newv (from-to-by i j 1))
                (and (integerp newv)
                     (<= i newv)
                     (<= newv j)))))
||#
; -----------------------------------------------------------------

; Member-equal Rules

; For plain loop$s

(defthm member-equal-when$
  (iff (member-equal e (when$ p lst))
       (and (member-equal e lst)
            (apply$ p (list e)))))

(defthm member-equal-until$
  (IFF (MEMBER-EQUAL NEWV (UNTIL$ Q LST))
       (and (member-equal newv lst) 
            (< (mempos newv lst)
               (len (until$ q lst))))))

; For fancy loop$s

(defthm member-equal-when$+
  (iff (member-equal e (when$+ p pglob lst))
       (and
        (member-equal e lst)
        (apply$ p (list pglob e)))))

(defthm member-equal-until$+
  (iff (member-equal newv (until$+ q qglob lst))
       (and (member-equal newv lst)
            (< (mempos newv lst)
               (len (until$+ q qglob lst))))))

(defthm member-equal-newvar-components-1
  (implies (member-equal newvar (loop$-as (list t1)))
           (member-equal (car newvar) t1)))

(defthm member-equal-newvar-components-2
  (implies (member-equal newvar (loop$-as (list t1 t2)))
           (and (member-equal (car newvar) t1)
                (member-equal (cadr newvar) t2)))
  :hints (("Goal" :induct (pairlis$ t1 t2))))

(defthm member-equal-newvar-components-3
  (implies (member-equal newvar (loop$-as (list t1 t2 t3)))
           (and (member-equal (car newvar) t1)
                (member-equal (cadr newvar) t2)
                (member-equal (caddr newvar) t3)))
  :hints (("Goal" :induct (list (pairlis$ t1 t2)
                                (pairlis$ t2 t3)))))

; These are the analogous theorems for showing that
; acl2-count decreases for certain common cases arising
; from loop$ recursion.

(defthm member-equal-acl2-count-smaller-0
 (implies (member-equal nv lst)
          (< (acl2-count nv) (acl2-count lst)))
 :rule-classes :linear)

(defthm member-equal-acl2-count-smaller-1
 (implies (member-equal nv (loop$-as (list lst1)))
          (< (acl2-count (car nv)) (acl2-count lst1)))
 :rule-classes :linear)

(defthm member-equal-acl2-count-smaller-2
 (implies (member-equal nv (loop$-as (list lst1 lst2)))
          (and (< (acl2-count (car nv)) (acl2-count lst1))
               (< (acl2-count (cadr nv)) (acl2-count lst2))))
 :hints (("Goal" :induct (pairlis$ lst1 lst2)))
 :rule-classes :linear)

(defthm member-equal-acl2-count-smaller-3
 (implies (member-equal nv (loop$-as (list lst1 lst2 lst3)))
          (and (< (acl2-count (car nv)) (acl2-count lst1))
               (< (acl2-count (cadr nv)) (acl2-count lst2))
               (< (acl2-count (caddr nv)) (acl2-count lst3))))
  :hints (("Goal" :induct (cons (pairlis$ lst1 lst2)
                                (pairlis$ lst2 lst3))))
  :rule-classes :linear)

; -----------------------------------------------------------------

; A crucial part of reasoning about loop$ guards is deducing properties of the
; elements of a list from properties of the list, e.g., if newv is an element
; of lst and lst is a list of numbers, then newv is a number.  The general rule
; can be stated:

(defthm always$-p-lst-implies-p-element
  (implies (and (always$ fnp lst)        ; <-- lst is free
                (member-equal newv lst))
           (apply$ fnp (list newv))))

; which is not really very helpful because of the free variable lst.  However, the
; free variable quickly stops the rule from firing so we have left it enabled.

; But there are some commonly used legacy ``universal quantifiers,'' like
; integer-listp, rational-listp, acl2-number-listp, symbol-listp, and
; true-list-listp, each of which implies that members of the list have a
; particular primitive type.

; We need to formalize these basic facts.  We don't want them to fire when the
; list in question is produced either by LOOP$-AS or TAILS because we'll have
; special versions for those cases below.  So we have a syntaxp hyp.

; Nevertheless, they are all rather inefficient because they backchain from
; simple primitives, e.g., integerp, to member-equal and integer-listp.
; However, they all have a free variable (as noted below) that is hoped to
; prevent excessive use.

; integer-listp --> integerp
(defthm integer-listp-implies-integerp
  (implies (and (member-equal newv lst)  ; <-- lst is free
                (syntaxp (not (and (consp lst)
                                   (or (eq (car lst) 'LOOP$-AS)
                                       (eq (car lst) 'TAILS)))))
                (integer-listp lst))
           (integerp newv)))



; rational-listp --> rationalp
(defthm rational-listp-implies-rationalp
  (implies (and (member-equal newv lst) ; <-- lst is free
                (syntaxp (not (and (consp lst)
                                   (or (eq (car lst) 'LOOP$-AS)
                                       (eq (car lst) 'TAILS)))))
                (rational-listp lst))
           (rationalp newv)))

; acl2-number-listp --> acl2-numberp
(defthm acl2-number-listp-implies-acl2-numberp
  (implies (and (member-equal newv lst)  ; <-- lst is free
                (syntaxp (not (and (consp lst)
                                   (or (eq (car lst) 'LOOP$-AS)
                                       (eq (car lst) 'TAILS)))))
                (acl2-number-listp lst))
           (acl2-numberp newv)))

; symbol-listp --> symbolp
(defthm symbol-listp-implies-symbolp
  (implies (and (member-equal newv lst)  ; <-- lst is free
                (syntaxp (not (and (consp lst)
                                   (or (eq (car lst) 'LOOP$-AS)
                                       (eq (car lst) 'TAILS)))))
                (symbol-listp lst))
           (symbolp newv)))


; Todo: This rule does not follow the scheme of the rules above.  It is in the
; contrapositive and the syntaxp is different.  Phrasing it this way was
; necessary for books/system/tests/loop-tests.  Whether the above rules should
; be re-phrased in this manner hasn't been investigated.  Also, I have a
; feeling that there some kind of redundancy between this lemma and
; not-member-tails-true-list-listp below, but I haven't investigated that
; either!  There is only so much time and the current configuration of lemmas
; works.

; true-list-listp --> true-listp 
(defthm true-list-listp-implies-true-listp-xxx
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'loop$-as))))
                (true-list-listp lst)
                (not (true-listp newv)))
           (not (member-equal newv lst))))

; Guard verification of plain loops involves reasoning about the implications of
; (member newv lst), where lst is not a LOOP$-AS expression.  We reason via the
; contrapositive, e.g., we'll sometimes show (member newv lst) is false given
; other hyps.  So what are common ways to do that?  The basic idea is that if
; lst is known to be a list of a certain type of element and newv is not of that
; type, then (member newv lst) is nil.  The general version of this is:

(defthm always$-p-lst-implies-p-element-corollary
  (implies (and (always$ fnp lst)   ; <-- fnp is free
                (syntaxp (not (and (consp lst)
                                   (or (eq (car lst) 'LOOP$-AS)
                                       (eq (car lst) 'TAILS)))))
                (not (apply$ fnp (list newv))))
           (not (member-equal newv lst))))

; This lemma is not really very useful because of the free occurrence of fnp in
; the first hypothesis.  However, we think that free variable quickly prevents
; the rule from even being tried and so we leave the rule enabled.

; (Integer-listp lst) is stronger than (always$ 'integerp lst) because the
; latter does not guarantee (true-listp lst).  Thus, in the rules below I use
; the weaker (always$ 'integerp lst) as the hyp rather than (integer-listp
; lst).

(defthm integer-listp-implies-always$-integerp
  (implies (integer-listp lst)
           (always$ 'integerp lst)))

(defthm rational-listp-implies-always$-rationalp
  (implies (rational-listp lst)
           (always$ 'rationalp lst)))

(defthm acl2-number-listp-implies-always$-acl2-numberp
  (implies (acl2-number-listp lst)
           (always$ 'acl2-numberp lst)))

(defthm symbol-listp-implies-always$-symbolp
  (implies (symbol-listp lst)
           (always$ 'symbolp lst)))

(defthm true-list-listp-implies-always$-true-listp
  (implies (true-list-listp lst)
           (always$ 'true-listp lst)))

(defthm acl2-number-listp-from-to-by
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (< 0 k))
           (acl2-number-listp (from-to-by i j k))))

(encapsulate
  nil
  (local (defthm member-equal-nth-car-loop$-as-tuple
           (implies (and (CONSP TUPLE)
                         (NOT (EMPTY-LOOP$-AS-TUPLEP TUPLE))
                         (natp n)
                         (< n (len tuple)))
                    (member-equal (NTH N (CAR-LOOP$-AS-TUPLE TUPLE))
                                  (NTH N TUPLE)))))

  (local (defthm member-equal-nth-cdr-loop$-as-tuple
           (implies (and (CONSP TUPLE)
                         (NOT (EMPTY-LOOP$-AS-TUPLEP TUPLE))
                         (member-equal (NTH N NEWV)
                                       (NTH N (CDR-LOOP$-AS-TUPLE TUPLE))))
                    (member-equal (nth n newv) (nth n tuple)))))

  (local (defthm member-equal-loop$-as-implies-member-equal-nth
           (implies (and (member-equal newv (loop$-as tuple))
                         (natp n)
                         (< n (len tuple)))
                    (member-equal (nth n newv) (nth n tuple)))))

  (defthm not-member-loop$-as-general
    (implies (and (always$ fnp (nth n tuple)) ; <-- fnp is free
                  (not (apply$ fnp (list (nth n newv))))
                  (natp n)
                  (< n (len tuple)))
             (not (member-equal newv (loop$-as tuple))))))

(defthm not-member-loop$-as-always$-1
  (implies (and (always$ fnp lst1) ; <-- fnp is free
                (not (apply$ fnp (list (car newv)))))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-always$-2
  (implies (and (always$ fnp lst2) ; <-- fnp is free
                (not (apply$ fnp (list (cadr newv)))))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-always-3
  (implies (and (always$ fnp lst3) ; <-- fnp is free
                (not (apply$ fnp (list (caddr newv)))))
           (not (member-equal newv (loop$-as
                                    (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                           (n 2)))))

(defthm not-member-loop$-as-integer-1
  (implies (and (not (integerp (car newv)))
                (integer-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'integerp)
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-integer-2
  (implies (and (not (integerp (cadr newv)))
                (integer-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'integerp)
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-integer-3
  (implies (and (not (integerp (caddr newv)))
                (integer-listp lst3))
           (not (member-equal newv
                              (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance
                 not-member-loop$-as-general
                 (fnp 'integerp)
                 (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                 (n 2)))))

(defthm not-member-loop$-as-rational-1
  (implies (and (not (rationalp (car newv)))
                (rational-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'rationalp)
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-rational-2
  (implies (and (not (rationalp (cadr newv)))
                (rational-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'rationalp)
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-rational-3
  (implies (and (not (rationalp (caddr newv)))
                (rational-listp lst3))
           (not (member-equal newv
                              (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance
                 not-member-loop$-as-general
                 (fnp 'rationalp)
                 (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                 (n 2)))))

(defthm not-member-loop$-as-acl2-number-1
  (implies (and (not (acl2-numberp (car newv)))
                (acl2-number-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'acl2-numberp)
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-acl2-number-2
  (implies (and (not (acl2-numberp (cadr newv)))
                (acl2-number-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'acl2-numberp)
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-acl2-number-3
  (implies (and (not (acl2-numberp (caddr newv)))
                (acl2-number-listp lst3))
           (not (member-equal newv
                              (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance
                 not-member-loop$-as-general
                 (fnp 'acl2-numberp)
                 (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                 (n 2)))))

(defthm not-member-loop$-as-symbol-1
  (implies (and (not (symbolp (car newv)))
                (symbol-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'symbolp)
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-symbol-2
  (implies (and (not (symbolp (cadr newv)))
                (symbol-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'symbolp)
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-symbol-3
  (implies (and (not (symbolp (caddr newv)))
                (symbol-listp lst3))
           (not (member-equal newv
                              (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance
                 not-member-loop$-as-general
                 (fnp 'symbolp)
                 (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                 (n 2)))))

(defthm not-member-loop$-as-true-list-1
  (implies (and (not (true-listp (car newv)))
                (true-list-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'true-listp)
                           (tuple (cons lst1 rest))
                           (n 0)))))

(defthm not-member-loop$-as-true-list-2
  (implies (and (not (true-listp (cadr newv)))
                (true-list-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance not-member-loop$-as-general
                           (fnp 'true-listp)
                           (tuple (cons lst1 (cons lst2 rest)))
                           (n 1)))))

(defthm not-member-loop$-as-true-list-3
  (implies (and (not (true-listp (caddr newv)))
                (true-list-listp lst3))
           (not (member-equal newv
                              (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :in-theory (disable not-member-loop$-as-general)
           :use (:instance
                 not-member-loop$-as-general
                 (fnp 'true-listp)
                 (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                 (n 2)))))
; -----------------------------------------------------------------


(defthm structure-of-loop$-as-elements
  (implies (member-equal newv (loop$-as tuple))
           (and (true-listp newv)
                (equal (len newv) (len tuple))))
  :rule-classes nil)

(defthm structure-of-loop$-as-elements-bridge
  (and (implies (not (true-listp newv))
                (not (member-equal newv (loop$-as tuple))))
       (implies (not (equal (len newv) (len tuple)))
                (not (member-equal newv (loop$-as tuple)))))
  :hints (("Goal" :use structure-of-loop$-as-elements)))



(defthm not-member-loop$-as-rational-listp-1
  (implies (and (not (rational-listp (car newv)))
                (always$ 'rational-listp lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :use (:instance not-member-loop$-as-general
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm not-member-loop$-as-rational-listp-2
  (implies (and (not (rational-listp (cadr newv)))
                (always$ 'rational-listp lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :use (:instance not-member-loop$-as-general
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm not-member-loop$-as-rational-listp-3
  (implies (and (not (rational-listp (caddr newv)))
                (always$ 'rational-listp lst3))
           (not (member-equal newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :use (:instance
                        not-member-loop$-as-general
                        (fnp 'rational-listp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm not-member-loop$-as-identity-1
  (implies (and (not (car newv))
                (always$ 'identity lst1))
           (not (member-equal newv (loop$-as (cons lst1 rest)))))
  :hints (("Goal" :use (:instance not-member-loop$-as-general
                                  (fnp 'identity)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm not-member-loop$-as-identity-2
  (implies (and (not (cadr newv))
                (always$ 'identity lst2))
           (not (member-equal newv (loop$-as (cons lst1 (cons lst2 rest))))))
  :hints (("Goal" :use (:instance not-member-loop$-as-general
                                  (fnp 'identity)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm not-member-loop$-as-identity-3
  (implies (and (not (caddr newv))
                (always$ 'identity lst3))
           (not (member-equal newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
  :hints (("Goal" :use (:instance
                        not-member-loop$-as-general
                        (fnp 'identity)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm always-rational-listp-tails
  (implies (rational-listp lst)
           (always$ 'rational-listp (tails lst))))

(defthm no-element-tails-empty
  (always$ 'identity (tails lst)))

; The need for either of the following lemmas disturbs me.  See the
; discussion after the big test in books/system/tests/loop-tests.lisp.

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b)) (true-listp b)))

; or

; (defthm boohoo-lemma
;   (implies (not (true-listp (append a b)))
;            (not (true-listp b))))

(defthm not-member-tails-integer-listp
  (implies (and (integer-listp lst)
                (not (integer-listp newv)))
           (not (member-equal newv (tails lst)))))

(defthm not-member-tails-rational-listp
  (implies (and (rational-listp lst)
                (not (rational-listp newv)))
           (not (member-equal newv (tails lst)))))

(defthm not-member-tails-acl2-number-listp
  (implies (and (acl2-number-listp lst)
                (not (acl2-number-listp newv)))
           (not (member-equal newv (tails lst)))))

(defthm not-member-tails-symbol-listp
  (implies (and (symbol-listp lst)
                (not (symbol-listp newv)))
           (not (member-equal newv (tails lst)))))

(defthm not-member-tails-true-list-listp
  (implies (and (true-list-listp lst)
                (not (true-list-listp newv)))
           (not (member-equal newv (tails lst)))))

; Historical Note: Through Version 8.3, this book ended here.  However, as
; loop$ recursion and rewriting of lambda objects were being developed (v8.2
; and v8.3) many additional loop$-related lemmas were identified.  They've been
; pasted below.  The reason for this note is to explain that there is no reason
; (other than continuous evolution) that these lemmas aren't sprinkled into the
; sequence above in some logical ordering.

(defun from-to-by-down (i j)
  (declare (xargs :measure (nfix (- (+ 1 (ifix j)) (ifix i)))))
  (cond
   ((integerp j)
    (if (< j (ifix i))
        nil
        (append (from-to-by-down i (- j 1)) (list j))))
   (t nil)))

(defthm from-to-by-down-induction
  t
  :rule-classes
  ((:induction :pattern (from-to-by i j 1)
               :scheme (from-to-by-down i j))))

(defthm from-to-by-down-opener
  (implies (and (integerp i)
                (integerp j))
           (equal (from-to-by i j 1)
                  (if (<= i j)
                      (append (from-to-by i (- j 1) 1) (list j))
                      nil)))
  :hints (("Subgoal *1/4'''" :expand ((from-to-by i i 1)
                                      (from-to-by (+ 1 i) i 1))))
  :rule-classes ((:definition :install-body nil)))

(defthm len-collect$+-1
  (equal (len (collect$+ fn gvars (loop$-as (list lst))))
         (len lst)))

(defthm loop$-as-1-induction
  t
  :rule-classes ((:induction :pattern (loop$-as (list lst1))
                             :scheme (len lst1))))

(defun loop$-as-hint-2 (lst1 lst2)
  (cond ((endp lst1) nil)
        ((endp lst2) nil)
        (t (loop$-as-hint-2 (cdr lst1) (cdr lst2)))))

(defthm loop$-as-2-induction
  t
  :rule-classes ((:induction :pattern (loop$-as (list lst1 lst2))
                             :scheme (loop$-as-hint-2 lst1 lst2))))

(defthm len-collect$+-2
  (equal (len (collect$+ fn gvars (loop$-as (list lst1 lst2))))
         (min (len lst1)
              (len lst2))))

(defthm always$-t
  (equal (always$ `(lambda (,e) 't) lst)
         t))

(defthm sum$-append
  (equal (sum$ fn (append a b))
         (+ (sum$ fn a) (sum$ fn b))))

(defthm always$-append
  (equal (always$ fn (append a b))
         (and (always$ fn a) (always$ fn b))))

(defthm thereis$-append
  (equal (thereis$ fn (append a b))
         (or (thereis$ fn a) (thereis$ fn b))))

(defthm collect$-append
  (equal (collect$ fn (append a b))
         (append (collect$ fn a) (collect$ fn b))))

(defthm append$-append
  (equal (append$ fn (append a b))
         (append (append$ fn a) (append$ fn b))))

(defthm until$-append
  (equal (until$ fn (append a b))
         (if (thereis$ fn a)
             (until$ fn a)
             (append a (until$ fn b)))))

(defthm when$-append
  (equal (when$ fn (append a b))
         (append (when$ fn a) (when$ fn b))))

(defthm sum$+-append-1
  (equal (sum$+ fn gvars (loop$-as (list (append a b))))
         (+ (sum$+ fn gvars (loop$-as (list a)))
            (sum$+ fn gvars (loop$-as (list b))))))

(defthm sum$+-append-2a
  (equal (sum$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (+ (sum$+ fn gvars (loop$-as (list a c)))
              (sum$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (sum$+ fn gvars (loop$-as (list a c)))))))

(defthm sum$+-append-2b
  (equal (sum$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (+ (sum$+ fn gvars (loop$-as (list c a)))
              (sum$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (sum$+ fn gvars (loop$-as (list c a)))))))

(defthm always$+-append-1
  (equal (always$+ fn gvars (loop$-as (list (append a b))))
         (and (always$+ fn gvars (loop$-as (list a)))
              (always$+ fn gvars (loop$-as (list b))))))

(defthm always$+-append-2a
  (equal (always$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (and (always$+ fn gvars (loop$-as (list a c)))
                (always$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (always$+ fn gvars (loop$-as (list a c)))))))

(defthm always$+-append-2b
  (equal (always$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (and (always$+ fn gvars (loop$-as (list c a)))
                (always$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (always$+ fn gvars (loop$-as (list c a)))))))

(defthm thereis$+-append-1
  (equal (thereis$+ fn gvars (loop$-as (list (append a b))))
         (or (thereis$+ fn gvars (loop$-as (list a)))
             (thereis$+ fn gvars (loop$-as (list b))))))

(defthm thereis$+-append-2a
  (equal (thereis$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (or (thereis$+ fn gvars (loop$-as (list a c)))
               (thereis$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (thereis$+ fn gvars (loop$-as (list a c)))))))

(defthm thereis$+-append-2b
  (equal (thereis$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (or (thereis$+ fn gvars (loop$-as (list c a)))
               (thereis$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (thereis$+ fn gvars (loop$-as (list c a)))))))

(defthm collect$+-append-1
  (equal (collect$+ fn gvars (loop$-as (list (append a b))))
         (append (collect$+ fn gvars (loop$-as (list a)))
                 (collect$+ fn gvars (loop$-as (list b))))))

(defthm collect$+-append-2a
  (equal (collect$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (append (collect$+ fn gvars (loop$-as (list a c)))
                   (collect$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (collect$+ fn gvars (loop$-as (list a c)))))))

(defthm collect$+-append-2b
  (equal (collect$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (append (collect$+ fn gvars (loop$-as (list c a)))
                   (collect$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (collect$+ fn gvars (loop$-as (list c a)))))))

(defthm append$+-append-1
  (equal (append$+ fn gvars (loop$-as (list (append a b))))
         (append (append$+ fn gvars (loop$-as (list a)))
                 (append$+ fn gvars (loop$-as (list b))))))

(defthm append$+-append-2a
  (equal (append$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (append (append$+ fn gvars (loop$-as (list a c)))
                   (append$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (append$+ fn gvars (loop$-as (list a c)))))))

(defthm append$+-append-2b
  (equal (append$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (append (append$+ fn gvars (loop$-as (list c a)))
                   (append$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (append$+ fn gvars (loop$-as (list c a)))))))

(defthm until$+-append-1
  (equal (until$+ fn gvars (loop$-as (list (append a b))))
         (if (thereis$+ fn gvars (loop$-as (list a)))
             (until$+ fn gvars (loop$-as (list a)))
             (append (loop$-as (list a)) (until$+ fn gvars (loop$-as (list b)))))))

(defthm until$+-append-2a
  (equal (until$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (if (thereis$+ fn gvars (loop$-as (list a c)))
               (until$+ fn gvars (loop$-as (list a c)))
               (append (loop$-as (list a c))
                       (until$+ fn gvars (loop$-as (list b (nthcdr (len a) c)))))))
          (t (until$+ fn gvars (loop$-as (list a c)))))))

(defthm until$+-append-2b
  (equal (until$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (if (thereis$+ fn gvars (loop$-as (list c a)))
               (until$+ fn gvars (loop$-as (list c a)))
               (append (loop$-as (list c a))
                       (until$+ fn gvars (loop$-as (list (nthcdr (len a) c) b))))))
          (t (until$+ fn gvars (loop$-as (list c a)))))))

(defthm when$+-append-1
  (equal (when$+ fn gvars (loop$-as (list (append a b))))
         (append (when$+ fn gvars (loop$-as (list a)))
                 (when$+ fn gvars (loop$-as (list b))))))

(defthm when$+-append-2a
  (equal (when$+ fn gvars (loop$-as (list (append a b) c)))
         (cond
          ((< (len a) (len c))
           (append (when$+ fn gvars (loop$-as (list a c)))
                   (when$+ fn gvars (loop$-as (list b (nthcdr (len a) c))))))
          (t (when$+ fn gvars (loop$-as (list a c)))))))

(defthm when$+-append-2b
  (equal (when$+ fn gvars (loop$-as (list c (append a b))))
         (cond
          ((< (len a) (len c))
           (append (when$+ fn gvars (loop$-as (list c a)))
                   (when$+ fn gvars (loop$-as (list (nthcdr (len a) c) b)))))
          (t (when$+ fn gvars (loop$-as (list c a)))))))

(defthm sum$-singleton
  (equal (sum$ fn (list x))
         (fix (apply$ fn (list x)))))

(defthm always$-singleton
  (equal (always$ fn (list x))
         (if (apply$ fn (list x)) t nil)))

(defthm thereis$-singleton
  (equal (thereis$ fn (list x))
         (apply$ fn (list x))))

(defthm collect$-singleton
  (equal (collect$ fn (list x))
         (list (apply$ fn (list x)))))

(defthm append$-singleton
  (equal (append$ fn (list x))
         (true-list-fix (apply$ fn (list x)))))

(defthm until$-singleton
  (equal (until$ fn (list x))
         (if (apply$ fn (list x))
             nil
             (list x))))

(defthm when$-singleton
  (equal (when$ fn (list x))
         (if (apply$ fn (list x))
             (list x)
             nil)))

; Here are the singleton theorems for the fancy loop$ scions.  However, we
; think that in general (loop$-as (list (list x))) will always expand to (list
; (list x)) and so phrase them in those terms rather than with a loop$-as.

(defthm sum$+-singleton
  (equal (sum$+ fn gvars (list ituple))
         (fix (apply$ fn (list gvars ituple)))))

(defthm always$+-singleton
  (equal (always$+ fn gvars (list ituple))
         (if (apply$ fn (list gvars ituple))
             t
             nil)))

(defthm thereis$+-singleton
  (equal (thereis$+ fn gvars (list ituple))
         (apply$ fn (list gvars ituple))))

(defthm collect$+-singleton
  (equal (collect$+ fn gvars (list ituple))
         (list (apply$ fn (list gvars ituple)))))

(defthm append$+-singleton
  (equal (append$+ fn gvars (list ituple))
         (true-list-fix (apply$ fn (list gvars ituple)))))

(defthm until$+-singleton
  (equal (until$+ fn gvars (list ituple))
         (if (apply$ fn (list gvars ituple))
             nil
             (list ituple))))

(defthm when$+-singleton
  (equal (when$+ fn gvars (list ituple))
         (if (apply$ fn (list gvars ituple))
             (list ituple)
             nil)))

; -----------------------------------------------------------------
; The Composition Rules: The motivation for these rules are theorems involving
; compositions like (pstermp (pssubst new old term)) and (psoccur var (pssubst
; new var term)), where the ``ps'' prefix stands for ``pseudo-term'' and name
; loop$-recursive versions of the obvious system functions.  Pstermp is defined
; loop$-recursively with an ALWAYS loop$ while psoccur is defined
; loop$-recursively with a THEREIS loop$.

; The second conjunct of theorems involving terms like these address the loop$s
; within these functions.  Consider a theorem about (psoccur var (pssubst new
; var term)).  The loop$ version might be

; (loop$ for e in term thereis (psoccur var (pssubst new var e)))   ; [1]

; but could alternatively be written 

; (loop$ for e in (loop$ for d in term collect (pssubst new var d)) ; [2]
;        thereis (psoccur var e))

; These are equivalent but we have no control over which of the two forms the
; user might choose.  The first theorem below rewrites [2] into [1].  The idea
; is that [1] is simpler and also gets the ppoccur and pssubst together in a
; single term where they might be rewritten.

; There are five versions of the rule depending on the free variables occuring
; in the two bodies.  The rule for handling [2] above is the fourth one below,
; because the THEREIS loop$ has one free variable, var, but the COLLECT has
; two, new and var.  Thus the fourth rule below uses two different variables,
; gvars1 and gvars2, for the values of the free variables being passed into
; their respective lambda objects.  So the five cases are: (1) the loop$s in
; both functions -- here psoccur and pssubst -- are plain, the loop$ in one is
; plain and the loop$ in the other is fancy (two versions, depending whether
; the inner or outer loop is plain), and both loop$s are fancy (two versions,
; depending on whether the gvars of the two scions are identical or not).  The
; last case is discussed in ``the next two rules'' comment below.

; It should be noted that the fourth rule below combines the two separate gvars
; into (list gvars1 gvars2) and relies on relink-fancy-scions to unpack that
; and the references to the corresponding free variables.

; We have an analogous composition rule for ALWAYS versus COLLECT.

; Other composition rules might be considered.  The most obviously analogous
; rules would be about THEREIS composed with APPEND, and ALWAYS composed with
; APPEND.  But we might want to investigate THEREIS composed with ALWAYS and
; vice versa.

(defthm compose-thereis-collect
  (and (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1))
                (equal (THEREIS$ `(LAMBDA (,u1) ,expr1)
                                 (COLLECT$ `(LAMBDA (,v1) ,expr2) lst))
                       (THEREIS$ `(LAMBDA (,v1) ((LAMBDA (,u1) ,expr1) ,expr2))
                                 lst)))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1)(symbolp v2))
                (equal (THEREIS$ `(LAMBDA (,u1) ,expr1)
                                 (COLLECT$+ `(LAMBDA (,v1 ,v2) ,expr2)
                                            gvars
                                            (LOOP$-AS (LIST lst))))
                       (THEREIS$+ `(LAMBDA (,v1 ,v2)
                                           ((LAMBDA (,u1) ,expr1) ,expr2))
                                  gvars
                                  (LOOP$-AS (LIST lst)))))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1) (not (eq u1 v1)) (not (eq u1 v2))
                     (symbolp u2) (symbolp v2) (not (eq u2 v2)))
                (equal (THEREIS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                  gvars
                                  (LOOP$-AS
                                   (LIST (COLLECT$ `(LAMBDA (,v2) ,expr2) lst))))
                       (THEREIS$+ `(LAMBDA (,u1 ,v2)
                                           ((LAMBDA (,u1 ,v1) ,expr1)
                                            ,u1
                                            (CONS ((LAMBDA (,v2) ,expr2) (CAR ,v2)) 'NIL)))
                                  gvars
                                  (LOOP$-AS (LIST lst)))))

; The next two rules rewrite thereis$+/collect$+, but with two cases: the
; general version in which each scion has its own gvars (i.e., gvars1 for the
; thereis$+ but gvars2 for the collect$+) and the special case when the gvars
; are identical.  We list the special case last so that it is tried first by
; the rewriter.

       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1) (not (eq u1 v1))
                     (symbolp u2) (symbolp v2) (not (eq u2 v2)))
                (equal (THEREIS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                  gvars1
                                  (LOOP$-AS
                                   (LIST (COLLECT$+ `(LAMBDA (,u2 ,v2) ,expr2)
                                                    gvars2
                                                    (LOOP$-AS (LIST lst))))))
                       (THEREIS$+ `(LAMBDA (,u2 ,v2)
                                           ((LAMBDA (,u1 ,v1) ,expr1)
                                            (car ,u2)
                                            ((lambda (,u2 ,v2) (CONS ,expr2 'NIL))
                                             (car (cdr ,u2))
                                             ,v2)))
                                  (list gvars1 gvars2)
                                  (LOOP$-AS (LIST lst)))))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1) (not (eq u1 v1))
                     (symbolp u2) (symbolp v2) (not (eq u2 v2)))
                (equal (THEREIS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                  gvars
                                  (LOOP$-AS
                                   (LIST (COLLECT$+ `(LAMBDA (,u2 ,v2) ,expr2)
                                                    gvars
                                                    (LOOP$-AS (LIST lst))))))
                       (THEREIS$+ `(LAMBDA (,u2 ,v2)
                                           ((LAMBDA (,u1 ,v1) ,expr1)
                                            ,u2
                                            (CONS ,expr2 'NIL)))
                                  gvars
                                  (LOOP$-AS (LIST lst)))))))

(defthm compose-always-collect
  (and (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1))
                (equal (ALWAYS$ `(LAMBDA (,u1) ,expr1)
                                (COLLECT$ `(LAMBDA (,v1) ,expr2) lst))
                       (ALWAYS$ `(LAMBDA (,v1) ((LAMBDA (,u1) ,expr1) ,expr2))
                                lst)))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1)(symbolp v2))
                (equal (ALWAYS$ `(LAMBDA (,u1) ,expr1)
                                (COLLECT$+ `(LAMBDA (,v1 ,v2) ,expr2)
                                           gvars
                                           (LOOP$-AS (LIST lst))))
                       (ALWAYS$+ `(LAMBDA (,v1 ,v2)
                                          ((LAMBDA (,u1) ,expr1) ,expr2))
                                 gvars
                                 (LOOP$-AS (LIST lst)))))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1)
                     (not (eq u1 v1)) (not (eq u1 v2))
                     (symbolp u2) (symbolp v2)
                     (not (eq u2 v2)))
                (equal (ALWAYS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                 gvars
                                 (LOOP$-AS
                                  (LIST (COLLECT$ `(LAMBDA (,v2) ,expr2)
                                                  lst))))
                       (ALWAYS$+ `(LAMBDA (,u1 ,v2)
                                          ((LAMBDA (,u1 ,v1) ,expr1)
                                           ,u1
                                           (CONS ((LAMBDA (,v2) ,expr2)
                                                  (CAR ,v2))
                                                 'NIL)))
                                 gvars
                                 (LOOP$-AS (LIST lst)))))

; The next two rules rewrite always$+/collect$+, but with two cases: the
; general version in which each scion has its own gvars (i.e., gvars1 for the
; always$+ but gvars2 for the collect$+) and the special case when the gvars
; are identical.  We list the special case last so that it is tried first by
; the rewriter.

       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1) (not (eq u1 v1))
                     (symbolp u2) (symbolp v2) (not (eq u2 v2)))
                (equal (ALWAYS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                 gvars1
                                 (LOOP$-AS
                                  (LIST (COLLECT$+ `(LAMBDA (,u2 ,v2) ,expr2)
                                                   gvars2
                                                   (LOOP$-AS (LIST lst))))))
                       (ALWAYS$+ `(LAMBDA (,u2 ,v2)
                                          ((LAMBDA (,u1 ,v1) ,expr1)
                                           (car ,u2)
                                           ((lambda (,u2 ,v2)
                                              (CONS ,expr2 'NIL))
                                            (car (cdr ,u2))
                                            ,v2)))
                                 (list gvars1 gvars2)
                                 (LOOP$-AS (LIST lst)))))
       (implies (and (tamep expr1) (tamep expr2)
                     (symbolp u1) (symbolp v1) (not (eq u1 v1))
                     (symbolp u2) (symbolp v2) (not (eq u2 v2)))
                (equal (ALWAYS$+ `(LAMBDA (,u1 ,v1) ,expr1)
                                 gvars
                                 (LOOP$-AS
                                  (LIST (COLLECT$+ `(LAMBDA (,u2 ,v2) ,expr2)
                                                   gvars
                                                   (LOOP$-AS (LIST lst))))))
                       (ALWAYS$+ `(LAMBDA (,u2 ,v2)
                                          ((LAMBDA (,u1 ,v1) ,expr1)
                                           ,u2
                                           (CONS ,expr2 'NIL)))
                                 gvars
                                 (LOOP$-AS (LIST lst)))))))
