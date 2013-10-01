;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Common utility functions.
;;
;; This file introduces several common functions for operating on lists.
;;
;; We find it easier to reason about functions which are not tail recursive.
;; However, we also provide tail recursive versions of many functions for
;; greater efficiency.  We typically call these variants fast-<foo>, then prove
;; fast-<foo> is somehow similar to <foo>.  Sometimes our variants produce
;; slightly different answers than their simple counterparts, and we mark these
;; differences with a $ suffix.  For example, fast-range$ computes (rev (range
;; x)) instead of (range x).

(defund len (x)
  ;; Compute the length of a list.
  ;;
  ;; Performance.  This is a straightforward but inefficient version of the
  ;; function.  It is not tail-recursive and may cause stack overflows on large
  ;; lists.  See the functions fast-len and same-lengthp, below, for some
  ;; performance oriented alternatives.
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (len (cdr x)))
    0))

(defthm len-when-not-consp
  (implies (not (consp x))
           (equal (len x)
                  0))
  :hints(("Goal" :in-theory (enable len))))

(defthm len-of-cons
  (equal (len (cons a x))
         (+ 1 (len x)))
  :hints(("Goal" :in-theory (enable len))))

(defthm natp-of-len
  (equal (natp (len x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm natp-of-len-free
  (implies (equal n (len x))
           (equal (natp n)
                  t)))

(defthm len-under-iff
  (iff (len x)
       t)
  :hints(("Goal"
          :in-theory (disable natp-of-len natp-of-len-free)
          :use ((:instance natp-of-len)))))



(defthm |(< 0 (len x))|
  (equal (< 0 (len x))
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm |(< 1 (len x))|
  (equal (< 1 (len x))
         (consp (cdr x))))

(defthm decrement-len-when-consp
  (implies (consp x)
           (equal (- (len x) 1)
                  (len (cdr x)))))

(defthm equal-of-len-and-zero
  ;; No symmetric rule because of term order.
  (equal (equal 0 (len x))
         (not (consp x))))

(defthm consp-of-cdr-when-len-two-cheap
  (implies (equal (len x) 2)
           (equal (consp (cdr x))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(encapsulate
 ()
 ;; We can solve (consp (cdr ... (cdr x))) when we know the length of x.
 (defthm consp-of-cdr-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n)))
            (equal (consp (cdr x))
                   (< 1 n))))

 (defthm consp-of-cdr-of-cdr-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n)))
            (equal (consp (cdr (cdr x)))
                   (< 2 n))))

 (defthm consp-of-cdr-of-cdr-of-cdr-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n)))
            (equal (consp (cdr (cdr (cdr x))))
                   (< 3 n)))))

(encapsulate
 ()
 ;; We can solve (cdr ... (cdr x)) under iff when we know the length of x.

 (defthm cdr-under-iff-with-len-free-in-bound
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< 1 n))
            (iff (cdr x)
                 t)))

 (defthm cdr-of-cdr-under-iff-with-len-free-in-bound
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< 2 n))
            (iff (cdr (cdr x))
                 t)))

 (defthm cdr-of-cdr-of-cdr-under-iff-with-len-free-in-bound
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< 3 n))
            (iff (cdr (cdr (cdr x)))
                 t)))

 (defthm cdr-of-cdr-with-len-free-past-the-end
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< n 2))
            (equal (cdr (cdr x))
                   nil)))

 (defthm cdr-of-cdr-of-cdr-with-len-free-past-the-end
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< n 3))
            (equal (cdr (cdr (cdr x)))
                   nil))))

(defthm len-2-when-not-cdr-of-cdr
  (implies (not (cdr (cdr x)))
           (equal (equal 2 (len x))
                  (consp (cdr x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))



(defthmd equal-when-length-different
  (implies (not (equal (len a) (len b)))
           (equal (equal a b)
                  nil)))




(defund fast-len (x acc)
  ;; Compute (+ (len x) acc)
  ;;
  ;; Performance.  This is a tail recursive variant of len which avoids stack
  ;; overflows.  It is between 4-18% faster than len in GCL, and 22-31% faster
  ;; than len in CMUCL.  Note that the benefits are consistently on the high
  ;; end of these ranges when the lengths are over 100.
  (declare (xargs :guard (natp acc)))
  (if (consp x)
      (fast-len (cdr x) (+ 1 acc))
    acc))

(defthm fast-len-removal
  (implies (force (natp acc))
           (equal (fast-len x acc)
                  (+ (len x) acc)))
  :hints(("Goal" :in-theory (enable fast-len))))




(defund same-lengthp (x y)
  ;; Are (len x) and (len y) the same?
  ;;
  ;; Performance.  We walk down both lists together and check if they end after
  ;; the same number of steps.  This is tail recursive and requires no
  ;; arithmetic.  As a result, it is very fast: 99% faster than using "len" in
  ;; GCL, and 96-97% faster in CMUCL.
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (same-lengthp (cdr x) (cdr y)))
    (not (consp y))))

(defthm same-lengthp-removal
  (equal (same-lengthp x y)
         (equal (len x) (len y)))
  :hints(("Goal" :in-theory (enable same-lengthp))))




(defund true-listp (x)
  ;; Is x a proper list, i.e., does it end with nil?
  ;;
  ;; Our standard interpretation of objects as lists ignore the final cdr,
  ;; e.g., (1 2 . 3) and (1 2 . nil) are both interpreted as the list [1, 2].
  ;; We think of nil as the canonical choice for this final cdr position, and
  ;; our list functions will typically create true-lists as their outputs.
  (declare (xargs :guard t))
  (if (consp x)
      (true-listp (cdr x))
    (equal x nil)))

(defthm true-listp-when-not-consp
  (implies (not (consp x))
           (equal (true-listp x)
                  (equal x nil)))
  :hints(("Goal" :in-theory (enable true-listp))))

(defthm true-listp-of-cons
  (equal (true-listp (cons a x))
         (true-listp x))
  :hints(("Goal" :in-theory (enable true-listp))))

(defthm booleanp-of-true-listp
  (equal (booleanp (true-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-cdr
  (implies (true-listp x)
           (equal (true-listp (cdr x))
                  t)))

(defthm consp-when-true-listp-cheap
  (implies (true-listp x)
           (equal (consp x)
                  (if x t nil)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm list-of-first-and-second-when-len-2
  (implies (and (equal (len x) 2)
                (true-listp x))
           (equal (list (first x) (second x))
                  x)))

(defthm list-of-first-and-second-and-third-when-len-3
  (implies (and (equal (len x) 3)
                (true-listp x))
           (equal (list (first x) (second x) (third x))
                  x)))

(encapsulate
 ()
 ;; If we also know x is a true list, then we even know the final cdr (and
 ;; every cdr past it) is exactly nil.

 (defthm cdr-when-true-listp-with-len-free-past-the-end
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< n 2)
                 (true-listp x))
            (equal (cdr x)
                   nil)))

 (defthm cdr-of-cdr-when-true-listp-with-len-free-past-the-end
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< n 3)
                 (true-listp x))
            (equal (cdr (cdr x))
                   nil)))

 (defthm cdr-of-cdr-of-cdr-when-true-listp-with-len-free-past-the-end
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (< n 4)
                 (true-listp x))
            (equal (cdr (cdr (cdr x)))
                   nil))))


(encapsulate
 ()
 ;; If we only care about iff and we know x is a true list, we can be more
 ;; precise about exactly when the cdr is nil or non-nil.

 (defthm cdr-under-iff-when-true-listp-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (true-listp x))
            (iff (cdr x)
                 (< 1 n))))

 (defthm cdr-of-cdr-under-iff-when-true-listp-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (true-listp x))
            (iff (cdr (cdr x))
                 (< 2 n))))

 (defthm cdr-of-cdr-of-cdr-under-iff-when-true-listp-with-len-free
   (implies (and (equal (len x) n)
                 (syntaxp (ACL2::quotep n))
                 (true-listp x))
            (iff (cdr (cdr (cdr x)))
                 (< 3 n)))))




(defund list-fix (x)
  ;; Canonicalize the list x.
  ;;
  ;; We keep all of the elements of x in order, but change the final cdr to nil
  ;; in order to create a proper true-listp.
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (list-fix (cdr x)))
    nil))

(defthm list-fix-when-not-consp
  (implies (not (consp x))
           (equal (list-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable list-fix))))

(defthm list-fix-of-cons
  (equal (list-fix (cons a x))
         (cons a (list-fix x)))
  :hints(("Goal" :in-theory (enable list-fix))))

(defthm car-of-list-fix
  (equal (car (list-fix x))
         (car x)))

(defthm cdr-of-list-fix
  (equal (cdr (list-fix x))
         (list-fix (cdr x))))

(defthm consp-of-list-fix
  (equal (consp (list-fix x))
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm list-fix-under-iff
  (iff (list-fix x)
       (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-list-fix
  (equal (len (list-fix x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-list-fix
  (equal (true-listp (list-fix x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm list-fix-when-true-listp
  (implies (true-listp x)
           (equal (list-fix x)
                  x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cdr-of-list-fix-under-iff
  (iff (cdr (list-fix x))
       (consp (cdr x))))

(defthm equal-of-list-fix-and-self
  (equal (equal x (list-fix x))
         (true-listp x))
  :hints(("Goal" :induct (cdr-induction x))))



(defund memberp (a x)
  ;; Is a an element of x?
  ;;
  ;; Related functions.  The function first-index tells you the position where
  ;; the element first occurs in the list.
  (declare (xargs :guard t))
  (if (consp x)
      (or (equal a (car x))
          (memberp a (cdr x)))
    nil))

(defthm memberp-when-not-consp
  (implies (not (consp x))
           (equal (memberp a x)
                  nil))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm memberp-of-cons
  (equal (memberp a (cons b x))
         (or (equal a b)
             (memberp a x)))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm booleanp-of-memberp
  (equal (booleanp (memberp a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-list-fix
  (equal (memberp a (list-fix x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-when-memberp-of-cdr
  (implies (memberp a (cdr x))
           (equal (memberp a x)
                  t)))

(defthm memberp-of-car
  (equal (memberp (car x) x)
         (consp x)))

(defthm memberp-of-second
  (implies (and (consp x)
                (consp (cdr x)))
           (equal (memberp (second x) x)
                  t)))

(defthm car-when-memberp-of-singleton-list-cheap
  (implies (and (memberp a x)
                (not (consp (cdr x))))
           (equal (car x)
                  a))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm car-when-memberp-and-not-memberp-of-cdr-cheap
  (implies (and (memberp a x)
                (not (memberp a (cdr x))))
           (equal (car x)
                  a))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm consp-when-memberp-cheap
  (implies (memberp a x)
           (equal (consp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm consp-of-cdr-when-memberp-not-car-cheap
  (implies (and (memberp a x)
                (not (equal (car x) a)))
           (equal (consp (cdr x))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm rank-when-memberp
  (implies (memberp a x)
           (equal (< (rank a) (rank x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rank-when-memberp-weak
  (implies (memberp a x)
           (equal (< (rank x) (rank a))
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))




(defund subsetp (x y)
  ;; Is every element of x an element of y?
  ;;
  ;; Related functions.  The function subsetp-badguy returns the first
  ;; "counterexample" to subsetp, if one exists.  That is, it tries to find an
  ;; element which is in x but which is not in y.  This is sometimes useful
  ;; when reasoning about subsets.
  ;;
  ;; Performance.  This is a straightforward O(n^2) implementation wherein we
  ;; just repeatedly call memberp in a loop.  This should be acceptable for
  ;; small lists, particularly since the function is tail recursive, never
  ;; needs to cons anything, and never does any arithmetic.  We could
  ;; eventually implement a variant of subsetp which would sort its inputs,
  ;; then do a step-wise comparison.  This could be O(n log n), but would
  ;; require consing and so it would probably not perform well for small lists.
  (declare (xargs :guard t))
  (if (consp x)
      (and (memberp (car x) y)
           (subsetp (cdr x) y))
    t))

(defthm subsetp-when-not-consp
  (implies (not (consp x))
           (equal (subsetp x y)
                  t))
  :hints(("Goal" :in-theory (enable subsetp))))

(defthm subsetp-when-not-consp-two
  (implies (not (consp y))
           (equal (subsetp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable subsetp))))

(defthm subsetp-of-cons
  (equal (subsetp (cons a x) y)
         (and (memberp a y)
              (subsetp x y)))
  :hints(("Goal" :in-theory (enable subsetp))))

(defthm subsetp-of-cons-two
  (implies (subsetp x y)
           (equal (subsetp x (cons a y))
                  t))
  :hints(("Goal" :in-theory (enable subsetp))))

(defthm booleanp-of-subsetp
  (equal (booleanp (subsetp x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-list-fix-one
  (equal (subsetp (list-fix x) y)
         (subsetp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-list-fix-two
  (equal (subsetp x (list-fix y))
         (subsetp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-cdr
  (implies (subsetp x y)
           (equal (subsetp (cdr x) y)
                  t)))

(defthm in-superset-when-in-subset-one
  (implies (and (subsetp x y)
                (memberp a x))
           (equal (memberp a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm in-superset-when-in-subset-two
  (implies (and (memberp a x)
                (subsetp x y))
           (equal (memberp a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm not-in-subset-when-not-in-superset-one
  (implies (and (not (memberp a y))
                (subsetp x y))
           (equal (memberp a x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm not-in-subset-when-not-in-superset-two
  (implies (and (subsetp x y)
                (not (memberp a y)))
           (equal (memberp a x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-when-nonempty-subset-cheap
  (implies (and (subsetp x y)
                (consp x))
           (equal (consp y)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm subsetp-reflexive
  (equal (subsetp x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-transitive-one
  (implies (and (subsetp x y)
                (subsetp y z))
           (equal (subsetp x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-transitive-two
  (implies (and (subsetp y z)
                (subsetp x y))
           (equal (subsetp x z)
                  t)))





(defund subsetp-badguy (x y)
  ;; Find a member of x which is not a member of y, if one exists.
  ;;
  ;; If we can find such a member, then we see that x is not a subset of y.
  ;; This is sometimes useful for pick-a-point proofs; search for uses of
  ;; subsetp-badguy-membership-property for examples, and see also the 2004
  ;; ACL2 workshop paper, "Finite Set Theory based on Fully Ordered Lists",
  ;; which you can easily find with Google.
  (declare (xargs :guard t))
  (if (consp x)
      (if (not (memberp (car x) y))
          (cons t (car x))
        (subsetp-badguy (cdr x) y))
    nil))

(defthm subsetp-badguy-membership-property
  (implies (subsetp-badguy x y)
           (and (memberp (cdr (subsetp-badguy x y)) x)
                (not (memberp (cdr (subsetp-badguy x y)) y))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (enable subsetp-badguy)
          :induct (cdr-induction x))))

(defthm subsetp-badguy-under-iff
  (iff (subsetp-badguy x y)
       (not (subsetp x y)))
  :hints(("Goal"
          :in-theory (enable subsetp-badguy)
          :induct (cdr-induction x))))



(defund app (x y)
  ;; Append the lists x and y.
  ;;
  ;; Performance.  This is a straightforward but inefficient version of the
  ;; function.  It is not tail recursive and may cause stack overflows on large
  ;; lists.  It also list-fixes its argument, which is nice for us to reason
  ;; about but will always require (+ (len x) (len y)) conses.  See fast-app
  ;; and revappend for faster alternatives.
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (app (cdr x) y))
    (list-fix y)))

(defthm app-when-not-consp
  (implies (not (consp x))
           (equal (app x y)
                  (list-fix y)))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-cons
  (equal (app (cons a x) y)
         (cons a (app x y)))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-list-fix-one
  (equal (app (list-fix x) y)
         (app x y))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-list-fix-two
  (equal (app x (list-fix y))
         (app x y))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-when-not-consp-two
  (implies (not (consp y))
           (equal (app x y)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-of-singleton-list-cheap
  (implies (and (consp xs)
                (not (consp (cdr xs))))
           (equal (app xs ys)
                  (cons (car xs) (list-fix ys))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm true-listp-of-app
  (equal (true-listp (app x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-of-app
  (equal (app (app x y) z)
         (app x (app y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-app
  (equal (memberp a (app x y))
         (or (memberp a x)
             (memberp a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-app
  (equal (consp (app x y))
         (or (consp x)
             (consp y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-under-iff
  (iff (app x y)
       (or (consp x)
           (consp y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-app
  (equal (len (app x y))
         (+ (len x)
            (len y)))
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (subsetp x z)
                        (subsetp y z))
                   (subsetp (app x y) z))
          :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                          (x (app x y))
                                          (y z)))))))

 (local (defthm lemma2
          (implies (subsetp (app x y) z)
                   (subsetp x z))
          :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                          (x x)
                                          (y z)))))))

 (local (defthm lemma3
          (implies (subsetp (app x y) z)
                   (subsetp y z))
          :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                          (x y)
                                          (y z)))))))

 (defthm subsetp-of-app-one
   (equal (subsetp (app x y) z)
          (and (subsetp x z)
               (subsetp y z)))))

(defthm subsetp-of-app-two
  (equal (subsetp x (app x y))
         t)
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (app x y)))))))

(defthm subsetp-of-app-three
  (equal (subsetp y (app x y))
         t)
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x y)
                                  (y (app x y)))))))

(defthm subsetp-of-app-when-subsets
  (implies (and (subsetp x y)
                (subsetp w z))
           (equal (subsetp (app x w) (app y z))
                  t))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (app x w))
                                  (y (app y z)))))))

(defthm subsetp-of-symmetric-apps
  (equal (subsetp (app x y) (app y x))
         t)
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (app x y))
                                  (y (app y x)))))))

(defthm weirdo-rule-for-subsetp-of-app-one
  ;; bozo do we really need this?
  (equal (subsetp (app (cdr x) (cons (car x) y)) (app x y))
         (or (consp x)
             (memberp nil y))))

(defthm weirdo-rule-for-subsetp-of-app-two
  ;; bozo do we really need this?
  (equal (subsetp (app (cdr x) (cons (car x) y)) (app y x))
         (or (consp x)
             (memberp nil y))))

(defthm cdr-of-app-when-x-is-consp
  (implies (consp x)
           (equal (cdr (app x y))
                  (app (cdr x) y))))

(defthm car-of-app-when-x-is-consp
  (implies (consp x)
           (equal (car (app x y))
                  (car x))))

(defthm memberp-of-app-onto-singleton
  (equal (memberp a (app x (list b)))
         (or (memberp a x)
             (equal a b))))

(defthm subsetp-of-app-onto-singleton-with-cons
  (equal (subsetp (app x (list a)) (cons a x))
         t)
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (app x (list a)))
                                  (y (cons a x)))))))

(defthm subsetp-of-cons-with-app-onto-singleton
  (equal (subsetp (cons a x) (app x (list a)))
         t)
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (cons a x))
                                  (y (app x (list a))))))))

(defthm subsetp-of-cons-of-app-of-app-one
  (subsetp x (cons b (app y (app x z))))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (cons b (app y (app x z)))))))))

(defthm subsetp-of-cons-of-app-of-app-two
  (subsetp x (cons a (app y (app z x))))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (cons a (app y (app z x)))))))))

(defthm subsetp-of-app-of-app-when-subsetp-one
  (implies (subsetp x y)
           (subsetp x (app a (app y b))))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (app a (app y b))))))))

(defthm subsetp-of-app-of-app-when-subsetp-two
  (implies (subsetp x y)
           (subsetp x (app a (app b y))))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (app a (app b y))))))))

(defthm app-of-cons-of-list-fix-right
  (equal (app x (cons a (list-fix y)))
         (app x (cons a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-of-cons-when-not-consp-right
  (implies (and (not (consp y))
                (syntaxp (not (equal y ''nil))))
           (equal (app x (cons a y))
                  (app x (list a))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm equal-of-app-and-app-when-equal-lens
  (implies (equal (len a) (len c))
           (equal (equal (app a b)
                         (app c d))
                  (and (equal (list-fix a) (list-fix c))
                       (equal (list-fix b) (list-fix d)))))
  :hints(("Goal" :induct (cdr-cdr-induction a c))))

(encapsulate
 ()
 (defthmd lemma-for-equal-of-app-and-self
   (equal (equal (cdr x) (list-fix x))
          (not (consp x)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm equal-of-app-and-self
   (equal (equal y (app x y))
          (and (not (consp x))
               (true-listp y)))
   :hints(("Goal"
           :in-theory (e/d (lemma-for-equal-of-app-and-self)
                           (len-of-app))
           :use ((:instance len-of-app)
                 (:instance len-of-app (x (cdr x))))))))






(defund rev (x)
  ;; Reverse the order of the elements of x.
  ;;
  ;; Performance.  This is a straightforward but severely inefficient version
  ;; of the function.  See the function fast-rev for an alternative.
  (declare (xargs :guard t))
  (if (consp x)
      (app (rev (cdr x))
           (list (car x)))
    nil))

(defthm rev-when-not-consp
  (implies (not (consp x))
           (equal (rev x)
                  nil))
  :hints(("Goal" :in-theory (enable rev))))

(defthm rev-of-cons
  (equal (rev (cons a x))
         (app (rev x) (list a)))
  :hints(("Goal" :in-theory (enable rev))))

(defthm rev-of-list-fix
  (equal (rev (list-fix x))
         (rev x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-rev
  (equal (true-listp (rev x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-under-iff
  (iff (rev x)
       (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-rev
  (equal (len (rev x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-rev
  (equal (memberp a (rev x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-first-of-rev
  (equal (memberp (first (rev x)) x)
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-rev-one
  (equal (subsetp (rev x) y)
         (subsetp x y))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (rev x))
                                  (y x))
                       (:instance subsetp-badguy-membership-property
                                  (x x)
                                  (y (rev x)))))))

(defthm subsetp-of-rev-two
  (equal (subsetp x (rev y))
         (subsetp x y))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x y)
                                  (y (rev y)))
                       (:instance subsetp-badguy-membership-property
                                  (x (rev y))
                                  (y y))))))


(encapsulate
 ()
 (defthmd lemma-for-rev-of-rev
   (equal (rev (app x (list a)))
          (cons a (rev x)))
   :hints(("Goal" :in-theory (enable rev))))

 (defthm rev-of-rev
   (equal (rev (rev x))
          (list-fix x))
   :hints(("Goal"
           :in-theory (enable lemma-for-rev-of-rev)
           :induct (cdr-induction x)))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm rev-of-app
   (equal (rev (app x y))
          (app (rev y) (rev x)))
   :hints(("Goal" :induct (cdr-induction x)))))

(defthm subsetp-of-app-of-rev-of-self-one
  (equal (subsetp x (app (rev x) y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-app-of-rev-of-self-two
  (equal (subsetp x (app y (rev x)))
         t)
  :hints(("Goal" :induct (cdr-induction x))))




(defund revappend (x y)
  ;; Compute (app (rev x) y); almost
  ;;
  ;; Performance.  This is the fastest way I know how to join lists together:
  ;; it is 58-73% faster than app in GCL, and 54-82% faster in CMUCL, with the
  ;; larger benefits on larger lists.  This is because it is tail recursive, and
  ;; it does not list-fix y which saves (len y) conses.
  (declare (xargs :guard (true-listp y)))
  (if (consp x)
      (revappend (cdr x) (cons (car x) y))
    y))

(defthmd revappend-when-not-consp
  (implies (not (consp x))
           (equal (revappend x y)
                  y))
  :hints(("Goal" :in-theory (enable revappend))))

(defthmd revappend-of-cons
  (equal (revappend (cons a x) y)
         (revappend x (cons a y)))
  :hints(("Goal" :in-theory (enable revappend))))

(defthm forcing-revappend-removal
   (implies (force (true-listp y))
            (equal (revappend x y)
                   (app (rev x) y)))
   :hints(("Goal" :in-theory (enable revappend))))




(defund fast-rev (x)
  ;; Compute (rev x)
  ;;
  ;; Performance.  We use revappend to perform the reversal.  This gives much
  ;; better performance than rev.  It's as much as 86% faster on even small
  ;; lists of 10 elements in both CMUCL and GCL, and rapidly becomes orders of
  ;; magnitude faster as the size of the list to reverse increases.
  (declare (xargs :guard t))
  (revappend x nil))

(defthm fast-rev-removal
  (equal (fast-rev x)
         (rev x))
  :hints(("Goal" :in-theory (enable fast-rev))))




(defund fast-app (x y)
  ;; Compute (app x y)
  ;;
  ;; Performance.  This is a faster version of app which operates by first
  ;; reversing x, then using revappend to join the lists.  It requires (* 2
  ;; (len x)) conses, compared to (+ (len x) (len y)) conses for app.  But, it
  ;; is also tail recursive, so no stack frames are needed and we can process
  ;; larger lists with it.  It's 9-43% faster than app in GCL, and 5-48% faster
  ;; in CMUCL, with the larger benefits on larger lists.
  (declare (xargs :guard (true-listp y)))
  (revappend (fast-rev x) y))

(defthm fast-app-removal
  (implies (force (true-listp y))
           (equal (fast-app x y)
                  (app x y)))
  :hints(("Goal" :in-theory (enable fast-app))))





(defund remove-all (a x)
  ;; Remove all occurrences of a from x.
  ;;
  ;; Performance.  The function is not tail recursive so it may overflow on
  ;; large inputs.  See fast-remove-all$ for a faster variant.
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal a (car x))
          (remove-all a (cdr x))
        (cons (car x) (remove-all a (cdr x))))
    nil))

(defthm remove-all-when-not-consp
  (implies (not (consp x))
           (equal (remove-all a x)
                  nil))
  :hints(("Goal" :in-theory (enable remove-all))))

(defthm remove-all-of-cons
  (equal (remove-all a (cons b x))
         (if (equal a b)
             (remove-all a x)
           (cons b (remove-all a x))))
  :hints(("Goal" :in-theory (enable remove-all))))

(defthm remove-all-of-list-fix
  (equal (remove-all a (list-fix x))
         (remove-all a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-remove-all
  (equal (true-listp (remove-all a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-remove-all
  (equal (memberp a (remove-all b x))
         (and (memberp a x)
              (not (equal a b))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-of-app
  (equal (remove-all a (app x y))
         (app (remove-all a x)
              (remove-all a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-remove-all
  (equal (rev (remove-all a x))
         (remove-all a (rev x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-remove-all-with-x
  (equal (subsetp (remove-all a x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-remove-all-with-remove-all
  (implies (subsetp x y)
           (equal (subsetp (remove-all a x)
                           (remove-all a y))
                  t))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (remove-all a x))
                                  (y (remove-all a y)))))))

(defthm subsetp-of-remove-all-when-subsetp
  (implies (subsetp x y)
           (subsetp (remove-all a x) y)))

(defthm remove-all-of-non-memberp
  (implies (not (memberp a x))
           (equal (remove-all a x)
                  (list-fix x)))
  :hints(("Goal" :in-theory (enable remove-all))))

(defthm remove-all-of-remove-all
  (equal (remove-all a (remove-all b x))
         (remove-all b (remove-all a x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-cons-and-remove-all-two
  (equal (subsetp x (cons a (remove-all a y)))
         (subsetp x (cons a y)))
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property
                           (x (cons a y))
                           (y (cons a (remove-all a y))))))))

(encapsulate
 ()
 (defthmd lemma-for-equal-of-len-of-remove-all-and-len
   (implies (memberp a x)
            (equal (< (len (remove-all a x)) (len x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm equal-of-len-of-remove-all-and-len
   (equal (equal (len (remove-all a x)) (len x))
          (not (memberp a x)))
   :hints(("Goal" :in-theory (enable lemma-for-equal-of-len-of-remove-all-and-len)))))




(defund fast-remove-all$ (a x acc)
  ;; Compute (app (rev (remove-all a x)) acc)
  ;;
  ;; Performance.  This is tail recursive but it returns the elements in
  ;; reverse order from remove-all.  It's consistently 16% faster in CMUCL for
  ;; most lists, and up to 37% faster on very long lists.  In GCL it's less
  ;; inconsistent, but it's usually around 8-30% faster.
  (declare (xargs :guard (true-listp acc)))
  (if (consp x)
      (if (equal a (car x))
          (fast-remove-all$ a (cdr x) acc)
        (fast-remove-all$ a (cdr x) (cons (car x) acc)))
    acc))

(defthmd fast-remove-all$-when-not-consp
  (implies (not (consp x))
           (equal (fast-remove-all$ a x acc)
                  acc))
  :hints(("Goal" :in-theory (enable fast-remove-all$))))

(defthmd fast-remove-all$-of-cons
  (equal (fast-remove-all$ a (cons b x) acc)
         (if (equal a b)
             (fast-remove-all$ a x acc)
           (fast-remove-all$ a x (cons b acc))))
  :hints(("Goal" :in-theory (enable fast-remove-all$))))

(defthm forcing-fast-remove-all$-removal
   (implies (force (true-listp acc))
            (equal (fast-remove-all$ a x acc)
                   (revappend (remove-all a x) acc)))
   :hints(("Goal" :in-theory (enable fast-remove-all$))))





(defund disjointp (x y)
  ;; Do x and y have no common members?
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (memberp (car x) y))
           (disjointp (cdr x) y))
    t))

(defthm disjointp-when-not-consp-one
  (implies (not (consp x))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :in-theory (enable disjointp))))

(defthm disjointp-of-cons-one
  (equal (disjointp (cons a x) y)
         (and (not (memberp a y))
              (disjointp x y)))
  :hints(("Goal" :in-theory (enable disjointp))))

(defthm booleanp-of-disjointp
  (equal (booleanp (disjointp x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-not-consp-two
  (implies (not (consp y))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-cons-two
  (equal (disjointp x (cons a y))
         (and (not (memberp a x))
              (disjointp x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm symmetry-of-disjointp
  (equal (disjointp x y)
         (disjointp y x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-list-fix-one
  (equal (disjointp (list-fix x) y)
         (disjointp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-list-fix-two
  (equal (disjointp x (list-fix y))
         (disjointp x y))
  :hints(("Goal"
          :in-theory (disable symmetry-of-disjointp)
          :use ((:instance symmetry-of-disjointp
                           (x x)
                           (y (list-fix y)))
                (:instance symmetry-of-disjointp
                           (x y)
                           (y x))))))

(defthm disjointp-of-singleton-one
  (equal (disjointp (list a) x)
         (not (memberp a x))))

(defthm disjointp-of-singleton-two
  (equal (disjointp x (list a))
         (not (memberp a x))))

(defthm disjointp-when-common-member-one
  (implies (and (memberp a x)
                (memberp a y))
           (equal (disjointp x y)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-common-member-two
  (implies (and (memberp a y)
                (memberp a x))
           (equal (disjointp x y)
                  nil)))

(defthm disjointp-of-app-two
  (equal (disjointp x (app y z))
         (and (disjointp x y)
              (disjointp x z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-app-one
  (equal (disjointp (app x y) z)
         (and (disjointp x z)
              (disjointp y z))))

(defthm disjointp-of-rev-two
  (equal (disjointp x (rev y))
         (disjointp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-rev-one
  (equal (disjointp (rev x) y)
         (disjointp x y)))

;; disjointp-when-subsetp-of-disjointp[-one,two,three,four]
;;
;; If we know (disjointp y z), then:
;;
;;   (subsetp x y) -> (disjointp x z) and (disjointp z x)
;;   (subsetp x z) -> (disjointp x y) and (disjointp y x)

(defthm disjointp-when-subsetp-of-disjointp-one
  (implies (and (disjointp y z)
                (subsetp x y))
           (equal (disjointp x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-subsetp-of-disjointp-two
  (implies (and (disjointp y z)
                (subsetp x y))
           (equal (disjointp z x)
                  t)))

(defthm disjointp-when-subsetp-of-disjointp-three
  (implies (and (disjointp y z)
                (subsetp x z))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-subsetp-of-disjointp-four
  (implies (and (disjointp y z)
                (subsetp x z))
           (equal (disjointp y x)
                  t)))

(defthm disjointp-when-subsetp-of-other-one
  (implies (subsetp x y)
           (equal (disjointp x y)
                  (not (consp x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-subsetp-of-other-two
  (implies (subsetp y x)
           (equal (disjointp x y)
                  (not (consp y))))
  :hints(("Goal" :induct (cdr-induction y))))

;; (thm (implies (disjointp x y) (disjointp x (remove-all a y))))
;; (thm (implies (disjointp x y) (disjointp (remove-all a x) y)))
;; (thm (implies (disjointp x y) (disjointp x (cdr y))))
;; (thm (implies (disjointp x y) (disjointp (cdr x) y)))
;; (thm (implies (disjointp x y) (disjointp (cdr x) (cdr y))))

(defthm disjointp-of-remove-all-of-remove-all-when-disjointp-right
  (implies (disjointp x y)
           (equal (disjointp x (remove-all a (remove-all b y)))
                  t)))

(defthm disjointp-of-remove-all-when-disjointp-left
  (implies (disjointp x y)
           (equal (disjointp (remove-all a x) y)
                  t)))

(defthm memberp-when-disjointp-one
  (implies (and (disjointp x y)
                (memberp a x))
           (equal (memberp a y)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-when-disjointp-two
  (implies (and (disjointp x y)
                (memberp a y))
           (equal (memberp a x)
                  nil)))





(defund uniquep (x)
  ;; Is x free from recurring elements?
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (memberp (car x) (cdr x)))
           (uniquep (cdr x)))
    t))

(defthm uniquep-when-not-consp
  (implies (not (consp x))
           (equal (uniquep x)
                  t))
  :hints(("Goal" :in-theory (enable uniquep))))

(defthm uniquep-of-cons
  (equal (uniquep (cons a x))
         (and (not (memberp a x))
              (uniquep x)))
  :hints(("Goal" :in-theory (enable uniquep))))

(defthm uniquep-of-list-fix
  (equal (uniquep (list-fix x))
         (uniquep x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-uniquep
  (equal (booleanp (uniquep x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-cdr-when-uniquep
  (implies (uniquep x)
           (equal (uniquep (cdr x))
                  t)))

(defthm memberp-of-car-in-cdr-when-uniquep
  (implies (uniquep x)
           (equal (memberp (car x) (cdr x))
                  nil)))

(defthm uniquep-of-app
  (equal (uniquep (app x y))
         (and (uniquep x)
              (uniquep y)
              (disjointp x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-rev
  (equal (uniquep (rev x))
         (uniquep x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-remove-all-when-uniquep
  (implies (uniquep x)
           (uniquep (remove-all a x)))
  :hints(("Goal" :induct (cdr-induction x))))




(defund difference (x y)
  ;; Collect the members of x which aren't in y.
  ;;
  ;; This function is not tail recursive so it may overflow for large inputs.
  ;; See also fast-difference$ for a tail recursive alternative.
  (declare (xargs :guard t))
  (if (consp x)
      (if (memberp (car x) y)
          (difference (cdr x) y)
        (cons (car x)
              (difference (cdr x) y)))
    nil))

(defthm difference-when-not-consp
  (implies (not (consp x))
           (equal (difference x y)
                  nil))
  :hints(("Goal" :in-theory (enable difference))))

(defthm difference-of-cons
  (equal (difference (cons a x) y)
         (if (memberp a y)
             (difference x y)
           (cons a (difference x y))))
  :hints(("Goal" :in-theory (enable difference))))

(defthm true-listp-of-difference
  (equal (true-listp (difference x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm difference-of-list-fix-one
  (equal (difference (list-fix x) y)
         (difference x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm difference-of-list-fix-two
  (equal (difference x (list-fix y))
         (difference x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm difference-of-app-one
  (equal (difference (app x y) z)
         (app (difference x z)
              (difference y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm difference-of-difference
  (equal (difference (difference x y) z)
         (difference x (app y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-difference
  (equal (rev (difference x y))
         (difference (rev x) y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd difference-of-rev
  (equal (difference (rev x) y)
         (rev (difference x y))))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite difference-of-rev) (:rewrite rev-of-difference)))

(defthm difference-of-rev-two
  (equal (difference x (rev y))
         (difference x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-difference
  (equal (memberp a (difference x y))
         (and (memberp a x)
              (not (memberp a y))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-difference-when-uniquep
  (implies (uniquep x)
           (uniquep (difference x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-difference-with-y
  (equal (disjointp (difference x y) y)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-difference-with-y-alt
  (equal (disjointp y (difference x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm difference-when-subsetp
  (implies (subsetp x y)
           (equal (difference x y)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-with-app-of-difference-onto-takeaway
  (equal (subsetp x (app (difference x y) y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))




(defund fast-difference$ (x y acc)
  ;; Compute (app (rev (difference x y)) acc)
  ;;
  ;; BOZO how much faster is this function?  Is it faster?
  (declare (xargs :guard (true-listp acc)))
  (if (consp x)
      (if (memberp (car x) y)
          (fast-difference$ (cdr x) y acc)
        (fast-difference$ (cdr x) y (cons (car x) acc)))
    acc))

(defthmd fast-difference$-when-not-consp
  (implies (not (consp x))
           (equal (fast-difference$ x y acc)
                  acc))
  :hints(("Goal" :in-theory (enable fast-difference$))))

(defthmd fast-difference$-of-cons
  (equal (fast-difference$ (cons a x) y acc)
         (if (memberp a y)
             (fast-difference$ x y acc)
           (fast-difference$ x y (cons a acc))))
  :hints(("Goal" :in-theory (enable fast-difference$))))

(defthm forcing-fast-difference$-removal
  (implies (force (true-listp acc))
           (equal (fast-difference$ x y acc)
                  (revappend (difference x y)
                             acc)))
  :hints(("Goal" :in-theory (enable fast-difference$))))




(defund remove-duplicates (x)
  ;; Collect the distinct members of x.
  ;;
  ;; Performance.  We looked at writing a fast-remove-duplicates$, but found
  ;; that the benefits of tail recursion were overwhelmed by the consing and
  ;; time spent in memberp.  If you need a faster function, consider ordered
  ;; insertion or sorting.
  (declare (xargs :guard t))
  (if (consp x)
      (if (memberp (car x) (cdr x))
          (remove-duplicates (cdr x))
        (cons (car x) (remove-duplicates (cdr x))))
    nil))

(defthm remove-duplicates-when-not-consp
  (implies (not (consp x))
           (equal (remove-duplicates x)
                  nil))
  :hints(("Goal" :in-theory (enable remove-duplicates))))

(defthm remove-duplicates-of-cons
  (equal (remove-duplicates (cons a x))
         (if (memberp a x)
             (remove-duplicates x)
           (cons a (remove-duplicates x))))
  :hints(("Goal" :in-theory (enable remove-duplicates))))

(defthm true-listp-of-remove-duplicates
  (equal (true-listp (remove-duplicates x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-remove-duplicates
  (equal (< (len x) (len (remove-duplicates x)))
         nil)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-duplicates-of-list-fix
  (equal (remove-duplicates (list-fix x))
         (remove-duplicates x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-remove-duplicates
  (equal (memberp a (remove-duplicates x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-remove-duplicates
  (equal (uniquep (remove-duplicates x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-duplicates-of-difference
  (equal (remove-duplicates (difference x y))
         (difference (remove-duplicates x) y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-duplicates-when-unique
  (implies (uniquep x)
           (equal (remove-duplicates x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-remove-duplicates-one
  (equal (subsetp (remove-duplicates x) y)
         (subsetp x y))
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property (x (remove-duplicates x)) (y x))
                (:instance subsetp-badguy-membership-property (x x) (y (remove-duplicates x)))))))

(defthm subsetp-of-remove-duplicates-two
  (equal (subsetp x (remove-duplicates y))
         (subsetp x y))
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property (x (remove-duplicates y)) (y y))
                (:instance subsetp-badguy-membership-property (x y) (y (remove-duplicates y)))))))

(defthm app-of-remove-duplicates-with-unique-and-disjoint
  (implies (and (uniquep y)
                (disjointp x y))
           (equal (remove-duplicates (app x y))
                  (app (remove-duplicates x) y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-duplicates-of-remove-all
  (equal (remove-duplicates (remove-all a x))
         (remove-all a (remove-duplicates x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-cons-onto-remove-duplicates
  (equal (subsetp x (cons a (remove-duplicates y)))
         (subsetp x (cons a y))))

(defthm subsetp-of-remove-all-of-remove-duplicates
  (equal (subsetp (remove-all a (remove-duplicates x)) y)
         (subsetp (remove-all a x) y)))



(defund tuplep (n x)
  ;; Is x a proper n-tuple?
  ;;
  ;; That is, we check to see if x is a true-listp whose length is n.  This has
  ;; a certain performance advantage over testing both separately; we only do
  ;; one pass over the structure and we have to recur at most n times.
  ;;
  ;; BOZO consider rewriting tuplep into (and (true-listp x) (equal (len x) n))
  ;; and getting rid of all these rules.
  (declare (xargs :guard (natp n)
                  :measure (nfix n)))
  (if (zp n)
      (equal x nil)
    (and (consp x)
         (tuplep (- n 1) (cdr x)))))

(defthm tuplep-when-not-consp
  (implies (not (consp x))
           (equal (tuplep n x)
                  (and (zp n)
                       (not x))))
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm tuplep-when-zp
  (implies (zp n)
           (equal (tuplep n x)
                  (equal x nil)))
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm tuplep-of-cons
  (equal (tuplep n (cons a x))
         (and (< 0 n)
              (tuplep (- n 1) x)))
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm booleanp-of-tuplep
  (equal (booleanp (tuplep n x))
         t)
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm true-listp-when-tuplep
  (implies (tuplep n x)
           (equal (true-listp x)
                  t))
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm len-when-tuplep
  (implies (tuplep n x)
           (equal (len x)
                  (nfix n)))
  :hints(("Goal" :in-theory (enable tuplep))))

(defthm tuplep-when-true-listp
  (implies (true-listp x)
           (equal (tuplep n x)
                  (equal (len x) (nfix n))))
  :hints(("Goal"
          :in-theory (enable tuplep)
          :induct (tuplep n x))))

(defthm consp-of-cdr-when-tuplep-2-cheap
  (implies (tuplep 2 x)
           (equal (consp (cdr x))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm consp-of-cdr-when-tuplep-3-cheap
  (implies (tuplep 3 x)
           (equal (consp (cdr x))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm consp-of-cdr-of-cdr-when-tuplep-3-cheap
  (implies (tuplep 3 x)
           (equal (consp (cdr (cdr x)))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))



(defund repeat (a n)
  ;; Create n copies of a in a list.
  ;;
  ;; Performance.  This is not tail recursive and requires n conses.  You
  ;; should typically not need to call repeat, but it is sometimes useful for
  ;; stating theorems.
  (declare (xargs :guard (natp n)
                  :measure (nfix n)))
  (if (zp n)
      nil
    (cons a (repeat a (- n 1)))))

(defthm repeat-of-zero
  (equal (repeat a 0)
         nil)
  :hints(("Goal" :expand (repeat a 0))))

(defthm repeat-of-one
  (equal (repeat a 1)
         (list a))
  :hints(("Goal" :expand (repeat a 1))))

(defthm consp-of-repeat
  (equal (consp (repeat a n))
         (not (zp n)))
  :hints(("Goal" :expand (repeat a n))))

(defthm repeat-under-iff
  (iff (repeat a n)
       (not (zp n)))
  :hints(("Goal" :expand (repeat a n))))

(defthm car-of-repeat
  (equal (car (repeat a n))
         (if (zp n)
             nil
           a))
  :hints(("Goal" :expand (repeat a n))))

(defthm cdr-of-repeat
  (equal (cdr (repeat a n))
         (if (zp n)
             nil
           (repeat a (- n 1))))
  :hints(("Goal" :expand (repeat a n))))

(defthm repeat-of-nfix
  (equal (repeat a (nfix n))
         (repeat a n))
  :hints(("Goal"
          :expand (repeat a (nfix n))
          :induct (dec-induction n))))

(defthm len-of-repeat
  (equal (len (repeat a n))
         (nfix n))
  :hints(("Goal"
          :expand (repeat a n)
          :induct (dec-induction n))))

(defthm true-listp-of-repeat
  (equal (true-listp (repeat a n))
         t)
  :hints(("Goal"
          :expand (repeat a n)
          :induct (dec-induction n))))

(defthm memberp-of-repeat
  (equal (memberp a (repeat b n))
         (and (< 0 (nfix n))
              (equal a b)))
  :hints(("Goal"
          :expand (repeat b n)
          :induct (dec-induction n))))

(defthm app-of-repeat
  (equal (app (repeat a n1)
              (repeat a n2))
         (repeat a (+ n1 n2)))
  :hints(("Goal"
          :expand ((repeat a n1)
                   (repeat a n2))
          :induct (dec-induction n1))))

(encapsulate
 ()
 (defthmd lemma-for-rev-of-repeat
   (implies (not (zp n))
            (equal (app (repeat a (- n 1)) (list a))
                   (repeat a n)))
   :hints(("Goal"
           :in-theory (enable repeat)
           :induct (dec-induction n))))

 (defthm rev-of-repeat
   (equal (rev (repeat a n))
          (repeat a n))
   :hints(("Goal"
           :expand (repeat a n)
           :induct (dec-induction n)
           :in-theory (enable lemma-for-rev-of-repeat)))))




(defund nth (n x)
  ;; Retrieve the nth element of a list
  (declare (xargs :guard (natp n)
                  :measure (rank x)))
  (if (consp x)
      (if (zp n)
          (car x)
        (nth (- n 1) (cdr x)))
    nil))

(defthm nth-when-zp
  (implies (zp n)
           (equal (nth n x)
                  (car x)))
  :hints(("Goal" :expand (nth n x))))

(defthm nth-of-nfix
  (equal (nth (nfix n) x)
         (nth n x))
  :hints(("Goal" :expand ((nth (nfix n) x)
                          (nth n x)))))

(defthm nth-of-list-fix
  (equal (nth n (list-fix x))
         (nth n x))
  :hints(("Goal" :in-theory (enable nth))))

(defthm nth-when-index-too-large
  ;; BOZO consider removing this backchain limit.  We added it because the
  ;; rule was expensive in Milawa's rewriter, before it had a cache.  Now it
  ;; may be less expensive.
  (implies (not (< n (len x)))
           (equal (nth n x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable nth))))

(defthm nth-of-increment
  (equal (nth (+ 1 n) x)
         (nth n (cdr x)))
  :hints(("Goal" :in-theory (enable nth))))

(defthm nth-of-app
  (equal (nth n (app x y))
         (if (< n (len x))
             (nth n x)
           (nth (- n (len x)) y)))
  :hints(("Goal"
          :in-theory (enable nth)
          :induct (nth n x))))

(defthm nth-of-rev
  (equal (nth n (rev x))
         (if (< n (len x))
             (nth (- (len x) (+ 1 n)) x)
           nil))
  :hints(("Goal"
          :in-theory (enable nth)
          :induct (cdr-induction x))))

(defthm memberp-of-nth
  (implies (< n (len x))
           (equal (memberp (nth n x) x)
                  t))
  :hints(("Goal" :in-theory (enable nth))))

(encapsulate
 ()
 (local (defun my-induction (m n vars)
          (declare (xargs :measure (rank vars)
                          :verify-guards nil
                          :export nil))
          (if (consp vars)
              (if (or (zp m)
                      (zp n))
                  nil
                (my-induction (- m 1) (- n 1) (cdr vars)))
            nil)))

 (local (defthm lemma
          (implies (and (memberp (nth m vars) vars)
                        (not (memberp (nth m vars) (cdr vars))))
                   (equal (nth m vars)
                          (car vars)))))

 (local (defthm lemma2
          (implies (and (not (memberp (nth m vars) (cdr vars)))
                        (consp vars))
                   (equal (< m (len vars))
                          (zp m)))
          :hints(("Goal" :in-theory (enable nth)))))

 (defthm equal-of-nths-when-uniquep
   (implies (and (uniquep x)
                 (< n (len x))
                 (< m (len x)))
            (equal (equal (nth n x) (nth m x))
                   (equal (nfix m) (nfix n))))
   :hints(("Goal"
           :in-theory (enable nth)
           :induct (my-induction n m x)))))




(defund prefixp (x y)
  ;; Do x and y agree on their elements up until x ends?
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(defthm prefixp-when-not-consp-one
  (implies (not (consp x))
           (equal (prefixp x y)
                  t))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-when-not-consp-two
  (implies (not (consp y))
           (equal (prefixp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-cons-and-cons
  (equal (prefixp (cons a x) (cons b y))
         (and (equal a b)
              (prefixp x y)))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm booleanp-of-prefixp
  (equal (booleanp (prefixp x y))
         t)
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-list-fix-one
  (equal (prefixp (list-fix x) y)
         (prefixp x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm prefixp-of-list-fix-two
  (equal (prefixp x (list-fix y))
         (prefixp x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm same-length-prefixes-equal-cheap
  ;; I tried this rule with no backchain limit for some time, but it was really
  ;; slow in some cases.  A backchain limit of 0 is too restrictive and was
  ;; causing some rules to fail, so without much thought I changed it to 1.
  (implies (and (prefixp x y)
                (true-listp x)
                (true-listp y))
           (equal (equal x y)
                  (equal (len x) (len y))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm prefixp-when-lengths-wrong
  (implies (< (len y) (len x))
           (equal (prefixp x y)
                  nil))
  :hints(("Goal" :in-theory (enable prefixp))))

(defund prefixp-badguy (x y)
  ;; We search for the index of the first location where x and y differ, i.e.,
  ;; the first element which violates prefixp.
  (declare (xargs :guard (<= (len x) (len y))))
  (if (consp x)
      (if (equal (car x) (car y))
          (let ((index (prefixp-badguy (cdr x) (cdr y))))
            (if index
                (+ 1 index)
              nil))
        0)
    nil))

(defthmd prefixp-badguy-when-not-consp
  (implies (not (consp x))
           (equal (prefixp-badguy x y)
                  nil))
  :hints(("Goal" :in-theory (enable prefixp-badguy))))

(defthmd prefixp-badguy-of-cons
  (equal (prefixp-badguy (cons a x) y)
         (if (equal a (car y))
             (let ((index (prefixp-badguy x (cdr y))))
               (if index
                   (+ 1 index)
                 nil))
           0))
  :hints(("Goal" :in-theory (enable prefixp-badguy))))

(defthm natp-of-prefixp-badguy
  (equal (natp (prefixp-badguy x y))
         (if (prefixp-badguy x y)
             t
           nil))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable prefixp-badguy-when-not-consp prefixp-badguy-of-cons))))

(encapsulate
 ()
 (defthm lemma-for-prefixp-badguy-index-property
   (implies (natp (prefixp-badguy x y))
            (equal (< (prefixp-badguy x y) (len x))
                   t))
   :hints(("Goal" :in-theory (enable prefixp-badguy))))

 (defthm lemma-2-for-prefixp-badguy-index-property
   (implies (natp (prefixp-badguy x y))
            (not (equal (nth (prefixp-badguy x y) x)
                        (nth (prefixp-badguy x y) y))))
   :hints(("Goal" :in-theory (enable prefixp-badguy))))

 (defthm prefixp-badguy-index-property
   (implies (natp (prefixp-badguy x y))
            (and (equal (< (prefixp-badguy x y) 0)
                        nil)
                 (equal (< (prefixp-badguy x y) (len x))
                        t)
                 (not (equal (nth (prefixp-badguy x y) x)
                             (nth (prefixp-badguy x y) y)))))
   :rule-classes nil))

(defthm forcing-prefixp-when-not-prefixp-badguy
  (implies (and (not (prefixp-badguy x y))
                (force (not (< (len y) (len x)))))
           (equal (prefixp x y)
                  t))
  :hints(("Goal" :in-theory (enable prefixp-badguy))))

(defthm subsetp-when-prefixp-cheap
  (implies (prefixp x y)
           (equal (subsetp x y)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))




(defund firstn (n x)
  ;; Extract the first n elements from x.
  ;;
  ;; We stop early if we run out of elements to extract, so that the firstn of
  ;; x are always a prefix of x.
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      nil
    (if (not (consp x))
        nil
      (cons (car x) (firstn (- n 1) (cdr x))))))

(defthm firstn-of-zero
  (equal (firstn 0 x)
         nil)
  :hints(("Goal" :in-theory (enable firstn))))

(defthm true-listp-of-firstn
  (equal (true-listp (firstn n x))
         t)
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm consp-of-firstn
  (equal (consp (firstn n x))
         (and (< 0 n)
              (consp x)))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm firstn-under-iff
  (iff (firstn n x)
       (and (< 0 n)
            (consp x)))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm firstn-of-list-fix
  (equal (firstn n (list-fix x))
         (firstn n x))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm firstn-of-len
  (equal (firstn (len x) x)
         (list-fix x))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (cdr-induction x))))

(defthm len-of-firstn
  (equal (len (firstn n x))
         (min n (len x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm firstn-of-too-many
  (implies (< (len x) n)
           (equal (firstn n x)
                  (list-fix x)))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm firstn-of-app
  (equal (firstn n (app x y))
         (if (< (len x) n)
             (app x (firstn (- n (len x)) y))
           (firstn n x)))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm prefixp-of-firstn
  (equal (prefixp (firstn n x) x)
         t)
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm prefixp-of-firstn-unusual
  (equal (prefixp x (firstn n x))
         (not (< n (len x))))
  :hints(("Goal"
          :in-theory (enable firstn)
          :induct (firstn n x))))

(defthm subsetp-of-firstn-when-in-range
  (equal (subsetp (firstn n x) x)
         t))




(defund restn (n x)
  ;; Skip the first n elements of x and return the remaining elements.
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      (list-fix x)
    (restn (- n 1) (cdr x))))

(defthm restn-of-zero
  (equal (restn 0 x)
         (list-fix x))
  :hints(("Goal" :in-theory (enable restn))))

(defthm restn-of-one
  (equal (restn 1 x)
         (list-fix (cdr x)))
  :hints(("Goal" :in-theory (enable restn))))

(defthm true-listp-of-restn
  (equal (true-listp (restn n x))
         t)
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm consp-of-restn
  (equal (consp (restn n x))
         (< n (len x)))
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm restn-under-iff
  (iff (restn n x)
       (< n (len x)))
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm restn-of-list-fix
  (equal (restn n (list-fix x))
         (restn n x))
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm restn-when-not-natp
  (implies (not (natp n))
           (equal (restn n x)
                  (list-fix x)))
  :hints(("Goal" :in-theory (enable restn))))

(defthm restn-of-app
  (equal (restn n (app x y))
         (if (< (len x) n)
             (restn (- n (len x)) y)
           (app (restn n x) y)))
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm app-of-firstn-and-restn
  (equal (app (firstn n x) (restn n x))
         (if (< n (len x))
             (list-fix x)
           (firstn n x)))
  :hints(("Goal"
          :in-theory (enable firstn restn)
          :induct (firstn n x))))

(defthm subsetp-of-restn
  (equal (subsetp (restn n x) x)
         t)
  :hints(("Goal"
          :in-theory (enable restn)
          :induct (restn n x))))

(defthm restn-of-len
   (equal (restn (len x) x)
          nil))

(encapsulate
 ()
 (defthmd lemma-for-equal-of-app-with-firstn-and-restn
   (implies (< n (len x))
            (equal (app (firstn n x) (restn n x))
                   (list-fix x))))

 (defthmd lemma-2-for-equal-of-app-with-firstn-and-restn
   (implies (equal (firstn n x) y)
            (equal (< (len x) (len y))
                   nil))
   :hints(("Goal" :in-theory (enable firstn))))

 (defthmd lemma-3-for-equal-of-app-with-firstn-and-restn
   (implies (not (< (len x) (len y)))
            (equal (< (len y) (len x))
                   (not (equal (len x) (len y))))))

 (defthmd lemma-4-for-equal-of-app-with-firstn-and-restn
   (implies (and (equal (firstn (len y) x) (list-fix y))
                 (equal (restn (len y) x) (list-fix z))
                 (true-listp x))
            (equal (equal x (app y z))
                   t))
   :hints(("Goal"
           :in-theory (enable lemma-3-for-equal-of-app-with-firstn-and-restn)
           :use ((:instance lemma-for-equal-of-app-with-firstn-and-restn
                            (n (len y))
                            (x x))
                 (:instance lemma-2-for-equal-of-app-with-firstn-and-restn
                            (n (len y))
                            (y (list-fix y)))))))

 (defthmd equal-of-app-with-firstn-and-restn
   (equal (equal x (app y z))
          (and (true-listp x)
               (equal (firstn (len y) x) (list-fix y))
               (equal (restn (len y) x) (list-fix z))))
   :hints(("Goal" :use ((:instance lemma-4-for-equal-of-app-with-firstn-and-restn))))))




(defund first-index (a x)
  ;; We return the smallest index of x which contains element a, or len(x) if
  ;; no such index exists.
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) a)
          0
        (+ 1 (first-index a (cdr x))))
    0))

(defthm first-index-when-not-consp
  (implies (not (consp x))
           (equal (first-index a x)
                  0))
  :hints(("Goal" :in-theory (enable first-index))))

(defthm first-index-of-cons
  (equal (first-index a (cons b x))
         (if (equal a b)
             0
           (+ 1 (first-index a x))))
  :hints(("Goal" :in-theory (enable first-index))))

(defthm natp-of-first-index
  (equal (natp (first-index a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-of-list-fix
  (equal (first-index a (list-fix x))
         (first-index a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-binds-first-index-range
  (implies (memberp a x)
           (equal (< (first-index a x) (len x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-of-app
  (equal (first-index a (app x y))
         (if (memberp a x)
             (first-index a x)
           (+ (len x) (first-index a y))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-of-rev-when-unique
  (implies (and (uniquep x)
                (memberp a x))
           (equal (first-index a (rev x))
                  (- (len x) (+ 1 (first-index a x)))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-of-car
  (equal (first-index (car x) x)
         0))

(defthm nth-of-first-index-when-memberp
  (implies (memberp a x)
           (equal (nth (first-index a x) x)
                  a))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-less-than-len
  (equal (< (first-index a x) (len x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-less-than-len-free
  (implies (and (equal (len x) n)
                (memberp a x))
           (equal (< (first-index a x) n)
                  t)))

(defthm nth-of-first-index-of-nth
  (implies (< n (len x))
           (equal (nth (first-index (nth n x) x) x)
                  (nth n x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm first-index-of-nth-when-unique
  (implies (and (uniquep x)
                (< n (len x)))
           (equal (first-index (nth n x) x)
                  (nfix n)))
  :hints(("Goal"
          :use ((:instance equal-of-nths-when-uniquep
                           (n (first-index (nth n x) x))
                           (m n)
                           (x x))))))

(defthm equal-of-first-index-and-n-when-len
  ;; BOZO it seems weird that this rule would ever fire.  Don't we want to
  ;; reorder the n and the first-index?  Or, I guess, we might want to have
  ;; both rules, since I suppose n could be some big expression instead of
  ;; just a constant.
  (implies (equal (len x) n)
           (equal (equal (first-index a x) n)
                  (not (memberp a x))))
  :hints(("Goal" :in-theory (enable first-index))))





(defund mapp (x)
  ;; Is x a list of (key . value) pairs?
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (mapp (cdr x)))
    t))

(defthm mapp-when-not-consp
  (implies (not (consp x))
           (equal (mapp x)
                  t))
  :hints(("Goal" :in-theory (enable mapp))))

(defthm mapp-of-cons
  (equal (mapp (cons a x))
         (and (consp a)
              (mapp x)))
  :hints(("Goal" :in-theory (enable mapp))))

(defthm mapp-of-list-fix
  (equal (mapp (list-fix x))
         (mapp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-mapp
  (equal (booleanp (mapp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-app
  (equal (mapp (app x y))
         (and (mapp x)
              (mapp y)))
  :hints(("Goal" :induct (cdr-induction x))))




(defund cons-fix (x)
  ;; Compute (cons (car x) (cdr x))
  (declare (xargs :guard t))
  (if (consp x)
      x
    (cons nil nil)))

(defthm cons-fix-when-not-consp
  (implies (not (consp x))
           (equal (cons-fix x)
                  (cons nil nil)))
  :hints(("Goal" :in-theory (enable cons-fix))))

(defthm cons-fix-when-consp
  (implies (consp x)
           (equal (cons-fix x)
                  x))
  :hints(("Goal" :in-theory (enable cons-fix))))

(defthm consp-of-cons-fix
  (equal (consp (cons-fix x))
         t)
  :hints(("Goal" :cases ((consp x)))))

(defthm cons-fix-under-iff
  (iff (cons-fix x)
       t)
  :hints(("Goal" :cases ((consp x)))))

(defthm cons-fix-of-cons
  (equal (cons-fix (cons x y))
         (cons x y)))

(defthm car-of-cons-fix
  (equal (car (cons-fix x))
         (car x)))

(defthm cdr-of-cons-fix
  (equal (cdr (cons-fix x))
         (cdr x)))




(defund lookup (a x)
  ;; Find the first pair of the form (a . b) in the map x
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (if (equal a (car (car x)))
          (if (consp (car x))
              (car x)
            (cons (car (car x))
                  (cdr (car x))))
        (lookup a (cdr x)))
    nil))

(defthm lookup-when-not-consp
  (implies (not (consp x))
           (equal (lookup a x)
                  nil))
  :hints(("Goal" :in-theory (enable lookup))))

(defthm lookup-of-cons
  (equal (lookup a (cons b x))
         (if (equal a (car b))
             (cons-fix b)
           (lookup a x)))
  :hints(("Goal" :in-theory (enable lookup))))

(defthm lookup-of-list-fix
  (equal (lookup a (list-fix x))
         (lookup a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm lookup-of-app
  (equal (lookup a (app x y))
         (if (lookup a x)
             (lookup a x)
           (lookup a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm car-of-lookup-when-found
  (implies (lookup key map)
           (equal (car (lookup key map))
                  key))
  :hints(("Goal" :induct (cdr-induction map))))

(defthm consp-of-lookup-under-iff
  (iff (consp (lookup a x))
       (lookup a x))
  :hints(("Goal" :induct (cdr-induction x))))




(defund update (key val map)
  ;; Update the map with (key . val)
  (declare (xargs :guard (mapp map)))
  (cons (cons key val)
        (list-fix map)))

(defthm car-of-update
  (equal (car (update key val map))
         (cons key val))
  :hints(("Goal" :in-theory (enable update))))

(defthm cdr-of-update
  (equal (cdr (update key val map))
         (list-fix map))
  :hints(("Goal" :in-theory (enable update))))

(defthm consp-of-update
  (equal (consp (update key val map))
         t)
  :hints(("Goal" :in-theory (enable update))))

(defthm update-of-list-fix
  (equal (update key val (list-fix map))
         (update key val map))
  :hints(("Goal" :in-theory (enable update))))

(defthm mapp-of-update-when-mapp
  (implies (mapp map)
           (equal (mapp (update key val map))
                  t))
  :hints(("Goal" :in-theory (enable update))))

(defthm lookup-of-update
  (equal (lookup a (update b val map))
         (if (equal a b)
             (cons a val)
           (lookup a map)))
  :hints(("Goal" :in-theory (enable update))))




(defund domain (x)
  ;; List all the keys in a map.
  ;;
  ;; Performance.  This function isn't tail recursive and it might overflow
  ;; on large lists.  See also fast-domain$ for an alternative.
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (car (car x))
            (domain (cdr x)))
    nil))

(defthm domain-when-not-consp
  (implies (not (consp x))
           (equal (domain x)
                  nil))
  :hints(("Goal" :in-theory (enable domain))))

(defthm domain-of-cons
  (equal (domain (cons a x))
         (cons (car a) (domain x)))
  :hints(("Goal" :in-theory (enable domain))))

(defthm domain-of-list-fix
  (equal (domain (list-fix x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-domain
  (equal (consp (domain x))
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-domain
  (equal (true-listp (domain x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-app
  (equal (domain (app x y))
         (app (domain x)
              (domain y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-update
  (equal (domain (update a x map))
         (cons a (domain map)))
  :hints(("Goal" :in-theory (enable update))))

(defthm memberp-of-domain-when-memberp
  (implies (memberp a x)
           (equal (memberp (car a) (domain x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-domain-when-memberp-of-subset-domain
  (implies (and (memberp a (domain x))
                (subsetp x y))
           (equal (memberp a (domain y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-domains
  (implies (subsetp x y)
           (equal (subsetp (domain x) (domain y))
                  t))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (domain x))
                                  (y (domain y)))))))

(defthm uniquep-when-uniquep-of-domain
  (implies (uniquep (domain x))
           (equal (uniquep x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-domain-under-iff
  (iff (memberp a (domain x))
       (lookup a x))
  :hints(("Goal" :in-theory (enable lookup))))

(defthm rev-of-domain
  (equal (rev (domain x))
         (domain (rev x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd domain-of-rev
  (equal (domain (rev x))
         (rev (domain x))))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite domain-of-rev) (:rewrite rev-of-domain)))



(defund fast-domain$ (x acc)
  ;; Compute (app (rev (domain x)) acc)
  ;;
  ;; Performance.  This is tail recursive and was as up to 40-44% faster than
  ;; domain on GCL for lists of length 100-10000.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-domain$ (cdr x) (cons (car (car x)) acc))
    acc))

(defthmd fast-domain$-when-not-consp
  (implies (not (consp x))
           (equal (fast-domain$ x acc)
                  acc))
  :hints(("Goal" :in-theory (enable fast-domain$))))

(defthmd fast-domain$-of-cons
  (equal (fast-domain$ (cons a x) acc)
         (fast-domain$ x (cons (car a) acc)))
  :hints(("Goal" :in-theory (enable fast-domain$))))

(defthm forcing-fast-domain$-removal
  (implies (force (true-listp acc))
           (equal (fast-domain$ x acc)
                  (revappend (domain x) acc)))
  :hints(("Goal" :in-theory (enable fast-domain$))))




(defund range (x)
  ;; List all the values in a map.
  ;;
  ;; Performance.  This function isn't tail recursive and it might overflow on
  ;; large lists.  See also fast-domain$ for an alternative.
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cdr (car x))
            (range (cdr x)))
    nil))

(defthm range-when-not-consp
  (implies (not (consp x))
           (equal (range x)
                  nil))
  :hints(("Goal" :in-theory (enable range))))

(defthm range-of-cons
  (equal (range (cons a x))
         (cons (cdr a) (range x)))
  :hints(("Goal" :in-theory (enable range))))

(defthm range-of-list-fix
  (equal (range (list-fix x))
         (range x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-range
  (equal (true-listp (range x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-range
  (equal (len (range x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm range-of-app
  (equal (range (app x y))
         (app (range x)
              (range y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm nth-of-first-index-of-domain-and-range
  (equal (nth (first-index a (domain x)) (range x))
         (cdr (lookup a x)))
  :hints(("Goal"
          :in-theory (enable first-index)
          :induct (cdr-induction x))))


(defund fast-range$ (x acc)
  ;; Compute (app (rev (range x)) acc)
  ;;
  ;; Performance.  This is tail recursive and was up to 32-41% faster than
  ;; range on GCL for lists of length 100-10000.  I'm not sure why these
  ;; numbers are different than fast-domain$'s, since they're almost identical
  ;; functions.  Whatever.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-range$ (cdr x) (cons (cdr (car x)) acc))
    acc))

(defthmd fast-range$-when-not-consp
  (implies (not (consp x))
           (equal (fast-range$ x acc)
                  acc))
  :hints(("Goal" :in-theory (enable fast-range$))))

(defthmd fast-range$-of-cons
  (equal (fast-range$ (cons a x) acc)
         (fast-range$ x (cons (cdr a) acc)))
  :hints(("Goal" :in-theory (enable fast-range$))))

(defthm forcing-fast-range$-removal
  (implies (force (true-listp acc))
           (equal (fast-range$ x acc)
                  (revappend (range x) acc)))
  :hints(("Goal" :in-theory (enable fast-range$))))




(defund submapp1 (domain x y)
  ;; Do x and y agree on the values for all keys in domain?
  (declare (xargs :guard (and (mapp x) (mapp y))))
  (if (consp domain)
      (and (equal (lookup (car domain) x)
                  (lookup (car domain) y))
           (submapp1 (cdr domain) x y))
    t))

(defthm submapp1-when-not-consp
  (implies (not (consp domain))
           (equal (submapp1 domain x y)
                  t))
  :hints(("Goal" :in-theory (enable submapp1))))

(defthm submapp1-of-cons
  (equal (submapp1 (cons a domain) x y)
         (and (equal (lookup a x) (lookup a y))
              (submapp1 domain x y)))
  :hints(("Goal" :in-theory (enable submapp1))))

(defthm booleanp-of-submapp1
  (equal (booleanp (submapp1 domain x y))
         t)
  :hints(("Goal" :induct (cdr-induction domain))))

(defthm equal-of-lookups-when-memberp-of-submapp1-domain
  (implies (and (submapp1 domain x y)
                (memberp a domain))
           (equal (equal (lookup a x)
                         (lookup a y))
                  t))
  :hints(("Goal" :induct (cdr-induction domain))))

(defthm lookup-when-memberp-of-submapp1
  (implies (and (submapp1 domain x y)
                (memberp a domain)
                (lookup a x))
           (iff (lookup a y)
                t))
  :hints(("Goal" :induct (cdr-induction domain))))




(defund submapp1-badguy (domain x y)
  ;; Find the first key in domain for which x and y do not agree.
  (declare (xargs :guard (and (mapp x) (mapp y))))
  (if (consp domain)
      (if (not (equal (lookup (car domain) x)
                      (lookup (car domain) y)))
          (cons t (car domain))
        (submapp1-badguy (cdr domain) x y))
    nil))

(defthmd submapp1-badguy-when-not-consp
  (implies (not (consp domain))
           (equal (submapp1-badguy domain x y)
                  nil))
  :hints(("Goal" :in-theory (enable submapp1-badguy))))

(defthmd submapp1-badguy-of-cons
  (equal (submapp1-badguy (cons a domain) x y)
         (if (not (equal (lookup a x) (lookup a y)))
             (cons t a)
           (submapp1-badguy domain x y)))
  :hints(("Goal" :in-theory (enable submapp1-badguy))))

(defthm submapp1-badguy-membership-property
  (implies (submapp1-badguy domain x y)
           (and (memberp (cdr (submapp1-badguy domain x y)) domain)
                (not (equal (lookup (cdr (submapp1-badguy domain x y)) x)
                            (lookup (cdr (submapp1-badguy domain x y)) y)))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (enable submapp1-badguy)
          :induct (cdr-induction domain))))

(defthm submapp1-badguy-under-iff
  (iff (submapp1-badguy domain x y)
       (not (submapp1 domain x y)))
  :hints(("Goal"
          :in-theory (enable submapp1 submapp1-badguy)
          :induct (cdr-induction domain))))

(defthm submapp1-when-submapp1-of-domain-superset-one
  (implies (and (subsetp domain1 domain2)
                (submapp1 domain2 x y))
           (equal (submapp1 domain1 x y)
                  t))
  :hints(("Goal" :use ((:instance submapp1-badguy-membership-property
                                  (domain domain1)
                                  (x x)
                                  (y y))))))

(defthm submapp1-when-submapp1-of-domain-superset-two
  (implies (and (submapp1 domain2 x y)
                (subsetp domain1 domain2))
           (equal (submapp1 domain1 x y)
                  t)))

(defthm submapp1-of-list-fix-one
  (equal (submapp1 (list-fix domain) x y)
         (submapp1 domain x y)))

(defthm submapp1-of-list-fix-two
  (equal (submapp1 domain (list-fix x) y)
         (submapp1 domain x y))
  :hints(("Goal" :induct (cdr-induction domain))))

(defthm submapp1-of-list-fix-three
  (equal (submapp1 domain x (list-fix y))
         (submapp1 domain x y))
  :hints(("Goal" :induct (cdr-induction domain))))




(defund submapp (x y)
  ;; Do x and y agree on the values of every key in x?
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (submapp1 (domain x) x y))

(defthm booleanp-of-submapp
  (equal (booleanp (submapp x y))
         t)
  :hints(("Goal" :in-theory (enable submapp))))

(defthm submapp-of-list-fix-one
  (equal (submapp (list-fix x) y)
         (submapp x y))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm submapp-of-list-fix-two
  (equal (submapp x (list-fix y))
         (submapp x y))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm equal-of-lookups-when-submapp
  (implies (and (submapp x y)
                (lookup a x))
           (equal (equal (lookup a x) (lookup a y))
                  t))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm equal-of-cdrs-of-lookups-when-submapp
  (implies (and (submapp x y)
                (lookup a x))
           (equal (equal (cdr (lookup a x)) (cdr (lookup a y)))
                  t))
  :hints(("Goal"
          :in-theory (disable equal-of-lookups-when-submapp)
          :use ((:instance equal-of-lookups-when-submapp)))))

(defthm lookup-when-lookup-in-submapp-one
  (implies (and (submapp x y)
                (lookup a x))
           (iff (lookup a y)
                t))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm lookup-when-lookup-in-submapp-two
  (implies (and (lookup a x)
                (submapp x y))
           (iff (lookup a y)
                t))
  :hints(("Goal" :in-theory (enable submapp))))




(defund submapp-badguy (x y)
  ;; Find the first key in x such that x and y disagree upon its value
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (submapp1-badguy (domain x) x y))

(defthm submapp-badguy-membership-property
  (implies (submapp-badguy x y)
           (and (lookup (cdr (submapp-badguy x y)) x)
                (not (equal (lookup (cdr (submapp-badguy x y)) x)
                            (lookup (cdr (submapp-badguy x y)) y)))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (enable submapp-badguy)
          :use ((:instance submapp1-badguy-membership-property
                           (domain (domain x)))))))

(defthm submapp-badguy-under-iff
  (iff (submapp-badguy x y)
       (not (submapp x y)))
  :hints(("Goal" :in-theory (enable submapp submapp-badguy))))

(defthm subsetp-of-domains-when-submap
  (implies (submapp x y)
           (equal (subsetp (domain x) (domain y))
                  t))
  :hints(("Goal" :use ((:instance subsetp-badguy-membership-property
                                  (x (domain x))
                                  (y (domain y)))))))

(defthm submapp-reflexive
  (equal (submapp x x)
         t)
  :hints(("Goal" :use ((:instance submapp-badguy-membership-property
                                  (x x) (y x))))))

(defthm submapp-transitive
  (implies (and (submapp x y)
                (submapp y z))
           (equal (submapp x z)
                  t))
  :hints(("Goal"
          :in-theory (disable equal-of-lookups-when-submapp)
          :use ((:instance submapp-badguy-membership-property
                           (x x) (y z))
                (:instance equal-of-lookups-when-submapp
                           (a (cdr (submapp-badguy x z))) (x x) (y y))
                (:instance equal-of-lookups-when-submapp
                           (a (cdr (submapp-badguy x z))) (x y) (y z))))))

(defthm submapp-transitive-alt
  (implies (and (submapp y z)
                (submapp x y))
           (equal (submapp x z)
                  t)))

(encapsulate
 ()
 (defthmd lemma-for-submapp1-of-app
   (implies (and (submapp1 d1 a b)
                 (submapp1 d2 a b))
            (equal (submapp1 (app d1 d2) a b)
                   t))
   :hints(("Goal"
           :use ((:instance submapp1-badguy-membership-property
                            (domain (app d1 d2))
                            (x a)
                            (y b))))))

 (defthm submapp1-of-app
   (equal (submapp1 (app domain1 domain2) a b)
          (and (submapp1 domain1 a b)
               (submapp1 domain2 a b)))
   :hints(("Goal" :in-theory (enable lemma-for-submapp1-of-app)))))


(encapsulate
 ()
 (defthmd lemma-for-submapp-of-cons-onto-map
   (implies (and (submapp1 x map (cons (cons key val) map2))
                 (not (lookup key map)))
            (submapp1 x
                      (cons entry map)
                      (cons (cons key val)
                            (cons entry map2))))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm submapp-of-cons-onto-map
   (implies (not (consp (lookup key map)))
            (equal (submapp map (cons (cons key val) map))
                   t))
   :hints(("Goal"
           :induct (cdr-induction map)
           :in-theory (enable submapp submapp1 domain lemma-for-submapp-of-cons-onto-map)))))

(encapsulate
 ()
 (defthmd lemma-for-submapp-when-unique-domains-and-subsetp
   (implies (and (uniquep (domain x))
                 (memberp a x))
            (equal (lookup (car a) x)
                   (cons-fix a)))
   :hints(("Goal"
           :in-theory (enable lookup)
           :induct (lookup (car a) x))))

 (defthmd lemma2-for-submapp-when-unique-domains-and-subsetp
   (implies (and (uniquep (domain x))
                 (uniquep (domain y))
                 (subsetp x y)
                 (memberp a (domain x)))
            (equal (equal (lookup a x)
                          (lookup a y))
                   t))
   :hints(("Goal"
           :induct (cdr-induction x)
           :in-theory (enable lemma-for-submapp-when-unique-domains-and-subsetp))))

 (defthm submapp-when-unique-domains-and-subsetp
   (implies (and (uniquep (domain x))
                 (uniquep (domain y))
                 (subsetp x y))
            (equal (submapp x y)
                   t))
   :hints(("Goal"
           :in-theory (enable lemma2-for-submapp-when-unique-domains-and-subsetp)
           :use ((:instance submapp-badguy-membership-property
                            (x x)
                            (y y)))))))


(encapsulate
 ()
 (defthmd lemma-for-submapp-of-app-when-submapp
   (implies (and (submapp1 dom a b)
                 (subsetp dom (domain a)))
            (submapp1 dom a (app b c)))
   :hints(("Goal" :induct (cdr-induction dom))))

 (defthm submapp-of-app-when-submapp
   (implies (submapp a b)
            (submapp a (app b c)))
   :hints(("Goal" :in-theory (enable submapp lemma-for-submapp-of-app-when-submapp)))))


(defthm submapp-of-rev-when-uniquep
  (implies (uniquep (domain x))
           (submapp x (rev x)))
  :hints(("Goal"
          :in-theory (e/d (domain-of-rev)
                          (rev-of-domain)))))





(defund pair-lists (x y)
  ;; Create a list of pairs with cars from x and cdrs from y
  (declare (xargs :guard t))
  (if (consp x)
      (cons (cons (car x) (car y))
            (pair-lists (cdr x) (cdr y)))
    nil))

(defthm pair-lists-when-not-consp
  (implies (not (consp x))
           (equal (pair-lists x y)
                  nil))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm pair-lists-of-cons-one
  (equal (pair-lists (cons a x) y)
         (cons (cons a (car y))
               (pair-lists x (cdr y))))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm pair-lists-of-cons-two
  (equal (pair-lists x (cons a y))
         (if (consp x)
             (cons (cons (car x) a)
                   (pair-lists (cdr x) y))
           nil))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm true-listp-of-pair-lists
  (equal (true-listp (pair-lists x y))
         t)
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm pair-lists-of-list-fix-one
  (equal (pair-lists (list-fix x) y)
         (pair-lists x y))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm pair-lists-of-list-fix-two
  (equal (pair-lists x (list-fix y))
         (pair-lists x y))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm domain-of-pair-lists
  (equal (domain (pair-lists x y))
         (list-fix x))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm range-of-pair-lists
  (implies (force (equal (len domain) (len range)))
           (equal (range (pair-lists domain range))
                  (list-fix range)))
  :hints(("Goal" :in-theory (enable pair-lists))))

(defthm lookup-of-pair-lists
  (equal (lookup a (pair-lists keys vals))
         (if (memberp a keys)
             (cons a (nth (first-index a keys) vals))
           nil))
  :hints(("Goal" :in-theory (enable pair-lists first-index))))

(defthm lookup-of-pair-lists-of-rev
  (implies (and (uniquep keys)
                (equal (len keys) (len vals)))
           (equal (lookup a (pair-lists (rev keys) vals))
                  (if (memberp a keys)
                      (cons a (nth (- (len keys)
                                      (+ 1 (first-index a keys)))
                                   vals))
                    nil))))

(encapsulate
 ()
 (local (defun my-induction (n vars vals)
          (declare (xargs :verify-guards nil
                          :measure (rank vars)
                          :export nil))
          (if (or (not (consp vars))
                  (not (consp vals)))
              nil
            (if (zp n)
                nil
              (my-induction (- n 1) (cdr vars) (cdr vals))))))

 (defthm lookup-of-nth-in-pair-lists-when-unique-keys
   (implies (and (uniquep x)
                 (equal (len x) (len y))
                 (< n (len x)))
            (equal (lookup (nth n x) (pair-lists x y))
                   (cons (nth n x)
                         (nth n y))))
   :hints(("Goal" :induct (my-induction n x y)))))



(defund fast-pair-lists$ (x y acc)
  ;; Compute (app (rev (pair-lists x y)) acc)
  ;;
  ;; This is tail recursive and runs up to 10-21% faster than pair-lists for
  ;; lists of size 100-10000.
  (declare (xargs :guard t))
  (if (consp x)
      (fast-pair-lists$ (cdr x)
                        (cdr y)
                        (cons (cons (car x) (car y)) acc))
    acc))

(defthmd fast-pair-lists$-when-not-consp
  (implies (not (consp x))
           (equal (fast-pair-lists$ x y acc)
                  acc))
  :hints(("Goal" :in-theory (enable fast-pair-lists$))))

(defthmd fast-pair-lists$-of-cons
  (equal (fast-pair-lists$ (cons a x) y acc)
         (fast-pair-lists$ x (cdr y) (cons (cons a (car y)) acc)))
  :hints(("Goal" :in-theory (enable fast-pair-lists$))))

(defthm forcing-fast-pair-lists$-removal
  (implies (force (true-listp acc))
           (equal (fast-pair-lists$ x y acc)
                  (revappend (pair-lists x y) acc)))
  :hints(("Goal" :in-theory (enable fast-pair-lists$))))


