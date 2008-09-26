;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "revappend"))
(include-book "base10-digit-charp")

;; Explode-nonnegative-integer is a particularly nasty function to try to
;; reason about because it is tail recursive and has a very nasty base case.
;; Instead of reasoning about it directly, we will split it up into the
;; following, simpler definition.
 
(local (defun simpler-explode-nonnegative-integer (n ans)
         (declare (xargs :guard (and (integerp n) 
                                     (<= 0 n))))
         (if (zp n)
             ans
           (simpler-explode-nonnegative-integer 
            (floor n 10)
            (cons (digit-to-char (mod n 10)) ans)))))



;; We can now redefine explode-nonnegative-integer to be a simple nonrecursive
;; function that uses our simpler-explode-nonnegative-integer as its core, but
;; wraps it in a simple "or" statement.  We will then disable the previous
;; definition of explode-nonnegative-integer, so that only our new definition
;; will be used.

(local (defthm explode-nonnegative-integer-redefinition
         (equal (explode-nonnegative-integer n 10 ans)
                (or (simpler-explode-nonnegative-integer n ans)
                    '(#\0)))
         :rule-classes ((:definition :install-body nil))))

(local (in-theory (disable (:definition explode-nonnegative-integer))))
  


;; Sadly, even simpler-explode-nonnegative-integer is hard to reason about as
;; it is tail recursive.  So, we will introduce a non tail-recursive function
;; in its place that does almost the same thing.  We'll call this the "basic
;; explode-nonnegative-integer core", or the basic-eni-core for short.
 
(local (defun basic-eni-core (n)
         (declare (xargs :guard (natp n)))
         (if (zp n)
             nil
           (cons (digit-to-char (mod n 10))
                 (basic-eni-core (floor n 10))))))

(local (defun basic-eni-induction (n m)
         (declare (xargs :guard (and (natp n)
                                     (natp m))))
         (if (zp n) 
             nil
           (if (zp m)
               nil
             (basic-eni-induction (floor n 10) (floor m 10))))))

(local (defthm consp-of-basic-eni-core
         (equal (consp (basic-eni-core n))
                (not (zp n)))))

(local (defthm equal-of-basic-eni-cores
         (equal (equal (basic-eni-core n)
                       (basic-eni-core m))
                (equal (nfix n) (nfix m)))
         :hints(("Goal" :induct (basic-eni-induction n m)))))
 
(local (defthm basic-eni-core-under-iff
         (iff (basic-eni-core n)
              (not (zp n)))))
                  
(local (defthm equal-of-basic-eni-core-with-list-zero
         (not (equal (basic-eni-core n) '(#\0)))
         :hints(("Goal" :in-theory (enable digit-to-char)))))

(local (defthm basic/simpler-equivalence
         (equal (simpler-explode-nonnegative-integer n acc)
                (revappend (basic-eni-core n) acc))))

(local (defthm equal-of-simpler-explode-nonnegative-integers
         (equal (equal (simpler-explode-nonnegative-integer n acc)
                       (simpler-explode-nonnegative-integer m acc))
                (equal (nfix n) (nfix m)))))

(local (defthm simpler-eni-when-nonzero
         (implies (not (zp n))
                  (simpler-explode-nonnegative-integer n acc))))

(local (defthm simpler-eni-degenerate-lemma
         (equal (equal (simpler-explode-nonnegative-integer n acc) '(#\0))
                (and (equal acc '(#\0))
                     (zp n)))
         :hints(("Goal" :in-theory (enable digit-to-char)))))

(local (defthm not-of-simpler-explode-nonnegative-integer
         (equal (not (simpler-explode-nonnegative-integer n acc))
                (and (equal acc nil)
                     (zp n)))))

(local (defthm true-listp-of-simpler-explode-nonnegative-integer
         (equal (true-listp (simpler-explode-nonnegative-integer n acc))
                (true-listp acc))))

(local (defthm equal-of-explode-nonnegative-integers-lemma
         (implies (and (integerp n) (<= 0 n)
                       (integerp m) (<= 0 m)
                       (not (equal n m))
                       (not (simpler-explode-nonnegative-integer n acc)))
                  (simpler-explode-nonnegative-integer m acc))))

(defthm equal-of-explode-nonnegative-integers
  (implies (and (natp n)
                (natp m))
           (equal (equal (explode-nonnegative-integer n 10 acc)
                         (explode-nonnegative-integer m 10 acc))
                  (equal n m)))
  :hints(("Goal" :in-theory (disable simpler-explode-nonnegative-integer
                                     basic/simpler-equivalence))))

(defthm true-listp-of-explode-nonnegative-integer
  (equal (true-listp (explode-nonnegative-integer n 10 acc))
         (true-listp acc)))

(defthm true-listp-of-explode-nonnegative-integer-type
  (implies (true-listp acc)
           (true-listp (explode-nonnegative-integer n 10 acc)))
  :rule-classes :type-prescription)



(local (defthm base10-digit-char-listp-of-basic-eni-core
         (base10-digit-char-listp (basic-eni-core n))
         :hints(("Goal" :in-theory (enable base10-digit-char-listp)))))

(local (defthm base10-digit-char-listp-of-simpler-eni
         (implies (base10-digit-char-listp acc)
                  (base10-digit-char-listp 
                   (simpler-explode-nonnegative-integer n acc)))))

(defthm base10-digit-char-listp-of-explode-nonnegative-integer
  (implies (base10-digit-char-listp acc)
           (base10-digit-char-listp (explode-nonnegative-integer n 10 acc))))


(encapsulate
 ()
 (local (defthm lemma
          (equal (equal (revappend x acc) '(#\0))
                 (or (and (equal acc nil)
                          (consp x)
                          (equal (car x) #\0)
                          (atom (cdr x)))
                     (and (equal acc '(#\0))
                          (atom x))))))
 
 (defthm nonzeroness-of-explode-nonnegative-integer-when-nonzero
   (implies (not (zp n))
            (not (equal (explode-nonnegative-integer n 10 nil)
                        '(#\0))))
   :hints(("Goal" :in-theory (enable digit-to-char)))))




(defund base10-digit-char-to-nat (x)
  (declare (xargs :guard (base10-digit-charp x)))
  (case x
    (#\0 0)
    (#\1 1)
    (#\2 2)
    (#\3 3)
    (#\4 4)
    (#\5 5)
    (#\6 6)
    (#\7 7)
    (#\8 8)
    (otherwise 9)))

(defthm base10-digit-char-to-nat-of-digit-to-char
  (implies (and (force (natp n))
                (force (<= 0 n))
                (force (<= n 9)))
           (equal (base10-digit-char-to-nat (digit-to-char n))
                  n))
  :hints(("Goal" :in-theory (enable base10-digit-char-to-nat
                                    digit-to-char))))

(defthm digit-to-char-of-base10-digit-char-to-nat
  (implies (force (base10-digit-charp x))
           (equal (digit-to-char (base10-digit-char-to-nat x))
                  x))
  :hints(("Goal" :in-theory (enable base10-digit-charp
                                    base10-digit-char-to-nat
                                    digit-to-char))))

(defund basic-unexplode-core (x)
  (declare (xargs :guard (base10-digit-char-listp x)))
  (if (consp x)
      (+ (base10-digit-char-to-nat (car x))
         (* 10 (basic-unexplode-core (cdr x))))
    0))

(local (defthm basic-unexplode-core-of-basic-eni-core
         (implies (force (natp n))
                  (equal (basic-unexplode-core (basic-eni-core n))
                         n))
         :hints(("Goal" :in-theory (enable basic-eni-core
                                           basic-unexplode-core)))))

(defund unexplode-nonnegative-integer (x)
  (declare (xargs :guard (base10-digit-char-listp x)))
  (basic-unexplode-core (revappend x nil)))

(encapsulate
 ()
 (local (include-book "rev"))
 
 (defthm unexplode-nonnegative-integer-of-explode-nonnegative-integer
   (implies (force (natp n))
            (equal (unexplode-nonnegative-integer (explode-nonnegative-integer n 10 nil))
                   n))
   :hints(("Goal" :in-theory (e/d (unexplode-nonnegative-integer)
                                  (basic-eni-core))))))

  