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
(set-verify-guards-eagerness 2)

(include-book "std/lists/take" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(local (include-book "std/lists/repeat" :dir :system))

(in-theory (disable unsigned-byte-p))

(defund unsigned-byte-listp (n x)
  (if (atom x)
      (null x)
    (and (unsigned-byte-p n (car x))
         (unsigned-byte-listp n (cdr x)))))

(defthm unsigned-byte-listp-when-not-consp
  (implies (not (consp x))
           (equal (unsigned-byte-listp n x)
                  (not x)))
  :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-cons
  (equal (unsigned-byte-listp n (cons a x))
         (and (unsigned-byte-p n a)
              (unsigned-byte-listp n x)))
  :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-p-of-car-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (equal (unsigned-byte-p bytes (car x))
                  (consp x)))
  :rule-classes (:rewrite :forward-chaining))

(defthm nat-listp-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (nat-listp x))
  :hints(("Goal" :induct (len x))))

(defthm true-listp-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (true-listp x))
  :hints(("Goal" :induct (len x))))

(encapsulate
 ()

 (local (include-book "ihs/logops-lemmas" :dir :system))

 (local (in-theory (disable binary-logior
                            binary-logand
                            lognot
                            unsigned-byte-p)))

 (local (in-theory (enable signed-byte-p-logops)))

 (defthm unsigned-byte-p-logand
   (implies (and (or (unsigned-byte-p size i)
                     (unsigned-byte-p size j))
                 (force (integerp i))
                 (force (integerp j)))
            (unsigned-byte-p size (logand i j))))

 (defthm unsigned-byte-p-logior
   (implies (and (force (integerp i))
                 (force (integerp j)))
            (equal (unsigned-byte-p size (logior i j))
                   (and (unsigned-byte-p size i)
                        (unsigned-byte-p size j))))))


(defthm decrement-positive-unsigned-byte
  (implies (and (unsigned-byte-p n x)
                (< 0 x))
           (unsigned-byte-p n (1- x)))
  :hints(("Goal" :in-theory (enable unsigned-byte-p))))


(encapsulate
 ()

 (local (include-book "arithmetic-3/bind-free/top" :dir :system))
 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

 (local (set-default-hints
         '((nonlinearp-default-hint stable-under-simplificationp
                                    hist pspv))))

 (local (defthm signed-byte-promote
          (implies (and (signed-byte-p size1 x)
                        (integerp size2)
                        (<= size1 size2))
                   (signed-byte-p size2 x))))

 (defthm unsigned-byte-promote
   (implies (and (unsigned-byte-p size1 x)
                 (integerp size2)
                 (<= size1 size2))
            (unsigned-byte-p size2 x))
   :hints(("Goal" :in-theory (enable unsigned-byte-p))))

 (local (defthm lemma
          (implies (unsigned-byte-p a x)
                   (signed-byte-p (+ 1 a) x))
          :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

 (defthm unsigned-to-signed-promote
   (implies (and (unsigned-byte-p size1 x)
                 (integerp size2)
                 (< size1 size2))
            (signed-byte-p size2 x))
   :hints(("Goal"
           :in-theory (enable unsigned-byte-p)
           :use ((:instance lemma
                            (a size1))
                 (:instance signed-byte-promote
                            (size1 (+ 1 size1)))))))

  (defthm unsigned-byte-p-of-ash
    (implies (and (force (integerp x))
                  (force (integerp shift))
                  (force (integerp size))
                  (<= 0 size)
                  (< shift size))
             (equal (unsigned-byte-p size (ash x shift))
                    (unsigned-byte-p (- size shift) x)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p))))

  (defthmd signed-to-unsigned-promote
    (implies (and (force (integerp n))
                  (force (integerp x))
                  (<= 0 x))
             (equal (signed-byte-p n x)
                    (unsigned-byte-p (1- n) x)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p))))

  (defthm ash-positive
    (implies (and (integerp x)
                  (integerp n)
                  (<= 0 x))
             (<= 0 (ash x n)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm unsigned-byte-p-resolver
    (implies (and (integerp n) (<= 0 n)
                  (integerp x) (<= 0 x)
                  (< x (expt 2 n)))
             (unsigned-byte-p n x))
    :hints(("Goal" :in-theory (enable unsigned-byte-p))))

  )


(in-theory (disable ash))
(in-theory (disable binary-logior))
(in-theory (disable binary-logand))


(defthm unsigned-byte-listp-of-append
  (equal (unsigned-byte-listp bytes (append x y))
         (and (unsigned-byte-listp bytes (list-fix x))
              (unsigned-byte-listp bytes y)))
  :hints(("Goal" :induct (len x))))

(defthm unsigned-byte-listp-of-list-fix-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (unsigned-byte-listp bytes (list-fix x))))

(local (defthm unsigned-byte-listp-of-repeat
         (equal (unsigned-byte-listp bytes (repeat x n))
                (or (zp n)
                    (unsigned-byte-p bytes x)))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm lemma-for-arithmetic
         (implies (not (zp n))
                  (equal (not (< 1 n))
                         (equal 1 n)))))

(defthm unsigned-byte-listp-of-take
  (implies (unsigned-byte-listp bytes x)
           (equal (unsigned-byte-listp bytes (take n x))
                  (or (zp n)
                      (<= n (len x))))))

(defthm unsigned-byte-listp-of-take-past-length
  (implies (and (natp k)
                (< (len x) k))
           (not (unsigned-byte-listp bytes (take k x)))))

(defthm unsigned-byte-listp-of-nthcdr
  (implies (unsigned-byte-listp bytes x)
           (unsigned-byte-listp bytes (nthcdr n x))))

(defthm unsigned-byte-listp-when-take-and-nthcdr
  (implies (and (unsigned-byte-listp bytes (take n x))
                (unsigned-byte-listp bytes (nthcdr n x)))
           (unsigned-byte-listp bytes x)))

