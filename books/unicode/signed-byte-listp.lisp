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

(in-theory (disable signed-byte-p))

(defund signed-byte-listp (n x)
  (if (atom x)
      (null x)
    (and (signed-byte-p n (car x))
         (signed-byte-listp n (cdr x)))))

(defthm signed-byte-listp-when-not-consp
  (implies (not (consp x))
           (equal (signed-byte-listp n x)
                  (not x)))
  :hints(("Goal" :in-theory (enable signed-byte-listp))))

(defthm signed-byte-listp-of-cons
  (equal (signed-byte-listp n (cons a x))
         (and (signed-byte-p n a)
              (signed-byte-listp n x)))
  :hints(("Goal" :in-theory (enable signed-byte-listp))))

(defthm true-listp-when-signed-byte-listp
  (implies (signed-byte-listp bytes x)
           (true-listp x))
  :hints(("Goal" :induct (len x))))

(encapsulate
 ()
 (local (include-book "ihs/logops-lemmas" :dir :system))

 (local (in-theory (disable binary-logior
                            binary-logand
                            lognot)))

 (local (in-theory (enable signed-byte-p-logops)))

 (defthm signed-byte-p-logand
   (implies (and (signed-byte-p size x)
                 (signed-byte-p size y))
            (signed-byte-p size (logand x y))))

 (defthm signed-byte-p-logior
   (implies (and (signed-byte-p size x)
                 (signed-byte-p size y))
            (signed-byte-p size (logior x y))))

 (defthm signed-byte-p-lognot
   (implies (signed-byte-p size x)
            (signed-byte-p size (lognot x))))
 )


(defthm decrement-positive-signed-byte
  (implies (and (signed-byte-p n x)
                (< 0 x))
           (signed-byte-p n (1- x)))
  :hints(("Goal" :in-theory (enable signed-byte-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-3/bind-free/top" :dir :system))

 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

 (local (set-default-hints
         '((nonlinearp-default-hint stable-under-simplificationp
                                    hist pspv))))

 (local (include-book "unsigned-byte-listp"))

 (defthm signed-byte-promote
   (implies (and (signed-byte-p size1 x)
                 (integerp size2)
                 (<= size1 size2))
            (signed-byte-p size2 x))
   :hints(("Goal" :in-theory (enable signed-byte-p))))

 ; Added by Robert Krug 6/15/07 due to changes in non-linear arithmetic:
 (local (prefer-positive-exponents))

 (defthm signed-byte-p-of-ash
   (implies (and (force (integerp x))
                 (force (integerp shift))
                 (force (integerp size))
                 (<= 0 size)
                 (<= 0 shift)
                 (< shift size))
            (equal (signed-byte-p size (ash x shift))
                   (signed-byte-p (- size shift) x)))
   :hints(("Goal" :in-theory (enable signed-byte-p ash))))

 (defthm ash-sbyte-positive
   (implies (and (force (integerp x))
                 (force (integerp shift))
                 (force (integerp size))
                 (<= 0 x)
                 (<= 1 size)
                 (< shift (1- size)))
            (equal (signed-byte-p size (ash x shift))
                   (signed-byte-p (- size shift) x)))
   :hints(("Goal" :in-theory (e/d (signed-to-unsigned-promote)
                                  (ash)))))

 (defthm signed-byte-p-resolver
   (implies (and (integerp n)
                 (<= 1 n)
                 (integerp x)
                 (<= (- (expt 2 (1- n))) x)
                 (< x (expt 2 (1- n))))
            (signed-byte-p n x))
   :hints(("Goal" :in-theory (enable signed-byte-p))))

 )

(in-theory (disable ash))
(in-theory (disable binary-logior))
(in-theory (disable binary-logand))
