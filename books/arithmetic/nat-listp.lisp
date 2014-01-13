;; Nat-listp.
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

;; Note: Contributed initially by Sol Swords; modified by Matt Kaufmann.
;; Adapted from unicode/nat-listp.lisp, but INCOMPATIBLE with it.  This
;; version of nat-listp is similar to built-in ACL2 functions integer-listp,
;; symbol-listp, etc, in that it implies true-listp.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(in-theory (disable nat-listp))

(defsection arithmetic/nat-listp
  :parents (nat-listp)
  :short "Lemmas about @(see nat-listp) available in the @('arithmetic/nat-listp')
book."

  :long "<p>Note: this book is pretty minimal.  You should probably generally
instead see @(see std/typed-lists/nat-listp).</p>

<p>BOZO Should we get rid of this book?</p>"

  (local (in-theory (enable nat-listp)))

  (defthm nat-listp-implies-true-listp
    (implies (nat-listp x)
             (true-listp x))
    :rule-classes (:rewrite :compound-recognizer))

  (in-theory (disable (:rewrite nat-listp-implies-true-listp)))

  (defthm nat-listp-when-not-consp
    (implies (not (consp x))
             (equal (nat-listp x)
                    (not x)))
    :hints(("Goal" :in-theory (enable nat-listp))))

  (defthm nat-listp-of-cons
    (equal (nat-listp (cons a x))
           (and (natp a)
                (nat-listp x)))
    :hints(("Goal" :in-theory (enable nat-listp))))

  (defthm nat-listp-of-append-weak
    ;; [Jared] added "weak" in support of std/typed-lists/nat-listp
    (implies (true-listp x)
             (equal (nat-listp (append x y))
                    (and (nat-listp x)
                         (nat-listp y)))))

  (defthm car-nat-listp
    (implies (and (nat-listp x)
                  x)
             (natp (car x)))
    :rule-classes :forward-chaining)

  (defthm nat-listp-of-cdr-when-nat-listp
    ;; [Jared] added double-rewrite in support of std/typed-lists/nat-listp
    (implies (nat-listp (double-rewrite x))
             (equal (nat-listp (cdr x))
                    t))))
