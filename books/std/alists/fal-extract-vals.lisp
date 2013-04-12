; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "alist-equiv")
(local (include-book "../lists/append"))
(local (include-book "../lists/rev"))
(local (include-book "../lists/equiv"))

; FAL-EXTRACT-VALS: this is like FAL-EXTRACT except for two things
;  (1) it just returns the values, instead of a sub-alist
;  (2) it doesn't skip unbound keys

(defund fal-extract-vals1 (keys al)
  "Assumes AL is fast"
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (cdr (hons-get (car keys) al))
          (fal-extract-vals1 (cdr keys) al))))

(defund fal-extract-vals (keys al)
  "Makes AL fast if necessary"
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (atom keys)
           nil
         (cons (cdr (hons-get (car keys) al))
               (fal-extract-vals (cdr keys) al)))
       :exec
       (with-fast-alist al
         (fal-extract-vals1 keys al))))

(local (in-theory (enable fal-extract-vals)))

(defthm fal-extract-vals1-removal
  (equal (fal-extract-vals1 keys al)
         (fal-extract-vals keys al))
  :hints(("Goal" :in-theory (enable fal-extract-vals1))))

(verify-guards fal-extract-vals)

(defthm fal-extract-vals-when-atom
  (implies (atom keys)
           (equal (fal-extract-vals keys al)
                  nil)))

(defthm fal-extract-vals-of-cons
  (equal (fal-extract-vals (cons a keys) al)
         (cons (cdr (hons-get a al))
               (fal-extract-vals keys al))))

(defthm fal-extract-vals-of-list-fix
  (equal (fal-extract-vals (list-fix keys) al)
         (fal-extract-vals keys al)))

(defcong list-equiv equal (fal-extract-vals keys al) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (fal-extract-vals-of-list-fix))
          :use ((:instance fal-extract-vals-of-list-fix (keys keys))
                (:instance fal-extract-vals-of-list-fix (keys keys-equiv))))))

(defcong alist-equiv equal (fal-extract-vals keys al) 2)

(defthm fal-extract-vals-of-append
  (equal (fal-extract-vals (append x y) al)
         (append (fal-extract-vals x al)
                 (fal-extract-vals y al))))

(defthm fal-extract-vals-of-rev
  (equal (fal-extract-vals (rev x) al)
         (rev (fal-extract-vals x al))))

(defthm fal-extract-vals-of-revappend
  (equal (fal-extract-vals (revappend x y) al)
         (revappend (fal-extract-vals x al)
                    (fal-extract-vals y al))))

;; BOZO should probably add something like:
;; (defcong set-equiv set-equiv (fal-extract-vals keys al) 1)

(defthm len-of-fal-extract-vals
  (equal (len (fal-extract-vals x al))
         (len x)))
