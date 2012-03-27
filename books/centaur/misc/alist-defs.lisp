; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; for alist-keys, alist-vals:
(include-book "misc/hons-help" :dir :system)
(include-book "hons-extra")

(defund alists-agree (keys al1 al2)
  (declare (xargs :guard t))
  (or (atom keys)
      (and (equal (hons-get (car keys) al1)
                  (hons-get (car keys) al2))
           (alists-agree (cdr keys) al1 al2))))


(defund hons-acons-each (keys val al)
  (declare (xargs :guard t))
  (if (atom keys)
      al
    (hons-acons (car keys) val
                (hons-acons-each (Cdr keys) val al))))

;; This is just hshrink-alist with a NIL accumulator.
(defund al-shrink (al)
  (declare (xargs :guard t))
  (hons-shrink-alist al nil))


;; FAL-EXTRACT: given a list of variables and an alist, produces an alist
;; containing bindings for that list of variables.  Any variable not present in
;; the alist is skipped.
(defund fal-extract1 (keys al)
  "Assumes AL is fast"
  (declare (xargs :guard t))
  (b* (((when (atom keys))
        nil)
       (look (hons-get (car keys) al))
       ((when look)
        (cons look (fal-extract1 (cdr keys) al))))
    (fal-extract1 (cdr keys) al)))

(defund fal-extract (keys al)
  "Makes AL fast if necessary"
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (b* (((when (atom keys))
             nil)
            (look (hons-get (car keys) al))
            ((when look)
             (cons look (fal-extract (cdr keys) al))))
         (fal-extract (cdr keys) al))
       :exec
       (with-fast-alist al
         (fal-extract1 keys al))))

(defthm fal-extract1-removal
  (equal (fal-extract1 keys al)
         (fal-extract keys al))
  :hints(("Goal" :in-theory (enable fal-extract1
                                    fal-extract))))

(verify-guards fal-extract
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm alistp-fal-extract
  (equal (alistp (fal-extract keys al)) t)
  :hints(("Goal" :in-theory (enable fal-extract))))



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

(defthm fal-extract-vals1-removal
  (equal (fal-extract-vals1 keys al)
         (fal-extract-vals keys al))
  :hints(("Goal" :in-theory (enable fal-extract-vals1
                                    fal-extract-vals))))

(verify-guards fal-extract-vals
  :hints(("Goal" :in-theory (enable fal-extract-vals))))
