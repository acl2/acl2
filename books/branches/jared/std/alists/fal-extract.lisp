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
(include-book "tools/bstar" :dir :system)
(local (include-book "hons-assoc-equal"))
(local (include-book "../lists/append"))
(local (include-book "../lists/rev"))
(local (include-book "../lists/equiv"))


; FAL-EXTRACT: given a list of variables and an alist, produces an alist
; containing bindings for that list of variables.  Any variable not present in
; the alist is skipped.

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

(local (in-theory (enable fal-extract)))

(defthm fal-extract1-removal
  (equal (fal-extract1 keys al)
         (fal-extract keys al))
  :hints(("Goal" :in-theory (enable fal-extract1))))

(verify-guards fal-extract)

(defthm fal-extract-when-atom
  (implies (atom keys)
           (equal (fal-extract keys al)
                  nil)))

(defthm fal-extract-of-cons
  (equal (fal-extract (cons a keys) al)
         (if (hons-get a al)
             (cons (hons-get a al)
                   (fal-extract keys al))
           (fal-extract keys al))))

(defthm alistp-of-fal-extract
  (alistp (fal-extract keys al)))

(defthm fal-extract-of-list-fix-keys
  (equal (fal-extract (list-fix keys) al)
         (fal-extract keys al)))

(defcong list-equiv equal (fal-extract keys al) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (fal-extract-of-list-fix-keys))
          :use ((:instance fal-extract-of-list-fix-keys (keys keys))
                (:instance fal-extract-of-list-fix-keys (keys keys-equiv))))))

(defcong alist-equiv equal (fal-extract keys al) 2
  :hints(("Goal" :induct t)))

(defthm fal-extract-of-append
  (equal (fal-extract (append x y) al)
         (append (fal-extract x al)
                 (fal-extract y al))))

(defthm fal-extract-of-rev
  (equal (fal-extract (rev x) al)
         (rev (fal-extract x al))))

(defthm fal-extract-of-revappend
  (equal (fal-extract (revappend x y) al)
         (revappend (fal-extract x al)
                    (fal-extract y al))))

(defthm len-of-fal-extract
  (<= (len (fal-extract x al))
      (len x))
  :rule-classes ((:rewrite) (:linear)))



(defthm hons-assoc-equal-fal-extract
  (equal (hons-assoc-equal x (fal-extract keys al))
         (and (member-equal x keys)
              (hons-assoc-equal x al)))
  :hints(("Goal" :induct (fal-extract keys al))))

;; BOZO eventually add this... proven in centaur/misc/fast-alists, but uses
;; set-reasoning:
;;
;;  (defcong set-equiv alist-equiv (fal-extract keys al) 1)
