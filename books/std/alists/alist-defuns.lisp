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
(include-book "tools/bstar" :dir :system)
(include-book "../lists/list-defuns")
(local (include-book "alist-equiv"))
(local (include-book "alist-keys"))
(local (include-book "alist-vals"))
(local (include-book "hons-rassoc-equal"))
(local (include-book "fal-extract"))
(local (include-book "fal-extract-vals"))
(set-enforce-redundancy t)

(defund alist-keys (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-keys (cdr x)))
        (t
         (cons (caar x) (alist-keys (cdr x))))))

(defund alist-vals (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-vals (cdr x)))
        (t
         (cons (cdar x) (alist-vals (cdr x))))))

(defund hons-rassoc-equal (val alist)
  (declare (xargs :guard t))
  (cond ((atom alist)
         nil)
        ((and (consp (car alist))
              (equal val (cdar alist)))
         (car alist))
        (t
         (hons-rassoc-equal val (cdr alist)))))

(defund alists-agree (keys al1 al2)
  "Do AL1 and AL2 agree on the value of every KEY in KEYS?"
  (declare (xargs :guard t))
  (or (atom keys)
      (and (equal (hons-get (car keys) al1)
                  (hons-get (car keys) al2))
           (alists-agree (cdr keys) al1 al2))))

(defund sub-alistp (a b)
  "Is every key bound in A also bound to the same value in B?"
  (declare (xargs :guard t))
  (mbe :logic (alists-agree (alist-keys a) a b)
       :exec
       (with-fast-alist a
         (with-fast-alist b
           (alists-agree (alist-keys a) a b)))))

(defund alist-equiv (a b)
  "Do A and B agree on the values of every key?"
  (declare (xargs :guard t))
  (mbe :logic (and (sub-alistp a b)
                   (sub-alistp b a))
       :exec
       ;; Silly, make them both fast once instead of twice.
       (with-fast-alist a
         (with-fast-alist b
           (and (sub-alistp a b)
                (sub-alistp b a))))))

(defequiv alist-equiv
  ;; We include this, even though this book isn't really meant to include
  ;; theorems, in order to avoid subtle errors that can arise in different
  ;; books.  Without this, in book A we could just load ALIST-DEFUNS and then
  ;; prove a theorem that concluded (ALIST-EQUIV X Y).  If then in book B we
  ;; load alists/alist-equiv.lisp first and then include book A, this is no
  ;; longer a valid rewrite rule and we get a horrible error!
  )

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
  (declare (xargs :guard t))
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

(defund fal-extract-vals1 (keys al)
  "Assumes AL is fast"
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (cdr (hons-get (car keys) al))
          (fal-extract-vals1 (cdr keys) al))))

(defund fal-extract-vals (keys al)
  "Makes AL fast if necessary"
  (declare (xargs :guard t))
  (mbe :logic
       (if (atom keys)
           nil
         (cons (cdr (hons-get (car keys) al))
               (fal-extract-vals (cdr keys) al)))
       :exec
       (with-fast-alist al
         (fal-extract-vals1 keys al))))
