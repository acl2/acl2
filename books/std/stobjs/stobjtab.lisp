; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; This book introduces STOBJTAB, an abstract stobj that (logically) is just a
;; stobj-table field.  Its foundational stobj is STOBJ-TABLE.  You could choose
;; to use either one.  The tradeoff:
;;   - Stobjtab has simpler base accessors/updaters because it is itself the
;;   stobj-table field, no need to access that field through nth/update-nth.
;;   - Abstract stobj overhead makes updating uses of stobj-let a bit slower,
;;   around 10% in the worst case.


(include-book "stobj-table")
(include-book "absstobjs")

(defun stobjtab$ap (stobjtab$a)
  (declare (xargs :guard t)
           (ignorable stobjtab$a))
  t)

(defun create-stobjtab$a ()
  (declare (xargs :guard t))
  nil)

(defun stbl-get$a (k stobjtab$a)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal k stobjtab$a)))

(defun stbl-put$a (k v stobjtab$a)
  (declare (xargs :guard t))
  (cons (cons k v) stobjtab$a))

(defun stbl-boundp$a (k stobjtab$a)
  (declare (xargs :guard t))
  (consp (hons-assoc-equal k stobjtab$a)))

(defun stbl-rem$a (k stobjtab$a)
  (declare (xargs :guard t))
  (hons-remove-assoc k stobjtab$a))

(defun stbl-count$a (stobjtab$a)
  (declare (xargs :guard t))
  (count-keys stobjtab$a))

(defun stbl-clear$a (stobjtab$a)
  (declare (xargs :guard t)
           (ignorable stobjtab$a))
  nil)

(defun stbl-init$a (ht-size rehash-size rehash-threshold stobjtab$a)
  (declare (xargs :guard (and (or (natp ht-size) (not ht-size))
                              (or (and (rationalp rehash-size)
                                       (<= 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold))))
           (ignorable ht-size rehash-size rehash-threshold stobjtab$a))
  nil)

(defun-nx stbl-corr (stobj-table stobjtab$a)
  (equal stobj-table (list stobjtab$a)))

(local (in-theory (enable nth update-nth)))


(defabsstobj-events stobjtab
  :foundation stobj-table
  :recognizer (stobjtabp :logic stobjtab$ap :exec stobj-tablep)
  :creator (create-stobjtab :logic create-stobjtab$a :exec create-stobj-table)
  :corr-fn stbl-corr
  :exports ((stbl-get :logic stbl-get$a :exec tbl-get :updater stbl-put)
            (stbl-put :logic stbl-put$a :exec tbl-put)
            (stbl-boundp :logic stbl-boundp$a :exec tbl-boundp)
            (stbl-rem :logic stbl-rem$a :exec tbl-rem)
            (stbl-count :logic stbl-count$a :exec tbl-count)
            (stbl-clear :logic stbl-clear$a :exec tbl-clear)
            (stbl-init :logic stbl-init$a :exec tbl-init)))
