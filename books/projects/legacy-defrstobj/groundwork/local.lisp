; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/records" :dir :system)

; local.lisp -- supporting theorems to be only locally included

(in-theory (disable nth
                    update-nth
                    make-list-ac
                    (make-list-ac)))

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc)))
  :hints(("Goal" :in-theory (enable make-list-ac))))

(defthm acl2-count-of-nth-weak
  (<= (acl2-count (nth n x))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable nth))))

(defthm acl2-count-of-nth-strong
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable nth))))

(defthm true-listp-of-update-nth
  (implies (true-listp arr)
           (true-listp (update-nth n val arr))))

(defthm update-nth-switch
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n val1 (update-nth m val2 x))
                  (update-nth m val2 (update-nth n val1 x))))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm update-nth-of-nth
  (implies (and (natp n)
                (< n (len arr)))
           (equal (update-nth n (nth n arr) arr)
                  arr))
  :hints(("Goal" :in-theory (enable update-nth nth))))

(defthm update-nth-of-nth-other
  (implies (and (natp n)
                (< n (len arr))
                (natp m)
                (not (equal n m))
                (< m (len arr)))
           (equal (update-nth n (nth n arr)
                              (update-nth m val arr))
                  (update-nth m val arr))))

(defthm s-nil-nil
  (equal (s k nil nil)
         nil)
  :hints(("Goal" :in-theory (enable s acl2->rcd rcd->acl2))))

(defthm update-nth-same
  (implies (equal (nfix i) (nfix j))
           (equal (update-nth j b (update-nth i a l))
                  (update-nth j b l)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm true-listp-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
    (implies (true-listp ac)
             (true-listp (make-list-ac n val ac)))))
  :hints(("Goal" :in-theory (enable make-list-ac))))
