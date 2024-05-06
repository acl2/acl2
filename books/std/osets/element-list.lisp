; Fully Ordered Finite Sets -- Abstract typed list integration
; Copyright (C) 2014 Centaur Technology, Inc.
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

(include-book "top")
(include-book "std/lists/abstract" :dir :system)
(include-book "std/lists/list-fix" :dir :system)

(def-listp-rule element-list-p-of-sfix
  (iff (element-list-p (set::sfix x))
       (or (element-list-p x)
           (not (set::setp x))))
  :hints(("Goal" :in-theory (enable set::emptyp set::sfix)))
  :tags (:osets))

;; (local (defthm element-list-p-of-insert-implies-element-list-p-list-fix
;;          (implies (not (element-list-p (set::sfix x)))
;;                   (not (element-list-p (set::insert a x))))
;;          :hints(("Goal" :in-theory (e/d (set::insert set::tail set::head set::emptyp
;;                                                      set::setp)
;;                                         (iff))
;;                  :induct (len x)))))

(def-listp-rule element-list-p-of-insert
  (iff (element-list-p (set::insert a x))
       (and (element-list-p (set::sfix x))
            (element-p a)))
  :hints(("Goal" :in-theory (e/d (set::insert set::tail set::head set::emptyp
                                              set::setp)
                                 (iff))
          :induct (len x)))
  :tags (:osets))

(def-listp-rule element-list-p-of-delete
  (implies (element-list-p x)
           (element-list-p (set::delete k x)))
  :hints(("Goal" :in-theory (enable set::delete set::head set::tail set::emptyp)))
  :tags (:osets))

(def-listp-rule element-list-p-of-mergesort
  (iff (element-list-p (set::mergesort x))
       (element-list-p (list-fix x)))
  :hints(("Goal" :in-theory (enable set::mergesort)))
  :tags (:osets))

(def-listp-rule element-list-p-of-union
  (iff (element-list-p (set::union x y))
       (and (element-list-p (set::sfix x))
            (element-list-p (set::sfix y))))
  :hints(("Goal" :in-theory (enable set::union set::head set::tail set::emptyp
                                    set::setp)
          :induct (len x)))
  :tags (:osets))

(def-listp-rule element-list-p-of-intersect-1
  (implies (element-list-p x)
           (element-list-p (set::intersect x y)))
  :hints(("Goal" :in-theory (enable set::intersect set::head set::tail set::emptyp set::setp)))
  :tags (:osets))

(local (defthm element-p-when-in-element-list-p
         (implies (and (set::in a x)
                       (element-list-p x))
                  (element-p a))
         :hints(("Goal" :in-theory (enable set::in set::head set::tail set::emptyp)))))

(def-listp-rule element-list-p-of-intersect-2
  (implies (element-list-p y)
           (element-list-p (set::intersect x y)))
  :hints(("Goal" :in-theory (enable set::intersect set::head set::tail set::emptyp set::setp)))
  :tags (:osets))

(def-listp-rule element-list-p-of-difference
  (implies (element-list-p x)
           (element-list-p (set::difference x y)))
  :hints(("Goal" :in-theory (enable set::difference set::head set::tail set::emptyp set::setp)))
  :tags (:osets))
