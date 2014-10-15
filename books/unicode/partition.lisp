; Processing Unicode Files with ACL2
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

(include-book "std/lists/flatten" :dir :system)
(include-book "sum-list")
(local (include-book "std/lists/take" :dir :system))
(local (include-book "z-listp"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(defund partition (sizes x)
  (declare (xargs :guard (and (nat-listp sizes)
                              (true-listp x))))
  (if (consp sizes)
      (cons (take (car sizes) x)
            (partition (cdr sizes)
                       (nthcdr (car sizes) x)))
    nil))

(defthm partition-when-not-consp
  (implies (not (consp sizes))
           (equal (partition sizes x)
                  nil))
  :hints(("Goal" :in-theory (enable partition))))

(defthm partition-of-cons
  (equal (partition (cons size sizes) x)
         (cons (take size x)
               (partition sizes (nthcdr size x))))
  :hints(("Goal" :in-theory (enable partition))))

(defthm consp-of-partition-under-iff
  (equal (consp (partition sizes x))
         (if (partition sizes x)
             t
           nil))
  :hints(("Goal" :in-theory (enable partition))))

(local (defthm sum-list-when-nat-listp-and-z-listp
         (implies (and (nat-listp x)
                       (z-listp x))
                  (equal (sum-list x)
                         0))
         :hints(("Goal" :induct (len x)))))

(local (defthm reassemble-lemma
         (implies (<= (nfix n) (len x))
                  (equal (append (take n x)
                                 (list-fix (nthcdr n x)))
                         (list-fix x)))))

(defthm flatten-of-partition
  (implies (and (nat-listp sizes)
                (equal (sum-list sizes) (len x)))
           (equal (flatten (partition sizes x))
                  (list-fix x)))
  :hints(("Goal" :in-theory (enable partition))))

(defthm len-of-car-of-partition
  (equal (len (car (partition sizes x)))
         (nfix (car sizes))))

