; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

;; acl2-count.lisp
;; Jared and Eric are trying to make the perfect acl2-count book.  Send us feedback!

(in-package "ACL2")

(local (in-theory (disable acl2-count))) ;bzo would like this to be non-local?

(defthm acl2-count-of-cons
  (equal (acl2-count (cons x y))
         (+ 1 (acl2-count x) (acl2-count y)))
  :hints (("Goal" :in-theory (enable acl2-count))))

(defthm acl2-count-when-consp-linear
  (implies (consp x)
           (equal (acl2-count x)
                  (+ 1
                     (acl2-count (car x))
                     (acl2-count (cdr x)))))
  :rule-classes :linear)

;; ACL2-COUNT of CAR

(defthm acl2-count-of-car-bound-weak-linear
  (<= (acl2-count (car x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-car-bound-weak
  (equal (< (acl2-count x) (acl2-count (car x)))
         nil))

(defthm acl2-count-of-car-bound-tight
  (equal (< (acl2-count (car x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))

;; ACL2-COUNT of CDR

(defthm acl2-count-of-cdr-bound-weak-linear
  (<= (acl2-count (cdr x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-cdr-bound-weak
  (equal (< (acl2-count x) (acl2-count (cdr x)))
         nil))

(defthm acl2-count-of-cdr-bound-tight
  (equal (< (acl2-count (cdr x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))


;; ACL2-COUNT of NTH

(defthm acl2-count-of-nth-bound-weak-linear
  (<= (acl2-count (nth n l))
      (acl2-count l))
  :rule-classes :linear)

(defthm acl2-count-of-nth-bound-weak
  (equal (< (acl2-count l) (acl2-count (nth n l)))
         nil))

(defthm acl2-count-of-nth-bound-tight
  (equal (< (acl2-count (nth n l)) (acl2-count l))
         (or (consp l)
             (< 0 (acl2-count l)))))

(defthm acl2-count-of-nth-bound-tight-linear
  (implies (consp l)
           (< (acl2-count (nth n l)) (acl2-count l)))
  :rule-classes :linear)