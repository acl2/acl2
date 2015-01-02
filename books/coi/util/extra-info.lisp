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


(in-package "ACL2")

(include-book "in-conclusion")

;; extra-info

(defund extra-info (x y)
  (declare (xargs :guard t)
	   (ignore x y))
  t)

(local (in-theory (enable extra-info)))

(defthm no-extra-info
  (implies
   (not (extra-info x y))
   nil)
  :rule-classes (:forward-chaining))

(in-theory
 (disable (:type-prescription extra-info)
	  (extra-info)))

;; rule-info

(defund rule-info (x y b)
  (declare (type t x y b))
  (and (extra-info x y) b t))

(local (in-theory (enable rule-info)))

(defcong iff equal (rule-info x y b) 3)

;; driver rules ..

(defthm open-rule-info-backchain
  (implies
   (not-in-conclusion)
   (equal (rule-info x y b) (and b t))))

(defthm open-rule-info-positive
  (implies
   (in-conclusion-check (rule-info x y b) :top t)
   (equal (rule-info x y b)
	  (and (extra-info x y) b t))))

(defthm open-rule-info-negated
  (implies
   (in-conclusion-check (rule-info x y b) :top :negated)
   (equal (rule-info x y b)
	  (implies (extra-info x y) b))))