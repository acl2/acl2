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

(include-book "extra-info")
(include-book "std/testing/must-fail" :dir :system)

; We have to disable tau for this whole file.  The reason is that the
; author is taking advantage of disable to make a defined function, e.g.,
; (defun foo (x) t), seem like a constrained function.  Note, for example, the
; must-fail below, when in fact the theorem is trivial if the definition is not
; hidden -- and tau ``sees'' the definition whether foo is enabled or not!

(in-theory (disable (:executable-counterpart tau-system)))

(defun foo (x)
  (declare (ignore x))
  t)

(in-theory (disable foo (:type-prescription foo) (foo)))

(defun zoo (x)
  (declare (ignore x))
  t)

(in-theory (disable zoo (:type-prescription zoo) (zoo)))


(defun goo (x) (foo x))
(defun hoo (x) (foo x))

(in-theory (disable goo hoo))

(defun xoo (x)
  (declare (ignore x))
  t)

(in-theory (disable xoo (:type-prescription xoo) (xoo)))

(encapsulate
    ()

  (local (in-theory (enable goo hoo zoo foo)))

  (defthm xoo-implies-goo
    (implies
     (xoo x)
     (goo x)))

  (defthm xoo-implies-hoo
    (implies
     (xoo x)
     (hoo x)))

  (defthm backchaining-rule
    (implies
     (foo x)
     (zoo x)))
  )

;; Here is a case-split generating rule whose result we
;; want to monitor ..

(defthm foo-rule
  (iff (foo x)
       (if (oddp x) (rule-info 'foo-rule `(oddp ,x) (goo x))
	 (rule-info 'foo-rule `(evenp ,x) (hoo x))))
  :hints (("Goal" :in-theory (enable goo hoo))))

;;
;; General case ..
;;

(must-fail
 (defthmd test
   (zoo x)
   :otf-flg t
   :hints (("Goal" :cases ((foo x))))))

;;
;; Backchaining test ..
;;

(defthm xoo-implies-zoo
  (implies
   (xoo x)
   (zoo x)))

(defun koo (x)
  (declare (ignore x))
  t)

(in-theory (disable koo (:type-prescription koo) (koo)))


(defthm koo-to-foo
  (implies
   (not (zoo x))
   (equal (koo x) (foo x)))
  :hints (("Goal" :in-theory (enable koo foo))))

(must-fail
 (defthmd test
   (zoo x)
   :otf-flg t
   :hints (("Goal" :cases ((koo x))))))
