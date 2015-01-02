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

(include-book "fixequiv")

(defthm integerp-implies-ifix-reduction
  (implies
   (integerp x)
   (equal (ifix x) x))
  :hints (("Goal" :in-theory (enable ifix))))

(defun ifixequiv (x y)
  (declare (type t x y))
  (equal (ifix x) (ifix y)))

(defequiv ifixequiv)

(defrefinement fixequiv ifixequiv
  :hints (("Goal" :in-theory (e/d (fix fixequiv)
                                  (equal-fix)))))

(defthm ifixequiv-ifix
  (ifixequiv (ifix x) x))

(defcong ifixequiv equal (ifix x) 1)

(defthmd equal-ifix
  (equal (equal (ifix x) y)
         (and (integerp y)
              (ifixequiv x y))))

(in-theory (disable ifixequiv))

(theory-invariant
 (incompatible
  (:rewrite equal-ifix)
  (:definition ifixequiv)))

(in-theory (disable ifix))