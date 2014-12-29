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

(include-book "ifixequiv")

(defthm natp-implies-nfix-reduction
  (implies
   (natp x)
   (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix))))

(defun nfixequiv (x y)
  (declare (type t x y))
  (equal (nfix x) (nfix y)))

(defequiv nfixequiv)

(defrefinement ifixequiv nfixequiv
  :hints (("Goal" :in-theory (e/d (ifix ifixequiv)
                                  (equal-ifix)))))

(defthm nfixequiv-nfix
  (nfixequiv (nfix x) x))

(defcong nfixequiv equal (nfix x) 1)

(defthmd equal-nfix
  (equal (equal (nfix x) y)
         (and (natp y)
              (nfixequiv x y))))

(in-theory (disable nfixequiv))

(theory-invariant
 (incompatible
  (:rewrite equal-nfix)
  (:definition nfixequiv)))

(in-theory (disable nfix))