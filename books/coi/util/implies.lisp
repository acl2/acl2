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

(defund imp (a x)
  (if x t (and a t)))

(defcong iff equal (imp a x) 1
  :hints (("Goal" :in-theory (enable imp))))

(defthm open-imp-in-conclusion
  (implies
   (in-conclusion-check (imp a x) :top :any)
   (equal (imp a x) (if x t (and a t))))
  :hints (("Goal" :in-theory (enable imp))))

(defthm implies-imp
  (implies a (imp a x))
  :hints (("Goal" :in-theory (enable imp))))

;; The idea here is to rewrite a boolean term into an expression that
;; implies that term.
;;
;; For example: (=> (acl2-numberp x) (integerp x))
;;
;; Note that this can very easily render a provable goal unprovable.
;;
;; Note that we will usually only want to do this to terms we find in
;; our conclusion.

(defmacro => (x a)
  `(iff ,x (imp ,a (hide ,x))))

