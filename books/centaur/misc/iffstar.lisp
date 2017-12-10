; Centaur Misc Books
; Copyright (C) 2008-2013 Centaur Technology
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


(include-book "std/util/define" :dir :system)


;; IFF* is just like IFF, but doesn't automatically cause case splits.
(define iff* (x y)
  (iff x y)
  ///
  (defequiv iff*)
  (defrefinement iff iff*)
  (defrefinement iff* iff)
  (defthm iff*-of-nonnils
    (implies (and x y)
             (equal (iff* x y) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))
  (defthm iff*-with-nil
    (and (equal (iff* x nil)
                (not x))
         (equal (iff* nil x)
                (not x))))
  (defthm iff*-with-t
    (and (iff (iff* x t) x)
         (iff (iff* t x) x))))
