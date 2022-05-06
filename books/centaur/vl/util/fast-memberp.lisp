; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/lists/list-defuns" :dir :system) ; for list-fix
(include-book "misc/hons-help" :dir :system) ; for alist-keys
(local (include-book "std/lists/list-fix" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))

;; It might be good to move this material to a more general library.

(define make-lookup-alist (x)
  :parents (utilities)
  :short "Make a fast-alist for use with @(see fast-memberp)."

  :long "<p>@(call make-lookup-alist) produces a fast-alist binding every
member of @('x') to @('t').</p>

<p>Constructing a lookup alist allows you to use @(see fast-memberp) in lieu of
@(see member) or @(see member-equal), which may be quite a lot faster on large
lists.</p>

<p>Don't forget to free the alist after you are done using it, via @(see
fast-alist-free).</p>"

  (if (consp x)
      (hons-acons (car x)
                  t
                  (make-lookup-alist (cdr x)))
    nil)

  :returns (ans alistp)

  ///
  (defrule hons-assoc-equal-of-make-lookup-alist
    (iff (hons-assoc-equal a (make-lookup-alist x))
         (member-equal a (double-rewrite x))))

  (defrule consp-of-make-lookup-alist
    (equal (consp (make-lookup-alist x))
           (consp x)))

  (defrule make-lookup-alist-under-iff
    (iff (make-lookup-alist x)
         (consp x)))

  (defrule strip-cars-of-make-lookup-alist
    (equal (strip-cars (make-lookup-alist x))
           (list-fix x)))

  (defrule alist-keys-of-make-lookup-alist
    (equal (alist-keys (make-lookup-alist x))
           (list-fix x))))



(define fast-memberp (a
                      x
                      (alist (set-equiv (alist-keys alist)
                                        (list-fix x))))
  :parents (utilities)
  :short "Fast list membership using @(see make-lookup-alist)."

  :long "<p>In the logic, @(call fast-memberp) is just a list membership check;
we leave @('fast-memberp') enabled and always reason about @('member-equal')
instead.</p>

<p>However, our guard requires that @('alist') is the result of running @(see
make-lookup-alist) on @('x').  Because of this, in the execution, the call of
@(see member-equal) call is instead carried out using @(see hons-get) on the
alist, and hence is a hash table lookup.</p>"

  :inline t
  :enabled t

  (mbe :logic (if (member-equal a x) t nil)
       :exec (if (hons-get a alist) t nil)))
