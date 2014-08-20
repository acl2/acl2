; Standard Utilities Library
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

(in-package "STD")

;; NOTE: Including "deflist" here in order to bring in the list theory that it
;; includes, which affects the rules produced by defalist.
(include-book "deflist")
(include-book "defalist-base")
(include-book "misc/hons-help" :dir :system)

#!acl2
(progn

  (def-alistp-rule consp-when-member-equal-of-keyval-alist-p
    (implies (and (keyval-alist-p x)
                  (member-equal a x))
             (consp a))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   (:rewrite :backchain-limit-lst 0
                    :corollary (implies (and (member-equal a x)
                                             (keyval-alist-p x))
                                        (consp a))))
    :tags (:member :cons-member))

  (def-alistp-rule keytype-p-of-car-when-member-equal-of-keyval-alist-p
    (and (implies (and (keyval-alist-p x)
                       (member-equal a x))
                  (keytype-p (car a)))
         (implies (and (member-equal a x)
                       (keyval-alist-p x))
                  (keytype-p (car a))))
    :requirement (and keytype-simple (not key-negatedp))
    :tags (:member :keytype-member))

  (def-alistp-rule valtype-p-of-cdr-when-member-equal-of-keyval-alist-p
    (and (implies (and (keyval-alist-p x)
                       (member-equal a x))
                  (valtype-p (cdr a)))
         (implies (and (member-equal a x)
                       (keyval-alist-p x))
                  (valtype-p (cdr a))))
    :requirement (and valtype-simple (not val-negatedp))
    :tags (:member :valtype-member))

  (def-alistp-rule keyval-alist-p-of-make-fal
    (implies (and (keyval-alist-p x)
                  (keyval-alist-p y))
             (keyval-alist-p (make-fal x y)))))

