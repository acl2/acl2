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
(include-book "maybe-defthm")
(include-book "std/testing/assert" :dir :system)

;; Some basic tests

(maybe-defthm-as-rewrite foo (equal (car (cons x y)) x))
(maybe-defthm-as-rewrite bar (equal (not 'nil) 't))
(maybe-defthm-as-rewrite baz (equal (stringp 'nil) 'nil))

(assert! (is-theorem-p 'foo (w state)))
(assert! (not (is-theorem-p 'bar (w state))))
(assert! (not (is-theorem-p 'baz (w state))))

(assert! (let ((acl2::ens (acl2::ens state))) (active-runep '(:rewrite foo))))
(assert! (let ((acl2::ens (acl2::ens state))) (not (active-runep '(:rewrite bar)))))

(enable-if-theorem foo)

(assert! (let ((acl2::ens (acl2::ens state)))
           (active-runep '(:rewrite foo))))

(disable-if-theorem foo)

(assert! (let ((acl2::ens (acl2::ens state)))
           (not (active-runep '(:rewrite foo)))))

(enable-if-theorem foo)

(assert! (let ((acl2::ens (acl2::ens state)))
           (active-runep '(:rewrite foo))))
