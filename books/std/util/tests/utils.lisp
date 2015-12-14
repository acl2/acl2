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
(include-book "../look-up")

(defmacro assert-disabled (fn)
  `(make-event
    (b* ((acl2::ens (acl2::ens state))
         ((when (active-runep '(:definition ,fn)))
          (er soft 'assert-disabled "Function ~x0 is enabled (expected disabled)!" ',fn)))
      (value '(value-triple :success)))))

(defmacro assert-enabled (fn)
  `(make-event
    (b* ((acl2::ens (acl2::ens state))
         ((when (active-runep '(:definition ,fn)))
          (value '(value-triple :success))))
      (er soft 'assert-enabled "Function ~x0 is disabled (expected enabled)!" ',fn))))

(assert-enabled binary-append)

(local (defund disabled-fn (x) x))
(local (assert-disabled disabled-fn))

(defmacro assert-logic-mode (fn)
  `(make-event
    (if (logic-mode-p ',fn (w state))
        (value '(value-triple :success))
      (er soft 'assert-logic-mode "Function ~x0 is program mode (expected logic)!" ',fn))))

(defmacro assert-program-mode (fn)
  `(make-event
    (if (logic-mode-p ',fn (w state))
        (er soft 'assert-program-mode "Function ~x0 is logic mode (expected program)!" ',fn)
      (value '(value-triple :success)))))

(assert-logic-mode binary-append)

(local (defun program-fn (x) (declare (xargs :mode :program)) x))
(local (assert-program-mode program-fn))

(defmacro assert-guard-verified (fn)
  `(make-event
    (if (eq (fgetprop ',fn 'acl2::symbol-class nil (w state)) :common-lisp-compliant)
        (value '(value-triple :success))
      (er soft 'assert-guard-verified "Function ~x0 is not guard verified!" ',fn))))

(defmacro assert-guard-unverified (fn)
  `(make-event
    (if (eq (fgetprop ',fn 'acl2::symbol-class nil (w state)) :common-lisp-compliant)
        (er soft 'assert-guard-verified "Function ~x0 is unexpectedly guard verified!" ',fn)
      (value '(value-triple :success)))))

(local (assert-guard-verified binary-append))
(local (defun unverified-fn (x) (declare (xargs :verify-guards nil)) x))
(local (assert-guard-unverified unverified-fn))
(local (verify-guards unverified-fn))
(local (assert-guard-verified unverified-fn))
