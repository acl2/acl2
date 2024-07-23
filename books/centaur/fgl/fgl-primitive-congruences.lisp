; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2024 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "FGL")

(include-book "congruence-rules")
(include-book "arith-base")
(include-book "syntax-bind")

(local (in-theory (enable fgl-time-fn
                          fgl-sat-check
                          fgl-vacuity-check
                          fgl-prove-fn
                          show-counterexample
                          show-top-counterexample
                          run-counterexample)))

(defcong unequiv equal (fgl-time-fn time-val x) 1)
(add-fgl-congruence unequiv-implies-equal-fgl-time-fn-1)

(defcong unequiv equal (fgl-sat-check params x) 1)
(add-fgl-congruence unequiv-implies-equal-fgl-sat-check-1)

(defcong unequiv equal (fgl-vacuity-check params x) 1)
(add-fgl-congruence unequiv-implies-equal-fgl-vacuity-check-1)

(defcong unequiv equal (fgl-prove-fn params msg x stop-on-ctrex stop-on-fail) 1)
(defcong unequiv equal (fgl-prove-fn params msg x stop-on-ctrex stop-on-fail) 2)
(defcong unequiv equal (fgl-prove-fn params msg x stop-on-ctrex stop-on-fail) 4)
(defcong unequiv equal (fgl-prove-fn params msg x stop-on-ctrex stop-on-fail) 5)
(add-fgl-congruence unequiv-implies-equal-fgl-prove-fn-1)
(add-fgl-congruence unequiv-implies-equal-fgl-prove-fn-2)
(add-fgl-congruence unequiv-implies-equal-fgl-prove-fn-4)
(add-fgl-congruence unequiv-implies-equal-fgl-prove-fn-5)

(defcong unequiv equal (show-counterexample params msg) 1)
(defcong unequiv equal (show-counterexample params msg) 2)
(add-fgl-congruence unequiv-implies-equal-show-counterexample-1)
(add-fgl-congruence unequiv-implies-equal-show-counterexample-2)


(defcong unequiv equal (show-top-counterexample params msg) 1)
(defcong unequiv equal (show-top-counterexample params msg) 2)
(add-fgl-congruence unequiv-implies-equal-show-top-counterexample-1)
(add-fgl-congruence unequiv-implies-equal-show-top-counterexample-2)

(defcong unequiv equal (run-counterexample params msg) 1)
(defcong unequiv equal (run-counterexample params msg) 2)
(add-fgl-congruence unequiv-implies-equal-run-counterexample-1)
(add-fgl-congruence unequiv-implies-equal-run-counterexample-2)
