; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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

(in-package "SV")

(include-book "../svex/override-transparency-and-monotonicity")
(include-book "../svex/override-transparency-and-ovmonotonicity")
(include-book "fsm-base")
(local (include-book "std/lists/sets" :dir :system))


(define fsm-overridekey-transparent-p ((x fsm-p)
                                            (overridekeys svarlist-p))
  (b* (((fsm x)))
    (and (ec-call (svex-alist-overridekey-transparent-p x.values overridekeys x.values))
         (ec-call (svex-alist-overridekey-transparent-p x.nextstate overridekeys x.values))))
  ///
  (defcong set-equiv equal (fsm-overridekey-transparent-p x overridekeys) 2)

  (defthm fsm-overridekey-transparent-p-of-svarlist-change-override
    (equal (fsm-overridekey-transparent-p x (svarlist-change-override overridekeys type))
           (fsm-overridekey-transparent-p x overridekeys))))

(define fsm-ovmonotonic ((x fsm-p))
  (b* (((fsm x)))
    (and (ec-call (svex-alist-ovmonotonic x.values))
         (ec-call (svex-alist-ovmonotonic x.nextstate)))))

(define fsm-ovcongruent ((x fsm-p))
  (b* (((fsm x)))
    (and (ec-call (svex-alist-ovcongruent x.values))
         (ec-call (svex-alist-ovcongruent x.nextstate)))))


(define fsm-<<= ((x fsm-p) (y fsm-p))
  (b* (((fsm x)) ((fsm y)))
    (and (ec-call (svex-alist-<<= x.values y.values))
         (ec-call (svex-alist-<<= x.nextstate y.nextstate)))))

(define overridekeys-envlists-ok ((overridekeys svarlist-p)
                                  (impl-envs svex-envlist-p)
                                  (spec-envs svex-envlist-p)
                                  (spec-outs svex-envlist-p))
  :guard (eql (len spec-envs) (len spec-outs))
  :returns (ok)
  :measure (len spec-envs)
  (if (atom spec-envs)
      (atom impl-envs)
    (and (overridekeys-envs-ok overridekeys (car impl-envs) (car spec-envs) (car spec-outs))
         (overridekeys-envlists-ok overridekeys (cdr impl-envs) (cdr spec-envs) (cdr spec-outs)))))

(define overridekeys-envlists-agree* ((overridekeys svarlist-p)
                                      (impl-envs svex-envlist-p)
                                      (spec-envs svex-envlist-p)
                                      (spec-outs svex-envlist-p))
  :guard (eql (len spec-envs) (len spec-outs))
  :returns (ok)
  :measure (len spec-envs)
  (if (atom spec-envs)
      (atom impl-envs)
    (and (consp impl-envs)
         (overridekeys-envs-agree* overridekeys (car impl-envs) (car spec-envs) (car spec-outs))
         (overridekeys-envlists-agree* overridekeys (cdr impl-envs) (cdr spec-envs) (cdr spec-outs)))))
