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

(include-book "svtv-spec")
(include-book "svtv-stobj-export")
(local (include-book "std/lists/take" :dir :system))


(encapsulate nil
  (local (defthm svex-alist-eval-equiv!-redef
           (Equal (svex-alist-eval-equiv! x y)
                  (and (svex-alist-eval-equiv x y)
                       (equal (svex-alist-keys x) (svex-alist-keys y))))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv!-when-svex-alist-eval-equiv)))))

  (defthm cycle-fsm-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->cycle-fsm-validp x)
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  ((base-fsm x.phase-fsm))
                  ((base-fsm x.cycle-fsm)))
               (base-fsm-eval-equiv x.cycle-fsm
                                    (base-fsm-to-cycle x.cycle-phases x.phase-fsm nil))))
    :hints (("goal" :in-theory (e/d (base-fsm-eval-equiv
                                     base-fsm-to-cycle)))
            (and stable-under-simplificationp
                 `(:expand ((:with svex-alist-eval-equiv-in-terms-of-envs-equivalent
                             ,(car (last clause)))))))))

(define svtv-data-obj->spec ((x svtv-data-obj-p))
  :returns (spec svtv-spec-p)
  (b* (((svtv-data-obj x))
       ((pipeline-setup x.pipeline-setup)))
    (make-svtv-spec :fsm x.phase-fsm
                    :cycle-phases x.cycle-phases
                    :namemap x.namemap
                    :probes x.pipeline-setup.probes
                    :in-alists x.pipeline-setup.inputs
                    :override-test-alists x.pipeline-setup.override-tests
                    :override-val-alists x.pipeline-setup.override-vals
                    :initst-alist x.pipeline-setup.initst))
  ///
  (local (include-book "centaur/bitops/floor-mod" :dir :system))
  (local (defun count-down (y)
           (if (zp y) y (count-down (1- y)))))
  (local (defthm mod-of-*-self
           (implies (and (natp x) (natp y))
                    (equal (mod (* x y) x) 0))
           :hints (("goal" 
                    :induct (count-down y)
                    :expand ((:with acl2::mod-redef (mod (* x y) x))
                             (:with acl2::mod-redef (mod 0 x)))))))
  
  (defret svtv-spec-run-of-<fn>
    (b* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    x.flatten-validp
                    (svtv-cyclephaselist-has-outputs-captured x.cycle-phases))
               (svex-envs-equivalent (svex-alist-eval x.pipeline env)
                                     (svtv-spec-run spec env))))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svtv-spec-phase-outs->pipe-out
                                      svtv-spec-pipe-env->phase-envs
                                      svtv-fsm-run-is-base-fsm-run
                                      base-fsm-run
                                      base-fsm-eval-of-svtv-fsm->renamed-fsm
                                      )))))
