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
(include-book "svtv-fsm-ideal")

(include-book "svtv-data-obj-spec")
(include-book "override-common")
(include-book "../svex/override-mux")
(include-book "centaur/misc/hons-extra" :dir :system)

(local (std::add-default-post-define-hook :fix))

(defxdoc svtv-idealize-internals
  :short "Umbrella topic for internal concepts used in the proofs for the svtv-idealize framework."
  :parents (svtv-idealize))


;; (define 4vec-override-values-ok-<<= ((test 4vec-p)
;;                                      (val 4vec-p)
;;                                      (ref 4vec-p))
;;   (4vec-<<= (4vec-bit?! test val 0)
;;             (4vec-bit?! test ref 0))
;;   ///
;;   (defthm 4vec-override-values-ok-<<=-of-x-val
;;     (equal (4vec-override-values-ok-<<= test (4vec-x) ref)
;;            t)
;;     :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

;;   (defthm 4vec-override-values-ok-<<=-of-x-test
;;     (equal (4vec-override-values-ok-<<= (4vec-x) val ref)
;;            t)
;;     :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

;;   (defthm 4vec-override-values-ok-of-greater-ref
;;     (implies (and (4vec-override-values-ok-<<= test val ref1)
;;                   (4vec-<<= ref1 ref2))
;;              (4vec-override-values-ok-<<= test val ref2))
;;     :hints(("Goal" :in-theory (enable 4vec-<<=-transitive-1)))))



(define svtv-data-obj->ideal-spec ((x svtv-data-obj-p))
  :returns (spec svtv-spec-p)
  :non-executable t
  :guard (non-exec (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                        (svtv-data-obj->flatten-validp x)))
  :guard-hints (("goal" :in-theory (enable design-flatten-okp)))
  (b* (((svtv-data-obj x))
       ((pipeline-setup x.pipeline-setup)))
    (make-svtv-spec :fsm (design->ideal-fsm x.design x.phase-fsm-setup)
                    :cycle-phases x.cycle-phases
                    :namemap x.namemap
                    :probes x.pipeline-setup.probes
                    :in-alists x.pipeline-setup.inputs
                    :override-test-alists x.pipeline-setup.override-tests
                    :override-val-alists x.pipeline-setup.override-vals                    
                    :initst-alist x.pipeline-setup.initst))
  ///
  (defret fields-of-<fn>
    (b* (((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup)))
      (and (equal spec.fsm (design->ideal-fsm x.design x.phase-fsm-setup))
           (equal spec.cycle-phases x.cycle-phases)
           (equal spec.namemap x.namemap)
           (equal spec.probes x.pipeline-setup.probes)
           (equal spec.in-alists x.pipeline-setup.inputs)
           (equal spec.override-test-alists x.pipeline-setup.override-tests)
           (equal spec.override-val-alists x.pipeline-setup.override-vals)                 
           (equal spec.initst-alist x.pipeline-setup.initst)))))



