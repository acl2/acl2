; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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

(include-book "svtv-to-fsm")
(include-book "svtv-generalize")
(include-book "centaur/fgl/top" :dir :system)
(include-book "svtv-stobj-defsvtv")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/vl/top" :dir :system)
(include-book "oslib/ls" :dir :system)
(include-book "svtv-stobj-debug")
; cert_param: (uses-glucose)

(defconsts (*vl-design* state)
  (b* (((mv (vl::vl-loadresult loadres) state)
        (vl::vl-load (vl::make-vl-loadconfig :start-files '("svtv_to_fsm_test_counter.sv")))))
    (mv loadres.design state)))

(defconsts (*sv-design* *vl-good* *vl-bad*)
  (b* (((mv errmsg svex good bad)
        (vl::vl-design->sv-design "counter" *vl-design* (vl::make-vl-simpconfig))))
    (and errmsg
         (raise "~@0~%" errmsg))
    (mv svex good bad)))


(defsvtv$ counter-invar0-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" sum1 :cond sum1-ovr)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(def-svtv-data-export counter-invar0-run-data)

(def-svtv-refinement counter-invar0-run counter-invar0-run-data
  :svtv-spec counter-invar0-spec :inclusive-overridekeys t
  :fsm counter-fsm :define-fsm t)

(value-triple (acl2::tshell-ensure))

(def-svtv-generalized-thm counter-invar0-svtv-thm
  :svtv counter-invar0-run
  :svtv-spec counter-invar0-spec
  :input-vars :all
  :output-vars (sum-out sum1-out)
  :unsigned-byte-hyps t
  :override-vars (sum)
  :spec-override-vars (sum1)
  :hyp (and (<= sum 11)
            (<= sum1 10))
  :concl (and (<= sum-out 11)
              (<= sum1-out 10)))


(def-svtv-to-fsm-thm counter-invar0-fsm-thm
  :svtv-spec-thmname counter-invar0-svtv-thm)

(def-svtv-to-fsm-thm counter-invar0-fsm-thm2
  :svtv-spec-thmname counter-invar0-svtv-thm
  :eliminate-override-vars (sum1))





(defsvtv$ counter-invar1-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" sum1)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(def-svtv-data-export counter-invar1-run-data)

(def-svtv-refinement counter-invar1-run counter-invar1-run-data
  :svtv-spec counter-invar1-spec
  :inclusive-overridekeys t
  :fsm counter-fsm)



(def-svtv-generalized-thm counter-invar1-svtv-thm
  :svtv counter-invar1-run
  :svtv-spec counter-invar1-spec
  :input-vars :all
  :output-vars (sum-out sum1-out)
  :unsigned-byte-hyps t
  :override-vars (sum)
  :spec-override-vars ()
  :hyp (and (<= sum 11)
            (<= sum1 10))
  :concl (and (<= sum-out 11)
              (<= sum1-out 10)))

(def-svtv-to-fsm-thm counter-invar1-fsm-thm
  :svtv-spec-thmname counter-invar1-svtv-thm)

(def-svtv-to-fsm-thm counter-invar1-fsm-thm2
  :svtv-spec-thmname counter-invar1-svtv-thm
  ;; BOZO we should only have to specify one of these
  :eliminate-override-vars (sum1)
  :eliminate-override-signals ("sum1"))



(defsvtv$ counter-invar2-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" 5)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(def-svtv-data-export counter-invar2-run-data)

(def-svtv-refinement counter-invar2-run counter-invar2-run-data
  :svtv-spec counter-invar2-spec
  :fsm counter-fsm
  :inclusive-overridekeys t)



(def-svtv-generalized-thm counter-invar2-svtv-thm
  :svtv counter-invar2-run
  :svtv-spec counter-invar2-spec
  :input-vars :all
  :output-vars (sum-out sum1-out)
  :unsigned-byte-hyps t
  :override-vars (sum)
  :spec-override-vars ()
  :hyp (and (<= sum 11)
            ;; (<= sum1 10)
            )
  :concl (and (<= sum-out 11)
              (<= sum1-out 10)))

(def-svtv-to-fsm-thm counter-invar2-fsm-thm
  :svtv-spec-thmname counter-invar2-svtv-thm)

(def-svtv-to-fsm-thm counter-invar2-fsm-thm2
  :svtv-spec-thmname counter-invar2-svtv-thm
  :eliminate-override-signals ("sum1"))

