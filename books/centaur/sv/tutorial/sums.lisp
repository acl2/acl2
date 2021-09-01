; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
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

(in-package "SV")

;; Placeholder for a tutorial on using aignet transforms such as fraiging,
;; observability, balance.  So far we show the basic events but don't document
;; much and don't describe why each of the transforms are useful.

(include-book "../top")
(include-book "support")
(include-book "centaur/gl/bfr-fraig-satlink" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/ipasir/ipasir-backend" :dir :system)
(include-book "oslib/top" :dir :system)

;; (local (include-book "centaur/esim/stv/stv-decomp-proofs-even-better" :dir :system))
; (depends-on "sums.sv")
; cert_param: (uses-glucose)
; cert_param: (uses-ipasir)
(value-triple (acl2::set-max-mem (* 3 (expt 2 30))))
(value-triple (acl2::tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (f-get-global 'acl2::parallel-execution-enabled state)
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))
(local (include-book "centaur/aig/g-aig-eval" :dir :system))
(local (gl::def-gl-clause-processor sums-glcp))

(local (include-book "centaur/vl/loader/top" :dir :system))


(defconsts (*sums* state)
  (b* (((mv loadres state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files (list "sums.sv"))))
       (design (vl::vl-loadresult->design loadres))
       ((mv ?err svdesign ?good ?bad)
        (vl::cwtime (vl::vl-design->svex-design "shifted_sums" design (vl::make-vl-simpconfig)))))
    (and err
         (er hard? 'sums "Error: ~@0~%Warnings: ~s1~%" err
             (vl::vl-reportcard-to-string (vl::vl-design-reportcard bad))))
    (mv svdesign state)))


(defsvtv sums-run
  :design *sums*
  :inputs '(("a" a)
            ("b" b)
            ("shift" shift))
  :outputs '(("sum" sum)))


(define sums-spec-aux ((n natp)
                       (a natp)
                       (b natp)
                       (shift natp))
  :returns (sum natp :rule-classes :type-prescription)
  (b* (((when (zp n)) 0)
       (i (1- n))
       (shifted (nth-slice 8 (loghead 4 (+ shift i)) b))
       (prod (loghead 8 (* shifted (nth-slice 8 i a))))
       (rest (sums-spec-aux (1- n) a b shift)))
    (+ prod rest)))

(define sums-spec ((a natp)
                   (b natp)
                   (shift natp))
  :returns (sum natp :rule-classes :type-prescription)
  (loghead 16 (sums-spec-aux 16 a b shift)))



(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose -model"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach gl::gl-satlink-config my-glucose-config)))



;; (local (setup-satlink))
(local (gl::gl-simplify-satlink-mode))

(value-triple (clear-memoize-statistics))

(encapsulate nil
  (local (defun transforms-config ()
           (declare (Xargs :guard t))
           #!aignet
           (list (make-prune-config :gatesimp (default-gatesimp))
                 (make-constprop-config)

                 (make-balance-config :search-higher-levels t
                                      :search-second-lit t)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :sim-words 1
                                      :ctrex-force-resim nil
                                      :ipasir-limit 1)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :ipasir-limit 20))))
  (local (defattach gl::gl-transforms-config transforms-config))

  ;; With shift assumed to be 0, using either the observability or constprop
  ;; transforms before fraiging suffices to reduce the problem from about 140
  ;; sec to about 8 sec.  Without either of these, fraiging doesn't achieve
  ;; much reduction (9616 to 7807 gates in the first pass).  Constprop itself
  ;; reduces the network from 9692 post-prune to 5098 gates, balance to 5002,
  ;; fraiging first pass to 4435, second pass to 0.  Observability reduces the
  ;; network from 9692 post-prune to 9230, balance to 9159, fraiging to 4370,
  ;; second pass to 0 -- constprop is marginally faster.

  (gl::def-gl-thm sums-correct-when-shift-0
    :hyp (sums-run-autohyps)
    :concl (implies (equal shift 0)
                    (b* ((spec (sums-spec a b 0))
                         (impl (cdr (assoc 'sum (svtv-run (sums-run)
                                                          (sums-run-autoins))))))
                      (cw "a:     ~s0~%" (str::hexify a))
                      (cw "b:     ~s0~%" (str::hexify b))
                      (cw "shift: ~s0~%" (str::hexify shift))
                      (cw "spec:  ~s0~%" (str::hexify spec))
                      (cw "impl:  ~s0~%" (str::hexify impl))
                      (equal impl spec)))
    :g-bindings (sums-run-autobinds)))


(encapsulate nil
  (local (defun transforms-config ()
           (declare (Xargs :guard t))
           #!aignet
           (list (make-prune-config :gatesimp (default-gatesimp))
                 (make-observability-config)

                 (make-balance-config :search-higher-levels t
                                      :search-second-lit t)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :sim-words 1
                                      :ctrex-force-resim nil
                                      :ipasir-limit 1)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :ipasir-limit 20))))
  (local (defattach gl::gl-transforms-config transforms-config))

  ;; With shift assumed to be either 0 or 15, using constprop doesn't reduce
  ;; much because none of those bits are constant.  Observability still does
  ;; the job nicely, however -- this solves in about 9 sec, versus 226 sec with
  ;; constprop instead of observability.

  (gl::def-gl-thm sums-correct-when-shift-0-or-1
    :hyp (sums-run-autohyps)
    :concl (implies (or (equal shift 0)
                        (equal shift #xf))
                    (b* ((spec (sums-spec a b (if (eql shift #xf) #xf 0)))
                         (impl (cdr (assoc 'sum (svtv-run (sums-run)
                                                          (sums-run-autoins))))))
                      (cw "a:     ~s0~%" (str::hexify a))
                      (cw "b:     ~s0~%" (str::hexify b))
                      (cw "shift: ~s0~%" (str::hexify shift))
                      (cw "spec:  ~s0~%" (str::hexify spec))
                      (cw "impl:  ~s0~%" (str::hexify impl))
                      (equal impl spec)))
    :g-bindings (sums-run-autobinds)))

(encapsulate nil
  (local (defun transforms-config ()
           (declare (Xargs :guard t))
           #!aignet
           (list (make-prune-config :gatesimp (default-gatesimp))

                 (make-balance-config :search-higher-levels t
                                      :search-second-lit t)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :sim-words 1
                                      :ctrex-force-resim nil
                                      :ipasir-limit 1)

                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 32
                                      :ipasir-limit 20))))
  (local (defattach gl::gl-transforms-config transforms-config))

  ;; This version doesn't require observability or constprop, just fraiging --
  ;; but it illustrates how important fraiging is relative to relying only on
  ;; SAT at the top level.  Fraiging solves in 9 sec -- omitting fraiging made
  ;; it take 16 minutes.
  
  (gl::def-gl-thm sums-correct
    :hyp (sums-run-autohyps)
    :concl (b* ((spec (sums-spec a b shift))
                (impl (cdr (assoc 'sum (svtv-run (sums-run)
                                                 (sums-run-autoins))))))
             (cw "a:     ~s0~%" (str::hexify a))
             (cw "b:     ~s0~%" (str::hexify b))
             (cw "shift: ~s0~%" (str::hexify shift))
             (cw "spec:  ~s0~%" (str::hexify spec))
             (cw "impl:  ~s0~%" (str::hexify impl))
             (equal impl spec))
    :g-bindings (sums-run-autobinds)))
