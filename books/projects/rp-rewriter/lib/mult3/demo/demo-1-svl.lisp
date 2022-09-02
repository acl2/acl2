
; MULTIPLIER RULES

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

;; To load the verilog designs:
(include-book "centaur/sv/top" :dir :system) ;; a big book; takes around 30 seconds
(include-book "centaur/vl/loader/top" :dir :system) ;; takes around 10 seconds
(include-book "oslib/ls" :dir :system)

(include-book "centaur/svl/top" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

;; for correctness proof
(include-book "projects/rp-rewriter/lib/mult3/svl-top" :dir :system)

;; load VL design for the modules in DT_SB4_HC_64_64_multgen.sv
;; this is a 64x64 Signed, Booth radix-4 encoded, Dadda Tree integer multiplier
(acl2::defconsts
 (*vl-design* state)
 (b* (((mv loadresult state)
       (vl::vl-load (vl::make-vl-loadconfig
                     :start-files '("DT_SB4_HC_64_64_multgen.sv")))))
   (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design
(acl2::defconsts
 (*sv-design*
  *simplified-good*
  *simplified-bad*)
 (b* (((mv errmsg sv-design good bad)
       (vl::vl-design->sv-design "DT_SB4_HC_64_64"
                                 *vl-design* (vl::make-vl-simpconfig))))
   (and errmsg
        (acl2::raise "~@0~%" errmsg))
   (mv sv-design good bad)))

;; Load SVL design ;; takes less than a second
(acl2::defconsts (*svl-design* rp::rp-state)
                 (svl::svl-flatten-design *sv-design*
                                          *vl-design*
                                          :dont-flatten :all))



;; in/out lemma for full adder
;; def-rp-rule is the same as defthm but saves the rule in rp-rewriter's ruleset
(def-rp-rule svl-run-phase-of-FullAdder
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (svl::svl-run-phase-wog "fa"
                                          (list x y z)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (s-c-spec (list x y z))
                      svl::*empty-state*)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))

(def-rp-rule svl-run-phase-of-HalfAdder
  (implies (and (bitp x)
                (bitp y))
           (equal (svl::svl-run-phase-wog "ha"
                                          (list x y)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (s-c-spec (list x y))
                      svl::*empty-state*)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))

; Matt K. mod: Avoid ACL2(p) error from a clause-processor that returns one or
; more stobjs.
(set-waterfall-parallelism nil)

;; Lemma for final stage adder.
(defthmrp final-stage-adder-correct
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog "HC_128"
                                          (list in1 in2)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (list (loghead 129 (+ (loghead 128 in1)
                                            (loghead 128 in2))))
                      svl::*empty-state*)))
  :disable-meta-rules (s-c-spec-meta)
  :enable-rules rp::*adder-rules*)

(progn
  (defconst *input-bindings*
    '(("IN1" a)
      ("IN2" b)))

  (defconst *out-bindings*
    '(("result" out)))

  ;; A way to state correctness proof for the multiplier.
  ;; Similar to SVTV-run
  ;; takes around 1.5 seconds
  (defthmrp multiplier-correct-v1
    (implies (and (integerp in1)
                  (integerp in2))
             (equal (svl::svl-run "DT_SB4_HC_64_64"
                                  `((a . ,in1)
                                    (b . ,in2))
                                  *input-bindings*
                                  *out-bindings*
                                  *svl-design*)
                    `((out . ,(loghead 128 (* (sign-ext in1 64)
                                              (sign-ext in2 64)))))))))

;; Another Way to state the final correctness theorem.  Less user-friendly but
;; if you want to use this proof hierarchically, this is better.
;; takes arond 1.5 seconds
(defthmrp multiplier-correct-v2
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog "DT_SB4_HC_64_64"
                                          (list in1 in2)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv  (list (loghead 128 (* (sign-ext in1 64)
                                             (sign-ext in2 64))))
                       svl::*empty-state*))))
