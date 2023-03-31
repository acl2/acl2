
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

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

;; for correctness proof
(include-book "projects/rp-rewriter/lib/mult3/svtv-top" :dir :system)

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

;; Get the svtv so the design can be simulated.
(sv::defsvtv mult-run
  :mod *sv-design*
  :inputs '(("IN1" a)
            ("IN2" b))
  :outputs
  '(("result" res)))

; Matt K. mod: Avoid ACL2(p) error from a clause-processor that returns one or
; more stobjs.
(set-waterfall-parallelism nil)

;; takes around 1-1.5 seconds.
(defthmrp-multiplier multiplier-correct
  (implies (and (integerp a)
                (integerp b))
           (b* (((sv::assocs res)
                 (sv::svtv-run (mult-run)
                               `((a . ,a)
                                 (b . ,b)))))
             (equal res
                    (loghead 128 (* (logext 64 a)
                                    (logext 64 b)))))))
