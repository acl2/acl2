
; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2023 Intel Corporation

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

; Matt K. mod: Avoid ACL2(p) error from a clause-processor that returns one or
; more stobjs.
(set-waterfall-parallelism nil)

(include-book "projects/vescmul/top" :dir :system) ;; a big book; takes around 30 seconds

;; VeSCmul  may  not  always be  able  to  find  adder  components in  a  given
;; design. However, our system still supports hierarhical reasoning, and we can
;; provide hierarhical  reasoning hints to  help the  program. Below is  a demo
;; showing  how it  can  be achieved  for a  64x64-bit  multiplier with  7-to-3
;; compressor    tree.     This    module    is    given    in    this    file:
;; homma-7-to-3-64x64-signed-carry-select.v

;; 1. As  a hierarchical reasonign  hint, we offer alternative  definitions for
;; some of the  adder modules in this design. Particularly,  we redefined 7to3,
;; 6to3, 5to3,  and 4to3  compressor modules.  So first, we  create a  new file
;; contaning those better defitions.

(defwarrant str::fast-string-append-lst)
(defwarrant str::int-to-dec-string$inline)

(write-string-to-file-event
 "better-homma-7-3.v"
 ;; homma  designs for  some  reason repeat  the same  module  many times  with
 ;; different names. So below creates a  better copy of some adder modules with
 ;; a loop.
 (string-append-lst
  (append
   (loop$ for x from 0 to 123 collect
          (str::cat "module UB7_3C" (str::intstr x) " (output S1, S2, S3, input X1,X2,X3,X4,X5,X6,X7);
     assign {S1,S2,S3} = X1+X2+X3+X4+X5+X6+X7;
endmodule
"))
   (loop$ for x from 0 to 123 collect
          (str::cat "module UB6_3C" (str::intstr x) " (output S1, S2, S3, input X1,X2,X3,X4,X5,X6);
     assign {S1,S2,S3} = X1+X2+X3+X4+X5+X6;
endmodule
"))

   (loop$ for x from 0 to 123 collect
          (str::cat "module UB5_3C" (str::intstr x) " (output S1, S2, S3, input X1,X2,X3,X4,X5);
     wire car1,car2,sum1,sum2,car3;
     assign {S1,S2,S3} = X1+X2+X3+X4+X5;
endmodule
"))

   (loop$ for x from 0 to 123 collect
          (str::cat "module UB4_3C" (str::intstr x) " (output S1, S2, S3, input X1,X2,X3,X4);
     assign {S1,S2,S3} = X1+X2+X3+X4;
endmodule
")))))

;; 2.  We tell  parse-and-create-svtv to  parse the  design. This  program will
;; parse and  create two  simulation vectors  for the design.  One will  be the
;; simulation of the  original design, and the other will  be similation of the
;; design whose adder modules are  replaced with the ones in better-homma-7-3.v
;; file. verify-svtv-of-mult will later perform equivalance checking between
;; the two to make sure that the two designs are functionally equivalant.

(vescmul-parse :file "homma-7-to-3-64x64-signed-carry-select.v"
               :topmodule "Multiplier_63_0_6000"
               :name homma-7-to-3
               :modified-modules-file "better-homma-7-3.v")

;; 3. Verify the design.  verify-svtv-of-mult will perform equivalance checking
;; between  the  modified  and  original  design first  using  FGL.   For  fast
;; equivalance checking, we set up AIG transforms which will use an incremental
;; SAT     solver.      Make    sure     you     have     IPASIR    set     up:
;; https://acl2.org/doc/?topic=IPASIR____IPASIR
;; After equivalance checking, vescmul will  use the modified version to verify
;; the multiplier and  once proved, state a theorem for  the correctness of the
;; unmodified, original design.

;; set up AIG trannsforms for fast  equiv checking. Tweaking the parameters can
;; affect the proof-time result a lot.
(progn
  (local (include-book "centaur/ipasir/ipasir-backend" :dir :system))
  (local (include-book "centaur/aignet/transforms" :dir :system))
  (local (defun transforms-config ()
           (declare (Xargs :guard t))
           #!aignet
           (list (make-observability-config)
                 (make-balance-config :search-higher-levels t
                                      :search-second-lit t)
                 (change-fraig-config *fraig-default-config*
                                      :random-seed-name 'my-random-seed
                                      :ctrex-queue-limit 8
                                      :sim-words 1
                                      :ctrex-force-resim nil
                                      :ipasir-limit 4
                                      :initial-sim-rounds 2
                                      :initial-sim-words 2
                                      :ipasir-recycle-count 2000)
                 )))
  (local (defattach fgl::fgl-aignet-transforms-config transforms-config))
  (local (define monolithic-sat-with-transforms ()
           (fgl::make-fgl-satlink-monolithic-sat-config :transform t)))
  (local (defattach fgl::fgl-toplevel-sat-check-config monolithic-sat-with-transforms)))

(vescmul-verify :name homma-7-to-3
                :concl (equal p
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
