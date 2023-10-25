
; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2023 Intel Corporation

; Redistribution  and  use  in  source   and  binary  forms,  with  or  without
; modification, are permitted provided that the following conditions are met:

; o Redistributions of source code must retain the above copyright notice, this
;   list of conditions and the following disclaimer.

; o Redistributions in  binary form must reproduce the  above copyright notice,
;   this list of  conditions and the following disclaimer  in the documentation
;   and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its contributors
;   may  be used  to endorse  or promote  products derived  from this  software
;   without specific prior written permission.

; THIS SOFTWARE IS  PROVIDED BY THE COPYRIGHT HOLDERS AND  CONTRIBUTORS "AS IS"
; AND ANY  EXPRESS OR IMPLIED  WARRANTIES, INCLUDING,  BUT NOT LIMITED  TO, THE
; IMPLIED WARRANTIES  OF MERCHANTABILITY AND  FITNESS FOR A  PARTICULAR PURPOSE
; ARE DISCLAIMED.  IN NO EVENT  SHALL THE  COPYRIGHT HOLDER OR  CONTRIBUTORS BE
; LIABLE  FOR   ANY  DIRECT,  INDIRECT,  INCIDENTAL,   SPECIAL,  EXEMPLARY,  OR
; CONSEQUENTIAL  DAMAGES  (INCLUDING,  BUT   NOT  LIMITED  TO,  PROCUREMENT  OF
; SUBSTITUTE GOODS  OR SERVICES;  LOSS OF  USE, DATA,  OR PROFITS;  OR BUSINESS
; INTERRUPTION)  HOWEVER CAUSED  AND ON  ANY  THEORY OF  LIABILITY, WHETHER  IN
; CONTRACT,  STRICT  LIABILITY, OR  TORT  (INCLUDING  NEGLIGENCE OR  OTHERWISE)
; ARISING IN ANY  WAY OUT OF THE USE  OF THIS SOFTWARE, EVEN IF  ADVISED OF THE
; POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>, <mert.temel@intel.com>

(in-package "RP")

;; To load the verilog designs:
(include-book "centaur/sv/top" :dir :system) ;; a big book; takes around 30 seconds
(include-book "centaur/vl/loader/top" :dir :system) ;; takes around 10 seconds
(include-book "oslib/ls" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

(set-waterfall-parallelism nil)

;; for correctness proof of multiplier
(include-book "projects/vescmul/svtv-top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example:   integrated_multipliers.sv  (Multiply-accumulate,   Dot-product,
;; Four-lane mult with truncation) (sequential or combinational)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Load VL Design.
(acl2::defconsts
  (*mult2-vl-design* state)
  (b* (((mv loadresult state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files '("integrated_multipliers.sv")))))
    (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
  (*mult2-sv-design*)
  (b* (((mv errmsg sv-design & &)
        (vl::vl-design->sv-design "Integrated_Multiplier"
                                  *mult2-vl-design*
                                  (vl::make-vl-simpconfig))))
    (and errmsg
         (acl2::raise "~@0~%" errmsg))
    sv-design))

;; We read the comments given in the integrated_multipliers.sv file,
;; and create the function below in order to calculate the value of "mode"
;; in a user-friendly fashion.  This  helps determine  the value  of
;; "mode" signal in the Integrated_Multiplier module.
(define control-mode (&key
                      (acc-on 'nil)
                      (reload-acc 'nil)
                      (signed 'nil)
                      (dot-product 'nil)
                      (four-lanes-lo 'nil)
                      (four-lanes-hi 'nil)
                      (one-lane 'nil))
  (b* (((unless (= 1 (+ (if dot-product 1 0)
                        (if four-lanes-lo 1 0)
                        (if four-lanes-hi 1 0)
                        (if one-lane 1 0))))
        (or (cw "one and only one of dot-product, four-lanes-lo,
four-lanes-hi and one-lane should be set to 1.~%")
            (hard-error 'control-mode "" nil)
            0))
       (mode 0)
       (mode (svl::sbits 0 1 (if acc-on 0 1) mode))
       (mode (svl::sbits 1 1 (if reload-acc 0 1) mode))
       (mode (svl::sbits 2 1 (if signed 0 1) mode))
       (mode
        (cond (dot-product   (svl::sbits 3 2 0 mode))
              (four-lanes-lo (svl::sbits 3 2 1 mode))
              (four-lanes-hi (svl::sbits 3 2 2 mode))
              (t             (svl::sbits 3 2 3 mode)))))
    mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 1 - Mode = one-lane: Signed One lane (64x64-bit) multiplication
(sv::defsvtv one-lane-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '(("clk" 0)
            ("IN1" in1)
            ("IN2" in2)
            ("IN3" in3)
            ("mode" mode))
  :outputs
  '(("result" result)))

;; above  event creates  the function  "one-lane-mult2-svtv-autoins-fn". If  we
;; choose  to use  it  in the  proof  below, then  we  should have  RP-Rewriter
;; recognize its definition rule.
(add-rp-rule one-lane-mult2-svtv-autoins-fn)

(defthmrp-multiplier signed-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (sv::svtv-run (one-lane-mult2-svtv)
                                (one-lane-mult2-svtv-autoins
                                 :mode (control-mode :one-lane t
                                                     :signed t)))
                  `((result . ,(loghead 128 (+ (* (logext 64 in1)
                                                  (logext 64 in2))
                                               in3)))))))

;; Unsigned One lane (64x64-bit) multiplication
(defthmrp-multiplier unsigned-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (sv::svtv-run (one-lane-mult2-svtv)
                                (one-lane-mult2-svtv-autoins
                                 :mode (control-mode :one-lane t
                                                     :signed nil)))
                  `((result . ,(loghead 128 (+ (* (loghead 64 in1)
                                                  (loghead 64 in2))
                                               in3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2 - Mode = dot-product. Dot Product (combinational)
(sv::defsvtv dotproduct-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '(("clk" 0)
            ("IN1[31:0]" in1_0)
            ("IN2[31:0]" in2_0)
            ("IN1[63:32]" in1_1)
            ("IN2[63:32]" in2_1)
            ("IN1[95:64]" in1_2)
            ("IN2[95:64]" in2_2)
            ("IN1[127:96]" in1_3)
            ("IN2[127:96]" in2_3)
            ("IN3" in3)
            ("mode" mode))
  :outputs '(("result" result)))

(add-rp-rule dotproduct-mult2-svtv-autoins-fn)

(defthmrp-multiplier
  signed-dot-product-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in1_1)
                (integerp in2_1)
                (integerp in1_2)
                (integerp in2_2)
                (integerp in1_3)
                (integerp in2_3)
                (integerp in3))
           (equal (sv::svtv-run (dotproduct-mult2-svtv)
                                (dotproduct-mult2-svtv-autoins
                                 :mode (control-mode :dot-product t
                                                     :signed t)))
                  `((result . ,(loghead 128 (+ (* (logext 32 in1_0)
                                                  (logext 32 in2_0))
                                               (* (logext 32 in1_1)
                                                  (logext 32 in2_1))
                                               (* (logext 32 in1_2)
                                                  (logext 32 in2_2))
                                               (* (logext 32 in1_3)
                                                  (logext 32 in2_3))
                                               in3)))))))

;; Unsigned
(defthmrp-multiplier
  unsigned-dot-product-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in1_1)
                (integerp in2_1)
                (integerp in1_2)
                (integerp in2_2)
                (integerp in1_3)
                (integerp in2_3)
                (integerp in3))
           (equal (sv::svtv-run (dotproduct-mult2-svtv)
                                (dotproduct-mult2-svtv-autoins
                                 :mode (control-mode :dot-product t
                                                     :signed nil)))
                  `((result . ,(loghead 128 (+ (* (loghead 32 in1_0)
                                                  (loghead 32 in2_0))
                                               (* (loghead 32 in1_1)
                                                  (loghead 32 in2_1))
                                               (* (loghead 32 in1_2)
                                                  (loghead 32 in2_2))
                                               (* (loghead 32 in1_3)
                                                  (loghead 32 in2_3))
                                               in3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 3 - mode = four-lanes-lo: Four Lanes Truncate Lower Half
(sv::defsvtv four-lanes-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '(("clk" 0)
            ("IN1[31:0]"   in1_0)
            ("IN2[31:0]"   in2_0)
            ("IN1[63:32]"  in1_1)
            ("IN2[63:32]"  in2_1)
            ("IN1[95:64]"  in1_2)
            ("IN2[95:64]"  in2_2)
            ("IN1[127:96]" in1_3)
            ("IN2[127:96]" in2_3)
            ("IN3[31:0]"   in3_0)
            ("IN3[63:32]"  in3_1)
            ("IN3[95:64]"  in3_2)
            ("IN3[127:96]" in3_3)
            ("mode"        mode))
  :outputs '(("result[31:0]"   result0)
             ("result[63:32]"  result1)
             ("result[95:64]"  result2)
             ("result[127:96]" result3)))

(add-rp-rule four-lanes-mult2-svtv-autoins-fn)

(defthmrp-multiplier
  signed-four-lanes-lo-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in3_0)

                (integerp in1_1)
                (integerp in2_1)
                (integerp in3_1)

                (integerp in1_2)
                (integerp in2_2)
                (integerp in3_2)

                (integerp in1_3)
                (integerp in2_3)
                (integerp in3_3))
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (control-mode :four-lanes-lo t
                                                     :signed t)))
                  `((result0 . ,(loghead 32 (+ (* (logext 32 in1_0)
                                                  (logext 32 in2_0))
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (* (logext 32 in1_1)
                                                  (logext 32 in2_1))
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (* (logext 32 in1_2)
                                                  (logext 32 in2_2))
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (* (logext 32 in1_3)
                                                  (logext 32 in2_3))
                                               in3_3)))))))

(defthmrp-multiplier
  unsigned-four-lanes-lo-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in3_0)

                (integerp in1_1)
                (integerp in2_1)
                (integerp in3_1)

                (integerp in1_2)
                (integerp in2_2)
                (integerp in3_2)

                (integerp in1_3)
                (integerp in2_3)
                (integerp in3_3))
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (control-mode :four-lanes-lo t
                                                     :signed nil)))
                  `((result0 . ,(loghead 32 (+ (* (loghead 32 in1_0)
                                                  (loghead 32 in2_0))
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (* (loghead 32 in1_1)
                                                  (loghead 32 in2_1))
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (* (loghead 32 in1_2)
                                                  (loghead 32 in2_2))
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (* (loghead 32 in1_3)
                                                  (loghead 32 in2_3))
                                               in3_3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 4 - mode = four-lanes-hi: Four Lanes Truncate Higher Half

(defthmrp-multiplier
  signed-four-lanes-hi-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in3_0)

                (integerp in1_1)
                (integerp in2_1)
                (integerp in3_1)

                (integerp in1_2)
                (integerp in2_2)
                (integerp in3_2)

                (integerp in1_3)
                (integerp in2_3)
                (integerp in3_3))
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (control-mode :four-lanes-hi t
                                                     :signed t)))
                  `((result0 . ,(loghead 32 (+ (ash (* (logext 32 in1_0)
                                                       (logext 32 in2_0))
                                                    -32)
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (ash (* (logext 32 in1_1)
                                                       (logext 32 in2_1))
                                                    -32)
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (ash (* (logext 32 in1_2)
                                                       (logext 32 in2_2))
                                                    -32)
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (ash (* (logext 32 in1_3)
                                                       (logext 32 in2_3))
                                                    -32)
                                               in3_3))))))
  )

(defthmrp-multiplier
  unsigned-four-lanes-hi-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in3_0)

                (integerp in1_1)
                (integerp in2_1)
                (integerp in3_1)

                (integerp in1_2)
                (integerp in2_2)
                (integerp in3_2)

                (integerp in1_3)
                (integerp in2_3)
                (integerp in3_3))
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (control-mode :four-lanes-hi t
                                                     :signed nil)))
                  `((result0 . ,(loghead 32 (+ (ash (* (loghead 32 in1_0)
                                                       (loghead 32 in2_0))
                                                    -32)
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (ash (* (loghead 32 in1_1)
                                                       (loghead 32 in2_1))
                                                    -32)
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (ash (* (loghead 32 in1_2)
                                                       (loghead 32 in2_2))
                                                    -32)
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (ash (* (loghead 32 in1_3)
                                                       (loghead 32 in2_3))
                                                    -32)
                                               in3_3))))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-5: Dot Product (Sequential)

;; With the simulation  pattern below, the accumulator (acc) will  be reset and
;; loaded with "acc-init-val".  Then we perform 8 multiplications  in two clock
;; cycles, sum them and accumulate the results in acc.
(sv::defsvtv sequential-dotproduct-mult2-svtv
  :mod *mult2-sv-design*
  :inputs `(("clk" 0 1 ~)
            ("IN1[31:0]"   _ _ in1[0] _ in1[4])
            ("IN2[31:0]"   _ _ in2[0] _ in2[4])
            ("IN1[63:32]"  _ _ in1[1] _ in1[5])
            ("IN2[63:32]"  _ _ in2[1] _ in2[5])
            ("IN1[95:64]"  _ _ in1[2] _ in1[6])
            ("IN2[95:64]"  _ _ in2[2] _ in2[6])
            ("IN1[127:96]" _ _ in1[3] _ in1[7])
            ("IN2[127:96]" _ _ in2[3] _ in2[7])
            ("IN3" acc-init-val)
            ("mode" ,(control-mode :acc-on t
                                   :dot-product t
                                   :reload-acc t)
             mode mode mode mode))
  :outputs '(("result" _ _ _ _ result)))

;; In  this  part,  we  show  how   our  method  can  be  used  for  sequential
;; circuits. The  design in integrated_multiplier.sv has  an accumulator, which
;; we  can  use  to  create  an 8-32x32-bit  dot  product  out  of  4-32x32-bit
;; dot-product module.
(define dot-product-spec ((in1-lst integer-listp)
                          (in2-lst integer-listp)
                          (dot-product-size natp)
                          (signed booleanp)
                          (acc-init-val integerp)
                          (acc-size natp))
  :verify-guards nil
  :guard (and (equal dot-product-size (len in1-lst))
              (equal dot-product-size (len in2-lst)))
  (if (zp dot-product-size)
      (loghead acc-size acc-init-val)
    (let* ((dot-product-size (1- dot-product-size)))
      (loghead acc-size
               (+ (if signed
                      (* (logext 32 (nth dot-product-size in1-lst))
                         (logext 32 (nth dot-product-size in2-lst)))
                    (* (loghead 32 (nth dot-product-size in1-lst))
                       (loghead 32 (nth dot-product-size in2-lst))))
                  (dot-product-spec in1-lst
                                    in2-lst
                                    dot-product-size
                                    signed
                                    acc-init-val
                                    acc-size)))))
  ///
  ;; We need to add the definition rule of this function to RP-Rewriter so that
  ;; it can know to expand it.
  (add-rp-rule dot-product-spec))

(add-rp-rule sequential-dotproduct-mult2-svtv-autohyps)
(add-rp-rule sequential-dotproduct-mult2-svtv-autoins)

;; finally the proof:
(defthmrp-multiplier
  signed-dot-product-with-acc-is-correct
  (implies (and (equal signed t)
                (equal acc-size 128)
                (equal dot-product-size 8)
                (equal mode (control-mode :dot-product t
                                          :acc-on t
                                          :signed signed))
                (sequential-dotproduct-mult2-svtv-autohyps))
           (equal
            (sv::svtv-run (sequential-dotproduct-mult2-svtv)
                          (sequential-dotproduct-mult2-svtv-autoins))
            `((result . ,(dot-product-spec (list in1[0] in1[1] in1[2] in1[3] in1[4] in1[5] in1[6] in1[7])
                                           (list in2[0] in2[1] in2[2] in2[3] in2[4] in2[5] in2[6] in2[7])
                                           dot-product-size ;
                                           signed acc-init-val acc-size))))))

(defthmrp-multiplier
  unsigned-dot-product-with-acc-is-correct
  (implies (and (equal signed nil)
                (equal acc-size 128)
                (equal dot-product-size 8)
                (equal mode (control-mode :dot-product t
                                          :acc-on t
                                          :signed signed))
                (sequential-dotproduct-mult2-svtv-autohyps))
           (equal
            (sv::svtv-run (sequential-dotproduct-mult2-svtv)
                          (sequential-dotproduct-mult2-svtv-autoins))
            `((result . ,(dot-product-spec (list in1[0] in1[1] in1[2] in1[3] in1[4] in1[5] in1[6] in1[7])
                                           (list in2[0] in2[1] in2[2] in2[3] in2[4] in2[5] in2[6] in2[7])
                                           dot-product-size ;
                                           signed acc-init-val acc-size))))))
