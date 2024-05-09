
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

(include-book "projects/vescmul/top" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example:   integrated_multipliers.sv  (Multiply-accumulate,   Dot-product,
;; Four-lane mult with truncation) (sequential or combinational)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This module has a control signal  called "mode". This signal determines what
;; operation this  module is  to perform.   We read the  comments given  in the
;; integrated_multipliers.sv file,  and create the  function below in  order to
;; calculate the  value of "mode"  in a  user-friendly fashion for  our proofs.
(define calculate-mode-value (&key
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
       (mode (install-bit 0 (if acc-on 0 1) mode))
       (mode (install-bit 1 (if reload-acc 0 1) mode))
       (mode (install-bit 2 (if signed 0 1) mode))
       (mode
        (cond (dot-product   (part-install 0 mode :low 3 :width 2))
              (four-lanes-lo (part-install 1 mode :low 3 :width 2))
              (four-lanes-hi (part-install 2 mode :low 3 :width 2))
              (t             (part-install 3 mode :low 3 :width 2)))))
    mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; parse design for combinational modes
(vescmul-parse :name integrated_multipliers-combinational-modes
               :file "integrated_multipliers.sv"
               :topmodule "Integrated_Multiplier")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 1,2 - Mode = one-lane: Signed One lane (64x64-bit) multiplication

;; one lane mode, signed
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name signed-one-lane-mult-correct
                :hyp (equal mode (calculate-mode-value :one-lane t
                                                       :signed t))
                :concl (equal result
                              (loghead 128 (+ (* (logext 64 in1)
                                                 (logext 64 in2))
                                              in3))))
;; one lane mode, unsigned
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name unsigned-one-lane-mult-correct
                :hyp (equal mode (calculate-mode-value :one-lane t
                                                       :signed nil))
                :concl (equal result
                              (loghead 128 (+ (* (loghead 64 in1)
                                                 (loghead 64 in2))
                                              in3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 3,4 - Mode = dot-product. Dot Product (combinational)

(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name signed-comb-dot-product-is-correct
                :hyp (equal mode (calculate-mode-value :dot-product t
                                                       :signed t))
                :concl (equal result
                              (loghead 128 (+ (* (logext 32 (nth-slice32 0 in1))
                                                 (logext 32 (nth-slice32 0 in2)))
                                              (* (logext 32 (nth-slice32 1 in1))
                                                 (logext 32 (nth-slice32 1 in2)))
                                              (* (logext 32 (nth-slice32 2 in1))
                                                 (logext 32 (nth-slice32 2 in2)))
                                              (* (logext 32 (nth-slice32 3 in1))
                                                 (logext 32 (nth-slice32 3 in2)))
                                              in3))))

(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name unsigned-comb-dot-product-is-correct
                :hyp (equal mode (calculate-mode-value :dot-product t
                                                       :signed nil))
                :concl (equal result
                              (loghead 128 (+ (* (nth-slice32 0 in1)
                                                 (nth-slice32 0 in2))
                                              (* (nth-slice32 1 in1)
                                                 (nth-slice32 1 in2))
                                              (* (nth-slice32 2 in1)
                                                 (nth-slice32 2 in2))
                                              (* (nth-slice32 3 in1)
                                                 (nth-slice32 3 in2))
                                              in3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 5,6 - mode = four-lanes-lo: Four Lanes multiplication of lower halves

;; signed or  unsigned modes  return the  same as values  are truncated  at the
;; first half.

(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name signed-four-lanes-lo-is-correct
                :hyp (equal mode (calculate-mode-value :four-lanes-lo t
                                                       :signed t))
                :concl (equal result
                              (merge-4-u32s
                               ;; most significant portion first.
                               (loghead 32
                                        (+ (* (nth-slice32 3 in1)
                                              (nth-slice32 3 in2))
                                           (nth-slice32 3 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 2 in1)
                                              (nth-slice32 2 in2))
                                           (nth-slice32 2 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 1 in1)
                                              (nth-slice32 1 in2))
                                           (nth-slice32 1 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 0 in1)
                                              (nth-slice32 0 in2))
                                           (nth-slice32 0 in3))))))

(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name unsigned-four-lanes-lo-is-correct
                :hyp (equal mode (calculate-mode-value :four-lanes-lo t
                                                       :signed nil))
                :concl (equal result
                              (merge-4-u32s
                               ;; most significant portion first.
                               (loghead 32
                                        (+ (* (nth-slice32 3 in1)
                                              (nth-slice32 3 in2))
                                           (nth-slice32 3 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 2 in1)
                                              (nth-slice32 2 in2))
                                           (nth-slice32 2 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 1 in1)
                                              (nth-slice32 1 in2))
                                           (nth-slice32 1 in3)))
                               (loghead 32
                                        (+ (* (nth-slice32 0 in1)
                                              (nth-slice32 0 in2))
                                           (nth-slice32 0 in3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 7,8  - mode =  four-lanes-hi: Four  Lanes of multiplication  of higher
;; halves

;; signed
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name signed-four-lanes-hi-is-correct
                :hyp (equal mode (calculate-mode-value :four-lanes-hi t
                                                       :signed t))
                :concl (equal result
                              (merge-4-u32s
                               ;; as   in   Verilog  concatenation,   most
                               ;; significant portion first.
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (logext 32 (nth-slice32 3 in1))
                                                       (logext 32 (nth-slice32 3 in2))))
                                           (nth-slice32 3 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (logext 32 (nth-slice32 2 in1))
                                                       (logext 32 (nth-slice32 2 in2))))
                                           (nth-slice32 2 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (logext 32 (nth-slice32 1 in1))
                                                       (logext 32 (nth-slice32 1 in2))))
                                           (nth-slice32 1 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (logext 32 (nth-slice32 0 in1))
                                                       (logext 32 (nth-slice32 0 in2))))
                                           (nth-slice32 0 in3))))))

;; unsigned
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name unsigned-four-lanes-hi-is-correct
                :hyp (equal mode (calculate-mode-value :four-lanes-hi t
                                                       :signed nil))
                :concl (equal result
                              (merge-4-u32s
                               ;; most significant portion first.
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (nth-slice32 3 in1)
                                                       (nth-slice32 3 in2)))
                                           (nth-slice32 3 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (nth-slice32 2 in1)
                                                       (nth-slice32 2 in2)))
                                           (nth-slice32 2 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (nth-slice32 1 in1)
                                                       (nth-slice32 1 in2)))
                                           (nth-slice32 1 in3)))
                               (loghead 32
                                        (+ (logtail 32
                                                    (* (nth-slice32 0 in1)
                                                       (nth-slice32 0 in2)))
                                           (nth-slice32 0 in3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now let's verify a sequential mode.

;; Goal: Create a different simulation vector for sequential simulation. We set
;; up the simulation vector  such that in the first clock  cycle, we reload the
;; accumulator (ACC)  with a  value (free  variable).  Then  in the  next clock
;; cycles, we  feed different values  for IN1 an IN2  inputs. We will  tell the
;; module  to  dot-product  these  values  and accumulate  the  result  in  ACC
;; register.  As  each lane is  32-bit wide, and  IN1-IN2 are 128-bit  wide, we
;; will have a 8-point dot-product accumulated onto an ACC register after the 2
;; clock cycles.  Potentially, this can be  increased to more clock  cycles for
;; larger dot-product.
(vescmul-parse :name integrated_multipliers-sequential-mode
               :file "integrated_multipliers.sv"
               :topmodule "Integrated_Multiplier"

               ;; Define the clock: (clk signal should continuously toggle)
               :cycle-phases (list (sv::make-svtv-cyclephase :constants '(("clk" . 0))
                                                             :inputs-free t
                                                             :outputs-captured t)
                                   (sv::make-svtv-cyclephase :constants '(("clk" . 1))))
               :stages
               (;; reload the ACC in the first clock cycle
                (:label reload-acc
                        :inputs (("IN3" acc-init-val)
                                 ("mode" mode-init-val)))
                ;; Feed some values in the second clock cycle for dot product
                (:label 1st-vectors
                        :inputs (("IN1" in1-1)
                                 ("IN2" in2-1)
                                 ;; keep the mode value the same in the next cycles.
                                 ("mode" mode :hold t))
                        :outputs (("result" result1)))
                ;; Feed more values for dot-product.
                (:label 2nd-vectors
                        :inputs (("IN1" in1-2)
                                 ("IN2" in2-2))
                        :outputs (("result" result2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 9,10: Dot Product (Sequential)

;; For a better readablity, we can define a spec function:
(define dot-product32 ((in1 integerp)
                       (in2 integerp)
                       (signed booleanp)
                       (dot-size natp))
  (if (zp dot-size)
      0
    (+ (if signed
           (* (logext 32 in1)
              (logext 32 in2))
         (* (loghead 32 in1)
            (loghead 32 in2)))
       (dot-product32 (logtail 32 in1)
                      (logtail 32 in2)
                      signed
                      (1- dot-size))))
  ///
  ;; tell the rewriter to expand the definition of this spec function.
  (add-rp-rule dot-product32))

;; signed
(vescmul-verify :name integrated_multipliers-sequential-mode

                :thm-name signed-dot-product-with-acc-is-correct
                :hyp (and
                      ;; set the first mode value to reload ACC.
                      (equal mode-init-val (calculate-mode-value :acc-on t
                                                                 :dot-product t
                                                                 :reload-acc t))
                      ;; mode  in  the following  clock  cycle  is set  to
                      ;; dot-product accumulate
                      (equal mode (calculate-mode-value :dot-product t
                                                        :acc-on t
                                                        :signed t)))
                ;; we can validate the value of the output in different cycles:
                :concl (and (equal result1
                                   (loghead 128
                                            (+ (dot-product32 in1-1 in2-1 t 4)
                                               acc-init-val)))
                            (equal result2
                                   (loghead 128
                                            (+ (dot-product32 in1-1 in2-1 t 4)
                                               (dot-product32 in1-2 in2-2 t 4)
                                               acc-init-val)))))

;; unsigned
(vescmul-verify :name integrated_multipliers-sequential-mode

                :thm-name unsigned-dot-product-with-acc-is-correct
                :hyp (and
                      ;; set the first mode value to reload ACC.
                      (equal mode-init-val (calculate-mode-value :acc-on t
                                                                 :dot-product t
                                                                 :reload-acc t))
                      ;; mode  in  the following  clock  cycle  is set  to
                      ;; dot-product accumulate
                      (equal mode (calculate-mode-value :dot-product t
                                                        :acc-on t
                                                        :signed nil)))
                :concl (equal result2
                              (loghead 128
                                       (+ (dot-product32 in1-1 in2-1 nil 4)
                                          (dot-product32 in1-2 in2-2 nil 4)
                                          acc-init-val))))
