
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

;; for ACL2(p)
(set-waterfall-parallelism nil)

;; "Stingy-pp-clean"  is one  of  the heuristics  that  improve the  proof-time
;; performance for verification  of Booth encoded designs. This  is disabled by
;; default as  it may potentially cause  proofs for some designs  to fail.  For
;; the design  we are  working on,  this does  not happen.   So we  enable this
;; heuristic  with the  event  below.   This gives  around  10% improvement  in
;; proof-time performance for  64x64-bit multipliers, and a lot  more in larger
;; designs.
(enable-stingy-pp-clean t)

;; Events to read the multiplier design from file.
(progn
  ;; load VL design for the modules in integrated_multipliers.sv
  (acl2::defconsts
   (*mult-vl-design* state)
   (b* (((mv loadresult state)
         (vl::vl-load (vl::make-vl-loadconfig
                       :start-files '("integrated_multipliers.sv")))))
     (mv (vl::vl-loadresult->design loadresult) state)))

  ;; Load SV design
  (acl2::defconsts
   (*mul-sv-design*
    *simplified-good*
    *simplified-bad*)
   (b* (((mv errmsg sv-design good bad)
         (vl::vl-design->sv-design "Integrated_Multiplier"
                                   *mult-vl-design* (vl::make-vl-simpconfig))))
     (and errmsg
          (acl2::raise "~@0~%" errmsg))
     (mv sv-design good bad)))

  ;; Load SVL design ;; takes less than a second
  (acl2::defconsts (*mult-svl-design* rp::rp-state)
                   (svl::svl-flatten-design *mul-sv-design*
                                            *mult-vl-design*
                                            :dont-flatten :all)))

;; We read the comments given in the integrated_multipliers.sv file,
;; and create the function below in order to calculate the value of "mode"
;; in a user-friendly fashion.
(define mode (&key
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
            (hard-error 'mode "" nil)
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
;; Adder module proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; As per  our method,  we need  reason about adder  modules first.   Below are
;; rewrite rules that  will replace the instantiations of the  adder modules in
;; the main multiplier module when we carry out the multiplier proofs.

;; Our main function to run SVL  designs is "svl-run". When svl-run expands the
;; definition of  circuits, it  calls another function  to evaluate  the output
;; value and next state of the instantiated modules. This function, during our
;; proofs, is svl::svl-run-phase-wog. Therefore, our rewrite rules about adder
;; modules are in terms of this function.

;; Below two  events are only for  debugging. These create rewrite  rules whose
;; LHS's    are   (svl::svl-run-phase-wog    "fa"   ins    env   design)    and
;; (svl::svl-run-phase-wog  "ha"  ins  env  design),  respectibely.   When  the
;; rewriter matches  these rules, the  program will  throw an error.   When the
;; rewriter starts,  rewrite rules  are prioritized with  respect to  the order
;; they are submitted to  ACL2, and the most recent rule  will have the highest
;; priority. With these events, we enforce  that the instances of "fa" and "ha"
;; modules are rewritten by the rewrite  rules defined from this point forward.
;; As per  our method, the  definition of these  adder modules should  never be
;; opened, and this system prevents that from happening and gives us an idea as
;; to why the intended rewrite rules for "fa" and "ha" were not applied.
(def-rw-opener-error svl-run-phase-of-FullAdder-opener-error
  (svl::svl-run-phase-wog "fa" ins env design)
  :do-not-print (env design))

(def-rw-opener-error svl-run-phase-of-HalfAdder-opener-error
  (svl::svl-run-phase-wog "ha" ins env design)
  :do-not-print (env design))

;; Full adder and half adder are very  small circuits. ACL2 can prove the below
;; lemmas easily  by case-splitting  on the  values of the  inputs and  try all
;; cases.
(def-rp-rule svl-run-phase-of-FullAdder
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (svl::svl-run-phase-wog "fa"
                                          (list x y z)
                                          svl::*empty-state*
                                          *mult-svl-design*)
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
                                          *mult-svl-design*)
                  (mv (s-c-spec (list x y))
                      svl::*empty-state*)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))

;; Lemma for the final stage adder.

;; defthmrp calls RP-Rewriter  as a clause processor to prove  the below lemma.
;; We  have a  set of  rewrite rules  (and meta  rules) to  reason about  adder
;; modules. So  the below event  enables/disables necessary rules to  prove the
;; final stage adder  correct. Alternatively, using a SAT solver  through GL or
;; FGL utilities is a possiblity to reason about such adder modules.
(defthmrp LF_131-final-stage-adder-correct
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog "LF_131"
                                          (list in1 in2)
                                          svl::*empty-state*
                                          *mult-svl-design*)
                  (mv (list (loghead 132 (+ (loghead 131 in1)
                                            (loghead 131 in2))))
                      svl::*empty-state*)))
  :disable-meta-rules (s-c-spec-meta)
  :enable-rules rp::*adder-rules*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplier module proofs
;; PART I. Without Accumulator (Only Combinational)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Below are proofs for different modes of this multiplier module that pertains
;; to only  the combinational modes.   PART II will show  an example of  how to
;; verify a sequential operation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Let's first prove the 'one-lane 64x64-bit multiplication' mode.
;; Note that this is actually an FMA.

;; for svl-run,  we create the  input and  output signal bindings  lists.  This
;; will tell which signals our variables should be connected to.
(defconst *in-binds-one-lane*
  '(("clk" 0)
    ("IN1" in1)
    ("IN2" in2)
    ("IN3" in3)
    ("mode" mode)))

(defconst *out-binds*
  '(("result" result)))

;; Below is our first correctness proof of a multiplier module. SVL-RUN returns
;; an alist of all the variables stated  in *out-binds*. In this case, there is
;; only one entry whose key is 'result'. We state the expression of this signal
;; in our conjecture.  In this case  it is [in3 + in2*in1 (both sign-extended)]
;; and the complete result is truncated at 128 bits.  This is the specification
;; of  this  multiplication  mode.   When  writing  the  specification,  it  is
;; imperative to have "loghead" wrapping the arithmetic functions as seen here.
(defthmrp signed-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1 . ,in1)
                                  (in2 . ,in2)
                                  (in3 . ,in3)
                                  (mode . ,(mode :one-lane t
                                                 :signed t)))
                                *in-binds-one-lane*
                                *out-binds*
                                *mult-svl-design*)
                  `((result . ,(loghead 128 (+ (* (sign-ext in1 64)
                                                  (sign-ext in2 64))
                                               in3)))))))

;; Alternatively, we can set certain inputs to constants. In this case, we can
;; set in3 to 0, and prove only the multiplication function (but not FMA).
(defthmrp signed-one-lane-mult-is-correct-for-in3=0
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1 . ,in1)
                                  (in2 . ,in2)
                                  (in3 . 0)
                                  (mode . ,(mode :one-lane t
                                                 :signed t)))
                                *in-binds-one-lane*
                                *out-binds*
                                *mult-svl-design*)
                  `((result . ,(loghead 128 (* (sign-ext in1 64)
                                               (sign-ext in2 64))))))))

;; We can prove the same for mode for unsigned numbers by changing the
;; specification accordingly.
(defthmrp unsigned-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1 . ,in1)
                                  (in2 . ,in2)
                                  (in3 . ,in3)
                                  (mode . ,(mode :one-lane t
                                                 :signed nil)))
                                *in-binds-one-lane*
                                *out-binds*
                                *mult-svl-design*)
                  `((result . ,(loghead 128 (+ (* (loghead 64 in1)
                                                  (loghead 64 in2))
                                               in3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now let's verify the dot product operation.

;; To make  it easy  on us  (more readable), we  define another  input bindings
;; alist for dot product mode.
(defconst *in-binds-dot-product*
  '(("clk" 0)
    ("IN1[31:0]" in1_0)
    ("IN2[31:0]" in2_0)
    ("IN1[63:32]" in1_1)
    ("IN2[63:32]" in2_1)
    ("IN1[95:64]" in1_2)
    ("IN2[95:64]" in2_2)
    ("IN1[127:96]" in1_3)
    ("IN2[127:96]" in2_3)
    ("IN3" in3)
    ("mode" mode)))

(defthmrp signed-dot-product-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in1_1)
                (integerp in2_1)
                (integerp in1_2)
                (integerp in2_2)
                (integerp in1_3)
                (integerp in2_3)
                (integerp in3))
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3   . ,in3)
                                  (mode  . ,(mode :dot-product t
                                                  :signed t)))
                                *in-binds-dot-product*
                                *out-binds*
                                *mult-svl-design*)
                  `((result . ,(loghead 128 (+ (* (sign-ext in1_0 32)
                                                  (sign-ext in2_0 32))
                                               (* (sign-ext in1_1 32)
                                                  (sign-ext in2_1 32))
                                               (* (sign-ext in1_2 32)
                                                  (sign-ext in2_2 32))
                                               (* (sign-ext in1_3 32)
                                                  (sign-ext in2_3 32))
                                               in3)))))))

(defthmrp unsigned-dot-product-is-correct
  (implies (and (integerp in1_0)
                (integerp in2_0)
                (integerp in1_1)
                (integerp in2_1)
                (integerp in1_2)
                (integerp in2_2)
                (integerp in1_3)
                (integerp in2_3)
                (integerp in3))
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3   . ,in3)
                                  (mode  . ,(mode :dot-product t
                                                  :signed nil)))
                                *in-binds-dot-product*
                                *out-binds*
                                *mult-svl-design*)
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
;; Now let's verify the four-lane multiplication that truncate at the lower
;; half of multiplication.

;; To make  it easy  on us  (more readable), we  define another  input bindings
;; alist for four-lanes multiplication, and also an output bindinds alist.

(defconst *in-binds-four-lanes*
  '(("clk" 0)
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
    ("mode"        mode)))

(defconst *out-binds-four-lanes*
  '(("result[31:0]"   result0)
    ("result[63:32]"  result1)
    ("result[95:64]"  result2)
    ("result[127:96]" result3)))

(defthmrp signed-four-lanes-lo-is-correct
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
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in3_0 . ,in3_0)

                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in3_1 . ,in3_1)

                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in3_2 . ,in3_2)

                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3_3 . ,in3_3)

                                  (mode  . ,(mode :four-lanes-lo t
                                                  :signed t)))
                                *in-binds-four-lanes*
                                *out-binds-four-lanes*
                                *mult-svl-design*)
                  `((result0 . ,(loghead 32 (+ (* (sign-ext in1_0 32)
                                                  (sign-ext in2_0 32))
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (* (sign-ext in1_1 32)
                                                  (sign-ext in2_1 32))
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (* (sign-ext in1_2 32)
                                                  (sign-ext in2_2 32))
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (* (sign-ext in1_3 32)
                                                  (sign-ext in2_3 32))
                                               in3_3)))))))

(defthmrp unsigned-four-lanes-lo-is-correct
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
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in3_0 . ,in3_0)

                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in3_1 . ,in3_1)

                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in3_2 . ,in3_2)

                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3_3 . ,in3_3)

                                  (mode  . ,(mode :four-lanes-lo t
                                                  :signed nil)))
                                *in-binds-four-lanes*
                                *out-binds-four-lanes*
                                *mult-svl-design*)
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
;; Finally, let's verify the four-lane multiplication that truncate at the higher
;; half of multiplication.

;; (ash x y) left shifts x by y. If y is negative, the operation becomes right
;; shift.

(defthmrp signed-four-lanes-hi-is-correct
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
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in3_0 . ,in3_0)

                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in3_1 . ,in3_1)

                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in3_2 . ,in3_2)

                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3_3 . ,in3_3)

                                  (mode  . ,(mode :four-lanes-hi t
                                                  :signed t)))
                                *in-binds-four-lanes*
                                *out-binds-four-lanes*
                                *mult-svl-design*)
                  `((result0 . ,(loghead 32 (+ (ash (* (sign-ext in1_0 32)
                                                       (sign-ext in2_0 32))
                                                    -32)
                                               in3_0)))
                    (result1 . ,(loghead 32 (+ (ash (* (sign-ext in1_1 32)
                                                       (sign-ext in2_1 32))
                                                    -32)
                                               in3_1)))
                    (result2 . ,(loghead 32 (+ (ash (* (sign-ext in1_2 32)
                                                       (sign-ext in2_2 32))
                                                    -32)
                                               in3_2)))
                    (result3 . ,(loghead 32 (+ (ash (* (sign-ext in1_3 32)
                                                       (sign-ext in2_3 32))
                                                    -32)
                                               in3_3)))))))

(defthmrp unsigned-four-lanes-hi-is-correct
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
           (equal (svl::svl-run "Integrated_Multiplier"
                                `((in1_0 . ,in1_0)
                                  (in2_0 . ,in2_0)
                                  (in3_0 . ,in3_0)

                                  (in1_1 . ,in1_1)
                                  (in2_1 . ,in2_1)
                                  (in3_1 . ,in3_1)

                                  (in1_2 . ,in1_2)
                                  (in2_2 . ,in2_2)
                                  (in3_2 . ,in3_2)

                                  (in1_3 . ,in1_3)
                                  (in2_3 . ,in2_3)
                                  (in3_3 . ,in3_3)

                                  (mode . ,(mode :four-lanes-hi t
                                                 :signed nil)))
                                *in-binds-four-lanes*
                                *out-binds-four-lanes*
                                *mult-svl-design*)
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
                                               in3_3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplier module proofs
;; PART II. With Accumulator (Sequential)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In  this  part,  we  show  how   our  method  can  be  used  for  sequential
;; circuits. The  design in integrated_multiplier.sv has  an accumulator, which
;; we  can  use  to  create  an 8-32x32-bit  dot  product  out  of  4-32x32-bit
;; dot-product module.

;; Let's first define the specification for dot-product of any length.
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
                      (* (sign-ext (nth dot-product-size in1-lst) 32)
                         (sign-ext (nth dot-product-size in2-lst) 32))
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

#|
An example run:
(sign-ext
 (dot_product_spec (list -10 12  12 -14)
                   (list 10  -12 12 14)
                   4 t 128)
 128)
||#

;; Let's define  the input bindings  list (simulation pattern) for  the 8-32x32
;; dot product operation.  We have the "clk" signal oscillate.  The mode in the
;; first clcok  cycle is  set to  load the  accumulator with  acc-init-val.  In
;; subsequent cycles, we let user decide what mode should be. In the next clock
;; cycles, we dot-product and accumulate in1[0-3] and in2[0-3], and in the next
;; one we dot-product and accumulate in1[4-7]  and in2[4-7]. Note that the form
;; in[i],  such as  in1[0], does  not designate  an array  access but  they are
;; independent free variables. LISP allows users to have such characters in
;; object names.

;; During the phases  where the values of inputs should  be "dont-care", we put
;; "0"s instead.   It is because our  method currently has a  very weak support
;; when some  of the  inputs are  four-valued even though  they don't  have any
;; effect on the  output.  It is possiple  to prove the same  lemmas below with
;; "dont-care"s instead  of zeros  but that  procedure entails  jumping through
;; hoops so we omit that for simplicity.

;; With the simulation  pattern below, the accumulator (acc) will  be reset and
;; loaded with "acc-init-val".  Then we perform 8 multiplications  in two clock
;; cycles, and accumulate the results in acc.
(defconst *in-binds-dot-product-with-acc*
  `(("clk" 0 1 ~)
    ("IN1[31:0]"   0 0 in1[0] 0 in1[4])
    ("IN2[31:0]"   0 0 in2[0] 0 in2[4])
    ("IN1[63:32]"  0 0 in1[1] 0 in1[5])
    ("IN2[63:32]"  0 0 in2[1] 0 in2[5])
    ("IN1[95:64]"  0 0 in1[2] 0 in1[6])
    ("IN2[95:64]"  0 0 in2[2] 0 in2[6])
    ("IN1[127:96]" 0 0 in1[3] 0 in1[7])
    ("IN2[127:96]" 0 0 in2[3] 0 in2[7])
    ("IN3" acc-init-val)
    ("mode" ,(mode :acc-on t
                   :dot-product t
                   :reload-acc t)
     mode mode mode mode)))

;; result is obtained on the 5th phase.
(defconst *out-binds-with-acc*
  '(("result" _ _ _ _ result)))

(defthmrp signed-dot-product-with-acc-is-correct
  (b* ((signed t) ;; set up the parameters first.
       (acc-size 128)
       (dot-product-size 8))
    (implies (and (integer-listp in1)
                  (integer-listp in2)
                  (integerp acc-init-val)
                  (equal (len in1) dot-product-size) ;; necessary to show that
                  ;; "nth" function returns a valid value (an integer).
                  (equal (len in2) dot-product-size) ;; same as above.
                  )
             (equal (svl::svl-run "Integrated_Multiplier"
                                  `(;; will be used in the
                                    ;; first cycle:
                                    (in1[0] . ,(nth 0 in1))
                                    (in2[0] . ,(nth 0 in2))
                                    (in1[1] . ,(nth 1 in1))
                                    (in2[1] . ,(nth 1 in2))
                                    (in1[2] . ,(nth 2 in1))
                                    (in2[2] . ,(nth 2 in2))
                                    (in1[3] . ,(nth 3 in1))
                                    (in2[3] . ,(nth 3 in2))
                                    ;; will be used in the
                                    ;; second cycle:
                                    (in1[4] . ,(nth 4 in1))
                                    (in2[4] . ,(nth 4 in2))
                                    (in1[5] . ,(nth 5 in1))
                                    (in2[5] . ,(nth 5 in2))
                                    (in1[6] . ,(nth 6 in1))
                                    (in2[6] . ,(nth 6 in2))
                                    (in1[7] . ,(nth 7 in1))
                                    (in2[7] . ,(nth 7 in2))

                                    (acc-init-val . ,acc-init-val)
                                    (mode   . ,(mode :dot-product t
                                                     :acc-on t
                                                     :signed signed)))
                                  *in-binds-dot-product-with-acc*
                                  *out-binds-with-acc*
                                  *mult-svl-design*)
                    `((result . ,(dot-product-spec in1 in2 dot-product-size ;
                                                   signed acc-init-val acc-size)))))))

(defthmrp unsigned-dot-product-with-acc-is-correct
  (b* ((signed nil) ;;signed=nil is the only difference here than the previous lemma
       (acc-size 128)
       (dot-product-size 8))
    (implies (and (integer-listp in1)
                  (integer-listp in2)
                  (integerp acc-init-val)
                  (equal (len in1) dot-product-size)
                  (equal (len in2) dot-product-size))
             (equal (svl::svl-run "Integrated_Multiplier"
                                  `((in1[0] . ,(nth 0 in1))
                                    (in2[0] . ,(nth 0 in2))
                                    (in1[1] . ,(nth 1 in1))
                                    (in2[1] . ,(nth 1 in2))
                                    (in1[2] . ,(nth 2 in1))
                                    (in2[2] . ,(nth 2 in2))
                                    (in1[3] . ,(nth 3 in1))
                                    (in2[3] . ,(nth 3 in2))

                                    (in1[4] . ,(nth 4 in1))
                                    (in2[4] . ,(nth 4 in2))
                                    (in1[5] . ,(nth 5 in1))
                                    (in2[5] . ,(nth 5 in2))
                                    (in1[6] . ,(nth 6 in1))
                                    (in2[6] . ,(nth 6 in2))
                                    (in1[7] . ,(nth 7 in1))
                                    (in2[7] . ,(nth 7 in2))

                                    (acc-init-val . ,acc-init-val)
                                    (mode   . ,(mode :dot-product t
                                                     :acc-on t
                                                     :signed signed)))
                                  *in-binds-dot-product-with-acc*
                                  *out-binds-with-acc*
                                  *mult-svl-design*)
                    `((result . ,(dot-product-spec in1 in2 dot-product-size
                                                   signed acc-init-val acc-size)))))))
