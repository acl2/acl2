; 3rd demo for the multiplier verification library.

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.

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
; Mertcan Temel         <mert@utexas.edu>

;; This demo  shows how  this tool can  be used to  verify a  multiplier module
;; translated with defsvtv. This is done by overriding the adder modules in the
;; original design before calling defsvtv.

;; Our tool requires identifying adder modules used by the candidate multiplier
;; design. When defsvtv is called, the  design is flattened completely. That is
;; why we mainly use SVL system where design hierarchy can be maintained during
;; symbolic simulation. However, the SVL system is not as capable as defsvtv at
;; handling  very   complex  designs  that  might   have  combinational  loops.
;; Therefore, we  provide an alternative way  to using SVL (which  was given in
;; demo-1 and  demo-2). First,  we create  copies of  the adder  modules (e.g.,
;; half-adder,  full-adder,  final stage  adder)  and  we redefine  them.   The
;; redefined adder modules have the same  functionality but use the Verilog "+"
;; arithmetic operator  only. Then, we  override the original adder  modules in
;; the SV design and  we create a test vector with  defsvtv with this redefined
;; module  list.   This   helps  our  tool  differentiate   the  adder  modules
;; individually, and rewrite them the same way as SVL designs.

;; Replacing the adder modules  without any check would not be  safe So we also
;; show  a sanity  check  mechanism.   We have  a  macro "replace-adders"  that
;; replaces the adders in  the original SV design, and create a  new one. As it
;; does that, it also  calls our tools to make sure  that the replacement adder
;; modules  have  the  same  signature  as the  original  ones,  and  they  are
;; functionally equivalent.

;; In this  file, we repeat a  subset of the  proofs (for svtv this  time) from
;; demo-1.lisp and demo-2.lisp: DT_SB4_HC_64_64_multgen.sv (64x64 Signed, Booth
;; radix-4  encoded,  Dadda  Tree)   and  integrated_multipliers.sv  (FMA,  Dot
;; product, Four-lanes truncated at lower and higher locations).

(in-package "RP")

;; To load the verilog designs:
(include-book "centaur/sv/top" :dir :system) ;; a big book; takes around 30 seconds
(include-book "centaur/vl/loader/top" :dir :system) ;; takes around 10 seconds
(include-book "oslib/ls" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

(set-waterfall-parallelism nil)

;; for correctness proof of multiplier
(include-book "projects/rp-rewriter/lib/mult3/svtv-top" :dir :system)

;; "Stingy-pp-clean"  is one  of  the heuristics  that  improve the  proof-time
;; performance for verification  of Booth encoded designs. This  is disabled by
;; default as  it may potentially cause  proofs for some designs  to fail.  For
;; the design  we are  working on,  this does  not happen.   So we  enable this
;; heuristic with the event below.
(enable-stingy-pp-clean t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example-1: DT_SB4_HC_64_64_multgen.sv (64X64  SIGNED, BOOTH RADIX-4 ENCODED,
;; DADDA TREE) (the module in demo-1.lisp)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Load VL Design.
(acl2::defconsts
 (*original-mult1-vl-design* state)
 (b* (((mv loadresult state)
       (vl::vl-load (vl::make-vl-loadconfig
                     :start-files '("DT_SB4_HC_64_64_multgen.sv")))))
   (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
 (*original-mult1-sv-design*)
 (b* (((mv errmsg sv-design & &)
       (vl::vl-design->sv-design "DT_SB4_HC_64_64"
                                 *original-mult1-vl-design*
                                 (vl::make-vl-simpconfig))))
   (and errmsg
        (acl2::raise "~@0~%" errmsg))
   sv-design))

;; We   cannot    use   our    tool   on   a    test   vector    created   with
;; *original-mult1-sv-design*  because the  adder  modules in  this design  get
;; mixed up  with each other  when flattened.  So  we will create  another test
;; vector whose adder modules will be distinguishable from rest of the circuit.
;; For that, we  created alternative versions of the adder  modules used in the
;; input multiplier design,  and saved them in  "adders_with_plus.sv".  The new
;; definitions of these  adder modules ("ha", "fa", and  "HC_128") only consist
;; of the "+" operator.   Pay attention to the definition of  "ha"; there is an
;; extra, redundant "+ 0" term. This is a work-around to a strange problem, and
;; it can be vital to some proofs.

;; Using   the   macro   below,   we   create  a   new   SV   design   instance
;; (*redefined-mult-sv-design*)  that is  a copy  of *original-mult1-sv-design*
;; but  with the  stated  adder modules  replaced.  In  order  to perform  this
;; replacement soundly, this macro also proves that the replacement modules are
;; equivalant to the original (when ":sanity-check" argument is set to t).

;; If the  adders used  in the  original design  are parameterized  (see Verilog
;; Parameters),   then  you'd   need  to   create   a  dummy   top  module   in
;; adders_with_plus.sv (or any  file name you'd like), and  instantiate all the
;; redefined adders the same way as the original design instantiates them. This
;; is to ensure that SV design creates instances of the same modules. Then pass
;; the name of  this dummy top module with ":dummy-top"  argument.  For example
;; :dummy-top "dummy_top_module".  And as the  adder module name(s), you'd need
;; to  pass  the   "SV"  version  of  the  instantiated  module   name  such  as
;; "ha$WIDTH=1".
(replace-adders :new-sv *redefined-mult1-sv-design*
                :original-sv *original-mult1-sv-design*
                :original-vl *original-mult1-vl-design*
                ;; prove that the replaced adders are equivalent to the originals:
                :sanity-check t
                ;; whether or not the non-essentials events be exported:
                :local nil
                ;; name of the file(s) that has the replacement adder modules:
                :new-adders-file ("adders_with_plus.sv")
                ;; Name of the modules to be replaced:
                :adder-module-names ("ha" "fa" "HC_128"))

;; Create a test vector with the new sv-design
(sv::defsvtv redefined-mult1-svtv
             :mod *redefined-mult1-sv-design*
             :inputs '(("IN1" a)
                       ("IN2" b))
             :outputs
             '(("result" res)))

;; prove that the new test-vector is correct.
(defthmrp multiplier-correct-for-redefined-design
  (implies (and (integerp in1)
                (integerp in2))
           (equal (sv::svtv-run (redefined-mult1-svtv)
                                `((a . ,in1)
                                  (b . ,in2)))
                  `((res . ,(loghead 128 (* (sign-ext in1 64)
                                            (sign-ext in2 64))))))))


;; I  tried to  create a  final  theorem for  a  test vector  created with  the
;; original SV  design instead of  the redefined one.  I  used a SAT  Solver to
;; prove the equivalance of "redefined-mult1-svtv"  to that vector.  I expected
;; that the SAT solver could easily prove that because only adders are replaced
;; and the overall structure of the design is mostly intact, But the SAT solver
;; seemed to  keep on running  forever.  There is probably  a way to  have that
;; proof  go   quickly.   However,   the  sanity   check  performed   with  the
;; "replace-adders" event should be enough to trust that the adder replacements
;; are correct and done soundly.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example-2: integrated_multipliers.sv (FMA,  Dot-product, Four-lane mult with
;; truncation) (sequential or combinational) (the module in demo-2.lisp)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We follow the  same steps from Example-1 to verify  an even more complicated
;; multiplier example.  See demo-2.lisp  and integrated_multipliers.sv for more
;; details about this module.

;; Load VL Design.
(acl2::defconsts
 (*original-mult2-vl-design* state)
 (b* (((mv loadresult state)
       (vl::vl-load (vl::make-vl-loadconfig
                     :start-files '("integrated_multipliers.sv")))))
   (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
 (*original-mult2-sv-design*)
 (b* (((mv errmsg sv-design & &)
       (vl::vl-design->sv-design "Integrated_Multiplier"
                                 *original-mult2-vl-design*
                                 (vl::make-vl-simpconfig))))
   (and errmsg
        (acl2::raise "~@0~%" errmsg))
   sv-design))

;; Replace the adder modules 
(replace-adders :new-sv *redefined-mult2-sv-design*
                :original-sv *original-mult2-sv-design*
                :original-vl *original-mult2-vl-design*
                :sanity-check t
                :local nil
                ;; name of the file(s) that has the replacement adder modules
                :new-adders-file ("adders_with_plus.sv")
                ;; Name of the modules to be replaced:
                :adder-module-names ("ha" "fa" "LF_131"))


;; The  same function  from "demo-2.lisp"  This  helps determine  the value  of
;; "mode" signal in the Integrated_Multiplier module.
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
;; Proof 2-1a: Signed One lane (64x64-bit) multiplication
(sv::defsvtv one-lane-mult2-svtv
             :mod *redefined-mult2-sv-design*
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

(defthmrp signed-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (sv::svtv-run (one-lane-mult2-svtv)
                                (one-lane-mult2-svtv-autoins
                                 :mode (mode :one-lane t
                                             :signed t)))
                  `((result . ,(loghead 128 (+ (* (sign-ext in1 64)
                                                  (sign-ext in2 64))
                                               in3)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-1b: Unsigned One lane (64x64-bit) multiplication

(defthmrp unsigned-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (sv::svtv-run (one-lane-mult2-svtv)
                                (one-lane-mult2-svtv-autoins
                                 :mode (mode :one-lane t
                                             :signed nil)))
                  `((result . ,(loghead 128 (+ (* (loghead 64 in1)
                                                  (loghead 64 in2))
                                               in3)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-2: Dot Product (combinational)
(sv::defsvtv dotproduct-mult2-svtv
             :mod *redefined-mult2-sv-design*
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
           (equal (sv::svtv-run (dotproduct-mult2-svtv)
                                (dotproduct-mult2-svtv-autoins
                                 :mode (mode :dot-product t
                                             :signed t)))
                  `((result . ,(loghead 128 (+ (* (sign-ext in1_0 32)
                                                  (sign-ext in2_0 32))
                                               (* (sign-ext in1_1 32)
                                                  (sign-ext in2_1 32))
                                               (* (sign-ext in1_2 32)
                                                  (sign-ext in2_2 32))
                                               (* (sign-ext in1_3 32)
                                                  (sign-ext in2_3 32))
                                               in3)))))))

;; We can prove also unsigned mode. But we omit that here to reduce clutter.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-3: Four Lanes Truncate Lower Half 
(sv::defsvtv four-lanes-mult2-svtv
             :mod *redefined-mult2-sv-design*
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
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (mode :four-lanes-lo t
                                             :signed t)))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-4: Four Lanes Truncate Higher Half 
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
           (equal (sv::svtv-run (four-lanes-mult2-svtv)
                                (four-lanes-mult2-svtv-autoins
                                 :mode (mode :four-lanes-hi t
                                             :signed t)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof 2-5: Dot Product (Sequential)

;; With the simulation  pattern below, the accumulator (acc) will  be reset and
;; loaded with "acc-init-val".  Then we perform 8 multiplications  in two clock
;; cycles, sum them and accumulate the results in acc.
(sv::defsvtv sequential-dotproduct-mult2-svtv
             :mod *redefined-mult2-sv-design*
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
                       ("mode" ,(mode :acc-on t
                                      :dot-product t
                                      :reload-acc t)
                        mode mode mode mode))
             :outputs '(("result" _ _ _ _ result)))

;; We copy paste the same dot-product spec function from demo-2.lisp
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

;; finally the proof:
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
             (equal
              (sv::svtv-run (sequential-dotproduct-mult2-svtv)
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
                                               :signed signed))))
              `((result . ,(dot-product-spec in1 in2 dot-product-size ;
                                             signed acc-init-val acc-size)))))))
