; MULTIPLIER RULES

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

(xdoc::defxdoc
 multiplier-proofs-2
 :parents (rp-rewriter/applications)
 :short "A demo for integer multiplier proofs 2.0"
 :long "<p> We implement an efficient and verified method for multiplier
 correctness proofs from (System) Verilog designs. There exists two
 implementations of the same method. Below is a demo for the second version,
 which is much faster and easier to use. </p>

<p> This program may run verify 64x64 multipliers in 1-3 seconds; 128x128 in
3-20 seconds depending on encoding; 256x256 in  15-60 seconds; and so on.
</p>

<p>
1. Include the book that has the rewriter rules and meta rules for RP-Rewriter
for multiplier proofs:
<code>
(include-book \"projects/rp-rewriter/lib/mult2/svl-top\" :dir :system)
</code>
</p>

<p>
2. Include the books to convert Verilog designs to SVL format.
<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system)
(include-book \"centaur/svl/top\" :dir :system)
</code>
SVL system uses @(see acl2::SV) and @(see acl2::VL) packages.
</p>
<p>
3. Load VL design for the modules in DT_SB4_HC_64_64_multgen.sv. This file is
located under books/projects/rp-rewriter/lib/mult2.
This is a 64x64 Signed, Booth radix-4 encoded, Dadda Tree integer multiplier.
<code>
@('
(acl2::defconsts
 (*vl-design* state)
 (b* (((mv loadresult state)
       (vl::vl-load (vl::make-vl-loadconfig
                     :start-files '(\"DT_SB4_HC_64_64_multgen.sv\")))))
   (mv ({vl::vl-loadresult->design loadresult) state)))
')
</code>
</p>


<p>
4. Load SV design:
<code>
@('
(acl2::defconsts
 (*sv-design*
  *simplified-good*
  *simplified-bad*)
 (b* (((mv errmsg sv-design good bad)
       (vl::vl-design->sv-design \"DT_SB4_HC_64_64\"
                                 *vl-design* (vl::make-vl-simpconfig))))
   (and errmsg
        (acl2::raise \"~@0~%\" errmsg))
   (mv sv-design good bad)))
')
</code>
</p>

<p>
5. Load SVL Design:
<code>
(acl2::defconsts (*svl-design* rp::rp-state)
                 (svl::svl-flatten-design *sv-design*
                                          *vl-design*
                                          :dont-flatten :all))
 </code>

SVL design is a simulation-ready version of SV design with circuit hierarchy
maintained. We cannot use @(see acl2::defsvtv) because our multiplier
verification method requires maintained hierarchy for adder modules used by the
main multiplier module. The ':dont-flatten :all' argument retains circuit
hierarchy. If users wants to flatten some modules, they should at least have
the adder module names instead of ':all'. 
</p>

<p>
6. Rewrite adder modules with our specification:

<code>
(def-rp-rule svl-run-phase-of-FullAdder
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (svl::svl-run-phase-wog \"fa\"
                                          (list x y z)
                                          '(nil nil)
                                          *svl-design*)
                  (mv (s-c-spec (list x y z))
                      '(nil nil))))
  :hints ((\"Goal\"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))
</code>
<code>
(def-rp-rule svl-run-phase-of-HalfAdder
  (implies (and (bitp x)
                (bitp y))
           (equal (svl::svl-run-phase-wog \"ha\"
                                          (list x y)
                                          '(nil nil)
                                          *svl-design*)
                  (mv (s-c-spec (list x y))
                      '(nil nil))))
  :hints ((\"Goal\"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))
</code>

The multiplier we are working on uses two types of bit-level adders: a
full-adder with module name \"fa\", and a half-adder with module name
\"ha\". We rewrite them with the lemmas given above. We use @(see rp::def-rp-rule)
to save these in the @(see rp::RP-Rewriter)'s rule-set. ACL2 can prove these lemmas
easily by case-splitting with bitp and trying all the combinations.

<code>
(defthmrp final-stage-adder-correct
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog \"HC_128\"
                                          (list in1 in2)
                                          '(nil nil)
                                          *svl-design*)
                  (mv (list (rp::4vec-adder (svl::bits in1 0 128)
                                            (svl::bits in2 0 128 )
                                            0 129))
                      (svl::make-svl-env))))
  :disable-meta-rules (s-c-spec-meta)
  :enable-rules rp::*adder-rules*)
</code>

This multiplier module uses a Han-Carlson parallel prefix adder with module
name \"HC_128\". We use our suggested rewriting scheme to prove this adder
equivalent to our specification. The macro @(see rp::defthmrp) calls
RP-Rewriter as a clause processor. In proofs for adder modules, the arguments
':disable-meta-rules (s-c-spec-meta)' and ':enable-rules rp::*adder-rules*' are
standard.

</p>

<p>
Rewriting all the adder logic in terms of their specification as given above is
a crucial step for multiplier correctness proofs. The adder proofs are usually
very fast and takes a split second. 
</p>

<p>
7. Finally, prove the multiplier correct:
<code>
(defthmrp multiplier-correct-v1
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog \"DT_SB4_HC_64_64\"
                                          (list in1 in2)
                                          '(nil nil)
                                          *svl-design*)
                  (mv  (list (loghead 128 (* (sign-ext in1 64)
                                             (sign-ext in2 64))))
                       (svl::make-svl-env)))))
</code>

This proof takes about 1.5 seconds to finish. Alternatively, users can run
a similar proof as follows:

<code>
(progn
  (defconst *input-bindings*
    '((\"IN1\" a)
      (\"IN2\" b)))

  (defconst *out-bindings*
    '((\"result\" out)))

  ;; Another way to state correctness proof for the multiplier.
  ;; Similar to SVTV-run
  ;; takes around 1.5 seconds
  (defthmrp multiplier-correct-v1
    (implies (and (integerp in1)
                  (integerp in2))
             (equal (svl::svl-run \"DT_SB4_HC_64_64\"
                                  (make-fast-alist `((a . ,in1)
                                                     (b . ,in2)))
                                  *input-bindings*
                                  *out-bindings*
                                  *svl-design*)
                    `((out . ,(loghead 128 (* (sign-ext in1 64)
                                              (sign-ext in2 64)))))))))
</code>

</p>

<p>
This program is tested for multipliers up to 1024x1024 with simple partial
products, and 512x512 with Booth Encoded partial products; and they finished in
5-10 minutes each. 
</p> 

<p>
For large multipliers, users may need to increase the stack size in ACL2 image
(e.g., saved_acl2 under you ACL2 directory) and run the proofs again. In our
tests, we have observed SBCL to be faster than CCL; however, for large
multipliers garbage collector of CCL does a better job with @(see
acl2::set-max-mem) and it can finish large proofs when SBCL terminates with memory
errors.  </p>
"

 )
