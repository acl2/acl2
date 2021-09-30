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

(include-book "centaur/svl/portcullis" :dir :system)

(include-book "centaur/fgl/portcullis" :dir :system)

   
(xdoc::defxdoc
 Multiplier-Verification
 :parents (rp-rewriter/applications)
 :short "An efficient library to verify large integer multiplier designs
 following the S-C-Rewriting algorithm."

 :long  " <p> Implemented and verified  completely in ACL2, we  provide a new
 method to  verify complex integer  multiplier designs implemented  in (System)
 Verilog. With a very efficient proof-time scaling factor, this tool can verify
 integer  multipliers that  may  be implemented  with  Booth Encoding,  various
 summation trees  such as Wallace  and Dadda,  and numerous final  stage adders
 such as carry-lookahead.  For example,  we can verify 64x64-bit multipliers in
 around  a  second;  128x128  in  2-4 seconds;  256x256  in  6-12  seconds  and
 1024x1024-bit  multipliers in  around  5  minutes as  tested  with almost  100
 different  designs.  This library  can  also  verify other  multiplier-centric
 designs such as multiply-accumulate and dot-product. Designs can be truncated,
 right-shifted, bit-masked, rounded, saturated, and input sizes can be arbitrary.</p>

  <p>  The outline  of  this  new verification  method  first  appeared in  CAV
2020 (Automated  and Scalable  Verification of  Integer Multipliers  by Mertcan
Temel,   Anna  Slobodova,   Warren   A.   Hunt,   Jr.)    available  here:   <a
href=\"http://doi.org/10.1007/978-3-030-53288-8_23\">
http://doi.org/10.1007/978-3-030-53288-8_23</a>. A follow-up study is to appear
in FMCAD21 by Mertcan Temel and Warran A. Hunt, Jr.. This method is also
described in Mertcan Temel's PhD thesis from University of Texas at Austin.  </p>

<p> Our framework currently supports  (System) Verilog with design hierarchy as
inputs only.  These  designs are translated to @(see  SVL) design without
flattening the adder  modules such as full-adders and  final stage-adders. Then
@(see  RP-Rewriter) are  used  as the  clause-processor to  carry  out all  the
rewriting instead  of the  built-in rewriter,  and our  meta rules  and rewrite
rules dedicated for multiplier designs are used to simplify them and prove them
equivalent to their specification. </p>

<p>  Our  library  uses  various  heuristics  and  modes  to  simplify  various
designs. We give the users the  option to enable/disable some of the heuristics
that might help speed-up the proofs (and/or reduce memory use) or in some cases
help proofs finish.   We enable very aggressive heuristics by  default for best
coverage.   If   you  wish  to   tune  the   performance  of  your   proofs  by
enabling/disabling    these   heuristics,    you    can    check   out    @(see
Multiplier-Verification-Heuristics). Enabling/disabling these heuristics might
help a proof attempt to go through. </p>

<p>  We  present  two demos  that  show  how  this  tool  can be  used  in  new
designs. @(see Multiplier-Verification-demo-1) shows  a very basic verification
case  on  a  stand-alone  64x64-bit  Booth  Encoded  Dadda  multiplier.   @(see
Multiplier-Verification-demo-2) shows  how this tool  can be used on  much more
complex designs where a stand-alone integer multiplier is reused as a submodule
for various operations  such as MAC dot-product and  merged multiplication. It
also shows a simple verification case on a sequential circuit.  </p>

<p>  Alternatively,   we  present  a   different  framework  that   uses  @(see
defsvtv) instead of @(see SVL). Defsvtv is more capable than SVL at
handling combinational loops but it  flattens designs completely. This prevents
our method from working properly because we need to identify instantiated adder
modules. Therefore,  we soundly replace  adder modules with  their identifiable
copies even when  flattened. Then, we call defsvtv on  the redefined multiplier
design and we can verify this test vector with out tool. This mechanism is
described in @(see Multiplier-Verification-demo-3).
</p>

<p> This library can be used to quickly generate counterexamples using an
external SAT solver, or help finish proofs with a SAT solver when our library
fails to finish the job. You may include the book
projects/rp-rewriter/lib/mult/fgl, @(see FGL::FGL) book and use
rp::defthmrp-then-fgl utility instead of rp::defthmrp to submit conjectures to
ACL2. </p>

<p> There  are two older  versions of  this library. If  you would like  to use
those   for    some   reason,    you   may   view    their   demo    files   at
@('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult/demo.lisp')    and
@('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult2/demo.lisp')     .
The second  version implements the  exact method as  described in our  CAV 2020
paper. The third version (i.e., the  library we describe in this documentation)
have some  significant improvements but  the methods are essentially  the same.
</p>
"
)


(xdoc::defxdoc
 Multiplier-Verification-Heuristics
 :parents (Multiplier-Verification)
 :short "Some heuristics that can be enabled/disabled by the user for
 @(see Multiplier-Verification)"
 :long   "<p>Our   @(see  Multiplier-Verification)  system   implements  various
 heuristics to efficiently  verify different designs. Some  of those heuristics
 are applied  for all the designs,  some are specific to  certain corner cases,
 and some are  just alternatives to others that might  prove more beneficial in
 different cases. We  are continually experimenting with  these heuristics, and
 we  let users  control  whether or  not  some of  these  heuristics should  be
 enabled.  By default, we leave our heuristic settings to be very aggressive so
 that   our  tool   is   readily   applicable  to   the   majority  of   design
 patterns. However,  that might  notably slow  down proof-time  performance for
 some designs,  or in  some cases,  they might be  too aggressive  (i.e., cause
 proofs to fail that otherwise would be  successful). If you are not happy with
 the   default   configuration  for   any   reason,   you  may   benefit   from
 enabling/disabling  some  of  our  heuristics by  following  the  instructions
 below.  Beware that  these heuristics  and  related events  might change  over
 time. </p>


<p> UNPACK-BOOTH-LATER </p>

<p>In  Booth encoded multipliers,  partial products are generated  with basic
logical gates. We perform algebraic rewriting on these gates when rewriting the
overall circuit.  In some corner  cases, this can prevent  some simplifications
and  cause a  proof attempt  to fail.  We implement  a heuristic  that we  call
\"unpack-booth-later\" that doesn't perform  algebraic rewriting right away but
leaves logical gates  from Booth encoding intact. When all  the other rewriting
is finished,  only then these gates  are rewriting in the  algebraic form. This
heuristic is not expected to be necessary for the majority of designs and it is
disabled by default. If a proof attempt of a Booth encoded design is failing,
we recommend that you enable this heuristic: </p>

<code> @('(rp::enable-unpack-booth-later <t-or-nil>)') </code>


<p> STINGY-PP-CLEAN </p>
<p>  Booth Encoded  designs produce  a  lot of  terms  as part  of the  partial
product  (pp) logic.   These  terms eventually  cancel out  each  other as  the
multiplier  designs are  expanded and  simplified.  This  happens through  some
\"pp-clean\"  operations. By  default,  \"pp-clean\" is  rather aggressive  and
creates a lot of copies of the same terms. When \"stingy-pp-clean\" is enabled,
this  operation  is  done  more   selectively  which  can  deliver  performance
improvements.  That  can range  from a  10% improvement to  2-3x or  even more,
depending on  many different  factors.  This heuristic  might cause  some proof
attempts to fail and it is disabled by default, and its setting is ignored when
unpack-booth-later is enabled.  </p>

<code> @('(rp::enable-stingy-pp-clean <t-or-nil>)') </code>


<p>S-PATTERN1-REDUCE</p>

<p> Enabled by default, this heuristic can cover some corner
cases  that emerge  especially in  merged  multipliers. This  usually does  not
affect the proof-time performance, but in some cases (e.g., constant propagated
designs), it can have a negative  impact. We have never observed this heuristic
to cause a proof to fail, therefore it is enabled by default. To disable it
(rp::enable-c-pattern1-reduce         nil),         or        to         enable
it (rp::enable-c-pattern1-reduce t).
</p>

<code> @('(rp::enable-s-pattern1-reduce <t-or-nil>)') </code>

<p>PATTERN2-REDUCE</p>
<p>            Similar       to     
S-PATTERN1-REDUCE. Enabled  by default. To  disable (rp::enable-pattern2-reduce
nil), to enable (rp::enable-pattern2-reduce t) </p>

<code> @('(rp::enable-pattern2-reduce <t-or-nil>)') </code>

<p>PATTERN3-REDUCE</p>

<p>  Similar  to other \"pattern-reduce\" heuristics  but it is
 too  aggressive  and  disabled by  default.  It  removes \"1\"
instances from
(s  1  others)  and  (c  1  others) terms.   We  have  added  this  pattern  for
experimentation  purposes and  have yet  to  observe its  usefulness. This  can
cause proofs to go through very slowly, therefore,  it is  disabled by
default. </p>

<code> @('(rp::enable-pattern3-reduce <t-or-nil>)') </code>


<p>C-OF-S-FIX-MODE</p>
<p>   We have  found mainly three  different efficient  ways to
merge sum of two instances of \"c\" terms. The first method is described in our
CAV2020 paper (see @(see Multiplier-Verification) for the link) and it pertains
to converting \"c\" terms to \"d\"  terms. We discontinued this support in this
new  library but  instead started  experimenting with  easier-to-debug methods.
You can  switch between these  two methods by  (rp::enable-c-of-s-fix-mode nil)
and
(rp::enable-c-of-s-fix-mode t). By default, c-of-s-fix-mode is enabled. We have
seen   that  the   performance  between   two  methods   is  very   similar  in
general. However, if c-of-s-fix-mode and stingy-pp-clean are both disabled, you
may  observe  a  significant  reduction in  proof-time  performance  for  large
Booth-Encoded designs. Disabling c-of-s-fix-mode may cause problems with the
unpack-booth-later heuristic.
</p>

<code> @('(rp::enable-c-of-s-fix-mode <t-or-nil>)') </code>

")


(xdoc::defxdoc
 Multiplier-Verification-demo-1
 :parents (Multiplier-Verification)
 :short "First demo for @(see  Multiplier-Verification) showing how an isolated
 integer multiplier is verified."
 :long " <p> Below is a demo that  shows how to input a multiplier design coded
in (System) Verilog into ACL2, and verify it efficiently. We choose a 64x64-bit
Booth Encoded Dadda Tree multiplier with  Han-Carlson adder as our example.  If
you  wish, you  can skip  to @(see  Multiplier-Verification-demo-2) for  a more
complex arithmetic module.  </p>


<p>   The   exact   events   given   in   this   page   are   also   given   in
@('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult3/demo/demo-1.lisp')
</p>

<p>
1. Include the books to convert Verilog designs to SVL format.
</p>
<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system)
(include-book \"centaur/svl/top\" :dir :system)
</code>
<p>
@(see SVL) system uses @(see SV) and @(see VL) packages.
</p>

<p> 2. Load VL design for  the modules in DT_SB4_HC_64_64_multgen.sv. This file
is                                 located                                under
@('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult3/demo').   This is
a 64x64 Signed,  Booth radix-4 encoded, Dadda Tree  integer multiplier.  <code>
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
3. Load SV design:
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
4. Load SVL Design:
<code>
@('(acl2::defconsts (*svl-design* rp::rp-state)
                 (svl-flatten-design *sv-design*
                                     *vl-design*
                                     :dont-flatten :all))
')
</code>

</p>

<p>  SVL  design is  a  simulation-ready  version  of  SV design  with  circuit
hierarchy maintained. Note  that we are telling the program  not to flatten all
the modules (with the ':dont-flatten :all' argument), which will reserve design
hierarchy, which  we will  use while  verifying the module.   If users  wish to
flatten some modules, they should at  least have the adder module names instead
of ':all'. See @(see svl-flatten-design).  </p>



<p>
5. Include the book that has the rewrite and meta rules
for multiplier proofs:
<code>
(include-book \"projects/rp-rewriter/lib/mult3/svl-top\" :dir :system)
</code>
</p>


<p>
6. Rewrite the adder modules with our specification:

</p>

<code>
(def-rp-rule svl-run-phase-of-FullAdder
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (svl::svl-run-phase-wog \"fa\"
                                          (list x y z)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (s-c-spec (list x y z))
                      svl::*empty-state*)))
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
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (s-c-spec (list x y))
                      svl::*empty-state*)))
  :hints ((\"Goal\"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))
</code>

<p>
The multiplier we are working on uses two types of bit-level adders: a
full-adder with module name \"fa\", and a half-adder with module name
\"ha\". We rewrite them with the lemmas given above. We use @(see rp::def-rp-rule)
to save these in the @(see rp::RP-Rewriter)'s rule-set. ACL2 can prove these lemmas
easily by case-splitting with @('bitp') and trying all the combinations.
</p>

<code>
(defthmrp final-stage-adder-correct
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog \"HC_128\"
                                          (list in1 in2)
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv (list (loghead 129 (+ (loghead 128 in1)
                                            (loghead 128 in2)))
                      svl::*empty-state*)))
  :disable-meta-rules (s-c-spec-meta)
  :enable-rules rp::*adder-rules*)
</code>

<p>
This multiplier  module uses  a Han-Carlson parallel  prefix adder  with module
name \"HC_128\".   We use our  suggested rewriting  scheme to prove  this adder
equivalent  to   our  specification.   The  macro   @(see  rp::defthmrp)  calls
RP-Rewriter as a  clause processor. In proofs for adder  modules, the arguments
':disable-meta-rules (s-c-spec-meta)' and ':enable-rules rp::*adder-rules*' are
standard. These arguments disable the  rules specific to multiplier modules and
enable the ones for adders.

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
                                          svl::*empty-state*
                                          *svl-design*)
                  (mv  (list (loghead 128 (* (sign-ext in1 64)
                                             (sign-ext in2 64))))
                       svl::*empty-state*))))
</code>

This proof takes about 1.5 seconds to finish. Alternatively, users can run
a similar proof as follows with a simulation pattern instead:

<code>
(progn
  (defconst *input-bindings*
    '((\"IN1\" a)
      (\"IN2\" b)))

  (defconst *output-bindings*
    '((\"result\" out)))

  ;; Another way to state correctness proof for the multiplier.
  ;; Similar to SVTV-run
  ;; takes around 1.5 seconds
  (defthmrp multiplier-correct-v1
    (implies (and (integerp in1)
                  (integerp in2))
             (equal (svl-run \"DT_SB4_HC_64_64\"
                             `((a . ,in1)
                               (b . ,in2))
                             *input-bindings*
                             *output-bindings*
                             *svl-design*)
                    `((out . ,(loghead 128 (* (sign-ext in1 64)
                                              (sign-ext in2 64)))))))))
</code>


Once we can successfully submit one of these events, we can conclude that the
given design is functionally correct.

</p>

<p> This program  is tested for multipliers up to  1024x1024; and they each finished
in at most 5 minutes on our machines.  </p>

<p>
For large multipliers, users may need to increase the stack size in ACL2 image
(e.g., saved_acl2 under you ACL2 directory) and run the proofs again. In our
tests, we have observed SBCL to be faster than CCL; however, for large
multipliers garbage collector of CCL does a better job with @(see
acl2::set-max-mem) and it can finish large proofs when SBCL terminates with memory
errors. 
</p>


<p>
You may continue to @(see Multiplier-Verification-demo-2).
</p>

"
 )

(xdoc::defxdoc
 Multiplier-Verification-demo-2
 :parents (Multiplier-Verification)
 :short  "The second  demo  for   @(see  Multiplier-Verification)  showing  how  an
 industrial-design-mimicking module  including a MAC, dot-product  and merged
 multipliers can be verified."
 :long "<p> In the first  demo (@(see Multiplier-Verification-demo-1)), we have
 shown how  our tool can  be used  on an isolated  multiplier.  This is  a good
 starting  point;  however,  real-world  applications  of  integer  multipliers
 involve more intricate  design strategies. We tried to recreate  some of those
 strategies  and   compiled  a   more  complex   multiplier  module   given  in
 @('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult3/demo/integrated_multipliers.sv'). You
 may            find            this           file            on            <a
 href=\"https://github.com/acl2/acl2/blob/master/books/projects/rp-rewriter/lib/mult3/demo/integrated_multipliers.sv\"
 target=\"_blank\"> GitHub </a> as well.   This module allocates four identical
 33x33-bit  signed  multipliers,  two  final  stage  adders  and  some  smaller
 reduction  trees to  perform  different multiplier  operations. These  include
 signed/unsigned  four-laned 32x32-bit  multiply-add (or  multiply-accumulate),
 one-lane  64x64-bit  multiply-add,  4-32x32-bit  dot-product  modes  (with  or
 without an accumulator). These operations  can be combinational or sequential,
 in which case  an accumulator is used to store  results across different clock
 cycles. </p>


<p>  The fact  that  this multiplier  module reuses  the  same smaller  integer
 multipliers for different  modes of operations, the design  itself is slightly
 more  complicated   which  may   cause  further  challenges   to  verification
 systems.  Therefore, we  show  how our  tool  can handle  such  cases and  our
 framework to verify them with a similar efficiency as stand-alone multipliers.
 The    same    events    we    give     below    are    also    included    in
 @('<your-acl2-directory>/books/projects/rp-rewriter/lib/mult3/demo/demo-2.lisp'). </p>

<p> 1.  Include necessary books.  @(see SVL) system uses  @(see SV)
and @(see VL) packages. So we start with them.
</p>

<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system) ;; takes just a few seconds
(include-book \"centaur/svl/top\" :dir :system) ;; takes just a few seconds
</code>

<p> Then, include has the rewrite and meta rules to carry out simplification of
multiplier modules:
</p>

<code>
(include-book \"projects/rp-rewriter/lib/mult3/svl-top\" :dir :system)
</code>


<p> 2. Convert the System Verilog design to SVL design. All three events take a few
seconds in total. </p>

<p> Load VL design: </p>
  <code> @('(acl2::defconsts
   (*mult-vl-design* state)
   (b* (((mv loadresult state)
         (vl::vl-load (vl::make-vl-loadconfig
                       :start-files '(\"integrated_multipliers.sv\")))))
     (mv (vl::vl-loadresult->design loadresult) state)))
')
</code>

<p> Load SV design: </p>
<code>
@('
(acl2::defconsts
   (*mul-sv-design*
    *simplified-good*
    *simplified-bad*)
   (b* (((mv errmsg sv-design good bad)
         (vl::vl-design->sv-design \"Integrated_Multiplier\"
                                   *mult-vl-design* (vl::make-vl-simpconfig))))
     (and errmsg
          (acl2::raise \"~@0~%\" errmsg))
     (mv sv-design good bad)))
')
</code>

<p> Load SVL Design: </p>
<code>
(acl2::defconsts (*mult-svl-design* rp::rp-state)
                 (svl-flatten-design *mul-sv-design*
                                     *mult-vl-design*
                                     :dont-flatten :all))
</code>


<p> 

3. Create rewrite rules for adder modules.

</p>


<p> For full-adder: </p>
<code> 
@('
(def-rp-rule svl-run-phase-of-FullAdder
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (svl::svl-run-phase-wog \"fa\"
                                          (list x y z)
                                          svl::*empty-state*
                                          *mult-svl-design*)
                  (mv (s-c-spec (list x y z))
                      svl::*empty-state*)))
  :hints ((\"Goal\"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))
')
</code>
<p> For half-adder: </p>
<code> 
@('
(def-rp-rule svl-run-phase-of-HalfAdder
  (implies (and (bitp x)
                (bitp y))
           (equal (svl::svl-run-phase-wog \"ha\"
                                          (list x y)
                                          svl::*empty-state*
                                          *mult-svl-design*)
                  (mv (s-c-spec (list x y))
                      svl::*empty-state*)))
  :hints ((\"Goal\"
           :do-not-induct t
           :in-theory (e/d (bitp)
                           ()))))
')
</code>
<p> For the final stage adder: </p>
<code> 
@('
(defthmrp LF_131-final-stage-adder-correct
  (implies (and (integerp in1)
                (integerp in2))
           (equal (svl::svl-run-phase-wog \"LF_131\"
                                          (list in1 in2)
                                          svl::*empty-state*
                                          *mult-svl-design*)
                  (mv (list (loghead 132 (+ (loghead 131 in1)
                                            (loghead 131 in2))))
                      svl::*empty-state*)))
  :disable-meta-rules (s-c-spec-meta)
  :enable-rules rp::*adder-rules*)
')
</code>



<p> 4. The integrated multiplier module has an input signal called
@('mode'). As the name implied, this signal determines the mode of operation
(e.g., dot-product or  4-lane multiplication) that the module needs  to run. We
create a  new function  also called  @('mode') to calculate  the value  of this
signal. This will make  our proofs more readable and easier  to manage. You may
find a description of how this signal should be assigned in the comments in the
Verilog file.</p>

<code>
@('
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
        (or (cw \"One and only one of dot-product, four-lanes-lo,
four-lanes-hi and one-lane should be set to 1.~%\")
            (hard-error 'mode \"\" nil)
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
')
</code> 

<p> 5.  We  are now ready to  verify the top module  for various multiplication
modes. First,  we verify various  combinational modes (one-lane  64x64-bit MAC
4-32x32-bit  dot-product, and four-lane  32x32-bit  multiplication  with lower  and
higher half truncation), then we show verification for a sequential mode
(accumulated dot-product).  </p>

<p>
We define our first simulation pattern. Since we are currently only interested
in the  combinational functionality,  we set  \"clk\" to  \"0\", and  the other
signals to some free variables.

  <code> @('
(defconst *in-binds-one-lane*
  '((\"clk\" 0)
    (\"IN1\" in1)
    (\"IN2\" in2)
    (\"IN3\" in3)
    (\"mode\" mode)))

(defconst *out-binds*
  '((\"result\" result)))
')
</code>
</p>

<p> 

 Below is our first correctness proof  of a multiplication mode SVL-RUN returns
an association list  of all the variables stated in  *out-binds*. In this case,
there is only one entry whose key  is 'result'. We state the expression of this
signal  in  our  conjecture.  Here  it  is  [in3  +  in2*in1  (both
sign-extended)] and the complete result is  truncated at 128 bits.  This is the
specification of this multiplication mode.   When writing the specification, it
is imperative to have @(see acl2::loghead) wrapping the arithmetic functions as
seen here. Proving this lemma takes around a second. Alternatively, we could set
in3 to  \"0\", and verify  only the multiplication  function (but not  MAC). In
fact, we could set any portion of any input signals to any constants.

<code>
 @('
(defthmrp signed-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (svl-run \"Integrated_Multiplier\"
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
')
</code>
</p>

<p>

We  can  prove  the  same  for  the mode  for  unsigned  numbers  by  changing  the
specification accordingly:
<code>
@('
(defthmrp unsigned-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (svl-run \"Integrated_Multiplier\"
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

')
</code>
</p>


<p> Now, let's verify  the dot product operation. To make  it more readable, we
define another input bindings  alist for the dot product mode.  We split two of
the input signals to four lanes. This conjecture, similarly, takes about a second to
prove. We omit the proofs for unsigned for brevity.

<code>
@('
(defconst *in-binds-dot-product*
  '((\"clk\" 0)
    (\"IN1[31:0]\" in1_0)
    (\"IN2[31:0]\" in2_0)
    (\"IN1[63:32]\" in1_1)
    (\"IN2[63:32]\" in2_1)
    (\"IN1[95:64]\" in1_2)
    (\"IN2[95:64]\" in2_2)
    (\"IN1[127:96]\" in1_3)
    (\"IN2[127:96]\" in2_3)
    (\"IN3\" in3)
    (\"mode\" mode)))

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
           (equal (svl-run \"Integrated_Multiplier\"
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

')
</code>

</p>

<p> Another mode is four-lane multiplication that truncate at the lower half of
 multiplication.   Similarly,  we  define   new  input  and  output  simulation
 patterns, splitting all three inputs and the output to four lanes:

<code>
@('
(defconst *in-binds-four-lanes*
  '((\"clk\" 0)
    (\"IN1[31:0]\"   in1_0)
    (\"IN2[31:0]\"   in2_0)
    (\"IN1[63:32]\"  in1_1)
    (\"IN2[63:32]\"  in2_1)
    (\"IN1[95:64]\"  in1_2)
    (\"IN2[95:64]\"  in2_2)
    (\"IN1[127:96]\" in1_3)
    (\"IN2[127:96]\" in2_3)
    (\"IN3[31:0]\"   in3_0)
    (\"IN3[63:32]\"  in3_1)
    (\"IN3[95:64]\"  in3_2)
    (\"IN3[127:96]\" in3_3)
    (\"mode\"        mode)))

(defconst *out-binds-four-lanes*
  '((\"result[31:0]\"   result0)
    (\"result[63:32]\"  result1)
    (\"result[95:64]\"  result2)
    (\"result[127:96]\" result3)))

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
           (equal (svl-run \"Integrated_Multiplier\"
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
')
</code>

We can  prove a  similar lemma  for unsigned  mode as  well.  Finally,  we have
another combinational  mode that is  four-lane multiplication that  truncate at
the higher  half.  Function @(see acl2::ash)  right or left shift  numbers.  In
this case, we right shift the multiplication  result by 32 bits to retrieve the
higher end of the result.

<code>
@('
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
           (equal (svl-run \"Integrated_Multiplier\"
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
')
</code>
</p>

<p> 

Finally, let's  show our  framework on  a sequential  operation. The  design in
integrated_multipliers.sv has an  accumulator that can store  the result across
different clock  cycles. We can  use this feature to  increase the size  of dot
product. So we  create a simulation pattern where we  load the accumulator with
an initial  value, and perform two  dot-product operations in two  clock cycles
and accumulate the  result. So we create  a 8-32x32-bit dot product  out of the
existing 4-32x32-bit one.

<code>
@('
(defconst *in-binds-dot-product-with-acc*
  `((\"clk\" 0 1 ~)
    (\"IN1[31:0]\"   0 0 in1[0] 0 in1[4])
    (\"IN2[31:0]\"   0 0 in2[0] 0 in2[4])
    (\"IN1[63:32]\"  0 0 in1[1] 0 in1[5])
    (\"IN2[63:32]\"  0 0 in2[1] 0 in2[5])
    (\"IN1[95:64]\"  0 0 in1[2] 0 in1[6])
    (\"IN2[95:64]\"  0 0 in2[2] 0 in2[6])
    (\"IN1[127:96]\" 0 0 in1[3] 0 in1[7])
    (\"IN2[127:96]\" 0 0 in2[3] 0 in2[7])
    (\"IN3\" acc-init-val)
    (\"mode\" ,(mode :acc-on t
                   :dot-product t
                   :reload-acc t)
     mode mode mode mode)))

;; result is obtained on the 5th phase.
(defconst *out-binds-with-acc*
  '((\"result\" _ _ _ _ result)))

')
</code>
</p>
<p> In the previous proofs given above, we stated the specification of each
mode explicitly in the conjectures. We can alternatively wrap these
specifications with new functions for better readability. So we create a dot
product specification function as given below.

<code>
@('
(define dot-product-spec ((in1 integer-listp)
                          (in2 integer-listp)
                          (dot-product-size natp)
                          (signed booleanp)
                          (acc-init-val integerp)
                          (acc-size natp))
  :verify-guards nil
  :guard (and (equal dot-product-size (len in1))
              (equal dot-product-size (len in2)))
  (if (zp dot-product-size)
      (loghead acc-size acc-init-val)
    (let* ((dot-product-size (1- dot-product-size)))
      (loghead acc-size
               (+ (if signed
                      (* (sign-ext (nth dot-product-size in1) 32)
                         (sign-ext (nth dot-product-size in2) 32))
                    (* (loghead 32 (nth dot-product-size in1))
                       (loghead 32 (nth dot-product-size in2))))
                  (dot-product-spec in1
                                    in2
                                    dot-product-size
                                    signed
                                    acc-init-val
                                    acc-size)))))
  ///
  ;; We need to add the definition rule of this function to RP-Rewriter so that
  ;; it can know to expand it.
  (add-rp-rule dot-product-spec))
')
</code>
</p>

<p> Then, we can state the correctness for the 8-32x32-bit dot product mode as:
<code>
@('
(defthmrp signed-dot-product-with-acc-is-correct
  (b* ((signed t) ;; set up the parameters first.
       (acc-size 128)
       (dot-product-size 8))
    (implies (and (integer-listp in1) 
                  (integer-listp in2)
                  (integerp acc-init-val)
                  (equal (len in1) dot-product-size) ;; necessary to show that
                  ;; \"nth\" function returns a valid value (an integer).
                  (equal (len in2) dot-product-size) ;; same as above.
                  )
             (equal (svl-run \"Integrated_Multiplier\"
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
                    `((result . ,(dot-product-spec in1 in2 dot-product-size 
                                                   signed acc-init-val acc-size)))))))
')
</code>
</p>


")


(xdoc::defxdoc
 Multiplier-Verification-demo-3
 :parents (Multiplier-Verification)
 :short  "Another  demo  for   @(see  Multiplier-Verification) showing how
 @(see svtv-run) can be used by overriding the adder modules."
 :long "

<p>This demo  shows how  this tool can  be used to  verify a  multiplier module
translated  with @(see  defsvtv). This  is done  by overriding  the adder
modules in the original design before calling defsvtv.  </p>

<p>Our tool requires identifying adder modules used by the candidate multiplier
design.  When defsvtv  is called, the design is flattened  completely.  That is
why we  mainly use SVL system  where design hierarchy can  be maintained during
symbolic simulation.  However, the @(see SVL) system is not as capable as
defsvtv at handling  very complex designs that might  have combinational loops.
Therefore, we provide an alternative way to  using SVL (which was used in @(see
Multiplier-Verification-demo-1)  and   @(see  Multiplier-Verification-demo-2)).
First, we  create copies  of the adder  modules (e.g.,  half-adder, full-adder,
final stage adder) and we redefine  them.  The redefined adder modules have the
same functionality but  use the Verilog \"+\" arithmetic  operator only.  Then,
we override the  original adder modules in  the SV design and we  create a test
vector  with  defsvtv  with  these  redefined modules.   This  helps  our  tool
differentiate the adder modules individually, and rewrite them in a similar way
as SVL designs.  </p>

<p> Replacing the adder modules without any check would not be safe. So we also
perform a  sanity check. We have  a macro \"replace-adders\" that  replaces the
adders in the  original SV design, and  create a new one. As  that happens, the
macro also calls our tools to make sure that the replacement adder modules have
the same signature as the original  ones, and they are functionally equivalent.
</p>

<p>   For   this   tutorial,   we   use   the   same   design   as   in   @(see
Multiplier-Verification-demo-1), which is a 64x64-bit Dadda tree, Booth Encoded
multiplier with Han-Carlson  final stage adder. The same events  given here can
also be  found in  /books/projects/rp-rewriter/lib/mult3/demo/demo-3.lisp. This
file   also   shows   the   same   procedure  for   the   module   from   @(see
Multiplier-Verification-demo-2), which is a more complex multiplier module that
can perform  MAC dot  product etc.  You can see  these demo  files also  on <a
href=\"https://github.com/acl2/acl2/blob/master/books/projects/rp-rewriter/lib/mult3/demo/\"
target=\"_blank\">GitHub</a> </p>

<p> Step 1. Include the necessary books: </p>

<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system)
(include-book \"projects/rp-rewriter/lib/mult3/svtv-top\" :dir :system)
</code>


<p> Step 2. Create VL and SV designs for the input design </p>
<code>
@('
(acl2::defconsts
 (*original-mult1-vl-design* state)
 (b* (((mv loadresult state)
       (vl::vl-load (vl::make-vl-loadconfig
                     :start-files '(\"DT_SB4_HC_64_64_multgen.sv\")))))
   (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
 (*original-mult1-sv-design*)
 (b* (((mv errmsg sv-design & &)
       (vl::vl-design->sv-design \"DT_SB4_HC_64_64\"
                                 *original-mult1-vl-design*
                                 (vl::make-vl-simpconfig))))
   (and errmsg
        (acl2::raise \"~@0~%\" errmsg))
   sv-design))
')
</code>


<p> Step 3. Replace the adder modules: </p>

<p>   We   cannot   use   our   tool    on   a   test   vector   created   with
*original-mult1-sv-design* because the  adder modules in this  design get mixed
up with each other when flattened.  So we will create another test vector whose
adder modules will be distinguishable from  the rest of the circuit.  For that,
we  created  alternative versions  of  the  adder  modules  used in  the  input
multiplier  design,  and  saved   them  in  \"adders_with_plus.sv\".   The  new
definitions  of  these adder  modules  (\"ha\",  \"fa\", and  \"HC_128\")  only
consist of the \"+\" operator. Examples  are given below.  Pay attention to the
definition of \"ha\"; there is an extra, redundant \"+ 0\" term. This makes the
pattern from half-adder to resemble that of a full-adder. This is a work-around
to a strange problem, and it can be vital to some proofs.  </p>

<code>
@('
module fa (
        input logic x,
        input logic y,
        input logic z,
        output logic s,
        output logic c);
    
    assign {c,s} = x + y + z;
endmodule // fa
module ha (
        input logic a,
        input logic b,
        output logic s,
        output logic c);
    assign {c,s} = a + b + 0;
endmodule // ha
')
</code>

<p>
Using   the   macro   below,   we   create  a   new   SV   design   instance
(*redefined-mult-sv-design*)  that is  a copy  of *original-mult1-sv-design*
but  with the  stated  adder modules  replaced.  In  order  to perform  this
replacement soundly, this macro also proves that the replacement modules are
equivalant to the original (when \":sanity-check\" argument is set to t).
</p>

<p>
If the  adders used  in the  original design  are parameterized  (see Verilog
Parameters),   then  you'd   need  to   create   a  dummy   top  module   in
adders_with_plus.sv (or any  file name you'd like), and  instantiate all the
redefined adders the same way as the original design instantiates them. This
is to ensure that SV design creates instances of the same modules. Then pass
the name of  this dummy top module with \":dummy-top\"  argument.  For example
:dummy-top \"dummy_top_module\".  And as the  adder module name(s), you'd need
to  pass  the   \"SV\"  version  of  the  instantiated  module   name  such  as
\"ha$WIDTH=1\".
</p>

<code>
@('
(replace-adders :new-sv *redefined-mult1-sv-design*
                :original-sv *original-mult1-sv-design*
                :original-vl *original-mult1-vl-design*
                ;; prove that the replaced adders are equivalent to the originals:
                :sanity-check t
                ;; whether or not the non-essentials events be exported:
                :local nil
                ;; name of the file(s) that has the replacement adder modules:
                :new-adders-file (\"adders_with_plus.sv\")
                ;; Name of the modules to be replaced:
                :adder-module-names (\"ha\" \"fa\" \"HC_128\"))
')
</code>


<p> Step 4. Create the test vector with @(see defsvtv): </p>

<code>
@('
(defsvtv redefined-mult1-svtv
  :mod *redefined-mult1-sv-design*
  :inputs '((\"IN1\" a)
            (\"IN2\" b))
  :outputs
  '((\"result\" res)))
')
</code>

<p> Step 5. Run our tool to verify that the multiplier design is correct: </p>

<code>
@('
(defthmrp multiplier-correct-for-redefined-design
  (implies (and (integerp in1)
                (integerp in2))
           (equal svtv-run (redefined-mult1-svtv)
                  `((a . ,in1)
                    (b . ,in2)))
           `((res . ,(loghead 128 (* (sign-ext in1 64)
                                     (sign-ext in2 64))))))))
')
</code>

<p> As mentioned above, there are more examples in
/books/projects/rp-rewriter/lib/mult3/demo/demo-3.lisp
</p>
"
)
