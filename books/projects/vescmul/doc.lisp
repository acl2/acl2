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

(xdoc::defxdoc Multiplier-Verification
  :parents (rp-rewriter/applications)
  :short "Verified Implementation of S-C-Rewriting algorithm for Multiplier
  Verification"
  :long "See @(see vescmul)")


(xdoc::defxdoc
  vescmul
  :parents (rp-rewriter/applications)
  :short "An efficient library to verify large integer multiplier designs
 following the S-C-Rewriting algorithm."

  :long  " <p> Implemented and verified  completely in ACL2, we  provide a new
 method to  verify complex integer  multiplier designs implemented  in (System)
 Verilog. With a very efficient proof-time scaling factor, this tool (VeSCmul) can verify
 integer  multipliers that  may  be implemented  with  Booth Encoding (e.g., radix-16),  various
 summation trees  such as Wallace  and Dadda,  and numerous final  stage adders
 such as carry-lookahead.  For example,  we can verify 64x64-bit multipliers in
 around  a  second;  128x128  in  2-4 seconds;  256x256  in  6-12  seconds  and
 1024x1024-bit  multipliers in  around  5-15  minutes as  tested  with
 thousands of
 different  designs.  This library  can  also  verify other  multiplier-centric
 designs such as multiply-accumulate and dot-product, or even be used in other
 verification flows to verify floating-point operations. Designs can be truncated,
 right-shifted, bit-masked, rounded, saturated, and input sizes can be
 arbitrary. This library now supports flattened designs.</p>

<p> This method is called S-C-Rewriting and the tool is called VeSCmul
(Verified Implementation of S-C-Rewriting algorithm for Multiplier
  Verification)</p>

  <p>  The outline  of  this  new verification  method  first  appeared in  CAV
2020 (Automated  and Scalable  Verification of  Integer Multipliers  by Mertcan
Temel,   Anna  Slobodova,   Warren   A.   Hunt,   Jr.)    available  here:   <a
href=\"http://doi.org/10.1007/978-3-030-53288-8_23\">
http://doi.org/10.1007/978-3-030-53288-8_23</a>. A follow-up study appeared
in FMCAD21 by Mertcan Temel and Warran A. Hunt, Jr. (<a
href=\"http://doi.org/10.34727/2021/isbn.978-3-85448-046-4_13\">
http://doi.org/10.34727/2021/isbn.978-3-85448-046-4_13</a>). This method is also
described in Mertcan Temel's (<a
href=\"https://repositories.lib.utexas.edu/handle/2152/88056\">
Ph.D. thesis</a>) from University of Texas at Austin. These papers describe
this method as working on hierarchical reasoning; however, VeSCmul now supports
flattened designs as well. More papers  are
coming soon.   </p>

<p> Our framework currently supports  (System) Verilog. In one of our schemes,
we use @(see sv::defsvtv$) (also see @(see sv::sv-tutorial)) to simulate
designs. This SVTV system has been used for complex design at Centaur
Technology and now at Intel Corporation. SVTV system flattens designs. The
multiplier verification program still
supports other simulators such as @(see SVL) but we now only use SVTV. </p>

<p>  This  library  uses  various  heuristics  and  modes  to  simplify  various
designs. Users have the  option to enable/disable some of the heuristics
that might help speed-up the proofs (and/or reduce memory use) or in some cases
help proofs finish.     Aggressive heuristics are enabled by  default for best
coverage.   If   you  wish  to   tune  the   performance  of  your   proofs  by
enabling/disabling    these   heuristics,    you    can    check   out    @(see
vescmul-heuristics). Enabling/disabling these heuristics might
help a proof attempt to go through, but in some cases, it may cause others to fail. </p>

<h3>Quick Start</h3>

<p> If you have a combinational multiplier design you need to verify, you may
follow these steps. </p>

<ol>
<li> Install ACL2 and certify books. </li>
<li> Start ACL2 and submit:
<code> @('(include-book \"projects/vescmul/top\" :dir :system)')
</code>
</li>

<li> Parse the Verilog file you'd like. For example:
<code> @('
(vesmul-parse :file \"DT_SB4_HC_64_64_multgen.sv\"
              :topmodule \"DT_SB4_HC_64_64\"
              :name my-multiplier-example)
')
</code>
</li>
<li> Verify that design:
<code> @('
(vescmul-verify :name my-multiplier-example
                :concl (equal result ;; -> output signal name
                              ;; design specification ->
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')
</code>

Here, @(see logext) sign-extends its argument, and @(see loghead) zero-extends it.

</li>
</ol>

<p> See @(see vesmul-parse) and @(see vescmul-verify) for more
ways to use these utilities. </p>


<p> Including projects/vescmul/top everytime can take a long time
(almost a minute). However, you can save an executable with that book in it to
quickly pull up this multiplier verification library. See @(see
acl2::save-exec). Alternatively, download a <a
href=\"https://temelmertcan.github.io/vescmul.zip\">package</a> that does that
for you. This package also includes some demo files.</p> 

<p> Various demos in much more detail are present to  show  how  this  tool  can be  used  in  new
designs.  @(see Multiplier-Verification-demo-1) shows  a very basic verification
case  on  a  stand-alone  64x64-bit  Booth  Encoded  Dadda  multiplier.   @(see
Multiplier-Verification-demo-2) shows  how this tool  can be used on  much more
complex designs where a stand-alone integer multiplier is reused as a submodule
for various operations  such as MAC dot-product and  merged multiplication. It
also shows a simple verification case on a sequential circuit. Finally, @(see
Multiplier-Verification-demo-3) shows how hierarchical reasoning may be used if
it ever becomes necessary to provide hints to the program. </p>

<h3>Calling a SAT solver after rewriting is done </h3>

<p> This library can be used to quickly generate counterexamples using an
external SAT solver, or help finish proofs with a SAT solver when our library
fails to finish the job. By default, glucose is used as SAT solver. This can be
configured to call a different SAT solver (see @(see fgl::fgl-solving)).</p>

<p> If you are using macros from Quick Start above, then \":then-fgl t\" argument as shown below will be enough to
call FGL, which will invoke a SAT solver after VeSCmul finishes rewriting:
<code> @('
(vescmul-verify :name my-multiplier-example
                :then-fgl t
                :concl (equal result 
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')
</code>
</p>


<h3>Exporting a Verilog file after the adder detection stage</h3>

<p> VeSCmul allows users to export a Verilog file after the adder detection
stage. The exported file contains basic adder modules and a large Verilog module
instantiating those adder modules.  The exported module is expected to be
equivalant to the original design. The difference will be the exported Verilog
module will have the design hierarchy around adder
components (even if the original design did not have any design hierarchy). If
the original design had any complex adders (e.g., 4-to-2 compressors, parallel
prefix adders), the exported module is expected to have replaced those with
only simple full/half-adders. Researchers may use this feature in their verification flows. </p>

<p> To use this tool, simply run: </p>

<code>
@('(export-to-verilog-after-adder-detection \"my-mult_module_with_hier\")')
</code>
<p> IMPORTANT: This program
should be run after the @(see vescmul-verify) event for the desired
multiplier design. The vescmul-verify event does not need to succeed for
this to work; that is, you can set the :keep-going flag and try to prove a false conjecture and the
export-to-verilog-after-adder-detection program can still export the processed design
for you anyway.  </p>


<p> The Verilog translation  is not
verified and it can potentially output a design with problems (syntactical or
purely functional). Therefore, users are strongly recommended to perform a
sanity check.  This program allows a reliable sanity
check mechanism, which performs
formal equivalance checking between the exported desig the original one. For
sanity check, run the following events:
</p>

<code>
@('
;; First load some libraries and setup AIG transforms for fast equivalance checking.
(progn
  (local (include-book \"centaur/ipasir/ipasir-backend\" :dir :system))
  (local (include-book \"centaur/aignet/transforms\" :dir :system))
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

;; Export the multiplier design and perform the sanity check. 
(export-to-verilog-after-adder-detection \"my-mult_module_with_hier\"
                                         :sanity-check t)

')
</code>

<p> Above, the first set of events configures FGL to perform AIG transformations which are
essential for equivalance checking to finish in a timely manner. You may need
to set up the @(see ipasir::ipasir) libraries before this if you are setting up
for the first time. If the
above export-to-verilog-after-adder-detection event succeeds, it means that the
exported design is proved to be equivalant to the original design. Speed of
sanity check is usually high but it can vary, and tweaking and tuning the parameters
above in
transforms-config may make a huge difference.
</p>
<p> If need be, another way to perform sanity check is as follows. The run-time performance of this
method may be better or worse. </p>
<code>
(export-to-verilog-after-adder-detection \"my-mult_module_with_hier\"
                                         :sanity-check :rp-then-fgl)
</code>

"
  )

(xdoc::defxdoc Multiplier-Verification-Heuristics
  :parents (vescmul-heuristics)
  :short "Verified Implementation of S-C-Rewriting algorithm for Multiplier
  Verification"
  :long "See @(see vescmul-heuristics)")

(xdoc::defxdoc
  vescmul-heuristics
  :parents (vescmul)
  :short "Some heuristics that can be enabled/disabled by the user for
 @(see vescmul)"
  :long   "<p>Our   @(see  vescmul) multiplier verification  system   implements  various
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

<p> UNPACK-BOOTH-LATER <i>(disabled by default)</i> </p>

<p>In  Booth encoded multipliers,  partial products are generated  with basic
logical gates. We perform algebraic rewriting on these gates when rewriting the
overall circuit.  In some corner  cases, this can prevent  some simplifications
and  cause a  proof attempt  to fail.  We implement  a heuristic  that we  call
\"unpack-booth-later\" that doesn't perform  algebraic rewriting right away but
leaves logical gates  from Booth encoding intact. When all  the other rewriting
is finished,  we perform a second pass and only then these gates  are rewritten in the  algebraic form. This
heuristic is not expected to be necessary for the majority of designs and it is
disabled by default. If a proof attempt of a Booth encoded design is failing,
we recommend that you enable this heuristic: </p>

<code> @('(rp::enable-unpack-booth-later <t-or-nil>)') </code>

<p><i> This feature might not be working for the time-being</i></p>

<p>S-PATTERN1-REDUCE <i>(enabled by default)</i></p>

<p> Enabled by default, this heuristic can cover some corner
cases  that emerge  especially in  merged  multipliers. This  usually does  not
affect the proof-time performance, but in some cases (e.g., constant propagated
designs), it can have a negative  impact. We have never observed this heuristic
to cause a proof to fail, therefore it is enabled by default. To disable it
(rp::enable-s-pattern1-reduce         nil),         or        to         enable
it (rp::enable-s-pattern1-reduce t).
</p>

<code> @('(rp::enable-s-pattern1-reduce <t-or-nil>)') </code>

<p>PATTERN2-REDUCE <i>(enabled by default)</i></p>
<p>            Similar       to
S-PATTERN1-REDUCE. Enabled  by default. To  disable (rp::enable-pattern2-reduce
nil), to enable (rp::enable-pattern2-reduce t) </p>

<code> @('(rp::enable-pattern2-reduce <t-or-nil>)') </code>

<p>PATTERN3-REDUCE <i>(disabled by default)</i></p>

<p>  Similar  to other \"pattern-reduce\" heuristics  but it is
 too  aggressive  and  disabled by  default.  It  removes \"1\"
instances from
(s  1  others)  and  (c  1  others) terms.   We  have  added  this  pattern  for
experimentation  purposes and  have yet  to  observe its  usefulness. This  can
cause proofs to go through very slowly, therefore,  it is  disabled by
default. </p>

<code> @('(rp::enable-pattern3-reduce <t-or-nil>)') </code>

<p>RECOLLECT-PP <i>(disabled by default)</i></p>
<p> We have discovered that after partial products are flatten (i.e., rewritten
 in algebraic form), the result can be shrunk by rewriting (collecting) some
terms into c and s terms. When enabled, this heuristic tries to perform such
rewriting. It is currently only modified for Booth encoding radix-4 multipliers
and may or may not have any performance effect on other configurations. We have
observed that it can have considerable advantages in proof-time and memory
usage in larger multipliers (up to 30%). This setting is not thoroughly tested
for comprehensiveness and it may cause failures in some cases so it is disabled
by default.
</p>

<code> @('(rp::enable-recollect-pp <t-or-nil>)') </code>

<p>UNPACK-BOOTH-LATER-HONS-COPY <i>(disabled by default)</i></p>
<p> When enabled, this causes terms to be hons-copied in the meta function that
performs the second pass when unpack-booth-later is enabled. This can help
prevent some repeated work for some memoized functions but we have seen so far
that cost of hons-copy mostly overwhelms the benefits it brings. So  we leave
this heuristic disabled. It might be worth a shot if you think that a
proof is too slow. This setting has no effect if unpack-booth-later is
disabled.</p>

<code> @('(rp::enable-unpack-booth-later-hons-copy <t-or-nil>)') </code>

<p>CROSS-PRODUCT-TWO-LARGES <i>(disabled by default)</i></p>
<p>Another experimental feature that may or may not ever find its
usefulness. When enabled, ANDed two s/c/s-c-res terms will be dissolved into a
large list of terms. This will likely slow down in some cases (e.g.,
saturated multipliers) but won't affect much else. </p>
<code> @('(rp::enable-cross-product-two-larges <t-or-nil>)') </code>


<p> C-PATTERN4-COMPRESS <i>(disabled by default)</i></p>
<p>Another newly-added experimental feature that is expected to speed up the
proofs for Booth radix-16 multipliers. It compresses some c instances by
pulling out common multipliers inside its terms. It is left disabled because it
is not properly integrated into all parts of the tool and it may cause proof
failures in some cases. </p>
<code> @('(rp::enable-c-pattern4-compress <t-or-nil>)') </code>


<p>PP-LISTS-LIMIT <i>(set to 16000 by default)</i></p>
<p>We don't want terms to blow up when doing algebraic rewriting of logical
gates. We call this function in this library pp-flatten, as we use it to
flatten out partial product logic. Since there could be other terms
representing logical gates in given conjectures, and they may cause blow-up if
this rewriting is performed on them, we set a limit to how large a term can
grow during the pp-flatten stage. This limit can be changed by the user byt
defining a funciton that returns a certain number, and calling defattach. For
example:
</p>

<code> @('(define return-16000 () 16000)')</code>
<code> @('(defattach pp-lists-limit return-16000)')</code>

<p> If this limit is set too low, then some proofs may fail - likely Booth encoded multipliers
with large radices, such as, radix-16. On the other hand, if this limit is set
 too high, the program may try to flatten parts of the design that is not
needed (parts that would be simplified away through other means), or in case
something goes wrong in adder identification and you end up with a large tree
of logical gates. In such a case,
you'd likely not want to flatten those gates, which might eventually help prove
the conjecture but it can also cause a blow up. If  you are tring to prove
something and it
 is stalling, then it may be a good idea to decrease this number to see
what is going on. </p>

<p> UNDO-RW-AND-OPEN-UP-ADDERS <i>(disabled by default)</i> </p>
<p> In some cases, our program might mistakenly mark some parts of a
multiplier design as half-adder. If we proceed to keep assuming that this was
correct, our proofs may fail. We implemented a system to undo some
rewriting and open up the definition of some adder instances when it
seems appropriate. If the proof-time performance is too slow,  disabling this
heuristic may help:</p>

<code> @('(rp::enable-undo-rw-and-open-up-adders <t-or-nil>)') </code>

")

(xdoc::defxdoc
  Multiplier-Verification-demo-1
  :parents (vescmul)
  :short "First demo for @(see  vescmul) showing how an isolated
 integer multiplier is verified."
  :long " <p> Below is a demo to verify a multiplier design coded
in (System) Verilog. We choose a 64x64-bit
Booth Encoded Dadda Tree multiplier with  Han-Carlson adder as our example.  If
you  wish, you  can skip  to @(see  Multiplier-Verification-demo-2) for  a more
complex arithmetic module.  </p>


<p>
1. Include the books to parse Verilog designs and crete symbolic simulation vectors.

<code>
(include-book \"projects/vescmul/top\" :dir :system)
</code>
</p><p>
Including this book can take a long time (around a minute). However, we can save an executable
that has this image already loaded. You can either follow the instructions at
@(see acl2::save-exec) or download a <a
href=\"https://temelmertcan.github.io/vescmul.zip\">package</a> that does that
for you. This package also includes some demo files.

</p>


<p> 2. Parse the design.
 <code>
@('
(vesmul-parse :name my-multiplier-example
              :file \"DT_SB4_HC_64_64_multgen.sv\"
              :topmodule \"DT_SB4_HC_64_64\")
')
</code>

</p><p>This verilog file is located in @('<ACL2-DIRECTORY>/books/projects/vescmul/demo').

</p>

<p>
3. Verify the design. 
<code>@('
(vescmul-verify :name my-multiplier-example 
                :concl (equal result 
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')</code>
</p><p>
Here, the variables are case-insensitive and they correspond to input/output
names in the original design. For example, \"result\" is the output signal
name, and \"in1\" and \"in2\" are input signals. This design performs 64x64-bit
signed multiplication; therefore, the inputs are sign-extended with @(see
logext) and the first 128-bit of multiplication is taken with @(see
loghead). This proof takes about 1.5 seconds to finish. 
</p>

<p> @(see vescmul-verify) event will also create a file under the
generated-proof-summary directory showing what the program proved and how long
it took. This can be handy when running many experiments. Alternatively, if you
would like to view what is proved you can run the following command in an
interactive session:
<code>@(':pe my-multiplier-example-is-correct')</code>
</p>

<p> @(see vesmul-parse) and @(see vescmul-verify) have other
options that may be useful in some cases. </p>

<p> This program  is tested for multipliers up to  1024x1024; and they each finished
in a matter of minutes on our machines. However, verifying large multiplier may
require users to increase the  the stack size in ACL2 image
(e.g., saved_acl2 under you ACL2 directory) and run the proofs again. What it
should be increased to depends on your system (e.g., memory), and it is best to
test and tune various options until you do not get an error. That is
straightforward for systems with large memory (e.g., 32gb). In our
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
  Multiplier-Verification-demo-1-expanded
  :parents (Multiplier-Verification-demo-1)
  :short "Expanded events for the first demo for @(see  vescmul) showing how an isolated
 integer multiplier is verified."
  :long " <p> Below is a demo that  showing every single event  to input a multiplier design coded
in (System) Verilog into ACL2, and verify it efficiently. We choose a 64x64-bit
Booth Encoded Dadda Tree multiplier with  Han-Carlson adder as our example.  If
you  wish, you  can skip  to @(see  Multiplier-Verification-demo-2) for  a more
complex arithmetic module. What is different here than @(see
  Multiplier-Verification-demo-1) is that this one does not use the @(see
  vesmul-parse) and @(see vescmul-verify) macros but deliver the
  events individually. This may be useful to some users.  </p>

<p>
1. Include the books to parse Verilog designs and crete symbolic simulation vectors.
</p>
<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system)
</code>

<p> 2. Load VL design for  the modules in DT_SB4_HC_64_64_multgen.sv. This file
is                                 located                                under
@('<your-acl2-directory>/books/projects/vescmul/demo').   This is
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
4. Create the test vector for symbolic simulation:
<code>
@('
(sv::defsvtv mult-run
  :mod *sv-design*
  :inputs '((\"IN1\" a)
            (\"IN2\" b))
  :outputs
  '((\"result\" res)))
')
</code>

</p>

<p>
5. Include the book that has the rewrite and meta rules
for multiplier proofs:
<code>
(include-book \"projects/vescmul/svtv-top\" :dir :system)
</code>
</p>

<p>
6. Finally, prove the multiplier correct:
<code>
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
</code>

This proof takes about 1.5 seconds to finish.
</p>

<p>Here, we first extract the output value from svtv-run function. Then on the
right hand-side, we state the specification. Here numbers a and b are sign
extended at 64th-bits and multiplied. Then the first 128-bit of the
multiplication result is compared to the design's output.

</p>

<p> This program  is tested for multipliers up to  1024x1024; and they each finished
in a matte of minutes on our machines.  </p>

<p>
For large multipliers, users may need to increase the stack size in ACL2 image
(e.g., saved_acl2 under you ACL2 directory) and run the proofs again. In our
tests, we have observed SBCL to be faster than CCL; however, for large
multipliers garbage collector of CCL does a better job with @(see
acl2::set-max-mem) and it can finish large proofs when SBCL terminates with memory
errors.
</p>

<p>
You may continue to @(see Multiplier-Verification-demo-2-expanded).
</p>

"
  )

(xdoc::defxdoc
  Multiplier-Verification-demo-2
  :parents (vescmul)
  :short  "The second  demo  for   @(see  vescmul)  showing  how  an
 industrial-design-mimicking module  including a MAC, dot-product  and merged
 multipliers can be verified."
  :long "<p> In the first  demo (@(see Multiplier-Verification-demo-1)), we have
 shown how  our tool can  be used  on an isolated  multiplier.  This is  a good
 starting  point;  however,  real-world  applications  of  integer  multipliers
 involve more intricate  design strategies. We tried to recreate  some of those
 strategies  and   compiled  a   more  complex   multiplier  module   given  in
 @('<your-acl2-directory>/books/projects/vescmul/demo/integrated_multipliers.sv'). You
 may            find            this           file            on            <a
 href=\"https://github.com/acl2/acl2/blob/master/books/projects/vescmul/demo/integrated_multipliers.sv\"
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
 @('<your-acl2-directory>/books/projects/vescmul/demo/demo-2.lisp'). </p>

<p>
1. Include the books to parse Verilog designs and crete symbolic simulation vectors.

<code>
(include-book \"projects/vescmul/top\" :dir :system)
</code>
</p>
<p>Including this book can take a long time (around a minute). However, we can save an executable
that has this image already loaded. You can either follow the instructions at
@(see acl2::save-exec) or download a <a
href=\"https://temelmertcan.github.io/vescmul.zip\">package</a> that does that
for you. This package also includes some demo files.

</p>

<p> 2. The integrated multiplier module has an input signal called
@('mode'). As the name implied, this signal determines the mode of operation
(e.g., dot-product or  4-lane multiplication) that the module needs  to run. We
create a  new function to calculate  the value  of this
signal. This will make  our proofs more readable and easier  to manage. You may
find a description of how this signal should be assigned in the comments in the
Verilog file.

<code>
@('
(define calculate-mode-value (&key
                              (acc-on 'nil)
                              (reload-acc 'nil)
                              (signed 'nil)
                              (dot-product 'nil)
                              (four-lanes-lo 'nil)
                              (four-lanes-hi 'nil)
                              (one-lane 'nil))
  (b* (((unless (= 1 (+ (if dot-product 1 0) ;; check for illegal combination
                        (if four-lanes-lo 1 0)
                        (if four-lanes-hi 1 0)
                        (if one-lane 1 0))))
        -1)
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
')
</code>

</p>

<p> 3. Parse the design and create the simulation vector to test out cases that
can be simulated combinationally.
<code>
@('
(vesmul-parse :name integrated_multipliers-combinational-modes
              :file \"integrated_multipliers.sv\"
              :topmodule \"Integrated_Multiplier\")
')
</code>
</p>

<p> 4.  We  are now ready to  verify the top module  for various multiplication
modes. First,  we verify various  combinational modes (one-lane  64x64-bit MAC
4-32x32-bit  dot-product, and four-lane  32x32-bit  multiplication  with lower  and
higher half truncation), then we show verification for a sequential mode
(accumulated dot-product).  </p>

<p>
 Below is our first correctness proof  of a multiplication mode. In this case
 it is signed one-lane mode, which is expected to implement  [in3  +  in2*in1  (both
sign-extended)] and the complete result is  truncated at 128 bits. We set the
 mode signals value in the hypothesis with the :hyp argument. We pass a custom
 name to the theorem that will be submitted with the :thm-name argument. 
<code>
 @('
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name signed-one-lane-mult-correct
                :hyp (equal mode (calculate-mode-value :one-lane t
                                                       :signed t))
                :concl (equal result
                              (loghead 128 (+ (* (logext 64 in1)
                                                 (logext 64 in2))
                                              in3))))
')
</code>
</p>

<p>

We  can  prove  the  same  for  the mode  for  unsigned  numbers  by  changing  the
specification accordingly:
<code>
@('
(vescmul-verify :name integrated_multipliers-combinational-modes

                :thm-name unsigned-one-lane-mult-correct
                :hyp (equal mode (calculate-mode-value :one-lane t
                                                       :signed nil))
                :concl (equal result
                              (loghead 128 (+ (* (loghead 64 in1)
                                                 (loghead 64 in2))
                                              in3))))
')
</code>
</p>

<p> 5. Now, let's verify  the dot product operation. To make it more readable,  we split two of
the input signals to four lanes. This conjecture, similarly, takes about a second to
prove. We omit the proofs for unsigned here for brevity.

<code>
@('
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
')
</code>

</p>

<p> 6. Another mode is four-lane multiplication that truncate at the lower half of
 multiplication.   Similarly,  we  define   new  input  and  output  simulation
 patterns, splitting all three inputs and the output to four lanes:

<code>
@('
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
')
</code>
</p>
<p>We can  prove a  similar lemma  for unsigned  mode as  well (omittied in this
  doc).</p>

<p> 7. We have
another combinational  mode that is  four-lane multiplication that  truncate at
the higher  half.  Function @(see logtail)  right shift  numbers.  In
this case, we right shift the multiplication  result by 32 bits to retrieve the
higher end of the result.

<code>
@('
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
')
</code>
</p>

<p>

8. Finally, let's  show our  framework on  a sequential  operation. The  design in
integrated_multipliers.sv has an  accumulator that can store  the result across
different clock  cycles. We can  use this feature to  increase the size  of dot
product. So we  create a simulation pattern where we  load the accumulator with
an initial  value, and perform two  dot-product operations in two  clock cycles
and accumulate the  result. So we create  a 8-32x32-bit dot product  out of the
existing 4-32x32-bit one.

<code>
@('
(vesmul-parse :name integrated_multipliers-sequential-mode
              :file \"integrated_multipliers.sv\"
              :topmodule \"Integrated_Multiplier\"

              ;; Define the clock: (clk signal should continuously toggle)
              :cycle-phases (list (sv::make-svtv-cyclephase :constants '((\"clk\" . 0))
                                                            :inputs-free t
                                                            :outputs-captured t)
                                  (sv::make-svtv-cyclephase :constants '((\"clk\" . 1))))
              :stages
              (;; reload the ACC in the first clock cycle
               (:label reload-acc
                       :inputs ((\"IN3\" acc-init-val)
                                (\"mode\" mode-init-val)))
               ;; Feed some values in the second clock cycle for dot product
               (:label 1st-vectors
                       :inputs ((\"IN1\" in1-1)
                                (\"IN2\" in2-1)
                                ;; keep the mode value the same in the next cycles.
                                (\"mode\" mode :hold t))
                       :outputs ((\"result\" result1)))
               ;; Feed more values for dot-product.
               (:label 2nd-vectors
                       :inputs ((\"IN1\" in1-2)
                                (\"IN2\" in2-2))
                       :outputs ((\"result\" result2)))))
')
</code>
</p><p>
The call for @(see vesmul-parse) is more complicated here as we need
to define what happens in each clock cycle. With the :cycle-phases argument we
tell the program what signal represents the clock in a given design. In this
case it is \"clk\". This defines stages (each clock cycle), and we describe how
the design should be simulated at each stage. The first clock cycle will be
used to load the accumulator. The second and third clock cycles will be used to
feed in the input vectors for dot-product. The lane width for dot-product is
32-bits. The input signals \"IN1\" and \"IN2\" are 128-bit wide, storing
4-lanes of data. We bind those signals to free variables (e.g., in1-1) which will be refered
to in the proofs we will run below.  

</p>
<p> The users of our tool can also define custom functions to define
specification. This can help with readability. As an example, we define the
spec function below.

<code>
@('
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
')
</code>
</p>

<p> Then, we can state the correctness for the 8-32x32-bit dot product mode as:
<code>
@('
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
')
</code>
</p><p>
Note that the conclusion has a conjunct of two expressions. This is optional
and only here to show the flexibility of our program. \"result1\" refers to the
value of the output signal at the second clock cycle, and \"result2\" refers to
the value of the output signal at the third clock cycle. 

</p>

")

(xdoc::defxdoc
  Multiplier-Verification-demo-2-expanded
  :parents (Multiplier-Verification-demo-2)
  :short  "Expanded events for the second  demo  for   @(see  vescmul)  showing  how  an
 industrial-design-mimicking module  including a MAC, dot-product  and merged
 multipliers can be verified."
  :long "<p> In the first  demo (@(see Multiplier-Verification-demo-1)), we have
 shown how  our tool can  be used  on an isolated  multiplier.  This is  a good
 starting  point;  however,  real-world  applications  of  integer  multipliers
 involve more intricate  design strategies. We tried to recreate  some of those
 strategies  and   compiled  a   more  complex   multiplier  module   given  in
 @('<your-acl2-directory>/books/projects/vescmul/demo/integrated_multipliers.sv'). You
 may            find            this           file            on            <a
 href=\"https://github.com/acl2/acl2/blob/master/books/projects/vescmul/demo/integrated_multipliers.sv\"
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
 @('<your-acl2-directory>/books/projects/vescmul/demo/demo-2.lisp'). </p>

<p> 1.  Include necessary books.  @(see SVL) system uses  @(see SV)
and @(see VL) packages. So we start with them.
</p>

<code>
(include-book \"centaur/sv/top\" :dir :system) ;; a big book; takes around 30 seconds
(include-book \"centaur/vl/loader/top\" :dir :system) ;; takes around 10 seconds
(include-book \"oslib/ls\" :dir :system) ;; takes just a few seconds
</code>

<p> Then, include has the rewrite and meta rules to carry out simplification of
multiplier modules:
</p>

<code>
(include-book \"projects/vescmul/svtv-top\" :dir :system)
</code>

<p> 2. Parse the System Verilog design. All events take a few
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

<p> 3. The integrated multiplier module has an input signal called
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

<p> 4.  We  are now ready to  verify the top module  for various multiplication
modes. First,  we verify various  combinational modes (one-lane  64x64-bit MAC
4-32x32-bit  dot-product, and four-lane  32x32-bit  multiplication  with lower  and
higher half truncation), then we show verification for a sequential mode
(accumulated dot-product).  </p>

<p>
We define our first simulation pattern. Since we are currently only interested
in the  combinational functionality,  we set  \"clk\" to  \"0\", and  the other
signals to some free variables.
<code>
 @('
(sv::defsvtv one-lane-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '((\"clk\" 0)
            (\"IN1\" in1)
            (\"IN2\" in2)
            (\"IN3\" in3)
            (\"mode\" mode))
  :outputs
  '((\"result\" result)))

(add-rp-rule one-lane-mult2-svtv-autoins-fn)
')
</code>
</p>

<p>

 Below is our first correctness proof  of a multiplication mode. SVTV-run returns
an association list  of all the variables stated in outputs above. In this case,
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
(defthmrp-multiplier signed-one-lane-mult-is-correct
  (implies (and (integerp in1)
                (integerp in2)
                (integerp in3))
           (equal (sv::svtv-run (one-lane-mult2-svtv)
                                (one-lane-mult2-svtv-autoins
                                 :mode (mode :one-lane t
                                             :signed t)))
                  `((result . ,(loghead 128 (+ (* (logext 64 in1)
                                                  (logext 64 in2))
                                               in3)))))))
')
</code>
</p>

<p>

We  can  prove  the  same  for  the mode  for  unsigned  numbers  by  changing  the
specification accordingly:
<code>
@('
(defthmrp-multiplier unsigned-one-lane-mult-is-correct
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

')
</code>
</p>

<p> 5. Now, let's verify  the dot product operation. To make it more readable,  we split two of
the input signals to four lanes. This conjecture, similarly, takes about a second to
prove. We omit the proofs for unsigned for brevity.

<code>
@('
(sv::defsvtv dotproduct-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '((\"clk\" 0)
            (\"IN1[31:0]\" in1_0)
            (\"IN2[31:0]\" in2_0)
            (\"IN1[63:32]\" in1_1)
            (\"IN2[63:32]\" in2_1)
            (\"IN1[95:64]\" in1_2)
            (\"IN2[95:64]\" in2_2)
            (\"IN1[127:96]\" in1_3)
            (\"IN2[127:96]\" in2_3)
            (\"IN3\" in3)
            (\"mode\" mode))
  :outputs '((\"result\" result)))

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
                                 :mode (mode :dot-product t
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

')
</code>

</p>

<p> 6. Another mode is four-lane multiplication that truncate at the lower half of
 multiplication.   Similarly,  we  define   new  input  and  output  simulation
 patterns, splitting all three inputs and the output to four lanes:

<code>
@('
(sv::defsvtv four-lanes-mult2-svtv
  :mod *mult2-sv-design*
  :inputs '((\"clk\" 0)
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
            (\"mode\"        mode))
  :outputs '((\"result[31:0]\"   result0)
             (\"result[63:32]\"  result1)
             (\"result[95:64]\"  result2)
             (\"result[127:96]\" result3)))

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
                                 :mode (mode :four-lanes-lo t
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

')
</code>

We can  prove a  similar lemma  for unsigned  mode as  well (omittied in this
  doc).</p>

<p> 7. We have
another combinational  mode that is  four-lane multiplication that  truncate at
the higher  half.  Function @(see acl2::ash)  right or left shift  numbers.  In
this case, we right shift the multiplication  result by 32 bits to retrieve the
higher end of the result.

<code>
@('
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
                                 :mode (mode :four-lanes-hi t
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
')
</code>
</p>

<p>

8. Finally, let's  show our  framework on  a sequential  operation. The  design in
integrated_multipliers.sv has an  accumulator that can store  the result across
different clock  cycles. We can  use this feature to  increase the size  of dot
product. So we  create a simulation pattern where we  load the accumulator with
an initial  value, and perform two  dot-product operations in two  clock cycles
and accumulate the  result. So we create  a 8-32x32-bit dot product  out of the
existing 4-32x32-bit one.

<code>
@('
(sv::defsvtv sequential-dotproduct-mult2-svtv
  :mod *mult2-sv-design*
  :inputs `((\"clk\" 0 1 ~)
            (\"IN1[31:0]\"   _ _ in1[0] _ in1[4])
            (\"IN2[31:0]\"   _ _ in2[0] _ in2[4])
            (\"IN1[63:32]\"  _ _ in1[1] _ in1[5])
            (\"IN2[63:32]\"  _ _ in2[1] _ in2[5])
            (\"IN1[95:64]\"  _ _ in1[2] _ in1[6])
            (\"IN2[95:64]\"  _ _ in2[2] _ in2[6])
            (\"IN1[127:96]\" _ _ in1[3] _ in1[7])
            (\"IN2[127:96]\" _ _ in2[3] _ in2[7])
            (\"IN3\" acc-init-val)
            (\"mode\" ,(mode :acc-on t
                           :dot-product t
                           :reload-acc t)
             mode mode mode mode))
  :outputs '((\"result\" _ _ _ _ result)))

(add-rp-rule sequential-dotproduct-mult2-svtv-autohyps)
(add-rp-rule sequential-dotproduct-mult2-svtv-autoins)

')
</code>
</p>
<p> In the previous proofs given above, we stated the specification of each
mode explicitly in the conjectures. We can alternatively wrap these
specifications with new functions for better readability. So we create a dot
product specification function as given below.

<code>
@('
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
')
</code>
</p>

<p> Then, we can state the correctness for the 8-32x32-bit dot product mode as:
<code>
@('
(defthmrp-multiplier
  signed-dot-product-with-acc-is-correct
  (implies (and (equal signed t)
                (equal acc-size 128)
                (equal dot-product-size 8)
                (equal mode (mode :dot-product t
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
')
</code>
</p>

")

(xdoc::defxdoc
  Multiplier-Verification-demo-3
  :parents (vescmul)
  :short  "The third  demo  for   @(see  vescmul)  showing  how  an
 a hierarchical reasoning hint may be passed for designs whose adders may not
  be automatically identified."
  :long "<p> VeSCmul  may  not  always be  able  to  find  adder  components in  a  given
design. However, our system still supports hierarhical reasoning, and we can
provide hierarhical  reasoning hints to  help the  program. Below is  a demo
showing  how it  can  be achieved  for a  64x64-bit  multiplier with  7-to-3
compressor    tree.     This    module    is    given    in    this    file:
  @('<your-acl2-directory>/books/projects/vescmul/demo/homma-7-to-3-64x64-signed-carry-select.v'). You
 may            find            this           file            on            <a
 href=\"https://github.com/acl2/acl2/blob/master/books/projects/vescmul/demo/homma-7-to-3-64x64-signed-carry-select.v\"
 target=\"_blank\"> GitHub </a> as well.</p>


<p>1. As  a hierarchical reasoning  hint, we offer alternative  definitions for
 some of the  adder modules in this design. Particularly,  we redefined 7to3,
 6to3, 5to3,  and 4to3  compressor modules.  So first, we  create a  new file
 contaning those easier-to-identify definitions.

<code>
@('

(defwarrant str::fast-string-append-lst)
(defwarrant str::int-to-dec-string$inline)

(write-string-to-file-event
 \"better-homma-7-3.v\"
 ;; homma  designs for  some  reason repeat  the same  module  many times  with
 ;; different names. So below creates a  better copy of some adder modules with
 ;; a loop.
 (string-append-lst
  (append
   (loop$ for x from 0 to 123 collect                           
         (str::cat \"module UB7_3C\" (str::intstr x) \" (output S1, S2, S3, input X1,X2,X3,X4,X5,X6,X7);
     wire car1,car2,sum1,sum2,car3;
     // make it look like a group of full-adders:
     assign {car1,sum1} = (X1+X2+X3);
     assign {car2,sum2} = (X5+X6+X7);
     assign {car3,S3} = (X4+sum1+sum2);
     assign {S1,S2} = car1+car2+car3;
endmodule
\"))
   (loop$ for x from 0 to 123 collect                           
         (str::cat \"module UB6_3C\" (str::intstr x) \" (output S1, S2, S3, input X1,X2,X3,X4,X5,X6);
     wire car1,car2,sum1,sum2,car3;
     // make it look like a group of full-adders:
     assign {car1,sum1} = (X1+X2+X3);
     assign {car2,sum2} = (X4+X5+X6);
     assign {car3,S3} = (sum1+sum2);
     assign {S1,S2} = car1+car2+car3;
endmodule
\"))

   (loop$ for x from 0 to 123 collect                           
         (str::cat \"module UB5_3C\" (str::intstr x) \" (output S1, S2, S3, input X1,X2,X3,X4,X5);
     wire car1,car2,sum1,sum2,car3;
     // make it look like a group of full-adders:
     assign {car1,sum1} = (X1+X2+X3);
     assign {car2,sum2} = (X4+X5);
     assign {car3,S3} = (sum1+sum2);
     assign {S1,S2} = car1+car2+car3;
endmodule
\"))

   (loop$ for x from 0 to 123 collect                           
         (str::cat \"module UB4_3C\" (str::intstr x) \" (output S1, S2, S3, input X1,X2,X3,X4);
     wire car1,car2,sum1,sum2,car3;
     // make it look like a group of full-adders:
     assign {car1,sum1} = (X1+X2+X3);
     assign {car3,S3} = (sum1+X4);
     assign {S1,S2} = car1+car3;
endmodule
\")))))
')
</code>
</p>


<p>
2. Parse the  design. This  program will
parse and  create two  simulation vectors  for the design.  One will  be the
simulation of the  original design, and the other will  be similation of the
design whose adder modules are  replaced with the ones in better-homma-7-3.v
file. vescmul-verify will later perform equivalance checking between
the two to make sure that the two designs are functionally equivalant. 

<code>
@('
(vesmul-parse :file \"homma-7-to-3-64x64-signed-carry-select.v\"
              :topmodule \"Multiplier_63_0_6000\"
              :name homma-7-to-3
              :modified-modules-file \"better-homma-7-3.v\")
')
</code>
</p>

<p>
 3. Verify the design.  vescmul-verify will perform equivalance checking
 between  the  modified  and  original  design first  using  FGL.   For  fast
 equivalance checking, we set up AIG transforms which will use an incremental
 SAT     solver.      Make    sure     you     have     IPASIR    set     up:
 @(see ipasir::ipasir).
 After equivalance checking, vescmul will  use the modified version to verify
 the multiplier and  once proved, state a theorem for  the correctness of the
 unmodified, original design.

</p>
<p>
Set up AIG trannsforms for fast  equiv checking. Tweaking the parameters can
affect the proof-time result a lot.
<code>
@('
(progn
  (local (include-book \"centaur/ipasir/ipasir-backend\" :dir :system))
  (local (include-book \"centaur/aignet/transforms\" :dir :system))
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
')
</code>
</p>
<p> Finally, call verify:
<code>
@('
(vescmul-verify :name homma-7-to-3
                :concl (equal p
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')
</code>
</p>


<p> This should take a few seconds to run all the proofs. You can see the generated proof summary file or run:
<code>@(':pe homma-7-to-3-is-correct')</code> to see what is proved. We have a
final corectness theorem based on the original design.
</p>
"
  )

(defxdoc vesmul-parse
  :parents (Multiplier-Verification vescmul)
  :short "A macro to parse a combinational RTL design and create a simulation
  test vector"
  :long "<p><b> vesmul-parse</b> can take the following arguments:</p>
<ul>
<li> <b>:file</b> has to be provided. It should be a string and point to the relative path to the
  target Verilog file. </li>
<li> <b>:topmodule</b> has to be provided. It should be a string and be the name of the top module
  of the Verilog file. </li>
<li> <b>:name</b>  is optional. It should be a symbol. It will be the name
  of the objects generated for symbolic simulation vectors in ACL2. When not
  provided, the program uses the topmodule for name.</li>
<li> <b>:save-to-file</b> is optional. It should be a string and be used as a prefix for the outputting file name. When provided, it will
  save the created simulation vectors to a file in a compact form (svexl) that
  can be read later more quickly. When not provided, the simulation vector will
  remain in the session (or in certificate files). </li>

<li> <b>:modified-modules-file</b> is optional. When provided, it should be a string
pointing to a Verilog file containing alternative definitions of adder modules
that may be used to override the modules of the same name in the original
design.
<br />
 This is useful
for hierarchical reasoning for cases VeSCmul cannot detect certain adder
patterns in some designs. This will create two simulation vectors: one for the
original design and another for the modified version. VeSCmul will be used to verify the modified
version. And @(see
vescmul-verify) macro will also prove equivalance between the two versions
with a SAT solver (through FGL).  In the end, a theorem stating the correctness of the original design
will be saved.
<br />
VeSCmul is usually very good at finding adders  on its own, and
hopefully, this option will not be necessary. However, should the need rise, we still
keep hierarchical reasoning as an option.  </li>

<li> <b>:stages</b> is optional. Users can opt to define the stages that will
be passed to @(see sv::defsvtv$). It is especially useful for sequential
circuits. Unless specified, the program will assume the given design is
combinational and bind input and output signals automatically to the variables
of the same case-insensitive names.</li>
<li> <b>:cycle-phases</b> is optional. Will be passed to @(see
sv::defsvtv$). It is relevant for sequential circuits only. </li>

</ul>

<p> Example call 1:
<code>
@('
(vesmul-parse :file \"demo/DT_SB4_HC_64_64_multgen.sv\"
              :topmodule \"DT_SB4_HC_64_64\"
              :name my-multiplier-example
              :save-to-file \"parsed/\")
')</code>
</p>

<p> Example call 2:
<code>
@('
(vesmul-parse :file \"demo/DT_SB4_HC_64_64_multgen.sv\"
              :topmodule \"DT_SB4_HC_64_64\"
              :name my-multiplier-example)
')</code>
</p>


<p> Example call 3 (providing hints with hierarchical reasoning):
<code>
@('
;; Create a Verilog file that has an alternative definition for Han-Carlson
;; vector adder used in the target multiplier. VeSCmul works well with the +
;; operator.
(write-string-to-file-event \"demo/modified-HC_128.v\"
   \"module HC_128(input [127:0] IN1, input [127:0] IN2, output [128:0] OUT);
     assign OUT = IN1+IN2;
   endmodule\")
;; Use this alternative definition to help the verification program 
(vesmul-parse :file \"demo/DT_SB4_HC_64_64_multgen.sv\"
              :modified-modules-file \"demo/modified-HC_128.v\"
              :topmodule \"DT_SB4_HC_64_64\"
              :name my-multiplier-example)
;; vescmul-verify will later use this alternative definition to get help
;; for  multiplier proofs. 
')</code>
</p>


<p> You can proceed to @(see vescmul-verify) to run the verification
event. </p>
")

(defxdoc vescmul-verify
  :parents (Multiplier-Verification vescmul)
  :short "A macro to verify a multiplier using @(see VeSCmul)  from an already created simulation
  test vector with @(see vesmul-parse)"
  :long "<p><b>vescmul-verify</b> can take the following arguments:</p>
<ul>
<li> <b>:name</b> has to be provided. It should be a symbol and be the name
  corresponding to the name picked in @(see vesmul-parse). </li>

<li> <b>:concl</b> has to be provided. The body of the conjecture to
  be proved. </li>

<li> <b>:thm-name</b> is optional. It will be the name of the final theorem
  proved. When provided, it should be a symbol. When not provided, the program
  will automatically calculate a thm-name by append \"-is-correct\" to the name
  provided with the :name argument. </li>

<li> <b>:hyp</b> is optional. A term that will be used as hypothesis when
verifying a multiplier. It can be useful when setting some control signals or
when assuming some simulation conditions. </li>

<li> <b>:then-fgl</b>  is optional. To invoke FGL (calls a SAT solver) after
  rewriter finishes. FGL is configurable, for example, to call the desired SAT
  solver and/or perform AIG transforms. See below.  </li>

<li> <b>:read-from-file</b> is optional. It should be a string be the value
  corresponding to the one in the :save-to-file argument of @(see
  vesmul-parse). </li>

<li> <b>:cases</b> is optional. A list of terms that can be used to casesplit
  upon starting the program. Casesplit hints may be useful for some corner cases. </li>
<li> <b>:keep-going</b> is optional, should be t or nil. When set to t, the
  program will not stop ACL2 if a proof-attempt fails. This is useful when
  running a lot of experiments in the same file, and you expect that some may
  fail to prove.</li>
<li> <b>:print-message</b> is optional and should be a string if given. The
  program will also generate a proof summary file after it has run. Users may
  pass a custom message through this argument that will appear in the proof summary file.</li>
</ul>

<p>vescmul-verify will create a proof-summary file under the
generated-proof-summary directory showing the proof time and what the program
verified about multiplier design.</p>


<p> Example call 1:
<code>
@('
(vescmul-verify :name my-multiplier-example
                :concl (equal result
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2))))
                :read-from-file \"parsed/\")
')</code>
</p>

<p> Example call 2:
<code>
@('
(vescmul-verify :name my-multiplier-example
                :concl (equal result
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')</code>
</p>

<p> Example call 3:
<code>
@('
;; Casesplit on 63th bits of in1 and in2. This may be helpful in some corner
;; cases. 
(vescmul-verify :name my-multiplier-example
                :cases ((logbitp 63 in1) (logbitp 63 in2))
                :concl (equal result
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')</code>

</p>

<p> Example call 4:
<code>
@('
;; If VeSCmul cannot finish the proofs, this will call FGL after rewriting is done 
(vescmul-verify :name my-multiplier-example
                :then-fgl t
                :concl (equal result
                              (loghead 128 (* (logext 64 in1)
                                              (logext 64 in2)))))
')</code>

</p>



<br />
<p>

You  may also configure FGL. For example this will call kissat for SAT Solver:
<code>
@('
(local
 (progn
   (defun my-sat-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline \"kissat \"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))
   (defattach fgl::fgl-satlink-config my-sat-config)))
')
</code>

Or, this will perform AIG transform using incremental SAT solvers. You need to
set up IPASIR library (see @(see
ipasir::ipasir)). This can improve the performance in some cases such as
equivalance checking during hierarchical reasoning scheme. 
<code>
@('
(progn
  (local (include-book \"centaur/ipasir/ipasir-backend\" :dir :system))
  (local (include-book \"centaur/aignet/transforms\" :dir :system))
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
')
</code>

</p>

")

