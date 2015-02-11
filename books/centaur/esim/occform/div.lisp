; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "add")
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))


(defval *vl-1-bit-div-rem*
  :parents (occform)
  :short "One-bit division and remainder."

  :long "<p>This module exactly implements the Verilog semantics for one-bit
division and remainder.</p>

<p>Dividing one-bit wires isn't a very useful thing to do.  Division by zero is
generally an error (in Verilog it produces X), and division by one is just a
copy.  But, if for some reason we do see a @('/') and @('%') operator being
applied to single-bit wires, we still need to implement it <i>somehow</i>.</p>

<p>The actual definition of this module is pretty weird and I don't think it's
really worth studying.  I basically just piled on X detection stuff until it
matched the Verilog semantics.</p>"

  (b* ((name (hons-copy "VL_1_BIT_DIV_REM"))

       ((mv q-expr q-port q-portdecl q-vardecl) (vl-primitive-mkport "quotient"  :vl-output))
       ((mv r-expr r-port r-portdecl r-vardecl) (vl-primitive-mkport "remainder" :vl-output))
       ((mv e-expr e-port e-portdecl e-vardecl) (vl-primitive-mkport "dividend"  :vl-input))
       ((mv d-expr d-port d-portdecl d-vardecl) (vl-primitive-mkport "divisor"   :vl-input))

       ;; wire 	 xwire;
       ;; VL_1_BIT_X xdriver (xwire);
       ((mv xwire-expr xwire-vardecl) (vl-primitive-mkwire "xwire"))
       (xwire-inst (vl-simple-inst *vl-1-bit-x* "xdriver" xwire-expr))

       ;; To treat divides by zero, x, and z in the same way, the basic idea is to let
       ;;    divisor_fix = (divisor === 1'b1) ? divisor : 1'bx;
       ;;
       ;; Implementation is slightly complex:
       ;;   wire divisor_bar, divisor_x, divisor_fix;
       ;;   VL_1_BIT_NOT dx1 (divisor_bar, divisor);
       ;;   VL_1_BIT_AND dx2 (divisor_x, divisor_bar, xwire);
       ;;   VL_1_BIT_OR  dx3 (divisor_fix, divisor, divisor_x) ;
       ((mv d~-expr d~-vardecl) (vl-primitive-mkwire "divisor_bar"))
       ((mv dx-expr dx-vardecl) (vl-primitive-mkwire "divisor_x"))
       ((mv df-expr df-vardecl) (vl-primitive-mkwire "divisor_fix"))
       (d~-inst (vl-simple-inst *vl-1-bit-not* "dx1" d~-expr d-expr))
       (dx-inst (vl-simple-inst *vl-1-bit-and* "dx2" dx-expr d~-expr xwire-expr))
       (df-inst (vl-simple-inst *vl-1-bit-or*  "dx3" df-expr d-expr dx-expr))

       ;; Now we do ordinary X detection on the dividend (a) and on the
       ;; divisor_fix.  It happens to be that remainder is X exactly when
       ;; either of these is X/Z and 0 otherwise, so the remainder comes right
       ;; from the x-detection.  That is:
       ;;
       ;;  wire xa, xb;
       ;;  VL_1_BIT_XOR x1 (xa, dividend, dividend);
       ;;  VL_1_BIT_XOR x2 (xb, divisor_fix, divisor_fix);
       ;;  VL_1_BIT_XOR x3 (remainder, xa, xb);
       ((mv xa-expr xa-vardecl) (vl-primitive-mkwire "xa"))
       ((mv xb-expr xb-vardecl) (vl-primitive-mkwire "xb"))
       (xa-inst (vl-simple-inst *vl-1-bit-xor* "x1" xa-expr e-expr e-expr))
       (xb-inst (vl-simple-inst *vl-1-bit-xor* "x2" xb-expr df-expr df-expr))
       (r-inst  (vl-simple-inst *vl-1-bit-xor* "x3" r-expr xa-expr xb-expr))

       ;; Finally, compute the quotient.  The quotient is only 1 when the
       ;; dividend is 1 and divisor is 1.  Otherwise it may as well be zero.
       ;; We call this Qmain.  We then adjust for Xes accordingly to create
       ;; the properly X-behaving quotient.
       ;;
       ;;  wire qmain;
       ;;  VL_1_BIT_AND q1 (qmain, dividend, divisor_fix);
       ;;  VL_1_BIT_XOR q2 (quotient, remainder, qmain);
       ((mv qm-expr qm-vardecl) (vl-primitive-mkwire "qmain"))
       (qm-inst (vl-simple-inst *vl-1-bit-and* "q1" qm-expr e-expr df-expr))
       (q-inst  (vl-simple-inst *vl-1-bit-xor* "q2" q-expr r-expr qm-expr)))

    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list q-port r-port e-port d-port)
                     :portdecls (list q-portdecl r-portdecl e-portdecl d-portdecl)
                     :vardecls  (list q-vardecl r-vardecl e-vardecl d-vardecl
                                      xwire-vardecl d~-vardecl dx-vardecl df-vardecl
                                      xa-vardecl xb-vardecl qm-vardecl)
                     :modinsts  (list xwire-inst d~-inst dx-inst df-inst
                                      xa-inst xb-inst r-inst
                                      qm-inst q-inst)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-n-bit-div-step ((n natp))
  :parents (vl-make-n-bit-div-rem)
  :short "Single step in a basic division/remainder algorithm."

  :long "<p>We generate the module @('VL_N_BIT_DIV_STEP') in terms of @(see
primitives).  This module carries out a single step in a simple restoring
division algorithm.</p>

<p>To understand this code you will need to understand restoring division.  We
sketch our implementation here, but to understand why it works you should see
a textbook on computer arithmetic.</p>

<p>Imagine a double-wide register, sometimes called AQ, whose halves we will
treat independently as A and Q.</p>

@({
        +--------------+--------------+
        |   'A' half   |   'Q' half   |    2n bits total
        +--------------+--------------+
            n bits         n bits
})

<p>Initially, A is zeroed and Q is set to the dividend.  Then we take N
steps (described below).  After these steps, A will contain the remainder and Q
will contain the quotient.</p>

<p>In each step, we are going to:</p>

<ol>
<li>Shift the whole register AQ left by 1, then</li>
<li>Modify A and the bottom bit of Q, i.e., Q[0].</li>
</ol>

<p>Note that, except for the shifting step, we don't touch Q besides its bottom
bit.  Since Q eventually becomes the quotient, what we're really doing here is
computing the quotient one bit at a time.  During the first iteration, we
compute its most significant bit.  During the next iteration, we compute its
next most significant bit, and so on.</p>

<p>The details of each step are as follows.  After shifting AQ, we compare the
divisor (which remains fixed throughout all iterations) against A.  If the
divisor \"fits\" into A, i.e., when @('divisor <= A'), we reduce A by the
divisor and set the low bit of Q to 1.  Otherwise, we leave A alone and set the
low bit of Q to 0.</p>

<p>How does @('VL_N_BIT_DIV_STEP') fit into this?  It computes the next value
of AQ, given the current value of AQ and the divisor.  For example, in the 5-bit
case, the general idea is something like this:</p>

@({
module VL_5_BIT_DIV_STEP (a_next, q_next,   // Updated AQ
                          a_prev, q_prev,   // Starting AQ
                          divisor) ;

  output [4:0] a_next, q_next;
  input [4:0] a_prev, q_prev;
  input [4:0] divisor;

  // Temporary AQ is the starting AQ, shifted left by 1,
  // which drops the top bit of A:

  wire [4:0] a, q;
  assign {a, q} = {a_prev[3:0], q_prev, 1'b0};

  wire fits = divisor <= a;                 // Does it fit?
  assign a_next = fits ? a - divisor : a;   // Maybe Adjust A
  assign q_next = {q[3:1], fits};           // Install Q[0]

endmodule
})

<p>The only twists are the following, basic optimizations:</p>

<ul>

<li>We do the comparison and subtraction using the same adder core.</li>

<li>We expect the divisor to be given to us already negated, instead of
separately negating it in each step.</li>

</ul>

<p>Note that the semantics of Verilog require that if any bit of the dividend
or divisor is @('X') or @('Z'), then every bit of the output is @('X').  We do
not deal with this requirement in the individual steps; it's part of the
wrapper.</p>"

  :guard (>= n 2) ;; we deal with the one-bit case separately
  :body
  (b* ((n     (lnfix n))
       (name  (hons-copy (cat "VL_" (natstr n) "_BIT_DIV_STEP")))

       ((mv an-expr an-port an-portdecl an-vardecl) (vl-occform-mkport "a_next"      :vl-output n))
       ((mv qn-expr qn-port qn-portdecl qn-vardecl) (vl-occform-mkport "q_next"      :vl-output n))
       ((mv ap-expr ap-port ap-portdecl ap-vardecl) (vl-occform-mkport "a_prev"      :vl-input n))
       ((mv qp-expr qp-port qp-portdecl qp-vardecl) (vl-occform-mkport "q_prev"      :vl-input n))
       ((mv d~-expr d~-port d~-portdecl d~-vardecl) (vl-occform-mkport "divisor_bar" :vl-input n))

       ;; wire [n-1:0]   a, q, diff;
       ;; wire 	         fits;
       ((mv a-expr    a-vardecl)    (vl-occform-mkwire "a"    n))
       ((mv diff-expr diff-vardecl) (vl-occform-mkwire "diff" n))
       ((mv fits-expr fits-vardecl) (vl-occform-mkwire "fits" 1))


       ;; VL_4_BIT_ASSIGN     init (a, {a_prev[n-2:0], q_prev[n-1]});
       ;; VL_4_BIT_ADDER_CORE core (diff, fits, a, divisor_bar, 1'b1);
       ;; VL_4_BIT_APPROX_MUX amux (a_next, fits, diff, a);
       ;; VL_4_BIT_ASSIGN     qout (q_next, {q_prev[n-2:0], fits});

       (ass-mods (vl-make-n-bit-assign n))
       (add-mods (vl-make-n-bit-adder-core n))
       (mux-mods (vl-make-n-bit-mux n t))
       (support  (append ass-mods add-mods mux-mods))
       (ass-mod  (car ass-mods))
       (add-mod  (car add-mods))
       (mux-mod  (car mux-mods))

       (init-inst (vl-simple-inst ass-mod "init" a-expr (make-vl-nonatom
                                                         :op :vl-concat
                                                         :args (list (vl-make-partselect ap-expr (- n 2) 0)
                                                                     (vl-make-bitselect qp-expr (- n 1)))
                                                         :finalwidth n
                                                         :finaltype :vl-unsigned)))
       (core-inst (vl-simple-inst add-mod "core" diff-expr fits-expr a-expr d~-expr |*sized-1'b1*|))
       (amux-inst (vl-simple-inst mux-mod "amux" an-expr fits-expr diff-expr a-expr))

       (qout-inst (vl-simple-inst ass-mod "qout" qn-expr (make-vl-nonatom
                                                          :op :vl-concat
                                                          :args (list (vl-make-partselect qp-expr (- n 2) 0)
                                                                      fits-expr)
                                                          :finalwidth n
                                                          :finaltype :vl-unsigned))))
    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list an-port qn-port ap-port qp-port d~-port)
                          :portdecls (list an-portdecl qn-portdecl ap-portdecl qp-portdecl d~-portdecl)
                          :vardecls  (list an-vardecl qn-vardecl ap-vardecl qp-vardecl d~-vardecl
                                           a-vardecl diff-vardecl fits-vardecl)
                          :modinsts  (list init-inst core-inst amux-inst qout-inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          support)))



(def-vl-modgen vl-make-n-bit-div-core ((n natp))
  :parents (vl-make-n-bit-div-rem)
  :short "Core of a division/remainder module."

  :long "<p>We generate the module @('VL_N_BIT_DIV_CORE') which implements a
basic restoring division algorithm in terms of @(see primitives).</p>

<p>The core modules we produce here do <b>not</b> properly handle zero divides
or detect X/Z values on the dividend and divisor.  To see how we correct for
these cases, see @(see vl-make-n-bit-div-rem).</p>

<p>Aside from these special cases, the core module does produce the right
answer by chaining together N division steps; for details about these steps and
for an overview of the algorithm, see @(see vl-make-n-bit-div-step).</p>

<p>As an example, here's what we generate in the four-bit case:</p>

@({
module VL_4_BIT_DIV_CORE (quotient, remainder, dividend, divisor);

  output [3:0] quotient;
  output [3:0] remainder;
  input [3:0] dividend;
  input [3:0] divisor;

  wire [3:0]  a1, a2, a3;
  wire [3:0]  q1, q2, q3;

  wire [3:0]  divisor_bar;
  VL_4_BIT_NOT divbar (divisor_bar, divisor);

  VL_4_BIT_DIV_STEP step0 (a1, q1, 4'b0, dividend, divisor_bar);
  VL_4_BIT_DIV_STEP step1 (a2, q2, a1, q1, divisor_bar);
  VL_4_BIT_DIV_STEP step2 (a3, q3, a2, q2, divisor_bar);
  VL_4_BIT_DIV_STEP step3 (remainder, quotient, a3, q3, divisor_bar);

endmodule
})"

  :guard (>= n 2)

  :body
  (b* ((n    (lnfix n))
       (name (hons-copy (cat "VL_" (natstr n) "_BIT_DIV_CORE")))

       ((mv q-expr q-port q-portdecl q-vardecl) (vl-occform-mkport "quotient"  :vl-output n))
       ((mv r-expr r-port r-portdecl r-vardecl) (vl-occform-mkport "remainder" :vl-output n))
       ((mv e-expr e-port e-portdecl e-vardecl) (vl-occform-mkport "dividend"  :vl-input n))
       ((mv d-expr d-port d-portdecl d-vardecl) (vl-occform-mkport "divisor"   :vl-input n))

       (neg-mods  (vl-make-n-bit-not n))
       (step-mods (vl-make-n-bit-div-step n))
       (neg-mod   (car neg-mods))
       (step-mod  (car step-mods))
       (support   (append neg-mods step-mods))

       ; wire [n-1:0] divisor_bar;
       ((mv d~-expr d~-vardecl) (vl-occform-mkwire "divisor_bar" n))
       (d~-inst (vl-simple-inst neg-mod "divbar" d~-expr d-expr))

       ; wire [n-1:0] a1, a2, ... a{n-1};
       ; wire [n-1:0] q1, q2, ..., q{n-1};
       ((mv a-exprs a-vardecls) (vl-occform-mkwires "a" 1 n :width n))
       ((mv q-exprs q-vardecls) (vl-occform-mkwires "q" 1 n :width n))

       (|n'b0| (make-vl-atom :guts (make-vl-constint :value 0
                                                     :origwidth n
                                                     :origtype :vl-unsigned)
                             :finalwidth n
                             :finaltype :vl-unsigned))

       (steps (vl-simple-inst-list step-mod "step"
                                   (append a-exprs (list r-expr))
                                   (append q-exprs (list q-expr))
                                   (cons |n'b0| a-exprs)
                                   (cons e-expr q-exprs)
                                   (replicate n d~-expr))))
    (cons (make-vl-module :name      name
                          :origname  name
                          :portdecls (list q-portdecl r-portdecl e-portdecl d-portdecl)
                          :ports     (list q-port r-port e-port d-port)
                          :vardecls  (list* q-vardecl r-vardecl e-vardecl d-vardecl
                                            d~-vardecl
                                            (append a-vardecls q-vardecls))
                          :modinsts  (cons d~-inst steps)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          support)))


(def-vl-modgen vl-make-n-bit-div-rem ((n posp))
  :short "Top-level division/remainder module."

  :long "<p>We generate the module @('VL_N_BIT_DIV_REM') which exactly
implements the Verilog semantics for division and remainder using @(see
primitives).</p>

<p>The actual division is carried out by a core module; see @(see
vl-make-n-bit-div-core).  But this core doesn't properly handle the cases where
the divisor is zero, or when there is an X/Z value on either the dividend or
the divisor.  In these cases, the Verilog semantics say that the entire result
must be X.</p>

<p>This module just wraps up the core module with zero- and x-detection
circuitry to achieve the desired behavior.</p>"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        ;; Custom definition for absurd case of 1-bit by 1-bit division
        (list *vl-1-bit-div-rem* *vl-1-bit-x* *vl-1-bit-not* *vl-1-bit-and*
              *vl-1-bit-or* *vl-1-bit-xor*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_DIV_REM")))

       ((mv q-expr q-port q-portdecl q-vardecl) (vl-occform-mkport "quotient"  :vl-output n))
       ((mv r-expr r-port r-portdecl r-vardecl) (vl-occform-mkport "remainder" :vl-output n))
       ((mv e-expr e-port e-portdecl e-vardecl) (vl-occform-mkport "dividend"  :vl-input n))
       ((mv d-expr d-port d-portdecl d-vardecl) (vl-occform-mkport "divisor"   :vl-input n))

       ;; Main divider.  May not produce the right answer when there are X bits
       ;; or when the divisor is zero.
       ;;
       ;;   wire [n-1:0]  qmain, rmain;
       ;;   VL_N_BIT_DIV_CORE core (qmain, rmain, dividend, divisor);

       ((mv qm-expr qm-vardecl) (vl-occform-mkwire "qmain" n))
       ((mv rm-expr rm-vardecl) (vl-occform-mkwire "rmain" n))

       (core-mods (vl-make-n-bit-div-core n))
       (core-mod  (car core-mods))
       (core-inst (vl-simple-inst core-mod "core" qm-expr rm-expr e-expr d-expr))

       ;; Detecting divides by zero.
       ;;
       ;; wire nonzero;
       ;; VL_4_BIT_REDUCTION_OR check0 (nonzero, divisor);

       ((mv nz-expr nz-vardecl) (vl-occform-mkwire "nonzero" 1))

       (nz-mods (vl-make-n-bit-reduction-op :vl-unary-bitor n))
       (nz-mod  (car nz-mods))
       (nz-inst (vl-simple-inst nz-mod "check0" nz-expr d-expr))

       ;; Fixup for divides by zero.
       ;;
       ;; We'll drive qfix/rfix with either:
       ;;   - copies of qmain/rmain for divides by nonzero, or
       ;;   - xxxxxx                for divides by zero
       ;;
       ;;   wire [3:0] xwire, qfix, rfix;
       ;;   VL_4_BIT_X xdriver (xwire);
       ;;   VL_4_BIT_APPROX_MUX q_zero_fix (qfix, nonzero, qmain, xwire);
       ;;   VL_4_BIT_APPROX_MUX r_zero_fix (rfix, nonzero, rmain, xwire);

       ((mv x-expr x-vardecl)   (vl-occform-mkwire "xwire" n))
       ((mv qf-expr qf-vardecl) (vl-occform-mkwire "qfix" n))
       ((mv rf-expr rf-vardecl) (vl-occform-mkwire "rfix" n))

       (x-mods   (vl-make-n-bit-x n))
       (x-mod    (car x-mods))
       (x-inst   (vl-simple-inst x-mod "xdriver" x-expr))

       (mux-mods (vl-make-n-bit-mux n t))
       (mux-mod  (car mux-mods))
       (qf-inst  (vl-simple-inst mux-mod "q_zero_fix" qf-expr nz-expr qm-expr x-expr))
       (rf-inst  (vl-simple-inst mux-mod "r_zero_fix" rf-expr nz-expr rm-expr x-expr))

       ;; Fixup for any X bit on either input.  Verilog semantics say: "drive
       ;; all bits to X."
       ;;
       ;; VL_4_BY_4_XPROP xdet_q (quotient, qfix, dividend, divisor);
       ;; VL_4_BY_4_XPROP xdet_r (remainder, rfix, dividend, divisor);

       (xprop-mods (vl-make-n-bit-x-propagator n n))
       (xprop-mod  (car xprop-mods))
       (q-inst     (vl-simple-inst xprop-mod "xdet_q" q-expr qf-expr e-expr d-expr))
       (r-inst     (vl-simple-inst xprop-mod "xdet_r" r-expr rf-expr e-expr d-expr)))

    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list q-port r-port e-port d-port)
                          :portdecls (list q-portdecl r-portdecl e-portdecl d-portdecl)
                          :vardecls  (list q-vardecl r-vardecl e-vardecl d-vardecl
                                           qm-vardecl rm-vardecl
                                           nz-vardecl
                                           x-vardecl qf-vardecl rf-vardecl)
                          :modinsts  (list core-inst nz-inst x-inst qf-inst rf-inst
                                           q-inst r-inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          (append x-mods
                  xprop-mods
                  mux-mods
                  nz-mods
                  core-mods))))



(def-vl-modgen vl-make-n-bit-unsigned-div ((n posp))
  :short "Generate an unsigned divider module."

  :long "<p>We generate @('VL_N_BIT_UNSIGNED_DIV') for the given @('n'), which is
written using @(see primitives) but is semantically equal to:</p>

@({
module VL_N_BIT_UNSIGNED_DIV (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [n-1:0] b;
  assign out = a / b;
endmodule
})

<p>This is a thin wrapper around @(see vl-make-n-bit-div-rem).  It uses a naive
N-step restoring division algorithm.</p>"

  :body
  (b* ((n    (lposfix n))
       (name (hons-copy (cat "VL_" (natstr n) "_BIT_UNSIGNED_DIV")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-occform-mkport "a"   :vl-input n))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-occform-mkport "b"   :vl-input n))

       ;; wire [n-1:0] unused;
       ;; VL_1_BIT_DIV_REM core (out, unused, a, b);
       ((mv u-expr u-vardecl) (vl-occform-mkwire "unused" n))
       (core-mods (vl-make-n-bit-div-rem n))
       (core-mod  (car core-mods))
       (core-inst (vl-simple-inst core-mod "core" out-expr u-expr a-expr b-expr)))
    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :vardecls  (list out-vardecl a-vardecl b-vardecl u-vardecl)
                          :modinsts  (list core-inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          core-mods)))


(def-vl-modgen vl-make-n-bit-unsigned-rem ((n posp))
  :short "Generate an unsigned remainder module."

  :long "<p>We generate @('VL_N_BIT_UNSIGNED_REM') for the given @('n'), which is
written using @(see primitives) but is semantically equal to:</p>

@({
module VL_N_BIT_UNSIGNED_REM (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [n-1:0] b;
  assign out = a % b;
endmodule
})

<p>This is a thin wrapper around @(see vl-make-n-bit-div-rem).  It uses a naive
N-step restoring division algorithm.</p>"

  :body
  (b* ((n    (lposfix n))
       (name (hons-copy (cat "VL_" (natstr n) "_BIT_UNSIGNED_REM")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-occform-mkport "a"   :vl-input n))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-occform-mkport "b"   :vl-input n))

       ;; wire [n-1:0] unused;
       ;; VL_1_BIT_DIV_REM core (unused, out, a, b);
       ((mv u-expr u-vardecl) (vl-occform-mkwire "unused" n))
       (core-mods (vl-make-n-bit-div-rem n))
       (core-mod  (car core-mods))
       (core-inst (vl-simple-inst core-mod "core" u-expr out-expr a-expr b-expr)))
    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :vardecls  (list out-vardecl a-vardecl b-vardecl u-vardecl)
                          :modinsts  (list core-inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          core-mods)))

#||

(include-book
 "centaur/vl2014/mlib/writer" :dir :system)

(top-level
 (with-ps-file "div4_support.v"
               (vl-ps-update-show-atts nil)
               (vl-pp-modulelist (mergesort
                                  (append (vl-make-n-bit-unsigned-div 4)
                                          (vl-make-n-bit-unsigned-rem 4))))))

(top-level
 (with-ps-file "div2_support.v"
               (vl-ps-update-show-atts nil)
               (vl-pp-modulelist (mergesort
                                  (append (vl-make-n-bit-unsigned-div 2)
                                          (vl-make-n-bit-unsigned-rem 2))))))

(top-level
 (with-ps-file "div1_support.v"
               (vl-ps-update-show-atts nil)
               (vl-pp-modulelist (mergesort
                                  (append (vl-make-n-bit-unsigned-div 1)
                                          (vl-make-n-bit-unsigned-rem 1))))))

||#
