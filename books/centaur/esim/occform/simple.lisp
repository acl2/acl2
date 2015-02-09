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
(include-book "centaur/vl2014/mlib/modgen" :dir :system)
(include-book "centaur/vl2014/primitives" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (non-parallel-book))

; This file has generators for:
;
;  - N-bit pointwise AND, OR, XOR, XNOR modules
;  - N-bit assignment modules
;  - N-bit negation modules
;  - N-bit reduction AND, OR, and XOR operator modules
;  - N-bit muxes (regular or approximations)
;  - N-bit "Z muxes" (tri-state buffers)
;  - N-bit case equality modules (===)
;  - N-bit pure-X module

(def-vl-modgen vl-make-n-bit-binary-op
  ((type (member type '(:vl-and :vl-or :vl-xor :vl-xnor)))
   (n    posp))

  :short "Generate a wide, pointwise AND, OR, XOR, or XNOR module."


  :long "<p>The @('type') must be either @(':VL-AND'), @(':VL-OR'),
@(':VL-XOR'), or @(':VL-XNOR').  Depending on the type, we generate a module
that is written using @(see primitives) but is semantically equivalent to:</p>

@({
module VL_N_BIT_POINTWISE_{AND,OR,XOR,XNOR} (out, a, b) ;
  output [N-1:0] out;
  input [N-1:0] a;
  input [N-1:0] b;

// Then, one of:

  assign out = a & b;     // for AND
  assign out = a | b;     // for OR
  assign out = a ^ b;     // for XOR
  assign out = a ~^ b;    // for XNOR

endmodule
})

<p>For instance, if @('N') is 4 and type is OR, we actually write:</p>

@({
  VL_1_BIT_OR bit3 (out[3], a[3], b[3]);
  VL_1_BIT_OR bit2 (out[2], a[2], b[2]);
  VL_1_BIT_OR bit1 (out[1], a[1], b[1]);
  VL_1_BIT_OR bit0 (out[0], a[0], b[0]);
})"

  :body
  (b* ((n (lposfix n))
       (prim (case type
               (:vl-and   *vl-1-bit-and*)
               (:vl-or    *vl-1-bit-or*)
               (:vl-xor   *vl-1-bit-xor*)
               (otherwise *vl-1-bit-xnor*)))


; [Jared and Sol]: It's tempting here to just return (list prim) in the special
; case that n = 1.  But after discussing this, we decided it seems nicer to put
; the wrapper in anyway, because that way you can see that this came from an
; pointwise AND.  This probably seems stupid: who is going to expect a
; VL_1_BIT_POINTWISE_AND and be surprised by a VL_1_BIT_AND?  Well, it is
; stupid in this case, but for reduction operators things get murkier.  A 1-bit
; reduction AND is just a BUF.  If you write foo = &bar, you probably don't
; expect to see a VL_1_BIT_BUF instead of a VL_1_BIT_REDUCTION_AND.  So for
; consistency we go ahead and try to keep the wrapper in all cases.

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_POINTWISE_"
                             (case type
                               (:vl-and "AND")
                               (:vl-or "OR")
                               (:vl-xor "XOR")
                               (:vl-xnor "XNOR")))))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-vardecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-vardecl)         (vl-occform-mkport "b" :vl-input n))
       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (a-wires   (vl-make-list-of-bitselects a-expr   0 (- n 1)))
       (b-wires   (vl-make-list-of-bitselects b-expr   0 (- n 1)))
       (insts     (vl-simple-inst-list prim "bit" out-wires a-wires b-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :vardecls  (list out-vardecl a-vardecl b-vardecl)
                          :modinsts  insts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          prim)))

#||
(vl-pps-modulelist (vl-make-n-bit-binary-op :vl-and 1))
(vl-pps-modulelist (vl-make-n-bit-binary-op :vl-and 2))
(vl-pps-modulelist (vl-make-n-bit-binary-op :vl-and 17))
||#



(def-vl-modgen vl-make-n-bit-assign ((n posp))
  :short "Generate a wide assignment module."

  :long "<p>We generate a module that is semantically equal to:</p>

@({
module VL_N_BIT_ASSIGN (out, in) ;
  output [n-1:0] out;
  input [n-1:0] in;
  assign out = in;
endmodule
})

<p>We actually implement these modules using a list of @(see *vl-1-bit-assign*)
instances, one for each bit.  For instance, we implement our four-bit
assignment module as:</p>

@({
module VL_4_BIT_ASSIGN (out, in);
  output [3:0] out ;
  input [3:0] in ;
  VL_1_BIT_ASSIGN bit_0 (out[0], in[0]) ;
  VL_1_BIT_ASSIGN bit_1 (out[1], in[1]) ;
  VL_1_BIT_ASSIGN bit_2 (out[2], in[2]) ;
  VL_1_BIT_ASSIGN bit_3 (out[3], in[3]) ;
endmodule
})"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-assign*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_ASSIGN")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (in-wires  (vl-make-list-of-bitselects in-expr  0 (- n 1)))
       (modinsts  (vl-simple-inst-list *vl-1-bit-assign* "bit" out-wires in-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port)
                          :portdecls (list out-portdecl in-portdecl)
                          :vardecls  (list out-vardecl in-vardecl)
                          :modinsts  modinsts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-assign*)))


#||
(vl-pps-modulelist (vl-make-n-bit-assign 1))
(vl-pps-modulelist (vl-make-n-bit-assign 4))
||#


(def-vl-modgen vl-make-n-bit-not ((n posp))
  :short "Generate a wide negation module."

  :long "<p>We generate a module that is written using gates and which is
semantically equivalent to:</p>

@({
module VL_N_BIT_NOT (out, in) ;
  output [N-1:0] out;
  input [N-1:0] in;
  assign out = ~in;
endmodule
})

<p>For instance, for a four-bit negation module, instead of the assignment
above we would have:</p>

@({
  VL_1_BIT_NOT bit0 (out[0], in[0]) ;
  VL_1_BIT_NOT bit1 (out[1], in[1]) ;
  VL_1_BIT_NOT bit2 (out[2], in[2]) ;
  VL_1_BIT_NOT bit3 (out[3], in[3]) ;
})"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-not*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_NOT")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (in-wires  (vl-make-list-of-bitselects in-expr 0 (- n 1)))
       (insts     (vl-simple-inst-list *vl-1-bit-not* "bit" out-wires in-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port)
                          :portdecls (list out-portdecl in-portdecl)
                          :vardecls  (list out-vardecl in-vardecl)
                          :modinsts  insts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-not*)))

#||
(vl-pps-modulelist (vl-make-n-bit-not 1))
(vl-pps-modulelist (vl-make-n-bit-not 4))
||#



(def-vl-modgen vl-make-n-bit-reduction-op
  ((type (member type (list :vl-unary-bitand :vl-unary-bitor :vl-unary-xor)))
   (n    posp))
  :short "Generate a wide reduction AND, OR, or XOR module."

  :long "<p>The @('type') must be either @(':VL-UNARY-BITAND'),
@(':VL-UNARY-BITOR'), or @(':VL-UNARY-XOR').  We don't deal with @('nand'),
@('nor'), or @('xnor') because those should be handled by @(see oprewrite)
instead.  Depending on the type, we generate a module that is written using
gates, and which is semantically equivalent to:</p>

@({
module VL_N_BIT_REDUCTION_{AND,OR,XOR} (out, in) ;
  output out;
  input [N-1:0] in;

// Then, one of:

  assign out = &in;     // For AND
  assign out = |in;     // For OR
  assign out = ^in;     // For XOR

endmodule
})

<p>For instance, for a 4-bit reduction xor, we actually generate:</p>

@({
  wire [2:0] temp;
  xor(temp0, in1, in0);
  xor(temp1, in2, temp0);
  xor(temp2, in3, temp1);
  xor(out,   in4, temp2);
})"

  :body
  (b* ((n (lposfix n))
       (name (hons-copy (cat "VL_" (natstr n) "_BIT_REDUCTION_"
                             (case type
                               (:vl-unary-bitand "AND")
                               (:vl-unary-bitor  "OR")
                               (otherwise        "XOR")))))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input n))
       (ports     (list out-port in-port))
       (portdecls (list out-portdecl in-portdecl))
       (prim      (case type
                    (:vl-unary-bitand *vl-1-bit-and*)
                    (:vl-unary-bitor  *vl-1-bit-or*)
                    (otherwise        *vl-1-bit-xor*)))

       ((when (< n 3))
        ;; Special cases.  See test-redux.v.
        (b* (((mv inst prim)
              (if (eql n 1)
                  (mv (vl-simple-inst *vl-1-bit-buf* "ans" out-expr in-expr)
                      *vl-1-bit-buf*)
                ;; Any two-bit op is just the op applied to the argument bits.
                (mv (vl-simple-inst prim "ans"
                                    out-expr
                                    (vl-make-bitselect in-expr 0)
                                    (vl-make-bitselect in-expr 1))
                    prim))))
          (list (make-vl-module :name      name
                                :origname  name
                                :ports     ports
                                :portdecls portdecls
                                :vardecls  (list in-vardecl out-vardecl)
                                :modinsts  (list inst)
                                :minloc    *vl-fakeloc*
                                :maxloc    *vl-fakeloc*)
                prim)))

       ;; Otherwise, n >= 3 and we use a temporary wire.

       ;; wire [n-3:0] temp;
       ((mv temp-expr temp-vardecl) (vl-occform-mkwire "temp" (- n 2)))

       (out-wires  (append (vl-make-list-of-bitselects temp-expr 0 (- n 3)) (list out-expr)))
       (lhs-wires  (vl-make-list-of-bitselects in-expr 1 (- n 1)))
       (rhs-wires  (cons (vl-make-bitselect in-expr 0) (vl-make-list-of-bitselects temp-expr 0 (- n 3))))
       (insts      (vl-simple-inst-list prim "bit" out-wires lhs-wires rhs-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     ports
                          :portdecls portdecls
                          :vardecls  (list in-vardecl out-vardecl temp-vardecl)
                          :modinsts  insts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          prim)))


#||
(vl-pps-modulelist (vl-make-n-bit-reduction-op :vl-unary-bitand 1))
(vl-pps-modulelist (vl-make-n-bit-reduction-op :vl-unary-bitand 2))
(vl-pps-modulelist (vl-make-n-bit-reduction-op :vl-unary-bitand 3))
(vl-pps-modulelist (vl-make-n-bit-reduction-op :vl-unary-bitand 130))
||#


(def-vl-modgen vl-make-n-bit-mux ((n       posp)
                                  (approxp booleanp))
  :short "Generate a wide multiplexor module."

  :long "<p>We generate a module that is written using gates and which is a
conservative approximation of the following:</p>

@({
module VL_N_BIT_MUX (out, sel, a, b);  // or VL_N_BIT_APPROX_MUX
  output [N-1:0] out;
  input sel;
  input [N-1:0] a;
  input [N-1:0] b;

  assign out = sel ? a : b;
endmodule
})

<p>We generate a \"regular\" or \"approx\" versions depending on @('approxp').
Either version is a conservative, inexact approximations of the Verilog
semantics of the conditional operator, because we cannot really preserve
@('Z')s appropriately using gates.  Perhaps the semantics of @('?:') are not
exactly synthesizable?</p>

<p>When @('approxp') is NIL, we try to model Verilog's semantics as closely as
possible; in this case @('X ? 1 : 1') and @('X ? 0 : 0') produce 1 and 0,
respectively.  But when @('approxp') is T, we conservatively produce X in these
cases, instead.</p>

<p>For some years we implemented both kinds of muxes using gates, roughly as</p>

<ul>
 <li>@('out[i] = (sel & a[i]) | (~sel & b[i])'), for approx muxes, or</li>
 <li>@('out[i] = (sel & a[i]) | (~sel & b[i]) | (a[i] & b[i])') otherwise</li>
</ul>

<p>But we later (October 2013) realized a bizarre inconsistency in the way that
approx-muxes handled things.  In particular:</p>

<ul>

<li>If both a[i] and b[i] are 0, then the approx-mux expression produces a good
0 output (because the AND gates propagate the zero.)  However,</li>

<li>If both a[i] and b[i] are 1, then the approx-mux expression produces an X
because the AND gates can't optimize things.</li>

</ul>

<p>Since our general intent is to model arbitrary mux implementations with
approx muxes, this optimistic treatment for 0 seems suspicious or incorrect.
We ultimately decided to adopt both kinds of muxes as new VL @(see primitives)
rather than implement them with gates.  See @(see *vl-1-bit-approx-mux*) and
@(see *vl-1-bit-mux*) for details.</p>

<p>You might expect that it's better to set @('approxp') to NIL and get the
behavior that is closest to Verilog.  But the more conservative version may
generally produce smaller AIGs since the output doesn't depend upon the inputs
when the select is X.  So, we generally set @('approxp') to T.</p>"

  :body
  (b* ((n         (lposfix n))
       (onebitmux (if approxp *vl-1-bit-approx-mux* *vl-1-bit-mux*))

       ((when (eql n 1))
        (list onebitmux))

       (name (cat "VL_" (natstr n) "_BIT_" (if approxp "APPROX_MUX" "MUX")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv sel-expr sel-port sel-portdecl sel-vardecl) (vl-primitive-mkport "sel" :vl-input))
       ((mv a-expr a-port a-portdecl a-vardecl)         (vl-occform-mkport "a"   :vl-input n))
       ((mv b-expr b-port b-portdecl b-vardecl)         (vl-occform-mkport "b"   :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (a-wires   (vl-make-list-of-bitselects a-expr 0 (- n 1)))
       (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))

       (insts     (vl-simple-inst-list onebitmux "bit" out-wires (replicate n sel-expr) a-wires b-wires))

       (mod  (make-vl-module :name      name
                             :origname  name
                             :ports     (list out-port sel-port a-port b-port)
                             :portdecls (list out-portdecl sel-portdecl a-portdecl b-portdecl)
                             :vardecls  (list out-vardecl sel-vardecl a-vardecl b-vardecl)
                             :modinsts  insts
                             :minloc    *vl-fakeloc*
                             :maxloc    *vl-fakeloc*)))
    (list mod onebitmux)))

#||
(vl-pps-modulelist (vl-make-n-bit-mux 5 t))
(vl-pps-modulelist (vl-make-n-bit-mux 5 nil))
||#


(def-vl-modgen vl-make-n-bit-zmux ((n posp))
  :short "Generate a wide tri-state buffer module."

  :long "<p>We generate a module using @(see *vl-1-bit-zmux*) primitives that
is semantically equivalent to:</p>

@({
module VL_N_BIT_ZMUX (out, sel, a);
  output [n-1:0] out;
  input sel;
  input [n-1:0] a;
  assign out = sel ? a : n'bz;
endmodule
})

<p><b>BOZO</b> is it really equivalent?  It seems like it might be
conservative.</p>

<p>These modules are used to implement conditional (a.k.a. the @('?:') or
ternary) operators whose last argument is @('Z').  Note that in @(see
oprewrite), we canonicalize @('sel ? Z : a') to @('~sel ? a : Z'), so this
actually handles both cases.</p>"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-zmux*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_ZMUX")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv sel-expr sel-port sel-portdecl sel-vardecl) (vl-primitive-mkport "sel" :vl-input))
       ((mv a-expr a-port a-portdecl a-vardecl)         (vl-occform-mkport "a"   :vl-input n))

       (out-wires        (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (a-wires          (vl-make-list-of-bitselects a-expr 0 (- n 1)))
       (insts            (vl-simple-inst-list *vl-1-bit-zmux* "bit" out-wires (replicate n sel-expr) a-wires))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list out-port sel-port a-port)
                            :portdecls (list out-portdecl sel-portdecl a-portdecl)
                            :vardecls  (list out-vardecl sel-vardecl a-vardecl)
                            :modinsts  insts
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))

    (list mod *vl-1-bit-zmux*)))


#||
(vl-pps-modulelist (vl-make-n-bit-zmux 5))
||#



(def-vl-modgen vl-make-n-bit-ceq ((n posp))
  :short "Generate a wide case-equality module."

  :long "<p>We generate a module that is written using gates and which is
semantically equivalent to:</p>

@({
module VL_N_BIT_CEQ (out, a, b) ;
  output out;
  input [N-1:0] a;
  input [N-1:0] b;
  assign out = (a === b);
endmodule
})

<p>We basically just instantiate @(see *vl-1-bit-ceq*) N times and then
reduction-and the results.</p> "

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-ceq*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_CEQ")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-occform-mkport "b" :vl-input n))
       ((mv tmp-expr tmp-vardecl)                       (vl-occform-mkwire "tmp" n))

       ;; A bunch of instances: VL_1_BIT_CEQ bit_i (tmp[i], a[i], b[i]);
       (tmp-wires (vl-make-list-of-bitselects tmp-expr 0 (- n 1)))
       (a-wires   (vl-make-list-of-bitselects a-expr 0 (- n 1)))
       (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))
       (insts     (vl-simple-inst-list *vl-1-bit-ceq* "bit" tmp-wires a-wires b-wires))

       ;; VL_N_BIT_REDUCTION_AND mk_out (out, tmp);
       (and-mods  (vl-make-n-bit-reduction-op :vl-unary-bitand n))
       (and-mod   (car and-mods))
       (and-inst  (vl-simple-inst and-mod "mk_out" out-expr tmp-expr)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port a-port b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :vardecls  (list out-vardecl a-vardecl b-vardecl tmp-vardecl)
                           :modinsts  (append insts (list and-inst))
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           *vl-1-bit-ceq*
           and-mods)))

#||
(vl-pps-modulelist (vl-make-n-bit-ceq 5))
||#


(def-vl-modgen vl-make-n-bit-x ((n posp))
  :short "Generate a wide X module."

  :long "<p>We generate a module that is semantically equal to:</p>

@({
module VL_N_BIT_ASSIGN (out, in) ;
  output [n-1:0] out;
  input [n-1:0] in;
  assign out = {n{1'bx}};
endmodule
})

<p>We actually implement these modules using a list of @(see *vl-1-bit-assign*)
instances, one for each bit.  For instance, we implement our four-bit X generator
like this:</p>

@({
module VL_4_BIT_X (out, in);
  output [3:0] out ;
  input [3:0] in ;

  wire xwire;
  VL_1_BIT_X xdriver (xwire);

  VL_1_BIT_ASSIGN bit_0 (out[0], xwire);
  VL_1_BIT_ASSIGN bit_1 (out[1], xwire) ;
  VL_1_BIT_ASSIGN bit_2 (out[2], xwire) ;
  VL_1_BIT_ASSIGN bit_3 (out[3], xwire) ;
endmodule
})"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-x*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_X")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))

       ((mv x-expr x-vardecl) (vl-occform-mkwire "xwire" 1))
       (x-inst (vl-simple-inst *vl-1-bit-x* "xdriver" x-expr))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (in-wires  (replicate n x-expr))
       (out-insts (vl-simple-inst-list *vl-1-bit-assign* "bit" out-wires in-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port)
                          :portdecls (list out-portdecl)
                          :vardecls  (list out-vardecl x-vardecl)
                          :modinsts  (cons x-inst out-insts)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-assign*
          *vl-1-bit-x*)))

#||
(vl-pps-modulelist (vl-make-n-bit-x 1))
(vl-pps-modulelist (vl-make-n-bit-x 2))
(vl-pps-modulelist (vl-make-n-bit-x 5))
||#
