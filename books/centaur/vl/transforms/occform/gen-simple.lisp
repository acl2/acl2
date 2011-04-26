; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "gen-util")
(include-book "../../primitives")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))

; gen-simple.lisp -- functions that generate
;
;  - N-bit pointwise AND, OR, XOR, XNOR modules
;  - N-bit assignment modules
;  - N-bit negation modules
;  - N-bit reduction AND, OR, and XOR operator modules
;  - N-bit muxes (regular or approximations)
;  - N-bit "Z muxes" (tri-state buffers)

(def-vl-modgen vl-make-n-bit-binary-op (type n)
  :short "Generate a wide, pointwise AND, OR, XOR, or XNOR module."

  :long "<p>The <tt>type</tt> must be either <tt>:VL-AND</tt>, <tt>:VL-OR</tt>,
<tt>:VL-XOR</tt>, or <tt>:VL-XNOR</tt>.  Depending on the type, we generate a
module that is written using gates but is semantically equivalent to:</p>

<code>
module VL_N_BIT_POINTWISE_{AND,OR,XOR,XNOR} (out, a, b) ;
  output [N-1:0] out;
  input [N-1:0] a;
  input [N-1:0] b;

// Then, one of:

  assign out = a &amp; b;     // for AND
  assign out = a | b;     // for OR
  assign out = a ^ b;     // for XOR
  assign out = a ~^ b;    // for XNOR

endmodule
</code>

<p>For instance, if <tt>N</tt> is 4 and type is OR, we actually write:</p>

<code>
  or(out[3], a[3], b[3]);
  or(out[2], a[2], b[2]);
  or(out[1], a[1], b[1]);
  or(out[0], a[0], b[0]);
</code>"

  :guard (and (member type '(:vl-and :vl-or :vl-xor :vl-xnor))
              (posp n))
  :body
  (b* ((name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_POINTWISE_"
                                  (case type
                                    (:vl-and "AND")
                                    (:vl-or "OR")
                                    (:vl-xor "XOR")
                                    (:vl-xnor "XNOR")))))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (a-wires   (vl-make-list-of-bitselects a-expr 0 (- n 1)))
       (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))
       (gates     (vl-make-binary-gateinstlist type out-wires a-wires b-wires nil)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :netdecls  (list out-netdecl a-netdecl b-netdecl)
                          :gateinsts gates
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))






(defsection vl-make-n-bit-assign-insts
  :parents (vl-make-n-bit-assign)
  :short "Generate a series of @(see *vl-1-bit-assign*) instances."

  (defund vl-make-n-bit-assign-insts (name-index out-bits in-bits)
    (declare (xargs :guard (and (natp name-index)
                                (vl-exprlist-p out-bits)
                                (vl-exprlist-p in-bits)
                                (same-lengthp out-bits in-bits))))
    (b* (((when (atom out-bits))
          nil)
         (args  (list (make-vl-plainarg :expr (car out-bits) :dir :vl-output :portname (hons-copy "out"))
                      (make-vl-plainarg :expr (car in-bits)  :dir :vl-input  :portname (hons-copy "in"))))
         (inst1 (make-vl-modinst :instname  (hons-copy (str::cat "bit_" (str::natstr name-index)))
                                 :modname   (vl-module->name *vl-1-bit-assign*)
                                 :portargs  (vl-arguments nil args)
                                 :paramargs (vl-arguments nil nil)
                                 :loc       *vl-fakeloc*))
         (rest  (vl-make-n-bit-assign-insts (+ 1 name-index) (cdr out-bits) (cdr in-bits))))
      (cons inst1 rest)))

  (defthm vl-modinstlist-p-of-vl-make-n-bit-assign-insts
    (implies (and (force (natp name-index))
                  (force (vl-exprlist-p out-bits))
                  (force (vl-exprlist-p in-bits))
                  (force (same-lengthp out-bits in-bits)))
             (vl-modinstlist-p (vl-make-n-bit-assign-insts name-index out-bits in-bits)))
    :hints(("Goal" :in-theory (enable vl-make-n-bit-assign-insts)))))


(def-vl-modgen vl-make-n-bit-assign (n)
  :short "Generate a wide assignment module."

  :long "<p>We generate a module that is semantically equal to:</p>

<code>
module VL_N_BIT_ASSIGN (out, in) ;
  output [n-1:0] out;
  input [n-1:0] in;
  assign out = in;
endmodule
</code>

<p>We actually implement these modules using a list of @(see *vl-1-bit-assign*)
instances, one for each bit.  For instance, we implement our four-bit
assignment module as:</p>

<code>
module VL_4_BIT_ASSIGN (out, in);
  output [3:0] out ;
  input [3:0] in ;
  VL_1_BIT_ASSIGN bit_0 (out[0], in[0]) ;
  VL_1_BIT_ASSIGN bit_1 (out[1], in[1]) ;
  VL_1_BIT_ASSIGN bit_2 (out[2], in[2]) ;
  VL_1_BIT_ASSIGN bit_3 (out[3], in[3]) ;
endmodule
</code>"

  :guard (posp n)

  :body
  (b* (((when (= n 1))
        (list *vl-1-bit-assign*))

       (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_ASSIGN")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (in-wires  (vl-make-list-of-bitselects in-expr  0 (- n 1)))
       (modinsts  (vl-make-n-bit-assign-insts 0 out-wires in-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port)
                          :portdecls (list out-portdecl in-portdecl)
                          :netdecls  (list out-netdecl in-netdecl)
                          :modinsts  modinsts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-assign*)))



(def-vl-modgen vl-make-n-bit-not (n)
  :short "Generate a wide negation module."

  :long "<p>We generate a module that is written using gates and which is
semantically equivalent to:</p>

<code>
module VL_N_BIT_NOT (out, in) ;
  output [N-1:0] out;
  input [N-1:0] in;
  assign out = ~in;
endmodule
</code>

<p>For instance, for a four-bit negation module, instead of the assignment
above we would have:</p>

<code>
 not(out[3], in[3]);
 not(out[2], in[2]);
 not(out[1], in[1]);
 not(out[0], in[0]);
</code>"

  :guard (posp n)
  :body
  (b* ((name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_NOT")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))

       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (in-wires  (vl-make-list-of-bitselects in-expr 0 (- n 1)))
       (gates     (vl-make-unary-gateinstlist :vl-not out-wires in-wires nil)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port)
                          :portdecls (list out-portdecl in-portdecl)
                          :netdecls  (list out-netdecl in-netdecl)
                          :gateinsts gates
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-n-bit-reduction-op (type n)
  :short "Generate a wide reduction AND, OR, or XOR module."

  :long "<p>The <tt>type</tt> must be either <tt>:VL-UNARY-BITAND</tt>,
<tt>:VL-UNARY-BITOR</tt>, or <tt>:VL-UNARY-XOR</tt>.  We don't deal with
<tt>nand</tt>, <tt>nor</tt>, or <tt>xnor</tt> because those should be handled
by @(see oprewrite) instead.  Depending on the type, we generate a module that
is written using gates, and which is semantically equivalent to:</p>

<code>
module VL_N_BIT_REDUCTION_{AND,OR,XOR} (out, in) ;
  output out;
  input [N-1:0] in;

// Then, one of:

  assign out = &amp;in;     // For AND
  assign out = |in;     // For OR
  assign out = ^in;     // For XOR

endmodule
</code>

<p>For instance, for a 4-bit reduction xor, we actually generate:</p>

<code>
  wire [2:0] temp;
  xor(temp0, in1, in0);
  xor(temp1, in2, temp0);
  xor(temp2, in3, temp1);
  xor(out,   in4, temp2);
</code>"

  :guard (and (member type (list :vl-unary-bitand :vl-unary-bitor :vl-unary-xor))
              (posp n))

  :body
  (b* ((name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_REDUCTION_"
                                  (case type
                                    (:vl-unary-bitand "AND")
                                    (:vl-unary-bitor "OR")
                                    (:vl-unary-xor "XOR")))))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))

       (ports     (list out-port in-port))
       (portdecls (list out-portdecl in-portdecl))
       (gtype     (case type
                    (:vl-unary-bitand :vl-and)
                    (:vl-unary-bitor :vl-or)
                    (:vl-unary-xor :vl-xor)))

       ((when (< n 3))
        ;; Special cases.  See test-redux.v.  Any one-bit reduction op is a
        ;; buf; any two-bit op is just the op applied to the argument bits.
        (let* ((gateinst (if (= n 1)
                             (vl-make-unary-gateinst :vl-buf out-expr in-expr nil *vl-fakeloc*)
                           (vl-make-binary-gateinst gtype
                                                    out-expr
                                                    (vl-make-bitselect in-expr 0)
                                                    (vl-make-bitselect in-expr 1)
                                                    nil
                                                    *vl-fakeloc*))))
          (list (make-vl-module :name      name
                                :origname  name
                                :ports     ports
                                :portdecls portdecls
                                :netdecls  (list in-netdecl out-netdecl)
                                :gateinsts (list gateinst)
                                :minloc    *vl-fakeloc*
                                :maxloc    *vl-fakeloc*))))

       ;; Otherwise, n >= 3 and we use a temporary wire.

       ;; wire [n-3:0] temp;
       ((mv temp-expr temp-netdecl) (vl-occform-mkwire "temp" (- n 2)))

       (gate-outs  (append (vl-make-list-of-bitselects temp-expr 0 (- n 3)) (list out-expr)))
       (gate-lhses (vl-make-list-of-bitselects in-expr 1 (- n 1)))
       (gate-rhses (cons (vl-make-bitselect in-expr 0) (vl-make-list-of-bitselects temp-expr 0 (- n 3))))
       (gates      (vl-make-binary-gateinstlist gtype gate-outs gate-lhses gate-rhses nil)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     ports
                          :portdecls portdecls
                          :netdecls  (list in-netdecl out-netdecl temp-netdecl)
                          :gateinsts gates
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-n-bit-mux (n approxp)
  :short "Generate a wide multiplexor module."

  :long "<p>We generate a module that is written using gates and which is a
conservative approximation of the following:</p>

<code>
module VL_N_BIT_MUX (out, sel, a, b);  // or VL_N_BIT_APPROX_MUX
  output [N-1:0] out;
  input sel;
  input [N-1:0] a;
  input [N-1:0] b;

  assign out = sel ? a : b;
endmodule
</code>

<p>We generate a \"regular\" or \"approx\" versions depending on
<tt>approxp</tt>.  Either version is a conservative, inexact approximations of
the Verilog semantics of the conditional operator, because we cannot really
preserve <tt>Z</tt>s appropriately using gates.  Perhaps the semantics of
<tt>?:</tt> are not exactly synthesizable?</p>

<p>When <tt>approxp</tt> is NIL, we try to model Verilog's semantics as closely
as possible; in this case <tt>X ? 1 : 1</tt> and <tt>X ? 0 : 0</tt> produce 1
and 0, respectively.  But when <tt>approxp</tt> is T, we conservatively produce
X in these cases, instead.</p>

<p>Our gate-based approximation combines the inputs bit-by-bit.  For each pair
of bits, <tt>a[i]</tt> and <tt>b[i]</tt>, we basically assign:</p>

<ul>
 <li><tt>out[i] = (sel &amp; a[i]) | (~sel &amp; b[i])</tt>, for approx muxes, or</li>
 <li><tt>out[i] = (sel &amp; a[i]) | (~sel &amp; b[i]) | (a[i] &amp; b[i])</tt> otherwise</li>
</ul>

<p>You might expect that it's better to set <tt>approxp</tt> to NIL and get the
behavior that is closest to Verilog.  But Sol has reported that the more
conservative version produces better AIGs since the output doesn't depend upon
the inputs when the select is X.  So, we generally set <tt>approxp</tt> to
T.</p>"

  :guard (and (posp n)
              (booleanp approxp))

  :body
  (b* ((name (str::cat "VL_" (str::natstr n) "_BIT_" (if approxp "APPROX_MUX" "MUX")))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
         ((mv sel-expr sel-port sel-portdecl sel-netdecl) (vl-occform-mkport "sel" :vl-input 1))
         ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
         ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

         (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
         (a-wires   (vl-make-list-of-bitselects a-expr 0 (- n 1)))
         (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))

         ((mv sbar-expr sbar-netdecl)   (vl-occform-mkwire "sbar" 1))   ;;; sbar      = ~sel;
         ((mv sa-expr sa-netdecl)       (vl-occform-mkwire "s_a" n))    ;;; s_a[i]    = s & a[i];
         ((mv sbarb-expr sbarb-netdecl) (vl-occform-mkwire "sbar_b" n)) ;;; sbar_b[i] = sbar & b[i];
         ((mv ab-expr ab-netdecl)       (vl-occform-mkwire "ab" n))     ;;; ab[i]     = a[i] & b[i];

         (sa-wires    (vl-make-list-of-bitselects sa-expr 0 (- n 1)))
         (ab-wires    (vl-make-list-of-bitselects ab-expr 0 (- n 1)))
         (sbarb-wires (vl-make-list-of-bitselects sbarb-expr 0 (- n 1)))

         (sbar-gate   (vl-make-unary-gateinst :vl-not sbar-expr sel-expr nil *vl-fakeloc*))
         (sa-gates    (vl-make-binary-gateinstlist :vl-and sa-wires (repeat sel-expr n) a-wires *vl-fakeloc*))
         (sbarb-gates (vl-make-binary-gateinstlist :vl-and sbarb-wires (repeat sbar-expr n) b-wires *vl-fakeloc*))
         (ab-gates    (vl-make-binary-gateinstlist :vl-and ab-wires a-wires b-wires *vl-fakeloc*))

         (ports     (list out-port sel-port a-port b-port))
         (portdecls (list out-portdecl sel-portdecl a-portdecl b-portdecl))
         (nets1     (list out-netdecl sel-netdecl a-netdecl b-netdecl sbar-netdecl sa-netdecl sbarb-netdecl ab-netdecl))
         (gates1    (append (list sbar-gate) sa-gates sbarb-gates ab-gates))

         ((when approxp)
          ;; Less exact version:
          ;; Set out[i] = sa[i] | sbar_b[i]
          (b* ((out-gates (vl-make-binary-gateinstlist :vl-or out-wires sa-wires sbarb-wires *vl-fakeloc*)))
            (list (make-vl-module :name      name
                                  :origname  name
                                  :ports     ports
                                  :portdecls portdecls
                                  :netdecls  nets1
                                  :gateinsts (append gates1 out-gates)
                                  :minloc    *vl-fakeloc*
                                  :maxloc    *vl-fakeloc*))))

         ;; More-exact version:
         ;; wire [n-1:0] main = s_a[i] | sbar_b[i];
         ;; assign out[i] = main[i] | ab[i];
         ((mv main-expr main-netdecl) (vl-occform-mkwire "main" n))
         (main-wires (vl-make-list-of-bitselects main-expr 0 (- n 1)))
         (main-gates (vl-make-binary-gateinstlist :vl-or main-wires sa-wires sbarb-wires *vl-fakeloc*))
         (out-gates  (vl-make-binary-gateinstlist :vl-or out-wires main-wires ab-wires *vl-fakeloc*)))

      (list (make-vl-module :name      name
                            :origname  name
                            :ports     ports
                            :portdecls portdecls
                            :netdecls  (cons main-netdecl nets1)
                            :gateinsts (append gates1 main-gates out-gates)
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*))))



(defsection vl-make-n-bit-zmux-aux
  :parents (occform)
  :short "Make a list of @(see *vl-1-bit-zmux*) instances."

  (defund vl-make-n-bit-zmux-aux
    (outs ; list of output wires
     sel  ; single select wire
     as   ; list of input wires
     nf   ; name factory for unique-name generation
     )
    "Returns (MV MODINSTS NF')"
    (declare (xargs :guard (and (vl-exprlist-p outs)
                                (vl-expr-p sel)
                                (vl-exprlist-p as)
                                (same-lengthp outs as)
                                (vl-namefactory-p nf))))
    (b* (((when (atom outs))
          (mv nil nf))
         ((mv inst1-name nf) (vl-namefactory-indexed-name "bit" nf))
         (args (list (make-vl-plainarg :expr (car outs) :dir :vl-output :portname (hons-copy "out"))
                     (make-vl-plainarg :expr sel        :dir :vl-input  :portname (hons-copy "sel"))
                     (make-vl-plainarg :expr (car as)   :dir :vl-input  :portname (hons-copy "a"))))
         (inst1 (make-vl-modinst :instname  inst1-name
                                 :modname   (vl-module->name *vl-1-bit-zmux*)
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :loc       *vl-fakeloc*))
         ((mv rest nf)
          (vl-make-n-bit-zmux-aux (cdr outs) sel (cdr as) nf)))
      (mv (cons inst1 rest) nf)))

  (defthm vl-make-n-bit-zmux-aux-basics
    (implies (and (force (vl-exprlist-p outs))
                  (force (vl-expr-p sel))
                  (force (vl-exprlist-p as))
                  (force (same-lengthp outs as))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-make-n-bit-zmux-aux outs sel as nf)))
               (and (vl-modinstlist-p (mv-nth 0 ret))
                    (vl-namefactory-p (mv-nth 1 ret)))))
    :hints(("Goal" :in-theory (enable vl-make-n-bit-zmux-aux)))))


(def-vl-modgen vl-make-n-bit-zmux (n)
  :short "Generate a wide tri-state buffer module."

  :long "<p>We generate a module using @(see *vl-1-bit-zmux*) primitives that
is semantically equivalent to:</p>

<code>
module VL_N_BIT_ZMUX (out, sel, a);
  output [n-1:0] out;
  input sel;
  input [n-1:0] a;
  assign out = sel ? a : n'bz;
endmodule
</code>

<p><b>BOZO</b> is it really equivalent?  It seems like it might be
conservative.</p>

<p>These modules are used to implement conditional (a.k.a. the <tt>?:</tt> or
ternary) operators whose last argument is <tt>Z</tt>.  Note that in @(see
oprewrite), we canonicalize <tt>sel ? Z : a</tt> to <tt>~sel ? a : Z</tt>, so
this actually handles both cases.</p>"

  :guard (posp n)

  :body
  (b* (((when (= n 1))
        (list *vl-1-bit-zmux*))

       (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_ZMUX")))
       (nf   (vl-empty-namefactory))

       ((mv out-name nf) (vl-namefactory-plain-name "out" nf))
       ((mv a-name nf)   (vl-namefactory-plain-name "a" nf))
       ((mv b-name nf)   (vl-namefactory-plain-name "b" nf))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport out-name :vl-output n))
       ((mv sel-expr sel-port sel-portdecl sel-netdecl) (vl-occform-mkport a-name :vl-input 1))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport b-name :vl-input n))

       (out-wires        (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (a-wires          (vl-make-list-of-bitselects a-expr 0 (- n 1)))
       ((mv modinsts nf) (vl-make-n-bit-zmux-aux out-wires sel-expr a-wires nf))

       (- (vl-free-namefactory nf))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list out-port sel-port a-port)
                            :portdecls (list out-portdecl sel-portdecl a-portdecl)
                            :netdecls  (list out-netdecl sel-netdecl a-netdecl)
                            :modinsts  modinsts
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))

    (list mod *vl-1-bit-zmux*)))

