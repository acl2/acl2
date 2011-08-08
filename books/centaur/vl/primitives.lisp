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
(include-book "util/defs")
(local (include-book "mlib/stmt-tools"))
(local (include-book "transforms/occform/gen-util"))


; BOZO consider simplifying the primitives, especially things like
; nand/nor/xnor which aren't used for much of anything, anyway.

(defxdoc primitives
  :parents (vl)
  :short "The primitive modules targetted by VL."

  :long "<p>The modules here can sort of be thought of as the target language
for VL's simplification scheme.  That is, our usual sequence of @(see
transforms) tries to convert rich Verilog modules that include expressions,
gates, parameters, etc., into simple, hierarchical modules that do nothing more
than instantiate other modules, with these primitive modules at the tips.</p>

<p>This set of primitives modules could be simplified, for instance we could
rewrite all of the basic gate modules into <tt>nand</tt> or some other basic
form.  We haven't done this yet, under the (probably misguided) theory that
having a richer set of primitives might somehow be more efficient for our
symbolic simulator.</p>")


(defxdoc *vl-1-bit-x*
  :parents (primitives)
  :short "Primitive X generator."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_X (out) ;
  output out;
  assign out = 1'bx;
endmodule
</code>

<p>VL takes this as a primitive.  This module is mainly used by @(see
weirdint-elim) to eliminate explicit X values from literals.</p>")

(defconsts *vl-1-bit-x*
  (b* ((name "VL_1_BIT_X")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'bx*| :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port)
                           :portdecls (list out-portdecl)
                           :netdecls  (list out-netdecl)
                           :assigns   (list out-assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-z*
  :parents (primitives)
  :short "Primitive Z generator."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_Z (out) ;
  output out;
  assign out = 1'bz;
endmodule
</code>

<p>VL takes this as a primitive.  This module is mainly used by @(see
weirdint-elim) to eliminate explicit Z values from literals.</p>")

(defconsts *vl-1-bit-z*
  (b* ((name "VL_1_BIT_Z")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'bz*| :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port)
                           :portdecls (list out-portdecl)
                           :netdecls  (list out-netdecl)
                           :assigns   (list out-assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-assign*
  :parents (primitives)
  :short "Primitive assignment module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_ASSIGN (out, in) ;
  output out;
  input in;
  assign out = in;
endmodule
</code>

<p>VL takes this as a primitive.  This module is also the basis for wider
assignment modules; see @(see vl-make-n-bit-assign).</p>

<p>Something subtle is that there is probably no way to implement
<tt>VL_1_BIT_ASSIGN</tt> in hardware.  One obvious approach would be to use a
buffer, but then <tt>out</tt> would be X when <tt>in</tt> is Z.  Another
approach would be to just wire together out and in, but then other assignments
to <tt>out</tt> would also affect <tt>in</tt>, and in Verilog this isn't the
case.</p>

<p>Originally our @(see occform) transformation tried to use buffers for
assignments since this seemed to be more conservative.  But these extra buffers
seemed to often be inappropriate, especially when dealing with lower level
modules that involve transistors.</p>")

(defconsts *vl-1-bit-assign*
  (b* ((name "VL_1_BIT_ASSIGN")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in"  :vl-input  1))
       (assign (make-vl-assign :lvalue out-expr :expr in-expr :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl  in-netdecl)
                           :assigns   (list assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-delay-1*
  :parents (primitives)
  :short "Primitive assignment with delay."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_DELAY_1 (out, in) ;
  output out;
  input in;
  assign #1 out = in;
endmodule
</code>

<p>VL takes this as a primitive.  It is used by our @(see assigndelays)
transform to separate delays from assignment statements.</p>")

(defconsts *vl-1-bit-delay-1*
  (b* ((name "VL_1_BIT_DELAY_1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in"  :vl-input  1))
       (one    (vl-make-index 1))
       (delay  (make-vl-gatedelay :rise one :fall one :high one))
       (assign (make-vl-assign :lvalue out-expr :expr in-expr :delay delay :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl  in-netdecl)
                           :assigns   (list assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-buf*
  :parents (primitives)
  :short "Primitive buffer module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_BUF (out, in) ;
  output out;
  input in;
  buf gate (out, in);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>buf</tt> gates,
but probably not for much else since ordinary assignments are handled with
@(see *vl-1-bit-assign*), instead.</p>")

(defconsts *vl-1-bit-buf*
  (b* ((name "VL_1_BIT_BUF")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in"  :vl-input  1))
       (gate (make-vl-gateinst :type :vl-buf
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr in-expr  :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl  in-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-not*
  :parents (primitives)
  :short "Primitive not-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_NOT (out, in) ;
  output out;
  input in;
  not gate (out, in);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>not</tt> gates
and <tt>~</tt> operators, and also in many modules we generate for other
operators like <tt>+</tt>.</p>")

(defconsts *vl-1-bit-not*
  (b* ((name "VL_1_BIT_NOT")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in"  :vl-input  1))
       (gate (make-vl-gateinst :type :vl-not
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr in-expr  :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl in-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-and*
  :parents (primitives)
  :short "Primitive and-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_AND (out, a, b) ;
  output out;
  input a;
  input b;
  and gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>and</tt> gates
and <tt>&amp;</tt> operators, and also in many modules we generate for other
operators like <tt>+</tt>.</p>")

(defconsts *vl-1-bit-and*
  (b* ((name "VL_1_BIT_AND")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-and
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-or*
  :parents (primitives)
  :short "Primitive or-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_OR (out, a, b) ;
  output out;
  input a;
  input b;
  or gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>or</tt> gates and
<tt>|</tt> operators, and also in many modules we generate for other operators
like <tt>+</tt>.</p>")

(defconsts *vl-1-bit-or*
  (b* ((name "VL_1_BIT_OR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-or
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-xor*
  :parents (primitives)
  :short "Primitive xor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_XOR (out, a, b) ;
  output out;
  input a;
  input b;
  xor gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>xor</tt> gates
and <tt>^</tt> operators, and also in many modules we generate for other
operators like <tt>+</tt>.</p>")

(defconsts *vl-1-bit-xor*
  (b* ((name "VL_1_BIT_XOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-xor
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-nand*
  :parents (primitives)
  :short "Primitive nand-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_NAND (out, a, b) ;
  output out;
  input a;
  input b;
  nand gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>nand</tt> gates
but probably not much else.</p>")

(defconsts *vl-1-bit-nand*
  ;; BOZO this should probably be a non-primitive.
  (b* ((name "VL_1_BIT_NAND")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-nand
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-nor*
  :parents (primitives)
  :short "Primitive nor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_NOR (out, a, b) ;
  output out;
  input a;
  input b;
  nor gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>nor</tt> gates,
but probably not much else.</p>")

(defconsts *vl-1-bit-nor*
  ;; BOZO this should probably be a non-primitive.
  (b* ((name "VL_1_BIT_NOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-nor
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-xnor*
  :parents (primitives)
  :short "Primitive xnor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

<code>
module VL_1_BIT_XNOR (out, a, b) ;
  output out;
  input a;
  input b;
  xnor gate (out, a, b);
endmodule
</code>

<p>VL takes this as a primitive.  We use this in place of <tt>xnor</tt> gates,
but probably not much else.</p>")

(defconsts *vl-1-bit-xnor*
  ;; BOZO this should probably be a non-primitive.
  (b* ((name "VL_1_BIT_XNOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr   a-port   a-portdecl   a-netdecl)   (vl-occform-mkport "a"   :vl-input  1))
       ((mv b-expr   b-port   b-portdecl   b-netdecl)   (vl-occform-mkport "b"   :vl-input  1))
       (gate (make-vl-gateinst :type :vl-xnor
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr a-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr b-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     a-port     b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl  a-netdecl  b-netdecl)
                           :gateinsts (list gate)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


(defxdoc *vl-1-bit-zmux*
  :parents (primitives)
  :short "Primitive tri-state buffer module."
  :long "<p>The Verilog meaning of this module is:</p>

<code>
module VL_1_BIT_ZMUX (out, sel, a);
  output out;
  input sel;
  input a;
  assign out = sel ? a : 1'bZ;
endmodule
</code>

<p>VL takes this as a primitive.  It is used in @(see vl-mux-occform) as the
basis for conditional expressions with <tt>Z</tt> branches that are typically
used to implement muxes.</p>")

(defconsts *vl-1-bit-zmux*
  ;; BOZO previous comments questioned whether E's *ft-buf* is equivalent to
  ;; the Verilog semantics, or conservative to it?
  (b* ((name "VL_1_BIT_ZMUX")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv sel-expr sel-port sel-portdecl sel-netdecl) (vl-occform-mkport "sel" :vl-input 1))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input 1))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom :op :vl-qmark
                                                      :args (list sel-expr a-expr |*sized-1'bz*|)
                                                      :finalwidth 1
                                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :ports     (list out-port     sel-port     a-port)
                           :portdecls (list out-portdecl sel-portdecl a-portdecl)
                           :netdecls  (list out-netdecl  sel-netdecl  a-netdecl)
                           :assigns   (list assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts
                           :origname  name)))


(defxdoc *vl-1-bit-flop*
  :parents (primitives)
  :short "Primitive edge-triggered register."
  :long "<p>The Verilog meaning of this module is:</p>

<code>
module VL_1_BIT_FLOP (q, clk, d) ;
  output reg q;
  input clk;
  input d;

  always @@(posedge clk)
     q &lt;= d;

endmodule
</code>

<p>VL takes this as a primitive.  The @(see flop-inference) transform converts
certain <tt>always</tt> statements into instances of this module.</p>")

(defconsts *vl-1-bit-flop*
  (b* ((name "VL_1_BIT_FLOP")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))

       ((mv q-expr   q-port   q-portdecl   &)           (vl-occform-mkport "q"   :vl-output 1))
       ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input  1))
       ((mv d-expr   d-port   d-portdecl   d-netdecl)   (vl-occform-mkport "d"   :vl-input  1))

       (q-regdecl    (make-vl-regdecl :name "q" :loc *vl-fakeloc*))

       ;; always @(posedge clk) q <= d;
       (q<=d         (make-vl-assignstmt :type :vl-nonblocking :lvalue q-expr :expr d-expr :loc *vl-fakeloc*))
       (posedge-clk  (make-vl-evatom :type :vl-posedge :expr clk-expr))
       (@posedge-clk (make-vl-eventcontrol :starp nil :atoms (list posedge-clk)))
       (stmt         (make-vl-timingstmt :ctrl @posedge-clk :body q<=d))
       (always       (make-vl-always :stmt stmt :loc *vl-fakeloc*)))

    (make-honsed-vl-module :name      name
                           :origname  name
                           :atts      atts
                           :ports     (list q-port      clk-port     d-port)
                           :portdecls (list q-portdecl  clk-portdecl d-portdecl)
                           :netdecls  (list             clk-netdecl  d-netdecl)
                           :regdecls  (list q-regdecl)
                           :alwayses  (list always)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)))


(defxdoc *vl-1-bit-latch*
  :parents (primitives)
  :short "Primitive level-sensitive latch."
  :long "<p>The Verilog meaning of this module is:</p>

<code>
module VL_1_BIT_LATCH (q, clk, d);
   output reg q;
   input clk;
   input d;

   always @@(d or clk)
     q &lt;= clk ? d : q;

endmodule
</code>

<p>VL takes this as a primitive.  The @(see latch-inference) transform converts
certain <tt>always</tt> statements into instances of this module.</p>")

(defconsts *vl-1-bit-latch*
  (b* ((name (hons-copy "VL_1_BIT_LATCH"))
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))

       ((mv q-expr   q-port   q-portdecl   &)           (vl-occform-mkport "q"   :vl-output 1))
       ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input  1))
       ((mv d-expr   d-port   d-portdecl   d-netdecl)   (vl-occform-mkport "d"   :vl-input  1))

       (q-regdecl     (make-vl-regdecl :name "q" :loc *vl-fakeloc*))

       ;; always @(d or clk) q <= clk ? d : q;
       (|clk?d:q|     (make-vl-nonatom :op :vl-qmark
                                       :args (list clk-expr d-expr q-expr)
                                       :finalwidth 1
                                       :finaltype :vl-unsigned))
       (|q<=clk?d:q|  (make-vl-assignstmt :type :vl-nonblocking
                                          :lvalue q-expr
                                          :expr |clk?d:q|
                                          :loc *vl-fakeloc*))
       (d-evatom      (make-vl-evatom :type :vl-noedge :expr d-expr))
       (clk-evatom    (make-vl-evatom :type :vl-noedge :expr clk-expr))
       (@d-or-clk     (make-vl-eventcontrol :starp nil :atoms (list d-evatom clk-evatom)))
       (stmt          (make-vl-timingstmt :ctrl @d-or-clk :body |q<=clk?d:q|))
       (always        (make-vl-always :stmt stmt :loc *vl-fakeloc*)))

    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list q-port     clk-port     d-port)
                           :portdecls (list q-portdecl clk-portdecl d-portdecl)
                           :netdecls  (list            clk-netdecl  d-netdecl)
                           :regdecls  (list q-regdecl)
                           :alwayses  (list always)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))





;; (include-book "../mlib/writer")
;; (vl-pps-module *vl-1-bit-x*)
;; (vl-pps-module *vl-1-bit-z*)
;; (vl-pps-module *vl-1-bit-assign*)
;; (vl-pps-module *vl-1-bit-delay-1*)
;; (vl-pps-module *vl-1-bit-buf*)
;; (vl-pps-module *vl-1-bit-not*)
;; (vl-pps-module *vl-1-bit-and*)
;; (vl-pps-module *vl-1-bit-or*)
;; (vl-pps-module *vl-1-bit-xor*)
;; (vl-pps-module *vl-1-bit-nand*)
;; (vl-pps-module *vl-1-bit-nor*)
;; (vl-pps-module *vl-1-bit-xnor*)
;; (vl-pps-module *vl-1-bit-zmux*)
;; (vl-pps-module *vl-1-bit-flop*)
;; (vl-pps-module *vl-1-bit-latch*)

