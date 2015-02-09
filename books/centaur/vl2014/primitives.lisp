; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
(include-book "mlib/expr-building")
(include-book "../esim/esim-primitives")
(local (include-book "mlib/stmt-tools"))
(local (std::add-default-post-define-hook :fix))

(defxdoc primitives
  :parents (vl2014)
  :short "The primitive modules targetted by VL."

  :long "<p>The modules here can sort of be thought of as the target language
for VL's simplification scheme.  That is, the sequence of @(see transforms)
applied by @(see vl-simplify) tries to convert rich Verilog modules that
include expressions, gates, parameters, etc., into simple, hierarchical modules
that do nothing more than instantiate other modules, with these primitive
modules at the tips.</p>

<p>This set of primitives modules could be simplified.  For instance we could
rewrite all of the basic gate modules into @('nand') or some other basic form.
We haven't done this yet, under the (probably misguided) theory that having a
richer set of primitives might somehow be more efficient for our symbolic
simulator.</p>

<p>Note that the list below is somewhat <b>incomplete</b>.  For instance, in
the final @(see e-conversion) step, we can generate \"resolution\" modules for
resolving multiple drivers.  These resolution modules are essentially
primitives.  But there isn't a fixed set of resolution primitives, instead we
generate the primitives we need on the fly; see @(see
vl-make-n-bit-res-module), for instance.</p>

<p>Similarly, historically VL had a single @('VL_1_BIT_FLOP') primitive, but
when we added support for @('always') blocks with multiple edge triggers, we
did away with this.  Instead, VL can now generate many kinds of primitive
flops, each with a supporting E module.  See, e.g., @(see
vl-make-1-bit-n-edge-flop).</p>")

(local (xdoc::set-default-parents primitives))

(define vl-primitive-mkport
  :short "Convenient way to generate a port for a primitive."
  ((name stringp)
   (dir  vl-direction-p))
  :verbosep t
  :returns (mv (expr     vl-expr-p)
               (port     vl-port-p)
               (portdecl vl-portdecl-p)
               (vardecl  vl-vardecl-p))
  :long "<p>This is like @(see vl-occform-mkport), but our primitives are all
one-bit things so we leave out the ranges to make them prettier.</p>"

  (b* ((name     (hons-copy (string-fix name)))
       (expr     (vl-idexpr name 1 :vl-unsigned))
       (port     (make-vl-regularport     :name name :expr expr :loc *vl-fakeloc*))
       (portdecl (make-vl-portdecl :name name :type *vl-plain-old-wire-type* :dir dir :loc *vl-fakeloc*))
       (vardecl  (make-vl-vardecl  :name name :type *vl-plain-old-wire-type*
                                   :nettype :vl-wire :loc *vl-fakeloc* :atts '(("VL_PORT_IMPLICIT")))))
    (mv expr port portdecl vardecl)))

(define vl-primitive-mkwire
  :short "Convenient way to generate an internal wire for a primitive."
  ((name stringp))
  :returns (mv (expr    vl-expr-p)
               (vardecl vl-vardecl-p))
  :long "<p>This is similar to @(see vl-occform-mkwire), but our primitives are
all one-bit things so we leave out the ranges to make them prettier.</p>"
  (b* ((name     (hons-copy (string-fix name)))
       (expr     (vl-idexpr name 1 :vl-unsigned))
       (vardecl  (make-vl-vardecl :name name :type *vl-plain-old-wire-type*
                                  :nettype :vl-wire :loc *vl-fakeloc*)))
    (mv expr vardecl)))

(defval *vl-1-bit-t*
  :short "Primitive 1 (true) generator."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_T (out) ;
  output out;
  assign out = 1'b1;
endmodule
})

<p>VL takes this as a primitive.  BOZO this module is currently unused but
we are going to start using it soon.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-t*).</p>"

  (b* ((name "VL_1_BIT_T")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'b1*| :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :assigns   (list out-assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-t*))))

(defval *vl-1-bit-f*
  :short "Primitive 0 (false) generator."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_F (out) ;
  output out;
  assign out = 1'b0;
endmodule
})

<p>VL takes this as a primitive.  BOZO this module is currently unused but
we are going to start using it soon.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-f*).</p>"

  (b* ((name "VL_1_BIT_F")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'b0*| :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :assigns   (list out-assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-f*))))

(defval *vl-1-bit-x*
  :short "Primitive X (unknown) generator."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_X (out) ;
  output out;
  assign out = 1'bx;
endmodule
})

<p>VL takes this as a primitive.  This module is mainly used by @(see
weirdint-elim) to eliminate explicit X values from literals.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-x*).</p>"

  (b* ((name "VL_1_BIT_X")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'bx*| :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :assigns   (list out-assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-x*))))

(defval *vl-1-bit-z*
  :short "Primitive Z (floating) generator."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_Z (out) ;
  output out;
  assign out = 1'bz;
endmodule
})

<p>VL takes this as a primitive.  This module is mainly used by @(see
weirdint-elim) to eliminate explicit Z values from literals.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-z*).</p>"

  (b* ((name "VL_1_BIT_Z")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (out-assign (make-vl-assign :lvalue out-expr :expr |*sized-1'bz*| :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :assigns   (list out-assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-z*))))

(defval *vl-1-bit-power*
  :short "Primitive power source or @('supply1') signal."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_POWER (out) ;
  output out;
  supply1 out;
endmodule
})

<p>VL takes this as a primitive.  This module is typically introduced by the
@(see elim-supplies) transform to replace @('supply1') wires.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-t*).  This is
also how esim treats @(see *vl-1-bit-t*), i.e., in esim there is no difference
between a power source and an ordinary constant @('1'b1') value.  We have a
separate primitive mainly so that other backends with more transistor-level
support can implement them in other ways.</p>"

  (b* ((name "VL_1_BIT_POWER")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv ?out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (nettype      :vl-supply1)
       (out-portdecl (change-vl-portdecl out-portdecl :nettype nettype))
       (out-vardecl  (change-vl-vardecl  out-vardecl  :nettype nettype)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-t*))))

(defval *vl-1-bit-ground*
  :short "Primitive ground or @('supply0') signal."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_GROUND (out) ;
  output out;
  supply0 out;
endmodule
})

<p>VL takes this as a primitive.  This module is typically introduced by the
@(see elim-supplies) transform to replace @('supply0') wires.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-f*).  This is
also how esim treats @(see *vl-1-bit-f*), i.e., in esim there is no difference
between ground and an ordinary constant @('1'b0') value.  We have a separate
primitive mainly so that other backends with more transistor-level support can
implement them in other ways.</p>"

  (b* ((name "VL_1_BIT_GROUND")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv ?out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       (nettype      :vl-supply0)
       (out-portdecl (change-vl-portdecl out-portdecl :nettype nettype))
       (out-vardecl  (change-vl-vardecl  out-vardecl  :nettype nettype)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-f*))))

(defval *vl-1-bit-assign*
  :short "Primitive assignment module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_ASSIGN (out, in) ;
  output out;
  input in;
  assign out = in;
endmodule
})

<p>VL takes this as a primitive.  This module is also the basis for wider
assignment modules; see @(see vl-make-n-bit-assign).</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-id*).</p>

<p>Something subtle is that there is probably no way to implement
@('VL_1_BIT_ASSIGN') in hardware.  One obvious approach would be to use a
buffer, but then @('out') would be X when @('in') is Z.  Another approach would
be to just wire together out and in, but then other assignments to @('out')
would also affect @('in'), and in Verilog this isn't the case.</p>

<p>Originally our @(see occform) transformation tried to use buffers for
assignments since this seemed to be more conservative.  But these extra buffers
seemed to often be inappropriate, especially when dealing with lower level
modules that involve transistors.</p>"

  (b* ((name "VL_1_BIT_ASSIGN")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-primitive-mkport "in"  :vl-input))
       (assign (make-vl-assign :lvalue out-expr :expr in-expr :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     in-port)
                     :portdecls (list out-portdecl in-portdecl)
                     :vardecls  (list out-vardecl  in-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-id*))))

(defval *vl-1-bit-delay-1*
  :short "Primitive assignment with delay."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_DELAY_1 (out, in) ;
  output out;
  input in;
  assign #1 out = in;
endmodule
})

<p>VL takes this as a primitive.  It is used by our @(see delayredux) transform
to separate delays from assignment statements.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-del*), but note
that esim really has no notion of delays and this ends up being equivalent to
an ordinary @(see *vl-1-bit-assign*).</p>"

  (b* ((name "VL_1_BIT_DELAY_1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-primitive-mkport "in"  :vl-input))
       (one    (vl-make-index 1))
       (delay  (make-vl-gatedelay :rise one :fall one :high one))
       (assign (make-vl-assign :lvalue out-expr :expr in-expr :delay delay :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     in-port)
                     :portdecls (list out-portdecl in-portdecl)
                     :vardecls  (list out-vardecl  in-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-del*))))

(defval *vl-1-bit-buf*
  :short "Primitive buffer module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_BUF (out, in) ;
  output out;
  input in;
  assign out = |in;
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('buf') gates, but
probably not for much else since ordinary assignments are handled with @(see
*vl-1-bit-assign*), instead.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-buf*).</p>

<p>We once tried to implement this primitive using @('out = ~ (~in)'), but
found that NCVerilog (incorrectly) canceled the double negation and could hence
produce Z bits on the output.  The or-based definition above does not appear to
have this problem.</p>"

  (b* ((name "VL_1_BIT_BUF")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-primitive-mkport "in"  :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-unary-bitor
                                      :args (list in-expr)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     in-port)
                     :portdecls (list out-portdecl in-portdecl)
                     :vardecls  (list out-vardecl  in-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-buf*))))

(defval *vl-1-bit-not*
  :short "Primitive not-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_NOT (out, in) ;
  output out;
  input in;
  assign out = ~in;
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('not') gates and
@('~') operators, and also in many modules we generate for other operators like
@('+').</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-not*).</p>"

  (b* ((name "VL_1_BIT_NOT")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-primitive-mkport "in"  :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-unary-bitnot
                                      :args (list in-expr)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port in-port)
                     :portdecls (list out-portdecl in-portdecl)
                     :vardecls  (list out-vardecl in-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-not*))))

(defval *vl-1-bit-and*
  :short "Primitive and-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_AND (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = a & b;
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('and') gates and
@('&') operators, and also in many modules we generate for other operators like
@('+').</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-and*)</p>"

  (b* ((name "VL_1_BIT_AND")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-binary-bitand
                                      :args (list a-expr b-expr)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-and*))))

(defval *vl-1-bit-or*
  :short "Primitive or-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_OR (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = a | b;
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('or') gates and
@('|') operators, and also in many modules we generate for other operators like
@('+').</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-or*)</p>"

  (b* ((name "VL_1_BIT_OR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-binary-bitor
                                      :args (list a-expr b-expr)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-or*))))

(defval *vl-1-bit-xor*
  :short "Primitive xor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_XOR (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = a ^ b;
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('xor') gates and
@('^') operators, and also in many modules we generate for other operators like
@('+').</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-xor*)</p>"

  (b* ((name "VL_1_BIT_XOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-binary-xor
                                      :args (list a-expr b-expr)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-xor*))))

(defval *vl-1-bit-nand*
  :short "Primitive nand-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_NAND (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = ~(a & b);
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('nand') gates but
probably not much else.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-nand*)</p>"

  (b* ((name "VL_1_BIT_NAND")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-unary-bitnot
                                      :args (list (make-vl-nonatom
                                                   :op :vl-binary-bitand
                                                   :args (list a-expr b-expr)
                                                   :finalwidth 1
                                                   :finaltype :vl-unsigned))
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-nand*))))

(defval *vl-1-bit-nor*
  :short "Primitive nor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_NOR (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = ~(a | b);
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('nor') gates, but
probably not much else.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-nor*)</p>"

  (b* ((name "VL_1_BIT_NOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-unary-bitnot
                                      :args (list (make-vl-nonatom
                                                   :op :vl-binary-bitor
                                                   :args (list a-expr b-expr)
                                                   :finalwidth 1
                                                   :finaltype :vl-unsigned))
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-nor*))))

(defval *vl-1-bit-xnor*
  :short "Primitive xnor-gate module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_XNOR (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = ~(a ^ b);
endmodule
})

<p>VL takes this as a primitive.  We use this in place of @('xnor') gates, but
probably not much else.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-xnor*)</p>"

  ;; BOZO this should probably be a non-primitive.
  (b* ((name "VL_1_BIT_XNOR")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-unary-bitnot
                                      :args (list (make-vl-nonatom
                                                   :op :vl-binary-xor
                                                   :args (list a-expr b-expr)
                                                   :finalwidth 1
                                                   :finaltype :vl-unsigned))
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-xnor*))))

(defval *vl-1-bit-approx-mux*
  :short "Primitive 1-bit (more conservative) multiplexor module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_APPROX_MUX (out, sel, a, b) ;
  output out;
  input sel;
  input a;
  input b;
  assign out = sel ? a : b;
endmodule
})

<p>VL takes this as a primitive, and we use it to implement @('?:')
expressions.  The corresponding @(see esim) primitive is @(see
acl2::*esim-safe-mux*).</p>

<p>The esim semantics are a <b>conservative, inexact approximation</b> of the
Verilog semantics, for two reasons.</p>

<h3>1. Z Input Handling</h3>

<p>In Verilog, the expression @('sel ? a : b') produces a @('Z') value when the
selected input is @('Z').  But our corresponding esim primitive produces X in
this case.</p>

<p>Occasionally, @('?:') operators with @('Z') inputs are used in Verilog
designs to model efficient muxes, based on tri-state buffers, where the selects
are expected to be one-hot.  For instance:</p>

@({
    assign out = sel1 ? data1 : 1'bz;
    assign out = sel2 ? data2 : 1'bz;
    assign out = sel3 ? data3 : 1'bz;
})

<p>Such a circuit could not be modeled correctly using approx-muxes; the esim
semantics would always produce an X on the output.  To avoid this, VL tries to
recognize @('?:') operators that literally are of the form @('a ?  b : Z'),
using a simple kind of pattern-matching, and in these cases it uses a different
primitive, @(see *vl-1-bit-zmux*), instead of approx muxes.</p>

<p>But in general, the Verilog semantics do not really correspond to any kind
of hardware that you would implement.  For instance, an AND/OR style mux would
always drive its output, regardless of whether its inputs were driven.  So the
ESIM semantics, which treat the output as X instead of Z in this case, are
arguably more realistic and safer than the Verilog semantics.</p>

<h3>2. X Select Handling</h3>

<p>In Verilog, when @('sel') evaluates to X or Z, the expression @('sel ? a :
b') may still produce a good 1 or 0 value when both data inputs @('a') and
@('b') share this value.</p>

<p>For certain kinds of mux implementations, this seems overly optimistic, and
our esim semantics for an approx mux is that whenever @('sel') is X, we output
is X, even if the inputs agree.  For more discussion about this issue and the
tradeoffs involved, see @(see acl2::4v-ite).</p>

<p>For special cases where this approximation is not acceptable, VL implements
a special @('VL_X_SELECT') that can be used to override this behavior.  @('?:')
operators that are annotated with this attribute will be implemented in a less
conservative way, as @(see *vl-1-bit-mux*) primitives.  See @(see
vl-mux-occform) for more information.</p>"

  (b* ((name "VL_1_BIT_APPROX_MUX")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv sel-expr sel-port sel-portdecl sel-vardecl) (vl-primitive-mkport "sel" :vl-input))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr   (make-vl-nonatom :op :vl-qmark
                                                        :args (list sel-expr a-expr b-expr)
                                                        :finalwidth 1
                                                        :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     sel-port     a-port     b-port)
                     :portdecls (list out-portdecl sel-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  sel-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-safe-mux*))))

(defval *vl-1-bit-mux*
  :short "Primitive 1-bit (less conservative) multiplexor module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_MUX (out, sel, a, b) ;
  output out;
  input sel;
  input a;
  input b;
  assign out = sel ? a : b;
endmodule
})

<p>VL takes this as a primitive.  The corresponding @(see esim) primitive is
@(see acl2::*esim-unsafe-mux*).</p>

<p>Ordinarily, VL <b>will not use this module</b>.  Instead, @('?:') operators
will be implemented using either @(see *vl-1-bit-approx-mux*) or @(see
*vl-1-bit-zmux*) modules.</p>

<p>The only reason we have this module at all is that, occasionally, you may
find that an approx mux is too conservative.  If this causes you problems, you
may instruct VL to instead produce a less-conservative @('*vl-1-bit-mux*') by
adding a @('VL_X_SELECT') attribute; see @(see vl-mux-occform) for more
information.</p>

<p>In the ESIM semantics, a @('*vl-1-bit-mux*') is identical to a
@('*vl-1-bit-approx-mux*') except in the cases where the select is unknown (X
or Z) and the data inputs agree on some good, Boolean value.  For instance:</p>

<ul>
<li> X ? 1 : 1 </li>
<li> X ? 0 : 0 </li>
</ul>

<p>In these cases, an approx-mux produces @('X'), whereas a non-approx mux will
produce the shared value of the data inputs.</p>

<p>This less-conservative behavior may not necessarily be a realistic model of
how some physical muxes will operate, and may lead to somewhat slower symbolic
simulation performance in certain cases.  For additional discussion of these
issues, see @(see *vl-1-bit-approx-mux*) and @(see acl2::4v-ite).</p>

<p>Note that, like an approx-mux, a @('vl-1-bit-mux') still produces X when the
selected data input is Z.</p>"

  (b* ((name "VL_1_BIT_MUX")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv sel-expr sel-port sel-portdecl sel-vardecl) (vl-primitive-mkport "sel" :vl-input))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr   (make-vl-nonatom :op :vl-qmark
                                                        :args (list sel-expr a-expr b-expr)
                                                        :finalwidth 1
                                                        :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     sel-port     a-port     b-port)
                     :portdecls (list out-portdecl sel-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  sel-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-unsafe-mux*))))

(defval *vl-1-bit-zmux*
  :short "Primitive tri-state buffer module."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_ZMUX (out, sel, a);
  output out;
  input sel;
  input a;
  assign out = sel ? a : 1'bZ;
endmodule
})

<p>VL takes this as a primitive.  It is used in @(see vl-mux-occform) as the
basis for conditional expressions with @('Z') branches that are typically used
to implement muxes.</p>

<p>Verilog truth table:</p>

@({
  sel    a    |   out         sel    a        out
 -------------+---------     -------------+-----------
   0     0    |    z           x     0    |    x
   0     1    |    z           x     1    |    x
   0     x    |    z           x     x    |    x
   0     z    |    z           x     z    |    x
   1     0    |    0           z     0    |    x
   1     1    |    1           z     1    |    x
   1     x    |    x           z     x    |    x
   1     z    |    z           z     z    |    x
})

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-tri*), which
drives its output to @('(tristate sel a)'); see @(see acl2::4v-tristate).  This
matches the Verilog truth table exactly.</p>"

  (b* ((name "VL_1_BIT_ZMUX")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv sel-expr sel-port sel-portdecl sel-vardecl) (vl-primitive-mkport "sel" :vl-input))
       ((mv a-expr a-port a-portdecl a-vardecl)         (vl-primitive-mkport "a" :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom :op :vl-qmark
                                                      :args (list sel-expr a-expr |*sized-1'bz*|)
                                                      :finalwidth 1
                                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :ports     (list out-port     sel-port     a-port)
                     :portdecls (list out-portdecl sel-portdecl a-portdecl)
                     :vardecls  (list out-vardecl  sel-vardecl  a-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :origname  name
                     :esim      acl2::*esim-tri*))))

(defval *vl-1-bit-ceq*
  :short "Primitive @('===') module."
  :long "<p>The Verilog definition of this module is:</p>

@({
module VL_1_BIT_CEQ (out, a, b) ;
  output out;
  input a;
  input b;
  assign out = (a === b);
endmodule
})

<p>VL takes this as a primitive, and uses it to implement @('===') and @('!==')
operators.</p>

<p>These operators are inherently unsound because they do not treat @('X') as
an unknown.  For our back-end tools, we usually conservatively approximate
@('VL_1_BIT_CEQ') with an @('xnor') gate.  But a less conservative tool might
choose to give it a different interpretation.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-ceq*), which is
just an @('xnor') gate.</p>"

  (b* ((name "VL_1_BIT_CEQ")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
       ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom :op :vl-binary-ceq
                                                      :args (list a-expr b-expr)
                                                      :finalwidth 1
                                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     a-port     b-port)
                     :portdecls (list out-portdecl a-portdecl b-portdecl)
                     :vardecls  (list out-vardecl  a-vardecl  b-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-ceq*))))

(defval *vl-1-bit-latch*
  :short "Primitive level-sensitive latch."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_LATCH (q, clk, d);
   output q;
   input clk;
   input d;
   reg q;

   always @@(d or clk)
     q <= clk ? d : q;

endmodule
})

<p>VL takes this as a primitive.  The @(see always-top) transform converts
certain @('always') statements into instances of this module.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-latch*).</p>"

  (b* ((name (hons-copy "VL_1_BIT_LATCH"))
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))

       ((mv q-expr   q-port   q-portdecl   q-vardecl)   (vl-primitive-mkport "q"   :vl-output))
       ((mv clk-expr clk-port clk-portdecl clk-vardecl) (vl-primitive-mkport "clk" :vl-input))
       ((mv d-expr   d-port   d-portdecl   d-vardecl)   (vl-primitive-mkport "d"   :vl-input))

       (q-portdecl (change-vl-portdecl q-portdecl :type *vl-plain-old-reg-type*))
       (q-vardecl  (change-vl-vardecl  q-vardecl  :type *vl-plain-old-reg-type*))

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
       (always        (make-vl-always :type :vl-always
                                      :stmt stmt
                                      :loc *vl-fakeloc*)))

    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list q-port     clk-port     d-port)
                     :portdecls (list q-portdecl clk-portdecl d-portdecl)
                     :vardecls  (list q-vardecl  clk-vardecl  d-vardecl)
                     :alwayses  (list always)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-latch*))))

(defval *vl-1-bit-bufif0*
  :short "Primitive conditional driver."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_BUFIF0 (out, data, ctrl);
   output out;
   input data;
   input ctrl;
   assign out = ctrl ? 1'bz : |data;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('bufif0') gates into instances of this module.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-bufif0*).</p>

<p>We once tried to implement this primitive using @('~~data') instead of
@('|data'), but we found that NCVerilog (incorrectly) canceled the double
negation and could hence produce Z bits on the output.  The or-based definition
above does not appear to have this problem.</p>"

  (b* ((name "VL_1_BIT_BUFIF0")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))

       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-qmark
                                      :args (list ctrl-expr
                                                  |*sized-1'bz*|
                                                  (make-vl-nonatom :op :vl-unary-bitor
                                                                   :args (list data-expr)
                                                                   :finalwidth 1
                                                                   :finaltype :vl-unsigned))
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-bufif0*))))

(defval *vl-1-bit-bufif1*
  :short "Primitive conditional driver."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_BUFIF1 (out, data, ctrl);
   output out;
   input data;
   input ctrl;
   assign out = ctrl ? ~~data : 1'bz;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('bufif1') gates into instances of this module.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-bufif1*).</p>

<p>We once tried to implement this primitive using @('~~data') instead of
@('|data'), but we found that NCVerilog (incorrectly) canceled the double
negation and could hence produce Z bits on the output.  The or-based definition
above does not appear to have this problem.</p>"

  (b* ((name "VL_1_BIT_BUFIF1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-qmark
                                      :args (list ctrl-expr
                                                  (make-vl-nonatom :op :vl-unary-bitor
                                                                   :args (list data-expr)
                                                                   :finalwidth 1
                                                                   :finaltype :vl-unsigned)
                                                  |*sized-1'bz*|)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-bufif1*))))

(defval *vl-1-bit-notif0*
  :short "Primitive conditional driver."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_NOTIF0 (out, data, ctrl);
   output out;
   input data;
   input ctrl;
   assign out = ctrl ? 1'bz : ~data;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('notif0') gates into instances of this module.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-notif0*).</p>"

  (b* ((name "VL_1_BIT_NOTIF0")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-qmark
                                      :args (list ctrl-expr
                                                  |*sized-1'bz*|
                                                  (make-vl-nonatom
                                                                :op :vl-unary-bitnot
                                                                :args (list data-expr)
                                                                :finalwidth 1
                                                                :finaltype :vl-unsigned))
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-notif0*))))

(defval *vl-1-bit-notif1*
  :short "Primitive conditional driver."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_NOTIF1 (out, data, ctrl);
   output out;
   input data;
   input ctrl;
   assign out = ctrl ? ~data : 1'bz;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('notif1') gates into instances of this module.</p>

<p>The corresponding @(see esim) primitive is @(see acl2::*esim-notif1*).</p>"

  (b* ((name "VL_1_BIT_NOTIF1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (assign (make-vl-assign :lvalue out-expr
                               :expr (make-vl-nonatom
                                      :op :vl-qmark
                                      :args (list ctrl-expr
                                                  (make-vl-nonatom
                                                                :op :vl-unary-bitnot
                                                                :args (list data-expr)
                                                                :finalwidth 1
                                                                :finaltype :vl-unsigned)
                                                  |*sized-1'bz*|)
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :assigns   (list assign)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-notif1*))))

(defval *vl-1-bit-nmos*
  :short "Primitive nmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_NMOS (out, data, ctrl);
  output out ;
  input data ;
  input ctrl ;
  nmos gate (out, data, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('nmos') gates into instances of this module.</p>

<p>ESIM has very little support for transistors, but this may be a useful
target for other back-end tools.  The corresponding @(see esim) primitive is
@(see acl2::*esim-nmos*).</p>"

  (b* ((name "VL_1_BIT_NMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-nmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr ctrl-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-nmos*))))

(defval *vl-1-bit-rnmos*
  :short "Primitive resistive nmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RNMOS (out, data, ctrl);
  output out ;
  input data ;
  input ctrl ;
  rnmos gate (out, data, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rnmos') gates into instances of this module.</p>

<p>ESIM has no notion of strengths and very little support for transistors, but
this may be a convenient target for other back-end tools.  The corresponding
@(see esim) primitive is @(see acl2::*esim-nmos*).</p>"

  (b* ((name "VL_1_BIT_RNMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-rnmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr ctrl-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-nmos*))))


(defval *vl-1-bit-pmos*
  :short "Primitive pmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_PMOS (out, data, ctrl);
  output out ;
  input data ;
  input ctrl ;
  pmos gate (out, data, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('pmos') gates into instances of this module.</p>

<p>ESIM has very little support for transistors, but this may be a useful
target for other back-end tools.  The corresponding @(see esim) primitive is
@(see acl2::*esim-pmos*).</p>"

  (b* ((name "VL_1_BIT_PMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-pmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr ctrl-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-pmos*))))

(defval *vl-1-bit-rpmos*
  :short "Primitive resistive pmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RPMOS (out, data, ctrl);
  output out ;
  input data ;
  input ctrl ;
  rpmos gate (out, data, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rpmos') gates into instances of this module.</p>

<p>ESIM has no notion of strengths and very little support for transistors, but
this may be a convenient target for other back-end tools.  The corresponding
@(see esim) primitive is @(see acl2::*esim-nmos*).</p>"

  (b* ((name "VL_1_BIT_RPMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"   :vl-input))
       ((mv ctrl-expr   ctrl-port   ctrl-portdecl   ctrl-vardecl)   (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-rpmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr   :dir :vl-input)
                                           (make-vl-plainarg :expr ctrl-expr   :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     ctrl-port)
                     :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-pmos*))))

(defval *vl-1-bit-cmos*
  :short "Primitive cmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_CMOS (out, data, nctrl, pctrl);
  output out ;
  input data ;
  input nctrl ;
  input pctrl ;
  cmos gate (out, data, nctrl, pctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('cmos') gates into instances of this module.</p>

<p>ESIM has very little support for transistors, but this may be a useful
target for other back-end tools.  The corresponding @(see esim) primitive is
@(see acl2::*esim-cmos*).</p>"

  (b* ((name "VL_1_BIT_CMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr    out-port    out-portdecl    out-vardecl)    (vl-primitive-mkport "out"   :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"  :vl-input))
       ((mv nctrl-expr  nctrl-port  nctrl-portdecl  nctrl-vardecl)  (vl-primitive-mkport "nctrl" :vl-input))
       ((mv pctrl-expr  pctrl-port  pctrl-portdecl  pctrl-vardecl)  (vl-primitive-mkport "pctrl" :vl-input))
       (gate (make-vl-gateinst :type :vl-cmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr   :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr  :dir :vl-input)
                                           (make-vl-plainarg :expr nctrl-expr :dir :vl-input)
                                           (make-vl-plainarg :expr pctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     nctrl-port     pctrl-port)
                     :portdecls (list out-portdecl data-portdecl nctrl-portdecl pctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  nctrl-vardecl  pctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-cmos*))))

(defval *vl-1-bit-rcmos*
  :short "Primitive resistive cmos transistor."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RCMOS (out, data, nctrl, pctrl);
  output out ;
  input data ;
  input nctrl ;
  input pctrl ;
  rcmos gate (out, data, nctrl, pctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rcmos') gates into instances of this module.</p>

<p>ESIM has no notion of strengths and very little support for transistors, but
this may be a convenient target for other back-end tools.  The corresponding
@(see esim) primitive is @(see acl2::*esim-cmos*).</p>"

  (b* ((name "VL_1_BIT_RCMOS")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr    out-port    out-portdecl    out-vardecl)    (vl-primitive-mkport "out"   :vl-output))
       ((mv data-expr   data-port   data-portdecl   data-vardecl)   (vl-primitive-mkport "data"  :vl-input))
       ((mv nctrl-expr  nctrl-port  nctrl-portdecl  nctrl-vardecl)  (vl-primitive-mkport "nctrl" :vl-input))
       ((mv pctrl-expr  pctrl-port  pctrl-portdecl  pctrl-vardecl)  (vl-primitive-mkport "pctrl" :vl-input))
       (gate (make-vl-gateinst :type :vl-rcmos
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr   :dir :vl-output)
                                           (make-vl-plainarg :expr data-expr  :dir :vl-input)
                                           (make-vl-plainarg :expr nctrl-expr :dir :vl-input)
                                           (make-vl-plainarg :expr pctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port     data-port     nctrl-port     pctrl-port)
                     :portdecls (list out-portdecl data-portdecl nctrl-portdecl pctrl-portdecl)
                     :vardecls  (list out-vardecl  data-vardecl  nctrl-vardecl  pctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      acl2::*esim-cmos*))))

(defval *vl-1-bit-tran*
  :short "Primitive bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_TRAN (a, b);
  inout a ;
  inout b ;
  tran gate (a, b) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('tran') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_TRAN")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       (gate (make-vl-gateinst :type :vl-tran
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr  :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr  :dir :vl-inout))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port)
                     :portdecls (list a-portdecl b-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-rtran*
  :short "Primitive, resistive bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RTRAN (a, b);
  inout a ;
  inout b ;
  rtran gate (a, b) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rtran') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_RTRAN")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       (gate (make-vl-gateinst :type :vl-rtran
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr  :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr  :dir :vl-inout))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port)
                     :portdecls (list a-portdecl b-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil   ;; no e equivalent
                     ))))

(defval *vl-1-bit-tranif0*
  :short "Primitive, conditional bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_TRANIF0 (a, b, ctrl);
  inout a ;
  inout b ;
  input ctrl ;
  tranif0 gate (a, b, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('tranif0') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_TRANIF0")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-vardecl) (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-tranif0
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr ctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port     ctrl-port)
                     :portdecls (list a-portdecl b-portdecl ctrl-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-rtranif0*
  :short "Primitive, resistive, conditional bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RTRANIF0 (a, b, ctrl);
  inout a ;
  inout b ;
  input ctrl ;
  rtranif0 gate (a, b, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rtranif0') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_RTRANIF0")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-vardecl) (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-rtranif0
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr ctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port     ctrl-port)
                     :portdecls (list a-portdecl b-portdecl ctrl-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-tranif1*
  :short "Primitive, conditional bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_TRANIF1 (a, b, ctrl);
  inout a ;
  inout b ;
  input ctrl ;
  tranif1 gate (a, b, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('tranif1') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_TRANIF1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-vardecl) (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-tranif1
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr ctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port     ctrl-port)
                     :portdecls (list a-portdecl b-portdecl ctrl-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-rtranif1*
  :short "Primitive, resistive, conditional bidirectional connection."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_RTRANIF1 (a, b, ctrl);
  inout a ;
  inout b ;
  input ctrl ;
  rtranif1 gate (a, b, ctrl) ;
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('rtranif1') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_RTRANIF1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv a-expr    a-port    a-portdecl    a-vardecl)    (vl-primitive-mkport "a"   :vl-inout))
       ((mv b-expr    b-port    b-portdecl    b-vardecl)    (vl-primitive-mkport "b"   :vl-inout))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-vardecl) (vl-primitive-mkport "ctrl"   :vl-input))
       (gate (make-vl-gateinst :type :vl-rtranif1
                               :name "gate"
                               :args (list (make-vl-plainarg :expr a-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr b-expr    :dir :vl-inout)
                                           (make-vl-plainarg :expr ctrl-expr :dir :vl-input))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list a-port     b-port     ctrl-port)
                     :portdecls (list a-portdecl b-portdecl ctrl-portdecl)
                     :vardecls  (list a-vardecl  b-vardecl  ctrl-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-pullup*
  :short "Primitive pullup element."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_PULLUP (a, b, ctrl);
  output out;
  pullup gate (out);
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('pullup') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_PULLUP")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr    out-port    out-portdecl    out-vardecl)    (vl-primitive-mkport "out"   :vl-output))
       (gate (make-vl-gateinst :type :vl-pullup
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr    :dir :vl-output))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defval *vl-1-bit-pulldown*
  :short "Primitive pulldown element."
  :long "<p>The Verilog meaning of this module is:</p>

@({
module VL_1_BIT_PULLDOWN (a, b, ctrl);
  output out;
  pulldown gate (out);
endmodule
})

<p>VL takes this as a primitive.  The @(see gate-elim) transform converts
certain @('pulldown') gates into instances of this module.</p>

<p>There is no sensible way to model this in ESIM and hence there is no ESIM
equivalent.  However, this module may be a convenient target for other back-end
tools.</p>"

  (b* ((name "VL_1_BIT_PULLDOWN")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr    out-port    out-portdecl    out-vardecl)    (vl-primitive-mkport "out"   :vl-output))
       (gate (make-vl-gateinst :type :vl-pulldown
                               :name "gate"
                               :args (list (make-vl-plainarg :expr out-expr    :dir :vl-output))
                               :loc *vl-fakeloc*)))
    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port)
                     :portdecls (list out-portdecl)
                     :vardecls  (list out-vardecl)
                     :gateinsts (list gate)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*
                     :atts      atts
                     :esim      nil ;; no e equivalent
                     ))))

(defconst *vl-primitive-mods*
  (list *vl-1-bit-t*
        *vl-1-bit-f*
        *vl-1-bit-x*
        *vl-1-bit-z*
        *vl-1-bit-power*
        *vl-1-bit-ground*
        *vl-1-bit-assign*
        *vl-1-bit-delay-1*
        *vl-1-bit-buf*
        *vl-1-bit-not*
        *vl-1-bit-and*
        *vl-1-bit-or*
        *vl-1-bit-xor*
        *vl-1-bit-nand*
        *vl-1-bit-nor*
        *vl-1-bit-xnor*
        *vl-1-bit-zmux*
        *vl-1-bit-ceq*
        ;; *vl-1-bit-flop*
        *vl-1-bit-latch*

        *vl-1-bit-bufif0*
        *vl-1-bit-bufif1*
        *vl-1-bit-notif0*
        *vl-1-bit-notif1*
        *vl-1-bit-nmos*
        *vl-1-bit-rnmos*
        *vl-1-bit-pmos*
        *vl-1-bit-rpmos*
        *vl-1-bit-cmos*
        *vl-1-bit-rcmos*
        *vl-1-bit-tran*
        *vl-1-bit-rtran*
        *vl-1-bit-tranif0*
        *vl-1-bit-rtranif0*
        *vl-1-bit-tranif1*
        *vl-1-bit-rtranif1*
        *vl-1-bit-pullup*
        *vl-1-bit-pulldown*
        ;; *vl-1-bit-resolve-wire*
        ))





;; Commenting this out for now, until we implement WAND/WOR.

;; (defxdoc *vl-1-bit-resolve-wor* :parents (primitives) :short "Primitive
;;   module that resolves multiple drivers on a @('wor') net."  :long "<p>The
;;   Verilog definition of this module is:</p>

;; @({
;; module VL_1_BIT_RESOLVE_WOR (out, a, b) ;
;;   output out;
;;   input a;
;;   input b;

;;   wor out;

;;   assign out = a;
;;   assign out = b;
;; endmodule
;; })

;; <p>VL takes this as a primitive.  This module, and wrappers that extend it to
;; higher arities and wider signals, may be introduced by the @(see multidrive)
;; transform to deal with multiply driven wired ors.</p>")

;; (defconsts *vl-1-bit-resolve-wor*
;;   (b* ((name "VL_1_BIT_RESOLVE_WOR")
;;        (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
;;        ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
;;        ((mv a-expr   a-port   a-portdecl   a-vardecl)   (vl-primitive-mkport "a"   :vl-input))
;;        ((mv b-expr   b-port   b-portdecl   b-vardecl)   (vl-primitive-mkport "b"   :vl-input))
;;        (out-vardecl  (change-vl-vardecl out-vardecl :type :vl-wor))
;;        (a-assign     (make-vl-assign :lvalue out-expr :expr a-expr :loc *vl-fakeloc*))
;;        (b-assign     (make-vl-assign :lvalue out-expr :expr b-expr :loc *vl-fakeloc*)))
;;     (make-honsed-vl-module :name      name
;;                            :origname  name
;;                            :ports     (list out-port     a-port      b-port)
;;                            :portdecls (list out-portdecl a-portdecl  b-portdecl)
;;                            :vardecls  (list out-vardecl  a-vardecl   b-vardecl)
;;                            :assigns   (list              a-assign    b-assign)
;;                            :minloc    *vl-fakeloc*
;;                            :maxloc    *vl-fakeloc*
;;                            :atts      atts)))




#||

(include-book ;; fool dependency scanner
 "mlib/writer")

(vl-pps-modulelist *vl-primitive-mods*)

||#
