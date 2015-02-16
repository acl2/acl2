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
(include-book "../../primitives")
(include-book "../../mlib/modgen")
(include-book "../delayredux")

(define vl-make-1-bit-latch-instances
  ((q-wires  vl-exprlist-p)
   (clk-wire vl-expr-p)
   (d-wires  vl-exprlist-p)
   &optional
   ((n "current index, for name generation, counts up" natp) '0))
  :guard (same-lengthp q-wires d-wires)
  :returns (insts vl-modinstlist-p)
  :parents (vl-make-n-bit-latch)
  :short "Build a list of @('VL_1_BIT_LATCH') instances."
  :long "<p>We produce a list of latch instances like:</p>

@({
   VL_1_BIT_LATCH bit_0 (q[0], clk, d[0]) ;
   VL_1_BIT_LATCH bit_1 (q[1], clk, d[1]) ;
   ...
   VL_1_BIT_LATCH bit_{n-1} (q[{n-1}], clk, d[{n-1}]) ;
})"
  (if (atom q-wires)
      nil
    (cons (vl-simple-inst *vl-1-bit-latch*
                          (hons-copy (cat "bit_" (natstr n)))
                          (car q-wires) clk-wire (car d-wires))
          (vl-make-1-bit-latch-instances (cdr q-wires) clk-wire (cdr d-wires)
                                         (+ n 1)))))


(def-vl-modgen vl-make-n-bit-latch (n)
  :parents (latchcode)
  :short "Generate an N-bit latch module."

  :long "<p>We generate a module that is written in terms of @(see primitives)
and is semantically equivalent to:</p>

@({
module VL_N_BIT_LATCH (q, clk, d);
  output q;
  input clk;
  input d;
  reg q;
  always @(d or clk)
    q <= clk ? d : q;
endmodule
})

<p>The actual definition uses a list of @(see *vl-1-bit-latch*) primitives,
e.g., for the four-bit case we would have:</p>

@({
module VL_4_BIT_LATCH (q, clk, d);
  output [3:0] q;
  input clk;
  input [3:0] d;

  VL_1_BIT_LATCH bit_0 (q[0], clk, d[0]);
  VL_1_BIT_LATCH bit_1 (q[1], clk, d[1]);
  VL_1_BIT_LATCH bit_2 (q[2], clk, d[2]);
  VL_1_BIT_LATCH bit_3 (q[3], clk, d[3]);
endmodule
})"

  :guard (posp n)

  :body
  (b* (((when (eql n 1))
        (list *vl-1-bit-latch*))

       (name        (hons-copy (cat "VL_" (natstr n) "_BIT_LATCH")))

       ((mv q-expr q-port q-portdecl q-vardecl)         (vl-occform-mkport "q" :vl-output n))
       ((mv clk-expr clk-port clk-portdecl clk-vardecl) (vl-occform-mkport "clk" :vl-input 1))
       ((mv d-expr d-port d-portdecl d-vardecl)         (vl-occform-mkport "d" :vl-input n))

       (q-wires     (vl-make-list-of-bitselects q-expr 0 (- n 1)))
       (d-wires     (vl-make-list-of-bitselects d-expr 0 (- n 1)))
       (modinsts    (vl-make-1-bit-latch-instances q-wires clk-expr d-wires 0)))
    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list q-port clk-port d-port)
                          :portdecls (list q-portdecl clk-portdecl d-portdecl)
                          :vardecls  (list q-vardecl clk-vardecl d-vardecl)
                          :modinsts  modinsts
                          :atts      (acons "VL_HANDS_OFF" nil nil) ; <-- may not be needed with the new sizing code
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-latch*)))

#||
(include-book ;; fool dependency scanner
 "../../mlib/writer")

(vl-pps-modulelist (vl-make-n-bit-latch 4))
||#



(def-vl-modgen vl-make-n-bit-latch-vec (n del)
  :parents (latchcode)
  :short "Generate an N-bit latch module for vector-oriented synthesis."

  :long "<p>We generate basically the following module:</p>

@({
module VL_n_BIT_d_TICK_LATCH (q, clk, d);
  output [n-1:0] q;
  input clk;
  input [n-1:0] d;
  wire [n-1:0] qdel;
  wire [n-1:0] qreg;

  // note: this should be a non-propagating delay,
  // since any change in qdel is only seen as a change in qreg
  // and is caused by a change in d or clk that has already propagated.
  VL_n_BIT_DELAY_1 qdelinst (qdel, qreg);
  VL_n_BIT_DELAY_d qoutinst (q, qreg);

  // should be a conservative mux
  assign qreg = clk ? d : qdel;

endmodule
})"

  :guard (and (posp n)
              (natp del))

  :body
  (b* ((n   (lposfix n))
       (del (lnfix del))

       (name (hons-copy (if (zp del)
                            (cat "VL_" (natstr n) "_BIT_LATCH")
                          (cat "VL_" (natstr n) "_BIT_" (natstr del) "_TICK_LATCH"))))

       ((mv q-expr q-port q-portdecl q-vardecl)         (vl-occform-mkport "q" :vl-output n))
       ((mv clk-expr clk-port clk-portdecl clk-vardecl) (vl-occform-mkport "clk" :vl-input 1))
       ((mv d-expr d-port d-portdecl d-vardecl)         (vl-occform-mkport "d" :vl-input n))

       ;; note qregdecls are netdecls not regdecls
       ((mv qreg-expr qreg-decls qreg-assigns)
        ;; this represents the final delay of q, which we don't need if
        ;; delay=0.  in that case rather than creating a new redundant wire we
        ;; just use q itself in the place of qreg above.
        (b* (((when (zp del))
              (mv q-expr nil nil))
             ((mv qregexpr qregdecl)
              (vl-occform-mkwire "qreg" n))
             (ddelassign (make-vl-assign :lvalue q-expr
                                         :expr qregexpr
                                         :delay (vl-make-constdelay del)
                                         :loc *vl-fakeloc*)))
          (mv qregexpr (list qregdecl) (list ddelassign))))

       ;; non-propagating atts
       (triggers (make-vl-nonatom :op :vl-concat
                                  :args (list clk-expr d-expr)
                                  :finalwidth (+ 1 n)
                                  :finaltype :vl-unsigned))
       (atts (list (cons "VL_NON_PROP_TRIGGERS" triggers)
                   (cons "VL_NON_PROP_BOUND" qreg-expr)
                   (list "VL_STATE_DELAY")))
       ((mv qdel-expr qdel-decl)      (vl-occform-mkwire "qdel" n))
       (qdel-assign (make-vl-assign :lvalue qdel-expr
                                    :expr qreg-expr
                                    :delay (vl-make-constdelay 1)
                                    :loc *vl-fakeloc*
                                    :atts atts))

       (qreg-assign (make-vl-assign
                     :lvalue qreg-expr
                     :expr (make-vl-nonatom
                            :op :vl-qmark
                            :args (list clk-expr
                                        d-expr
                                        qdel-expr)
                            :finalwidth n
                            :finaltype :vl-unsigned
                            ;; note that this should be a conservative
                            ;; if-then-else in order for the delay on q to be
                            ;; properly non-propagating
                            :atts (list (list "VL_LATCH_MUX")))
                     :loc *vl-fakeloc*)))
    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list q-port clk-port d-port)
                          :portdecls (list q-portdecl clk-portdecl d-portdecl)
                          :vardecls  (list* q-vardecl clk-vardecl d-vardecl
                                            qdel-decl qreg-decls)
                          :assigns (list* qreg-assign qdel-assign qreg-assigns)
                          ;; :modinsts  (cons qdel-inst qreg-insts)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))
