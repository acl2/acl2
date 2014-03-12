; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "../../primitives")
(include-book "../occform/util")

(define vl-make-1-bit-flop-instances
  ((q-wires  vl-exprlist-p)
   (clk-wire vl-expr-p)
   (d-wires  vl-exprlist-p)
   &optional
   ((n "current index, for name generation, counts up" natp) '0))
  :guard (same-lengthp q-wires d-wires)
  :returns (insts vl-modinstlist-p :hyp :fguard)
  :parents (vl-make-n-bit-flop)
  :short "Build a list of @('VL_1_BIT_FLOP') instances."
  :long "<p>We produce a list of flop instances like:</p>

@({
   VL_1_BIT_FLOP bit_0 (q[0], clk, d[0]) ;
   VL_1_BIT_FLOP bit_1 (q[1], clk, d[1]) ;
   ...
   VL_1_BIT_FLOP bit_{n-1} (q[{n-1}], clk, d[{n-1}]) ;
})"
  (if (atom q-wires)
      nil
    (cons (vl-simple-inst *vl-1-bit-flop*
                          (hons-copy (cat "bit_" (natstr n)))
                          (car q-wires) clk-wire (car d-wires))
          (vl-make-1-bit-flop-instances (cdr q-wires) clk-wire (cdr d-wires)
                                        (+ n 1)))))

(def-vl-modgen vl-make-n-bit-flop (n)
  :parents (flopcode)
  :short "Generate an N-bit register module."

  :long "<p>We generate a module that is written in terms of @(see primitives)
and is semantically equivalent to:</p>

@({
module VL_N_BIT_FLOP (q, clk, d);
  output q;
  input clk;
  input d;
  reg q;
  always @(posedge clk)
    q <= d;
endmodule
})

<p>The actual definition uses a list of @(see *vl-1-bit-flop*) primitives,
e.g., for the four-bit case we would have:</p>

@({
module VL_4_BIT_FLOP (q, clk, d);
  output [3:0] q;
  input clk;
  input [3:0] d;

  VL_1_BIT_FLOP bit_0 (q[0], clk, d[0]);
  VL_1_BIT_FLOP bit_1 (q[1], clk, d[1]);
  VL_1_BIT_FLOP bit_2 (q[2], clk, d[2]);
  VL_1_BIT_FLOP bit_3 (q[3], clk, d[3]);
endmodule
})"

  :guard (posp n)

  :body
  (b* (((when (eql n 1))
        (list *vl-1-bit-flop*))

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_FLOP")))

       ((mv q-expr q-port q-portdecl q-netdecl)         (vl-occform-mkport "q" :vl-output n))
       ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input 1))
       ((mv d-expr d-port d-portdecl d-netdecl)         (vl-occform-mkport "d" :vl-input n))

       (q-wires  (vl-make-list-of-bitselects q-expr 0 (- n 1)))
       (d-wires  (vl-make-list-of-bitselects d-expr 0 (- n 1)))
       (modinsts (vl-make-1-bit-flop-instances q-wires clk-expr d-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list q-port clk-port d-port)
                          :portdecls (list q-portdecl clk-portdecl d-portdecl)
                          :netdecls  (list q-netdecl clk-netdecl d-netdecl)
                          :modinsts  modinsts
                          :atts      (acons "VL_HANDS_OFF" nil nil) ;; <-- maybe not needed with the new sizing code now
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-flop*)))

#||
(include-book ;; fool dependency scanner
 "../../mlib/writer")

(vl-pps-modulelist (vl-make-n-bit-flop 4))
||#
