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
(include-book "simple")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

(def-vl-modgen vl-make-n-bit-xdetect (n)
  :short "Generate a module that detects X/Z bits."

  :long "<p>We generate a gate-based module with the following signature:</p>

@({
module VL_N_BIT_XDETECT (out, in) ;
  output out;
  input [n-1:0] in;

  ...
endmodule
})

<p>We set @('out') to X whenever any bit of @('in') is X or Z.  Otherwise, we
set @('out') to 0.</p>

<p>This module is useful because many of Verilog's arithmetic
expressions (compares, additions, subtractions, etc.) require that if any input
bit is X or Z, then the entire output should be X.  The basic idea is to use
@('VL_N_BIT_XDETECT') to see if any input bit is X or Z, then XOR the output
bit with every bit of the answer from a compare, addition, subtraction, etc.
If the X-DET bit is zero, then XOR'ing it with the answer just yields the
original answer.  But if it is X, then the resulting bits are all X.</p>"

  :guard (posp n)
  :body
  (b* ((name  (hons-copy (cat "VL_" (natstr n) "_BIT_X_DETECT")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))

;; BOZO might we get rid of this special case?

       ((when (= n 1))
        ;; xor (out, in, in);
        (let ((out-inst (vl-simple-inst *vl-1-bit-xor* "ans" out-expr in-expr in-expr)))
          (list (make-vl-module :name      name
                                :origname  name
                                :ports     (list out-port in-port)
                                :portdecls (list out-portdecl in-portdecl)
                                :netdecls  (list out-netdecl in-netdecl)
                                :modinsts  (list out-inst)
                                :minloc    *vl-fakeloc*
                                :maxloc    *vl-fakeloc*)
                *vl-1-bit-xor*)))

       ;; wire temp = ^in;
       ((mv temp-expr temp-netdecl)  (vl-occform-mkwire "temp" 1))
       ((cons temp-mod temp-support) (vl-make-n-bit-reduction-op :vl-unary-xor n))
       (temp-inst                    (vl-simple-inst temp-mod "mk_temp" temp-expr in-expr))

       ;; xor(out, temp, temp);
       (out-inst (vl-simple-inst *vl-1-bit-xor* "mk_out" out-expr temp-expr temp-expr)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl in-netdecl temp-netdecl)
                           :modinsts  (list temp-inst out-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           temp-mod
           temp-support)))

#||
(vl-pps-modulelist (vl-make-n-bit-xdetect 1))
(vl-pps-modulelist (vl-make-n-bit-xdetect 2))
(vl-pps-modulelist (vl-make-n-bit-xdetect 5))
||#


(def-vl-modgen vl-make-n-bit-xor-each (n)
  :short "Generate a module that XORs a bit with each bit of a vector."

  :long "<p>We generate a module that uses gates and is semantically equivalent
to:</p>

@({
module VL_N_BIT_XOR_EACH (out, a, b)
  output [n-1:0] out;
  input a;
  input [n-1:0] b;

  assign out[0]   = a ^ b[0];
  ...
  assign out[n-1] = a ^ b[n-1];
endmodule
})

<p>In other words, we xor @('a') with each bit of @('b') and return the xor'ed
vector.</p>"

  :guard (posp n)
  :body
  (b* ((name  (hons-copy (cat "VL_" (natstr n) "_BIT_XOR_EACH")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input 1))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       (a-wires   (replicate n a-expr))
       (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))
       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (insts     (vl-simple-inst-list *vl-1-bit-xor* "bit" out-wires a-wires b-wires)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :netdecls  (list out-netdecl a-netdecl b-netdecl)
                          :modinsts  insts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))

#||
(vl-pps-modulelist (vl-make-n-bit-xor-each 1))
(vl-pps-modulelist (vl-make-n-bit-xor-each 3))
||#



(def-vl-modgen vl-make-n-bit-x-propagator (n m)
  :short "Generate a module that propagates Xes from inputs into an answer."

  :long "<p>We generate a gate-based module that has the following interface:</p>

@({
module VL_N_BY_M_XPROP (out, ans, a, b);
  output [m-1:0] out;
  input [m-1:0] ans;
  input [n-1:0] a;
  input [n-1:0] b;
endmodule
})

<p>This propagator module can be understood as: if any bit of @('a') or @('b')
is X/Z, then @('out') will be all X bits.  Otherwise @('out') is just a copy of
@('ans').</p>"

  :guard (and (posp n)
              (posp m))

  :body
  (b* ((name (hons-copy (cat "VL_" (natstr n) "_BY_" (natstr m) "_XPROP")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output m))
       ((mv ans-expr ans-port ans-portdecl ans-netdecl) (vl-occform-mkport "ans" :vl-input m))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       ((mv xdeta-expr xdeta-netdecl) (vl-occform-mkwire "xdet_a" 1))
       ((mv xdetb-expr xdetb-netdecl) (vl-occform-mkwire "xdet_b" 1))
       ((mv xdet-expr xdet-netdecl)   (vl-occform-mkwire "xdet_ab" 1))

       ((cons xdet-mod xdet-support)   (vl-make-n-bit-xdetect n))
       ((cons xeach-mod xeach-support) (vl-make-n-bit-xor-each m))

       ;; xdet_a is X whenever A has any X/Z bits, or 0 otherwise
       (xdeta-inst (vl-simple-inst xdet-mod "mk_xdet_a" xdeta-expr a-expr))

       ;; xdet_b is X whenever B has any X/Z bits, or 0 otherwise
       (xdetb-inst (vl-simple-inst xdet-mod "mk_xdet_b" xdetb-expr b-expr))

       ;; xdet_ab is X whenever either A/B have any X/Z bits, or 0 otherwise
       (xdet-inst (vl-simple-inst *vl-1-bit-xor* "mk_xdet_ab" xdet-expr xdeta-expr xdetb-expr))

       ;; now xor xdet_ab with each bit of ans:
       ;;   - out becomes all Xes when xdet_ab is X, i.e., when any bit of A or B is X/Z
       ;;   - out becomes ans otherwise since xdet_ab is 0
       (xeach-inst (vl-simple-inst xeach-mod "mk_out" out-expr xdet-expr ans-expr)))

      (list* (make-vl-module :name      name
                             :origname  name
                             :ports     (list out-port ans-port a-port b-port)
                             :portdecls (list out-portdecl ans-portdecl a-portdecl b-portdecl)
                             :netdecls  (list out-netdecl ans-netdecl a-netdecl b-netdecl xdeta-netdecl xdetb-netdecl xdet-netdecl)
                             :modinsts  (list xdeta-inst xdetb-inst xdet-inst xeach-inst)
                             :minloc    *vl-fakeloc*
                             :maxloc    *vl-fakeloc*)
             xdet-mod
             xeach-mod
             (append xdet-support xeach-support))))


#||
(vl-pps-modulelist (vl-make-n-bit-x-propagator 3 5))
||#
