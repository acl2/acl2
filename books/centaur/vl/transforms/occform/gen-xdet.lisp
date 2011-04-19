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
(include-book "gen-simple")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

; gen-xdet.lisp -- functions that generate X-detection modules


(def-vl-modgen vl-make-n-bit-xdetect (n)
  :short "Generate a module that detects X/Z bits."

  :long "<p>We generate a gate-based module with the following signature:</p>

<code>
module VL_N_BIT_XDETECT (out, in) ;
  output out;
  input [n-1:0] in;

  ...
endmodule
</code>

<p>We set <tt>out</tt> to X whenever any bit of <tt>in</tt> is X or Z.
Otherwise, we set <tt>out</tt> to 0.</p>

<p>This module is useful because many of Verilog's arithmetic
expressions (compares, additions, subtractions, etc.) require that if any input
bit is X or Z, then the entire output should be X.  The basic idea is to use
<tt>VL_N_BIT_XDETECT</tt> to see if any input bit is X or Z, then XOR the
output bit with every bit of the answer from a compare, addition, subtraction,
etc.  If the X-DET bit is zero, then XOR'ing it with the answer just yields the
original answer.  But if it is X, then the resulting bits are all X.</p>"

  :guard (posp n)
  :body
  (b* ((name  (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_X_DETECT")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))

;; BOZO might we get rid of this special case?

       ((when (= n 1))
        ;; xor (out, in, in);
        (let ((out-gate (vl-make-binary-gateinst :vl-xor out-expr in-expr in-expr nil nil)))
          (list (make-vl-module :name      name
                                :origname  name
                                :ports     (list out-port in-port)
                                :portdecls (list out-portdecl in-portdecl)
                                :netdecls  (list out-netdecl in-netdecl)
                                :gateinsts (list out-gate)
                                :minloc    *vl-fakeloc*
                                :maxloc    *vl-fakeloc*))))

       ;; wire temp = ^in;
       ((mv temp-expr temp-netdecl)  (vl-occform-mkwire "temp" 1))
       ((cons temp-mod temp-support) (vl-make-n-bit-reduction-op :vl-unary-xor n))
       (temp-args (list (make-vl-plainarg :expr temp-expr :dir :vl-output :portname (hons-copy "out"))
                        (make-vl-plainarg :expr in-expr   :dir :vl-input  :portname (hons-copy "in"))))
       (temp-inst (make-vl-modinst :modname   (vl-module->name temp-mod)
                                   :instname  (hons-copy "mk_temp")
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil temp-args)
                                   :loc       *vl-fakeloc*))

       ;; xor(out, temp, temp);
       (out-gate (vl-make-binary-gateinst :vl-xor out-expr temp-expr temp-expr nil nil)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl in-netdecl temp-netdecl)
                           :gateinsts (list out-gate)
                           :modinsts  (list temp-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           temp-mod
           temp-support)))



(def-vl-modgen vl-make-n-bit-xor-each (n)
  :short "Generate a module that XORs a bit with each bit of a vector."

  :long "<p>We generate a module that uses gates and is semantically equivalent
to:</p>

<code>
module VL_N_BIT_XOR_EACH (out, a, b)
  output [n-1:0] out;
  input a;
  input [n-1:0] b;

  assign out[0]   = a ^ b[0];
  ...
  assign out[n-1] = a ^ b[n-1];
endmodule
</code>

<p>In other words, we xor <tt>a</tt> with each bit of <tt>b</tt> and return the
xor'ed vector.</p>"

  :guard (posp n)
  :body
  (b* ((name  (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_XOR_EACH")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input 1))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       (a-wires   (repeat a-expr n))
       (b-wires   (vl-make-list-of-bitselects b-expr 0 (- n 1)))
       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))
       (gates     (vl-make-binary-gateinstlist :vl-xor out-wires a-wires b-wires nil)))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port a-port b-port)
                          :portdecls (list out-portdecl a-portdecl b-portdecl)
                          :netdecls  (list out-netdecl a-netdecl b-netdecl)
                          :gateinsts gates
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*))))



(def-vl-modgen vl-make-n-bit-x-propagator (n m)
  :short "Generate a module that propagates Xes from inputs into an answer."

  :long "<p>We generate a gate-based module that has the following interface:</p>

<code>
module VL_N_BY_M_XPROP (out, ans, a, b);
  output [m-1:0] out;
  input [m-1:0] ans;
  input [n-1:0] a;
  input [n-1:0] b;
endmodule
</code>

<p>This propagator module can be understood as: if any bit of <tt>a</tt> or
<tt>b</tt> is X/Z, then <tt>out</tt> will be all X bits.  Otherwise
<tt>out</tt> is just a copy of <tt>ans</tt>.</p>"

  :guard (and (posp n)
              (posp m))

  :body
  (b* ((name (hons-copy (str::cat "VL_" (str::natstr n) "_BY_" (str::natstr m) "_XPROP")))

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
       (xdeta-args (list (make-vl-plainarg :expr xdeta-expr :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr a-expr     :dir :vl-input  :portname (hons-copy "in"))))
       (xdeta-inst (make-vl-modinst :instname  "mk_xdet_a"
                                    :modname   (vl-module->name xdet-mod)
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xdeta-args)
                                    :loc       *vl-fakeloc*))

       ;; xdet_b is X whenever B has any X/Z bits, or 0 otherwise
       (xdetb-args (list (make-vl-plainarg :expr xdetb-expr :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr b-expr     :dir :vl-input  :portname (hons-copy "in"))))
       (xdetb-inst (make-vl-modinst :instname  "mk_xdet_b"
                                    :modname   (vl-module->name xdet-mod)
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xdetb-args)
                                    :loc       *vl-fakeloc*))

       ;; xdet_ab is X whenever either A/B have any X/Z bits, or 0 otherwise
       (xdet-gate (vl-make-binary-gateinst :vl-xor xdet-expr xdeta-expr xdetb-expr nil *vl-fakeloc*))

       ;; now xor xdet_ab with each bit of ans:
       ;;   - out becomes all Xes when xdet_ab is X, i.e., when any bit of A or B is X/Z
       ;;   - out becomes ans otherwise since xdet_ab is 0
       (xeach-args (list (make-vl-plainarg :expr out-expr  :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr xdet-expr :dir :vl-input  :portname (hons-copy "a"))
                         (make-vl-plainarg :expr ans-expr  :dir :vl-input  :portname (hons-copy "b"))))
       (xeach-inst   (make-vl-modinst :instname  "mk_out"
                                      :modname   (vl-module->name xeach-mod)
                                      :paramargs (vl-arguments nil nil)
                                      :portargs  (vl-arguments nil xeach-args)
                                      :loc       *vl-fakeloc*)))

      (list* (make-vl-module :name      name
                             :origname  name
                             :ports     (list out-port ans-port a-port b-port)
                             :portdecls (list out-portdecl ans-portdecl a-portdecl b-portdecl)
                             :netdecls  (list out-netdecl ans-netdecl a-netdecl b-netdecl xdeta-netdecl xdetb-netdecl xdet-netdecl)
                             :gateinsts (list xdet-gate)
                             :modinsts  (list xdeta-inst xdetb-inst xeach-inst)
                             :minloc    *vl-fakeloc*
                             :maxloc    *vl-fakeloc*)
             xdet-mod
             xeach-mod
             (append xdet-support xeach-support))))

