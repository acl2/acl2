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
(include-book "gen-xdet")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

; gen-adder.lisp -- functions that generate addition/subtraction modules

(defsection *vl-1-bit-adder-core*
  :parents (occform)
  :short "Primitive one-bit full-adder module."

  :long "<p>A full-adder is a one-bit adder that produces a sum and carry.  We
use the following definition:</p>

<code>
module VL_1_BIT_ADDER_CORE (sum, cout, a, b, cin) ;
  output sum, cout;
  input a, b, cin;
  wire t1, t2, t3;

  assign t1 = a ^ b;
  assign sum = t1 ^ cin;
  assign t2 = t1 &amp; cin;
  assign t3 = a &amp; b;
  assign cout = t2 | t3;

endmodule
</code>

<p>This is only a \"core.\" It doesn't quite correspond to an addition like
<tt>assign {carry, sum} = a + b + cin</tt> in Verilog because of X handling.
See @(see vl-make-n-bit-plusminus) for the real module generator.</p>"

  (defconst *vl-1-bit-adder-core*

    (b* ((name (hons-copy "VL_1_BIT_ADDER_CORE"))

         ((mv sum-expr sum-port sum-portdecl sum-netdecl)     (vl-occform-mkport "sum" :vl-output 1))
         ((mv cout-expr cout-port cout-portdecl cout-netdecl) (vl-occform-mkport "cout" :vl-output 1))
         ((mv a-expr a-port a-portdecl a-netdecl)             (vl-occform-mkport "a" :vl-input 1))
         ((mv b-expr b-port b-portdecl b-netdecl)             (vl-occform-mkport "b" :vl-input 1))
         ((mv cin-expr cin-port cin-portdecl cin-netdecl)     (vl-occform-mkport "cin" :vl-input 1))

         ((mv t1-expr t1-netdecl) (vl-occform-mkwire "t1" 1))
         ((mv t2-expr t2-netdecl) (vl-occform-mkwire "t2" 1))
         ((mv t3-expr t3-netdecl) (vl-occform-mkwire "t3" 1))

         (t1-gate   (vl-make-binary-gateinst :vl-xor t1-expr   a-expr  b-expr   nil nil))
         (sum-gate  (vl-make-binary-gateinst :vl-xor sum-expr  t1-expr cin-expr nil nil))
         (t2-gate   (vl-make-binary-gateinst :vl-and t2-expr   t1-expr cin-expr nil nil))
         (t3-gate   (vl-make-binary-gateinst :vl-and t3-expr   a-expr  b-expr   nil nil))
         (cout-gate (vl-make-binary-gateinst :vl-or  cout-expr t2-expr t3-expr  nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list sum-port cout-port a-port b-port cin-port)
                      :portdecls (list sum-portdecl cout-portdecl a-portdecl b-portdecl cin-portdecl)
                      :netdecls  (list sum-netdecl cout-netdecl a-netdecl b-netdecl cin-netdecl t1-netdecl t2-netdecl t3-netdecl)
                      :gateinsts (list t1-gate sum-gate t2-gate t3-gate cout-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(defsection vl-make-full-adders
  :parents (occform)
  :short "Generate a list of @(see *vl-1-bit-adder-core*) instances."

  (defund vl-make-full-adders (name-index sum-bits cout-bits a-bits b-bits cin-bits)
    ;; Instance a bunch of full-adders
    (declare (xargs :guard (and (natp name-index)
                                (vl-exprlist-p sum-bits)
                                (vl-exprlist-p cout-bits)
                                (vl-exprlist-p a-bits)
                                (vl-exprlist-p b-bits)
                                (vl-exprlist-p cin-bits)
                                (same-lengthp sum-bits cout-bits)
                                (same-lengthp sum-bits a-bits)
                                (same-lengthp sum-bits b-bits)
                                (same-lengthp sum-bits cin-bits))))
    (b* (((when (atom sum-bits))
          nil)
         (args (list (make-vl-plainarg :expr (car sum-bits)  :dir :vl-output :portname (hons-copy "sum"))
                     (make-vl-plainarg :expr (car cout-bits) :dir :vl-output :portname (hons-copy "cout"))
                     (make-vl-plainarg :expr (car a-bits)    :dir :vl-input  :portname (hons-copy "a"))
                     (make-vl-plainarg :expr (car b-bits)    :dir :vl-input  :portname (hons-copy "b"))
                     (make-vl-plainarg :expr (car cin-bits)  :dir :vl-input  :portname (hons-copy "cin"))))
         (inst1 (make-vl-modinst :instname  (hons-copy (str::cat "fa_" (str::natstr name-index)))
                                 :modname   (vl-module->name *vl-1-bit-adder-core*)
                                 :portargs  (vl-arguments nil args)
                                 :paramargs (vl-arguments nil nil)
                                 :loc       *vl-fakeloc*))
         (rest  (vl-make-full-adders (+ 1 name-index) (cdr sum-bits) (cdr cout-bits)
                                     (cdr a-bits) (cdr b-bits) (cdr cin-bits))))
      (cons inst1 rest)))

  (defthm vl-modinstlist-p-of-vl-make-full-adders
    (implies (and (force (natp name-index))
                  (force (vl-exprlist-p sum-bits))
                  (force (vl-exprlist-p cout-bits))
                  (force (vl-exprlist-p a-bits))
                  (force (vl-exprlist-p b-bits))
                  (force (vl-exprlist-p cin-bits))
                  (force (same-lengthp sum-bits cout-bits))
                  (force (same-lengthp sum-bits a-bits))
                  (force (same-lengthp sum-bits b-bits))
                  (force (same-lengthp sum-bits cin-bits)))
             (vl-modinstlist-p (vl-make-full-adders name-index sum-bits cout-bits a-bits b-bits cin-bits)))
    :hints(("Goal" :in-theory (enable vl-make-full-adders)))))



(def-vl-modgen vl-make-n-bit-adder-core (n)
  :short "Generate an N-bit basic ripple-carry adder module."

  :long "<p>We generate a gate-based module with the following interface:</p>

<code>
module VL_N_BIT_ADDER_CORE (sum, cout, a, b, cin);
  output [n-1:0] sum;
  output cout;
  input [n-1:0] a;
  input [n-1:0] b;
  input cin;
  ...
endmodule
</code>

<p>This is a basic ripple-carry adder formed by chaining together several
full-adders; see @(see *vl-1-bit-adder-core*) and @(see vl-make-full-adders).</p>

<p>This module does NOT correspond to a full addition in Verilog.  It computes
something akin to <tt>assign {cout, sum} = a + b + cin</tt>, but it does not
handle X's like Verilog does.  See @(see vl-make-n-bit-plusminus) for the full
addition and subtraction modules.</p>

<p>We could probably make a leaner module by using a half-adder for the first
bit (which does not have a carry-in) and by dropping the wires on the carry for
the last bit, but we think it's best to keep things simple.</p>"

  :guard (posp n)

  :body
  (b* (((when (= n 1))
        (list *vl-1-bit-adder-core*))

       (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_ADDER_CORE")))

       ((mv sum-expr sum-port sum-portdecl sum-netdecl)     (vl-occform-mkport "sum" :vl-output n))
       ((mv cout-expr cout-port cout-portdecl cout-netdecl) (vl-occform-mkport "cout" :vl-output 1))
       ((mv a-expr a-port a-portdecl a-netdecl)             (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)             (vl-occform-mkport "b" :vl-input n))
       ((mv cin-expr cin-port cin-portdecl cin-netdecl)     (vl-occform-mkport "cin" :vl-input 1))

       ;; wire [n-2:0] carry;
       ((mv carry-expr carry-netdecl) (vl-occform-mkwire "carry" (- n 1)))

       ;; Now we build a big array of full-adders, basically:

       ;; VL_BASIC_FULL_ADDER fa_0     (sum[0],   carry[0],   a[0],   b[0],   cin);
       ;; VL_BASIC_FULL_ADDER fa_1     (sum[1],   carry[1],   a[1],   b[1],   carry[0]);
       ;; VL_BASIC_FULL_ADDER fa_2     (sum[2],   carry[2],   a[2],   b[2],   carry[1]);
       ;;    ...
       ;; VL_BASIC_FULL_ADDER fa_{n-2} (sum[n-2], carry[n-2], a[n-2], b[n-2], carry[n-3]);
       ;; VL_BASIC_FULL_ADDER fa_{n-1} (sum[n-1], cout,       a[n-1], b[n-2], carry[n-2]);

       (sum-wires   (vl-make-list-of-bitselects sum-expr   0 (- n 1)))
       (carry-wires (vl-make-list-of-bitselects carry-expr 0 (- n 2)))
       (a-wires     (vl-make-list-of-bitselects a-expr     0 (- n 1)))
       (b-wires     (vl-make-list-of-bitselects b-expr     0 (- n 1)))

       (fa-insts    (vl-make-full-adders 0
                                         sum-wires
                                         (append carry-wires (list cout-expr))
                                         a-wires
                                         b-wires
                                         (cons cin-expr carry-wires))))

    (list (make-vl-module :name      name
                          :origname  name
                          :ports     (list sum-port cout-port a-port b-port cin-port)
                          :portdecls (list sum-portdecl cout-portdecl a-portdecl b-portdecl cin-portdecl)
                          :netdecls  (list sum-netdecl cout-netdecl a-netdecl b-netdecl cin-netdecl carry-netdecl)
                          :modinsts  fa-insts
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          *vl-1-bit-adder-core*)))



(def-vl-modgen vl-make-n-bit-plusminus (type n)
  :short "Generate an addition or subtraction module."

  :long "<p>Depending on the <tt>type</tt>, which should be either
<tt>:vl-binary-plus</tt> or <tt>:vl-binary-minus</tt>, we generate a gate-based
addition or subtraction module that is semantically equivalent to:</p>

<code>
module VL_N_BIT_{PLUS,MINUS} (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [n-1:0] b;

// One of:

  assign out = a + b;  // For PLUS
  assign out = a - b;  // For MINUS

endmodule
</code>

<p>These modules capture the behavior specified by Verilog for addition and
subtraction, including the requirement that if any bit of <tt>a</tt> or
<tt>b</tt> is X/Z then the entire output is entirely X.</p>

<p>We basically combine a simple ripple-carry adder with some additional
X-detection and propagation circuitry.  This makes our adder rather bulky and
unlike the actual hardware that would probably be synthesized or
implemented.</p>"

  :guard (and (member type (list :vl-binary-plus :vl-binary-minus))
              (posp n))

  :body
  (b* ((name  (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_"
                                   (case type
                                     (:vl-binary-plus "PLUS")
                                     (:vl-binary-minus "MINUS")))))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       ((mv sum-expr sum-netdecl)     (vl-occform-mkwire "sum" n))
       ((mv carry-expr carry-netdecl) (vl-occform-mkwire "carry" 1))

       ;; For addition, we use a carry-in of zero and do not negate b.  But
       ;; if we are subtracting, we need to use a carry-in of 1 and negate
       ;; the B input.
       ((mv cin bin sub-netdecls sub-modinsts sub-support)
        (if (eq type :vl-binary-plus)
            ;; addition: carry in = 0, b-input = b
            (mv |*sized-1'b0*| b-expr nil nil nil)
          ;; subtraction: carry in = 1, b-input = ~b
          (b* (;; wire [n-1:0] bnot = ~b;
               ((mv bnot-expr bnot-netdecl)  (vl-occform-mkwire "bnot" n))
               ((cons bnot-mod bnot-support) (vl-make-n-bit-not n))
               (bnot-args (list (make-vl-plainarg :expr bnot-expr :dir :vl-output :portname (hons-copy "out"))
                                (make-vl-plainarg :expr b-expr    :dir :vl-input  :portname (hons-copy "in"))))
               (bnot-inst (make-vl-modinst :modname   (vl-module->name bnot-mod)
                                           :instname  (hons-copy "mk_bnot")
                                           :paramargs (vl-arguments nil nil)
                                           :portargs  (vl-arguments nil bnot-args)
                                           :loc       *vl-fakeloc*)))
            (mv |*sized-1'b1*|
                bnot-expr
                (list bnot-netdecl)
                (list bnot-inst)
                (cons bnot-mod bnot-support)))))

       ;; Instantiate a ripple-carry adder to do all the work
       ((cons core-mod core-support) (vl-make-n-bit-adder-core n))
       (core-args (list (make-vl-plainarg :expr sum-expr   :dir :vl-output :portname (hons-copy "sum"))
                        (make-vl-plainarg :expr carry-expr :dir :vl-output :portname (hons-copy "cout"))
                        (make-vl-plainarg :expr a-expr     :dir :vl-input  :portname (hons-copy "a"))
                        (make-vl-plainarg :expr bin        :dir :vl-input  :portname (hons-copy "b"))
                        (make-vl-plainarg :expr cin        :dir :vl-input  :portname (hons-copy "cin"))))
       (core-inst (make-vl-modinst :modname   (vl-module->name core-mod)
                                   :instname  (hons-copy "core")
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil core-args)
                                   :loc       *vl-fakeloc*))

       ;; Now slap x-detection onto the "sum" to compute the answer
       ((cons xprop-mod xprop-support) (vl-make-n-bit-x-propagator n n))
       (xprop-args (list (make-vl-plainarg :expr out-expr :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr sum-expr :dir :vl-input  :portname (hons-copy "ans"))
                         (make-vl-plainarg :expr a-expr   :dir :vl-input  :portname (hons-copy "a"))
                         (make-vl-plainarg :expr b-expr   :dir :vl-input  :portname (hons-copy "b"))))
       (xprop-inst (make-vl-modinst :modname   (vl-module->name xprop-mod)
                                    :instname  (hons-copy "xprop")
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xprop-args)
                                    :loc       *vl-fakeloc*)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port a-port b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list* out-netdecl a-netdecl b-netdecl sum-netdecl carry-netdecl sub-netdecls)
                           :modinsts  (append sub-modinsts (list core-inst xprop-inst))
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           core-mod
           xprop-mod
           (append sub-support core-support xprop-support))))


