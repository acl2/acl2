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
(include-book "gen-adder")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

(def-vl-modgen vl-make-n-bit-unsigned-gte (n)
  :short "Generate an unsigned greater-than or equal comparison module."

  :long "<p>We generate a gate-based module that is semantically equivalent
to:</p>

<code>
module VL_N_BIT_UNSIGNED_GTE (out, a, b) ;
  output out;
  input [n-1:0] a;
  input [n-1:0] b;
  assign out = a &gt;= b;
endmodule
</code>

<p>Note that in @(see oprewrite) we canonicalize any <tt>&lt;</tt>,
<tt>&lt;=</tt>, and <tt>&gt;</tt> operators into the <tt>&gt;=</tt> form, so
this module actually handles all inequality comparisons.</p>

<p>The basic idea is to compute <tt>a + ~b + 1</tt> and look at the carry
chain.  We do this by directly instantiating an adder.  This might be somewhat
inefficient since we really don't need to be computing the sum.  On the other
hand, there are really not very many comparison operators so we suspect we do
not need to be particularly efficient, and hopefully in any AIG or S-Expression
based representations the extra work will be automatically thrown away.</p>

<p>Note that the Verilog semantics require that if <tt>a</tt> or <tt>b</tt>
have any X/Z bits, then the answer should be X.  This is true even when the X
occurs in an insignificant place, e.g., <tt>1000 &gt; 000x</tt> is considered
to be X even though no matter what the X digit is, we can see that the
mathematical answer ought to be 1.  (This behavior might be intended to give
synthesis tools as much freedom as possible when implementing the
operation.)</p>"

  :guard (posp n)
  :body
  (b* ((name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_UNSIGNED_GTE")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       ((mv bnot-expr bnot-netdecl)  (vl-occform-mkwire "bnot" n))
       ((mv sum-expr sum-netdecl)    (vl-occform-mkwire "sum" n))
       ((mv cout-expr cout-netdecl)  (vl-occform-mkwire "cout" 1))

       ;; assign bnot = ~b;
       ((cons bnot-mod bnot-support) (vl-make-n-bit-unary-op :vl-not n))
       (bnot-args (list (make-vl-plainarg :expr bnot-expr :dir :vl-output :portname (hons-copy "out"))
                        (make-vl-plainarg :expr b-expr    :dir :vl-input  :portname (hons-copy "in"))))
       (bnot-inst (make-vl-modinst :modname   (vl-module->name bnot-mod)
                                   :instname  (hons-copy "mk_bnot")
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil bnot-args)
                                   :loc       *vl-fakeloc*))

       ;; VL_N_BIT_ADDER_CORE core (sum, cout, a, ~b, 1);
       ((cons core-mod core-support) (vl-make-n-bit-adder-core n))
       (core-args (list (make-vl-plainarg :expr sum-expr         :dir :vl-output :portname (hons-copy "sum"))
                        (make-vl-plainarg :expr cout-expr        :dir :vl-output :portname (hons-copy "cout"))
                        (make-vl-plainarg :expr a-expr           :dir :vl-input  :portname (hons-copy "a"))
                        (make-vl-plainarg :expr bnot-expr        :dir :vl-input  :portname (hons-copy "b"))
                        (make-vl-plainarg :expr |*occform-1'b1*| :dir :vl-input  :portname (hons-copy "cin"))))
       (core-inst (make-vl-modinst :modname   (vl-module->name core-mod)
                                   :instname  (hons-copy "core")
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil core-args)
                                   :loc       *vl-fakeloc*))

       ;; cout is almost right, but we also need to detect xes
       ((cons xprop-mod xprop-support) (vl-make-n-bit-x-propagator n 1))
       (xprop-args (list (make-vl-plainarg :expr out-expr  :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr cout-expr :dir :vl-input  :portname (hons-copy "ans"))
                         (make-vl-plainarg :expr a-expr    :dir :vl-input  :portname (hons-copy "a"))
                         (make-vl-plainarg :expr b-expr    :dir :vl-input  :portname (hons-copy "b"))))
       (xprop-inst (make-vl-modinst :modname   (vl-module->name xprop-mod)
                                    :instname  (hons-copy "xprop")
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xprop-args)
                                    :loc       *vl-fakeloc*)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port a-port b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl a-netdecl b-netdecl sum-netdecl cout-netdecl bnot-netdecl)
                           :modinsts  (list bnot-inst core-inst xprop-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           bnot-mod core-mod xprop-mod
           (append bnot-support core-support xprop-support))))






(defsection *vl-1-bit-signed-gte*
  :parents (occform)
  :short "Degenerate, single-bit signed greater-than-or-equal module."

  :long "<p>This is a gate-based module that is semantically equivalent to:</p>

<code>
module VL_1_BIT_SIGNED_GTE (out, a, b);
  output out;
  input signed a;
  input signed b;

  assign out = a &gt;= b;
endmodule
</code>

<p>Since Verilog uses 2's complement as its representation of signed numbers,
in the degenerate world of sign-bits we should have \"<em>0 means 0 and 1 means
-1</em>\".  So, counterintuitively, <tt>a &gt;= b</tt> holds except when <tt>a =
1</tt> and <tt>b = 0</tt>.</p>

<p><b>Warning:</b> The above is indeed the behavior implemented by NCVerilog.
But Verilog-XL appears to be buggy and instead produces results that are
consistent with an unsigned interpretation; see tests/test-scomp.v.</p>

<p>Our actual module is:</p>

<code>
module VL_1_BIT_SIGNED_GTE (out, a, b);
  output out;
  input a, b;
  wire bbar, mainbar, main, xa, xb, xab;

  not(bbar, b);                    // assign main = ~(a &amp; ~b)
  and(mainbar, a, bbar);
  not(main, mainbar);

  xor(xb, b, b);                   // Propagate Xes
  xor(xa, a, a);
  xor(xab, xa, xb);
  xor(out, xab, main);
endmodule
</code>"

  (defconst *vl-1-bit-signed-gte*

    (b* ((name (hons-copy "VL_1_BIT_SIGNED_GTE"))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input 1))
         ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input 1))

         ((mv bbar-expr bbar-netdecl)       (vl-occform-mkwire "bbar" 1))
         ((mv mainbar-expr mainbar-netdecl) (vl-occform-mkwire "mainbar" 1))
         ((mv main-expr main-netdecl)       (vl-occform-mkwire "main" 1))
         ((mv xa-expr xa-netdecl)           (vl-occform-mkwire "xa" 1))
         ((mv xb-expr xb-netdecl)           (vl-occform-mkwire "xb" 1))
         ((mv xab-expr xab-netdecl)         (vl-occform-mkwire "xab" 1))

         (bbar-gate    (vl-make-unary-gateinst  :vl-not bbar-expr    b-expr                 nil nil))
         (mainbar-gate (vl-make-binary-gateinst :vl-and mainbar-expr a-expr       bbar-expr nil nil))
         (main-gate    (vl-make-unary-gateinst  :vl-not main-expr    mainbar-expr           nil nil))
         (xb-gate      (vl-make-binary-gateinst :vl-xor xb-expr      b-expr       b-expr    nil nil))
         (xa-gate      (vl-make-binary-gateinst :vl-xor xa-expr      a-expr       a-expr    nil nil))
         (xab-gate     (vl-make-binary-gateinst :vl-xor xab-expr     xa-expr      xb-expr   nil nil))
         (out-gate     (vl-make-binary-gateinst :vl-xor out-expr     xab-expr     main-expr nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list out-port a-port b-port)
                      :portdecls (list out-portdecl a-portdecl b-portdecl)
                      :netdecls  (list out-netdecl a-netdecl b-netdecl
                                       bbar-netdecl mainbar-netdecl main-netdecl
                                       xa-netdecl xb-netdecl xab-netdecl)
                      :gateinsts (list bbar-gate mainbar-gate main-gate
                                       xa-gate xb-gate xab-gate out-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-n-bit-signed-gte (n)
  :short "Generate a signed greater-than or equal comparison module."

  :long "<p>We generate a gate-based module that is semantically equivalent
to:</p>

<code>
module VL_N_BIT_SIGNED_GTE (out, a, b) ;
  output out;
  input signed [n-1:0] a;
  input signed [n-1:0] b;
  assign out = a &gt;= b;
endmodule
</code>

<p>We just do the stupidest thing possible and do cases on the sign bit:</p>

<ul>
 <li>A positive, B positive: unsigned comparison of a &gt;= b</li>
 <li>A positive, B negative: 1 since positives &gt; negatives</li>
 <li>A negative, B positive: 0 since negatives &lt; positives</li>
 <li>A negative, B negative: unsigned comparison of a &gt;= b</li>
</ul>

<p>The middle two cases would ordinarily fool an unsigned comparison, e.g., if
A is positive and B is negative, then their leading bits are 0 and 1,
respectively, so B \"looks bigger\" even though A is actually bigger.  But
ordinary unsigned comparisons work in the other cases.</p>"

  :guard (posp n)
  :body
  (b* (((when (= n 1))
        (list *vl-1-bit-signed-gte*))

       (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_SIGNED_GTE")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input n))

       ((mv sdiff-expr sdiff-netdecl) (vl-occform-mkwire "signs_differ" 1))  ;; do signs differ?
       ((mv adiff-expr adiff-netdecl) (vl-occform-mkwire "ans_differ" 1))    ;; answer when signs differ
       ((mv asame-expr asame-netdecl) (vl-occform-mkwire "ans_same" 1))      ;; answer when signs are the same
       ((mv main-expr main-netdecl)   (vl-occform-mkwire "main" 1))          ;; final answer except for x detection

       (a-msb  (vl-make-bitselect a-expr (- n 1)))
       (b-msb  (vl-make-bitselect b-expr (- n 1)))
       (a-tail (vl-make-partselect a-expr (- n 2) 0))
       (b-tail (vl-make-partselect b-expr (- n 2) 0))

       ;; xor(signs_differ, a[n-1], b[n-1]);
       (sdiff-gate (vl-make-binary-gateinst :vl-xor sdiff-expr a-msb b-msb nil nil))

       ;; not(ans_differ, a[n-1]);    --- explanation:
       ;;
       ;;      a_msb     b_msb    answer
       ;;        0         1        a positive, b negative, answer is 1
       ;;        1         0        a negative, b positive, answer is 0
       (adiff-gate (vl-make-unary-gateinst :vl-not adiff-expr a-msb nil nil))

       ;; BOZO would be nice to have a GTE_CORE that doesn't do X detection.  Currently
       ;; this core will do its own X-detection unnecessarily.

       ;; VL_{N-1}_BIT_UNSIGNED_GTE core (ans_same, a[n-2:0], b[n-2:0]);
       ((cons ucmp-mod ucmp-support) (vl-make-n-bit-unsigned-gte (- n 1)))
       (ucmp-args (list (make-vl-plainarg :expr asame-expr :dir :vl-output :portname (hons-copy "out"))
                        (make-vl-plainarg :expr a-tail     :dir :vl-input  :portname (hons-copy "a"))
                        (make-vl-plainarg :expr b-tail     :dir :vl-input  :portname (hons-copy "b"))))
       (ucmp-inst (make-vl-modinst :modname   (vl-module->name ucmp-mod)
                                   :instname  (hons-copy "core")
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil ucmp-args)
                                   :loc       *vl-fakeloc*))


       ;; VL_1_BIT_MUX mux (main, signs_differ, ans_differ, ans_same);
       ((cons mux-mod mux-support) (vl-make-n-bit-mux 1 t))
       (mux-args (list (make-vl-plainarg :expr main-expr  :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr sdiff-expr :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr adiff-expr :dir :vl-input  :portname (hons-copy "a"))
                       (make-vl-plainarg :expr asame-expr :dir :vl-input  :portname (hons-copy "b"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name mux-mod)
                                  :instname  (hons-copy "mux")
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*))

       ;; VL_N_BY_1_XPROP xprop (out, main, a, b);
       ((cons xprop-mod xprop-support) (vl-make-n-bit-x-propagator n 1))
       (xprop-args (list (make-vl-plainarg :expr out-expr  :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr main-expr :dir :vl-input  :portname (hons-copy "ans"))
                         (make-vl-plainarg :expr a-expr    :dir :vl-input  :portname (hons-copy "a"))
                         (make-vl-plainarg :expr b-expr    :dir :vl-input  :portname (hons-copy "b"))))
       (xprop-inst (make-vl-modinst :modname   (vl-module->name xprop-mod)
                                    :instname  (hons-copy "xprop")
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xprop-args)
                                    :loc       *vl-fakeloc*)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port a-port b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list out-netdecl a-netdecl b-netdecl
                                            sdiff-netdecl adiff-netdecl asame-netdecl main-netdecl)
                           :gateinsts (list sdiff-gate adiff-gate)
                           :modinsts  (list ucmp-inst mux-inst xprop-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           ucmp-mod
           mux-mod
           xprop-mod
           (append mux-support xprop-support ucmp-support))))









