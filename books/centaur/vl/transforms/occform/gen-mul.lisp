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

; gen-mul.lisp -- functions that generate multipliers

(defsection *vl-1-bit-mult*
  :parents (occform)
  :short "One-bit multiplier."

  :long "<p>This module implements a one-bit multiply.  Normally you would
think of this as an <tt>and</tt> gate, but the X-detection semantics are
slightly different: a multiply must emit X whenever either argument is X or Z,
whereas, e.g., <tt>X &amp; 0</tt> yields <tt>0</tt>.</p>

<p>The actual Verilog definition of this module is as follows.  These gates
precisely implement the Verilog semantics for <tt>o = a * b</tt> when
<tt>o</tt>, <tt>a</tt>, and <tt>b</tt> are one-bit wide.</p>

<code>
module VL_1_BIT_MULT (o, a, b);
  output o;
  input a, b;

  wire p0, x0, x1;

  and (p0, a, b);
  xor (x0, a, b);
  xor (x1, x0, x0);
  xor (o, p0, x1);
endmodule
</code>"

  (defconst *vl-1-bit-mult*
    (b* ((name (hons-copy "VL_1_BIT_MULT"))

         ((mv o-expr o-port o-portdecl o-netdecl) (vl-occform-mkport "o" :vl-output 1))
         ((mv a-expr a-port a-portdecl a-netdecl) (vl-occform-mkport "a" :vl-input 1))
         ((mv b-expr b-port b-portdecl b-netdecl) (vl-occform-mkport "b" :vl-input 1))

         ((mv p0-expr p0-netdecl) (vl-occform-mkwire "p0" 1))
         ((mv x0-expr x0-netdecl) (vl-occform-mkwire "x0" 1))
         ((mv x1-expr x1-netdecl) (vl-occform-mkwire "x1" 1))

         (p0-gate (vl-make-binary-gateinst :vl-and p0-expr a-expr  b-expr  nil nil))
         (x0-gate (vl-make-binary-gateinst :vl-xor x0-expr a-expr  b-expr  nil nil))
         (x1-gate (vl-make-binary-gateinst :vl-xor x1-expr x0-expr x0-expr nil nil))
         (o-gate  (vl-make-binary-gateinst :vl-xor o-expr  p0-expr x1-expr nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list o-port a-port b-port)
                      :portdecls (list o-portdecl a-portdecl b-portdecl)
                      :netdecls  (list o-netdecl a-netdecl b-netdecl p0-netdecl x0-netdecl x1-netdecl)
                      :gateinsts (list p0-gate x0-gate x1-gate o-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


;; bozo this all needs to be documented.

(defsection vl-mult-netdecls
  ;; wire [range] prefix_i;
  ;; ...
  ;; wire [range] prefix_{n-1};
  (defund vl-mult-netdecls (prefix i n range)
    (declare (xargs :guard (and (stringp prefix)
                                (natp i)
                                (natp n)
                                (<= i n)
                                (vl-maybe-range-p range))
                    :measure (nfix (- (nfix n) (nfix i)))))
    (b* (((when (zp (- (nfix n) (nfix i))))
          nil)
         (name (hons-copy (str::cat prefix (str::natstr i))))
         (decl (make-vl-netdecl :name name
                                :type :vl-wire
                                :range range
                                :loc *vl-fakeloc*)))
      (cons decl (vl-mult-netdecls prefix (+ 1 (nfix i)) n range))))

  (local (in-theory (enable vl-mult-netdecls)))

  (defthm vl-netdecllist-p-of-vl-mult-netdecls
    (implies (and (force (stringp prefix))
                  (force (natp i))
                  (force (natp n))
                  (force (<= i n))
                  (force (vl-maybe-range-p range)))
             (vl-netdecllist-p (vl-mult-netdecls prefix i n range))))

  (defthm len-of-vl-mult-netdecls
    (equal (len (vl-mult-netdecls prefix i n range))
           (nfix (- (nfix n) (nfix i)))))

  (defthm vl-mult-netdecls-under-iff
    (iff (vl-mult-netdecls prefix i n range)
         (posp (- (nfix n) (nfix i))))))


(defsection vl-partprod-gates

  (defund vl-partprod-gates-aux (i n)
    ;; Create gates that drive pi, the i-th, shifted partial product for an
    ;; n-bit multiplier
    (declare (xargs :guard (and (natp i)
                                (natp n)
                                (< i n))))
    (b* ((p-name (hons-copy (str::cat "p" (str::natstr i))))
         (p-expr (vl-idexpr p-name n :vl-unsigned))
         (p-high (vl-make-list-of-bitselects p-expr i (- n 1)))
         (p-low  (if (zp i)
                     nil
                   (vl-make-list-of-bitselects p-expr 0 (- i 1))))

         (a-name (hons-copy "a"))
         (a-expr (vl-idexpr a-name n :vl-unsigned))
         (a[i]   (vl-make-bitselect a-expr i))
         (a-high (repeat a[i] (len p-high)))

         (b-name (hons-copy "b"))
         (b-expr (vl-idexpr b-name n :vl-unsigned))
         (b-bits (vl-make-list-of-bitselects b-expr 0 (- n 1)))
         (b-high (take (len p-high) b-bits))
         (b-low  (repeat |*sized-1'b0*| (len p-low)))

         (ands (vl-make-binary-gateinstlist :vl-and p-high a-high b-high nil))
         (bufs (vl-make-unary-gateinstlist :vl-buf p-low b-low nil)))
      (revappend ands (reverse bufs))))

  (defund vl-partprod-gates (i n)
    ;; Create gates that drive all all pi (0 <= i < n), all partial products
    ;; for an n-bit multiplier
    (declare (xargs :guard (and (natp i)
                                (natp n)
                                (<= i n))
                    :measure (nfix (- (nfix n) (nfix i)))))
    (if (zp (- (nfix n) (nfix i)))
        nil
      (append (vl-partprod-gates-aux i n)
              (vl-partprod-gates (+ 1 (nfix i)) n))))

  (defthm vl-gateinstlist-p-of-vl-partprod-gates-aux
    (implies (and (force (natp i))
                  (force (natp n))
                  (force (< i n)))
             (vl-gateinstlist-p (vl-partprod-gates-aux i n)))
    :hints(("Goal" :in-theory (enable vl-partprod-gates-aux))))

  (defthm vl-gateinstlist-p-of-vl-partprod-gates
    (implies (and (force (natp i))
                  (force (natp n))
                  (force (<= i n)))
             (vl-gateinstlist-p (vl-partprod-gates i n)))
    :hints(("Goal" :in-theory (enable vl-partprod-gates)))))



(defsection vl-mult-adders

  (defund vl-mult-adders (i modname sums couts as bs cins)
    (declare (xargs :guard (and (natp i)
                                (stringp modname)
                                (vl-exprlist-p sums)
                                (vl-exprlist-p couts)
                                (vl-exprlist-p as)
                                (vl-exprlist-p bs)
                                (vl-exprlist-p cins)
                                (same-lengthp sums couts)
                                (same-lengthp sums as)
                                (same-lengthp sums bs)
                                (same-lengthp sums cins))))
    (b* (((when (atom sums))
          nil)
         (instname (hons-copy (str::cat "add" (str::natstr i))))
         (args (list (make-vl-plainarg :expr (car sums)  :dir :vl-output :portname (hons-copy "sum"))
                     (make-vl-plainarg :expr (car couts) :dir :vl-output :portname (hons-copy "cout"))
                     (make-vl-plainarg :expr (car as)    :dir :vl-input  :portname (hons-copy "a"))
                     (make-vl-plainarg :expr (car bs)    :dir :vl-input  :portname (hons-copy "b"))
                     (make-vl-plainarg :expr (car cins)  :dir :vl-input  :portname (hons-copy "cin"))))
         (inst (make-vl-modinst :modname   modname
                                :instname  instname
                                :paramargs (vl-arguments nil nil)
                                :portargs  (vl-arguments nil args)
                                :loc       *vl-fakeloc*)))
      (cons inst
            (vl-mult-adders (+ i 1) modname (cdr sums) (cdr couts) (cdr as) (cdr bs) (cdr cins)))))

  (defthm vl-modinstlist-p-of-vl-mult-adders
    (implies (and (force (natp i))
                  (force (stringp modname))
                  (force (vl-exprlist-p sums))
                  (force (vl-exprlist-p couts))
                  (force (vl-exprlist-p as))
                  (force (vl-exprlist-p bs))
                  (force (vl-exprlist-p cins))
                  (force (same-lengthp sums couts))
                  (force (same-lengthp sums as))
                  (force (same-lengthp sums bs))
                  (force (same-lengthp sums cins)))
             (vl-modinstlist-p (vl-mult-adders i modname sums couts as bs cins)))
    :hints(("Goal" :in-theory (enable vl-mult-adders)))))



(local (defthm len-of-cdr
           (equal (len (cdr x))
                  (if (consp x)
                      (1- (len x))
                    0))))

(def-vl-modgen vl-make-n-bit-mult (n)
  :short "Generate an multiplier module."

  :long "<p>We produce <tt>VL_N_BIT_MULT</tt> for the given <tt>n</tt>, which
is written using gates but is semantically equal to:</p>

<code>
module VL_N_BIT_MULT (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [n-1:0] b;
  assign out = a * b;
endmodule
</code>

<p>We use a naive, sum-of-partial-products style multiplier.  It computes
N (shifted) partial products (using N gates apiece), then sums them together
with <tt>n-1</tt> instances of an N-bit wide adder circuit.</p>

<p>The semantics of Verilog require that if any bit of <tt>a</tt> or <tt>b</tt>
is <tt>X</tt> or <tt>Z</tt>, then every bit of the output is <tt>X</tt>.  We
implement this explicitly, which adds a layer of X-detection around the core
circuitry.</p>"

  :guard (posp n)
  :body
  (b* (((when (= n 1))
        (list *vl-1-bit-mult*))
       (name  (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_MULT")))
       (range (vl-make-n-bit-range n))

       ((mv o-expr o-port o-portdecl o-netdecl) (vl-occform-mkport "o" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl) (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl) (vl-occform-mkport "b" :vl-input n))

       ;; wire [n-1] p0, p1, ...;  // partial products
       ;; wire [n-1] s0, s1, ...;  // sums
       ;; wire c0, c1, ...;        // carry-outs

       (p-netdecls (vl-mult-netdecls "p" 0 n (vl-make-n-bit-range n)))
       (s-netdecls (vl-mult-netdecls "s" 0 (- n 1) range))
       (c-netdecls (vl-mult-netdecls "c" 0 (- n 1) nil))

       (p-exprs    (vl-make-idexpr-list (vl-netdecllist->names p-netdecls) n :vl-unsigned))
       (s-exprs    (vl-make-idexpr-list (vl-netdecllist->names s-netdecls) n :vl-unsigned))
       (c-exprs    (vl-make-idexpr-list (vl-netdecllist->names c-netdecls) 1 :vl-unsigned))

       ;; gates that generate the partial products
       (p-gates    (vl-partprod-gates 0 n))

       ;; adders that sum up the shifted partial products
       ;; the final result ends up in (car (last s-exprs)).

       ;; we do the x-detection on the outside, so we can use adder cores
       ;; instead of full VL_N_BIT_ADDER modules.
       (adder-mods (vl-make-n-bit-adder-core n))
       (adder-mod  (car adder-mods))
       (adders     (vl-mult-adders 0
                                   (vl-module->name adder-mod)
                                   s-exprs
                                   c-exprs
                                   (cons (car p-exprs) (butlast s-exprs 1))
                                   (cdr p-exprs)
                                   (repeat |*sized-1'b0*| (- n 1))))

       ;; this is the answer except for x-detection
       (ans (car (last s-exprs)))

       ;; generate x-detection stuff.
       (xprop-modules (vl-make-n-bit-x-propagator n n))
       (xprop-mod     (car xprop-modules))
       (xprop-args    (list (make-vl-plainarg :expr o-expr :dir :vl-output :portname (hons-copy "out"))
                            (make-vl-plainarg :expr ans    :dir :vl-input  :portname (hons-copy "ans"))
                            (make-vl-plainarg :expr a-expr :dir :vl-input  :portname (hons-copy "a"))
                            (make-vl-plainarg :expr b-expr :dir :vl-input  :portname (hons-copy "b"))))
       (xprop-inst (make-vl-modinst :instname  (hons-copy "xprop")
                                    :modname   (vl-module->name xprop-mod)
                                    :paramargs (vl-arguments nil nil)
                                    :portargs  (vl-arguments nil xprop-args)
                                    :loc       *vl-fakeloc*))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list o-port a-port b-port)
                            :portdecls (list o-portdecl a-portdecl b-portdecl)
                            :netdecls  (list* o-netdecl a-netdecl b-netdecl
                                              (append p-netdecls s-netdecls c-netdecls))
                            :modinsts  (append adders (list xprop-inst))
                            :gateinsts p-gates
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))

    (list* mod (append adder-mods xprop-modules))))


