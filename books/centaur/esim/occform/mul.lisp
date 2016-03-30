; ESIM Symbolic Hardware Simulator
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
(include-book "add")
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))
(local (in-theory (enable acl2::arith-equiv-forwarding)))

(defval *vl-1-bit-mult*
  :parents (occform)
  :short "One-bit multiplier."

  :long "<p>This module implements a one-bit multiply.  Normally you would
think of this as an @('and') gate, but the X-detection semantics are slightly
different: a multiply must emit X whenever either argument is X or Z, whereas,
e.g., @('X & 0') yields @('0').</p>

<p>The actual Verilog definition of this module is as follows.  These gates
precisely implement the Verilog semantics for @('o = a * b') when @('o'),
@('a'), and @('b') are one-bit wide.</p>

@({
module VL_1_BIT_MULT (o, a, b);
  output o;
  input a, b;

  wire p0, x0, x1;

  and (p0, a, b);
  xor (x0, a, b);
  xor (x1, x0, x0);
  xor (o, p0, x1);
endmodule
})"

  (b* ((name (hons-copy "VL_1_BIT_MULT"))

       ((mv o-expr o-port o-portdecl o-vardecl) (vl-primitive-mkport "o" :vl-output))
       ((mv a-expr a-port a-portdecl a-vardecl) (vl-primitive-mkport "a" :vl-input))
       ((mv b-expr b-port b-portdecl b-vardecl) (vl-primitive-mkport "b" :vl-input))

       ((mv p0-expr p0-vardecl) (vl-primitive-mkwire "p0"))
       ((mv x0-expr x0-vardecl) (vl-primitive-mkwire "x0"))
       ((mv x1-expr x1-vardecl) (vl-primitive-mkwire "x1"))

       (p0-inst (vl-simple-inst *vl-1-bit-and* "mk_p0" p0-expr a-expr  b-expr))
       (x0-inst (vl-simple-inst *vl-1-bit-xor* "mk_x0" x0-expr a-expr  b-expr))
       (x1-inst (vl-simple-inst *vl-1-bit-xor* "mk_x1" x1-expr x0-expr x0-expr))
       (o-inst  (vl-simple-inst *vl-1-bit-xor* "mk_o"  o-expr  p0-expr x1-expr)))

    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list o-port a-port b-port)
                     :portdecls (list o-portdecl a-portdecl b-portdecl)
                     :vardecls  (list o-vardecl a-vardecl b-vardecl p0-vardecl x0-vardecl x1-vardecl)
                     :modinsts  (list p0-inst x0-inst x1-inst o-inst)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*))))


;; bozo this all needs to be documented.

(define vl-partprod-insts-aux ((i natp)
                               (n natp))
  :returns (insts vl-modinstlist-p)
  :guard (< i n)
  ;; Create instances that drive pi, the i-th, shifted partial product for an
  ;; n-bit multiplier
  (b* ((i      (lnfix i))
       (n      (lnfix n))
       (p-name (hons-copy (cat "p" (natstr i))))
       (p-expr (vl-idexpr p-name n :vl-unsigned))
       (p-high (vl-make-list-of-bitselects p-expr i (- n 1)))
       (p-low  (if (zp i)
                   nil
                 (vl-make-list-of-bitselects p-expr 0 (- i 1))))

       (a-name (hons-copy "a"))
       (a-expr (vl-idexpr a-name n :vl-unsigned))
       (a[i]   (vl-make-bitselect a-expr i))
       (a-high (replicate (len p-high) a[i]))

       (b-name (hons-copy "b"))
       (b-expr (vl-idexpr b-name n :vl-unsigned))
       (b-bits (vl-make-list-of-bitselects b-expr 0 (- n 1)))
       (b-high (take (len p-high) b-bits))
       (b-low  (replicate (len p-low) |*sized-1'b0*|))

       (ands (vl-simple-inst-list *vl-1-bit-and* (cat "mk_" p-name "_high")
                                  p-high a-high b-high))
       (bufs (vl-simple-inst-list *vl-1-bit-buf* (cat "mk_" p-name "_low")
                                  p-low b-low nil)))
    (revappend ands (reverse bufs))))

(define vl-partprod-insts ((i natp)
                           (n natp))
  :returns (insts vl-modinstlist-p)
  :guard (<= i n)
  :measure (nfix (- (nfix n) (nfix i)))
  ;; Create instances that drive all all pi (0 <= i < n), all partial products
  ;; for an n-bit multiplier
  (if (zp (- (nfix n) (nfix i)))
      nil
    (append (vl-partprod-insts-aux i n)
            (vl-partprod-insts (+ 1 (nfix i)) n))))

(local (defthm l0
         (implies (vl-exprlist-p x)
                  (iff (car (last x))
                       (consp x)))
         :hints(("Goal" :in-theory (enable last)))))

(def-vl-modgen vl-make-n-bit-mult ((n posp))
  :short "Generate an multiplier module."

  :long "<p>We produce @('VL_N_BIT_MULT') for the given @('n'), which is
written using @(see primitives) but is semantically equal to:</p>

@({
module VL_N_BIT_MULT (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [n-1:0] b;
  assign out = a * b;
endmodule
})

<p>We use a naive, sum-of-partial-products style multiplier.  It computes
N (shifted) partial products (using N gates apiece), then sums them together
with @('n-1') instances of an N-bit wide adder circuit.</p>

<p>The semantics of Verilog require that if any bit of @('a') or @('b') is
@('X') or @('Z'), then every bit of the output is @('X').  We implement this
explicitly, which adds a layer of X-detection around the core circuitry.</p>"

  :body
  (b* ((n (lposfix n))
       ((when (eql n 1))
        (list *vl-1-bit-mult* *vl-1-bit-and* *vl-1-bit-xor*))
       (name  (hons-copy (cat "VL_" (natstr n) "_BIT_MULT")))

       ((mv o-expr o-port o-portdecl o-vardecl) (vl-occform-mkport "o" :vl-output n))
       ((mv a-expr a-port a-portdecl a-vardecl) (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-vardecl) (vl-occform-mkport "b" :vl-input n))

       ;; wire [n-1] p0, p1, ...;  // partial products
       ;; wire [n-1] s0, s1, ...;  // sums
       ;; wire c0, c1, ...;        // carry-outs

       ((mv p-exprs p-vardecls) (vl-occform-mkwires "p" 0 n :width n))
       ((mv s-exprs s-vardecls) (vl-occform-mkwires "s" 0 (- n 1) :width n))
       ((mv c-exprs c-vardecls) (vl-occform-mkwires "c" 0 (- n 1) :width 1))

       ;; instances that generate the partial products
       (p-insts    (vl-partprod-insts 0 n))

       ;; adders that sum up the shifted partial products
       ;; the final result ends up in (car (last s-exprs)).

       ;; we do the x-detection on the outside, so we can use adder cores
       ;; instead of full VL_N_BIT_ADDER modules.
       (adder-mods (vl-make-n-bit-adder-core n))
       (adder-mod  (car adder-mods))
       (adders     (vl-simple-inst-list adder-mod "add"
                                        s-exprs
                                        c-exprs

; Subtle!  I originally summed up the partial products in order.  That is, I
; did the adds like this:
;
;    s0 = p0 + p1
;    s1 = s0 + p2
;    s2 = s1 + p3
;    ...
;
; However, the above doesn't agree with the way that GL computes the sum.  To
; correct for this, I now sum them up in the opposite direction, e.g.,
;
;    s0 = p9 + p8  // for a 10-bit multiply
;    s1 = s0 + p7
;    s2 = s1 + p6
;     ...
;
; This isn't any kind of panacea, but it at least means that if you write a
; Verilog module that does assign o = a * b, and you write an ACL2 spec for it
; that also does (let ((o (* a b))) ...), then things basically work and you
; can end up with a trivial problem.  Of course, there's no helping you if you
; write (let ((o (* b a))) ...), instead.

                                        (cons (car (last p-exprs)) (butlast s-exprs 1))
                                        (cdr (rev p-exprs))
                                        (replicate (- n 1) |*sized-1'b0*|)))

       ;; this is the answer except for x-detection
       (ans (car (last s-exprs)))

       ;; generate x-detection stuff.
       (xprop-modules (vl-make-n-bit-x-propagator n n))
       (xprop-mod     (car xprop-modules))
       (xprop-inst    (vl-simple-inst xprop-mod "xprop" o-expr ans a-expr b-expr))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list o-port a-port b-port)
                            :portdecls (list o-portdecl a-portdecl b-portdecl)
                            :vardecls  (list* o-vardecl a-vardecl b-vardecl
                                              (append p-vardecls s-vardecls c-vardecls))
                            :modinsts  (append p-insts adders (list xprop-inst))
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))

    (list* mod
           (cons *vl-1-bit-buf* ;; used in partprod-insts
                 (append adder-mods xprop-modules)))))


#||
(vl-pps-module *vl-1-bit-mult*)
(vl-pps-modulelist (vl-make-n-bit-mult 3))
||#
