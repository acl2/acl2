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
(include-book "simple")
(include-book "centaur/vl2014/util/next-power-of-2" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))
(local (non-parallel-book))

(defval *vl-1-bit-dynamic-bitselect*
  :parents (occform)
  :short "Degenerate 1-bit dynamic bit-selection module."

  :long "<p>The module @('VL_1_BIT_DYNAMIC_BITSELECT(out, in, idx)') implements
@('assign out = in[idx]') in the (essentially degenerate) case that @('in') is
only one-bit wide, and @('idx') is only one-bit wide: if @('idx') is zero, we
return @('in'), otherwise the index is out-of-bounds and X is returned.</p>

@({
module VL_1_BIT_DYNAMIC_BITSELECT (out, in, idx);

  output out;
  input in;
  input idx;

  wire idx_bar;
  wire a;
  wire b;

  not(idx_bar, idx);
  and(a, idx_bar, in);
  and(b, idx, 1'bx);
  or(out, a, b);

endmodule
})"

  (b* ((name (hons-copy "VL_1_BIT_DYNAMIC_BITSELECT"))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-primitive-mkport "in"  :vl-input))
       ((mv idx-expr idx-port idx-portdecl idx-vardecl) (vl-primitive-mkport "idx" :vl-input))

       ((mv ~idx-expr ~idx-vardecl) (vl-primitive-mkwire "idx_bar"))
       ((mv a-expr a-vardecl)       (vl-primitive-mkwire "a"))
       ((mv b-expr b-vardecl)       (vl-primitive-mkwire "b"))

       (~idx-inst (vl-simple-inst *vl-1-bit-not* "mk_idx_bar" ~idx-expr idx-expr))
       (a-inst    (vl-simple-inst *vl-1-bit-and* "mk_a"       a-expr    ~idx-expr in-expr))
       (b-inst    (vl-simple-inst *vl-1-bit-and* "mk_b"       b-expr    idx-expr  |*sized-1'bx*|))
       (out-inst  (vl-simple-inst *vl-1-bit-or*  "mk_out"     out-expr  a-expr    b-expr)))

    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port in-port idx-port)
                     :portdecls (list out-portdecl in-portdecl idx-portdecl)
                     :vardecls  (list out-vardecl in-vardecl idx-vardecl ~idx-vardecl a-vardecl b-vardecl)
                     :modinsts  (list ~idx-inst a-inst b-inst out-inst)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*))))


(defval *vl-2-bit-dynamic-bitselect*
  :parents (occform)
  :short "Primitive dynamic bit-selection module."

  :long "<p>@('VL_2_BIT_DYNAMIC_BITSELECT(out, in, idx)') conservatively
approximates @('out = in[idx]') and is used to implement bit-selects where the
index is not fixed.  Its Verilog definition is as follows:</p>

@({
module VL_2_BIT_DYNAMIC_BITSELECT (out, in, idx) ;

   output out;
   input [1:0] in;
   input idx;

   wire idx_bar;
   wire idx_x;
   wire a;
   wire b;
   wire main;

   // Choose in[0] or in[1] based on idx

   not (idx_bar, idx);
   and (a, idx, in[1]) ;
   and (b, idx_bar, in[0]) ;
   or  (main, a, b) ;

   // Make sure we emit X if idx is X/Z

   xor (idx_x, idx, idx);
   xor (out, idx_x, main);

endmodule
})

<p>The only place we this inexactly approximates the real Verilog semantics is
when @('in') contains Z's.  In Verilog, such a Z can be selected and returned,
but in our module X is returned instead.  Actually this seems good -- our
behavior probably more closely corresponds to what real hardware would do for a
dynamic bit-select, anyway.</p>

<p>The XOR gates at the end are needed to obtain this X behavior.  Without
them, in cases where @('in[1] === in[0]'), we might return 0 or 1 even when idx
is @('X').  This wouldn't be okay: the Verilog specification mandates that if
any bit of @('idx') is @('X'), then @('X') is returned from the bit
select.</p>"

  (b* ((name (hons-copy "VL_2_BIT_DYNAMIC_BITSELECT"))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport   "in"  :vl-input 2))
       ((mv idx-expr idx-port idx-portdecl idx-vardecl) (vl-primitive-mkport "idx" :vl-input))

       ((mv ~idx-expr ~idx-vardecl)   (vl-primitive-mkwire "idx_bar"))
       ((mv idx_x-expr idx_x-vardecl) (vl-primitive-mkwire "idx_x"))
       ((mv a-expr a-vardecl)         (vl-primitive-mkwire "a"))
       ((mv b-expr b-vardecl)         (vl-primitive-mkwire "b"))
       ((mv main-expr main-vardecl)   (vl-primitive-mkwire "main"))

       (in[0]-expr  (vl-make-bitselect in-expr 0))
       (in[1]-expr  (vl-make-bitselect in-expr 1))

       ;; not (idx_bar, idx);
       ;; and (a, idx, in[1]) ;
       ;; and (b, idx_bar, in[0]) ;
       ;; or (main, a, b) ;
       ;; xor (idx_x, idx, idx);
       ;; xor (out, idx_x, main);
       (~idx-inst  (vl-simple-inst *vl-1-bit-not* "mk_idx_bar" ~idx-expr  idx-expr))
       (a-inst     (vl-simple-inst *vl-1-bit-and* "mk_a"       a-expr     idx-expr   in[1]-expr))
       (b-inst     (vl-simple-inst *vl-1-bit-and* "mk_b"       b-expr     ~idx-expr  in[0]-expr))
       (main-inst  (vl-simple-inst *vl-1-bit-or*  "mk_main"    main-expr  a-expr     b-expr))
       (idx_x-inst (vl-simple-inst *vl-1-bit-xor* "mk_idx_x"   idx_x-expr idx-expr   idx-expr))
       (out-inst   (vl-simple-inst *vl-1-bit-xor* "mk_out"     out-expr   idx_x-expr main-expr)))

    (hons-copy
     (make-vl-module :name      name
                     :origname  name
                     :ports     (list out-port in-port idx-port)
                     :portdecls (list out-portdecl in-portdecl idx-portdecl)
                     :vardecls  (list out-vardecl in-vardecl idx-vardecl
                                      ~idx-vardecl a-vardecl b-vardecl main-vardecl
                                      idx_x-vardecl)
                     :modinsts (list ~idx-inst a-inst b-inst main-inst idx_x-inst out-inst)
                     :minloc    *vl-fakeloc*
                     :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-2^n-bit-dynamic-bitselect ((n natp))
  :short "Generates a dynamic bit-selection module for wire widths that are
powers of 2."

  :long "<p>We construct @('VL_{2^N}_BIT_DYNAMIC_BITSELECT(out, in, idx)'), a
conservative approximation of @('out = in[idx]') where @('in') has width
@('2^N').  We generate this module inductively/recursively by using smaller
selectors.</p>

<p>As a basis, when N is 0 or 1, we use the 1-bit or 2-bit selectors that we
pre-define; see @(see *vl-1-bit-dynamic-bitselect*) and @(see
*vl-2-bit-dynamic-bitselect*).</p>

<p>When @('N > 1'), let @('M') be @('2^N') and @('K') be @('2^(N-1)').  We
define @('VL_M_BIT_DYNAMIC_BITSELECT') in Verilog as follows:</p>

@({
module VL_M_BIT_DYNAMIC_BITSELECT(out, in, idx) ;

   output out;
   input [M-1:0] in;
   input [N-1:0] idx;

   wire high; // result assuming idx[N-1] is high
   wire low;  // result assuming idx[N-1] is low

   VL_K_BIT_DYNAMIC_BITSELECT mk_high (high, in[M-1:K], idx[N-2:0]);
   VL_K_BIT_DYNAMIC_BITSELECT mk_low  (low,  in[K-1:0], idx[N-2:0]);

   // Choose high or low, per idx[N-1]

   wire idx_bar;
   wire a;
   wire b;
   wire main;

   not (idx_bar, idx[N-1]);
   and (a, idx[N-1], high) ;
   and (b, idx_bar, low) ;
   or  (main, a, b) ;

   // Fix up main so that if idx[N-1] is X we produce X.

   wire idx_x;
   xor (idx_x, idx[N-1], idx[N-1]);
   xor (out, idx_x, main);

endmodule
})"

  :verify-guards nil
  :body
  (b* (((when (zp n))
        (list *vl-1-bit-dynamic-bitselect*))
       ((when (eql n 1))
        (list *vl-2-bit-dynamic-bitselect*))

       (m (expt 2 n))
       (k (expt 2 (1- n)))

       (submods (vl-make-2^n-bit-dynamic-bitselect (- n 1)))
       (name (hons-copy (cat "VL_" (natstr m) "_BIT_DYNAMIC_BITSELECT")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input m))
       ((mv idx-expr idx-port idx-portdecl idx-vardecl) (vl-occform-mkport "idx" :vl-input n))

       ((mv high-expr high-vardecl)   (vl-primitive-mkwire "high"))
       ((mv low-expr low-vardecl)     (vl-primitive-mkwire "low"))
       ((mv ~idx-expr ~idx-vardecl)   (vl-primitive-mkwire "idx_bar"))
       ((mv a-expr a-vardecl)         (vl-primitive-mkwire "a"))
       ((mv b-expr b-vardecl)         (vl-primitive-mkwire "b"))
       ((mv main-expr main-vardecl)   (vl-primitive-mkwire "main"))
       ((mv idx_x-expr idx_x-vardecl) (vl-primitive-mkwire "idx_x"))

       (|in[m-1]:k|  (vl-make-partselect in-expr (- m 1) k))
       (|in[k-1:0]|  (vl-make-partselect in-expr (- k 1) 0))
       (idx[n-1]     (vl-make-bitselect  idx-expr (- n 1)))
       (|idx[n-2:0]| (vl-make-partselect idx-expr (- n 2) 0))

       ;; VL_K_BIT_DYNAMIC_BITSELECT mk_high (high, in[m-1]:k, idx[N-2:0]);
       ;; VL_K_BIT_DYNAMIC_BITSELECT mk_low (low, in[K-1:0], idx[N-2:0]);
       (high-inst    (vl-simple-inst (car submods) "mk_high" high-expr |in[m-1]:k| |idx[n-2:0]|))
       (low-inst     (vl-simple-inst (car submods) "mk_low"  low-expr  |in[k-1:0]| |idx[n-2:0]|))

       ;; not (idx_bar, idx[N-1]);
       ;; and (a, idx[N-1], high) ;
       ;; and (b, idx_bar, low) ;
       ;; or (main, a, b) ;
       ;; xor (idx_x, idx[N-1], idx[N-1]);
       ;; xor (out, idx_x, main);

       (~idx-inst  (vl-simple-inst *vl-1-bit-not* "mk_idx_bar" ~idx-expr  idx[n-1]))
       (a-inst     (vl-simple-inst *vl-1-bit-and* "mk_a"       a-expr     idx[n-1]   high-expr))
       (b-inst     (vl-simple-inst *vl-1-bit-and* "mk_b"       b-expr     ~idx-expr  low-expr))
       (main-inst  (vl-simple-inst *vl-1-bit-or*  "mk_main"    main-expr  a-expr     b-expr))
       (idx_x-inst (vl-simple-inst *vl-1-bit-xor* "mk_idx_x"   idx_x-expr idx[n-1]   idx[n-1]))
       (out-inst   (vl-simple-inst *vl-1-bit-xor* "mk_out"     out-expr   idx_x-expr main-expr)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port idx-port)
                           :portdecls (list out-portdecl in-portdecl idx-portdecl)
                           :vardecls  (list out-vardecl in-vardecl idx-vardecl high-vardecl low-vardecl
                                            ~idx-vardecl a-vardecl b-vardecl main-vardecl idx_x-vardecl)
                           :modinsts  (list high-inst low-inst ~idx-inst a-inst b-inst main-inst idx_x-inst out-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           *vl-1-bit-not* *vl-1-bit-and* *vl-1-bit-or* *vl-1-bit-xor*
           submods)))

(verify-guards vl-make-2^n-bit-dynamic-bitselect)

#||
(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 0))
(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 1))
(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 2))
(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 3))
||#



(local (defthm crock
         (implies (and (posp n)
                       (not (equal n (expt 2 (next-power-of-2 n)))))
                  (posp (next-power-of-2 n)))
         :hints(("Goal" :in-theory (enable next-power-of-2)))))


(def-vl-modgen vl-make-n-bit-dynamic-bitselect ((n posp))
  :short "Generate a basic dynamic bit-selection module."

  :long "<p>We construct @('VL_N_BIT_DYNAMIC_BITSELECT(out, in, idx)'), a
conservative approximation of @('out = in[idx]') where @('in') has width @('N')
and @('idx') has the minimum width necessary to select from N bits.  In
particular, the width of @('idx') is the smallest number W such that N &lt;=
2^W.</p>

<p>When @('N') is a power of 2, we simply construct the desired module using
@(see vl-make-2^n-bit-dynamic-bitselect).</p>

<p>Otherwise, the basic strategy is to instantiate the next biggest power of 2,
and then pad @('in') with however many X bits are necessary to obtain an input
of this larger size.  As an example, we implement a 6-bit select by using an
8-bit select as follows:</p>

@({
module VL_6_BIT_DYNAMIC_BITSELECT(out, in, idx) ;

   output out;
   input [5:0] in;
   input [2:0] idx;

   VL_8_BIT_DYNAMIC_BITSELECT core(out, {2'bxx, in}, idx);

endmodule
})"

  :body
  (b* ((n           (lposfix n))
       ;; bitlength = min { M : n <= 2^M }
       (bitlength   (next-power-of-2 n))
       (2^bitlength (expt 2 bitlength))

       (coremods (vl-make-2^n-bit-dynamic-bitselect bitlength))
       ((when (eql 2^bitlength n))
        ;; Powers of 2 -- don't need to do anything padding, just use the 2^n
        ;; modules directly.
        coremods)

       (name (hons-copy (cat "VL_" (natstr n) "_BIT_DYNAMIC_BITSELECT")))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
       ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input n))
       ((mv idx-expr idx-port idx-portdecl idx-vardecl) (vl-occform-mkport "idx" :vl-input bitlength))

       ;; pad-expr = { (2^bitlen-n)'bxxx...xxx, in }
       (padlen        (- 2^bitlength n))
       (|padlen'bxxx| (make-vl-atom :guts (make-vl-weirdint :bits (replicate padlen :vl-xval)
                                                            :origwidth padlen :origtype :vl-unsigned)
                                    :finalwidth padlen
                                    :finaltype :vl-unsigned))
       (pad-expr      (make-vl-nonatom :op :vl-concat
                                       :args (list |padlen'bxxx| in-expr)
                                       :finalwidth 2^bitlength
                                       :finaltype :vl-unsigned))

       ;; VL_{2^bitlength}_BIT_DYNAMIC_BITSELECT core(out, pad-expr, idx);
       (inst (vl-simple-inst (car coremods) "core" out-expr pad-expr idx-expr)))
    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port idx-port)
                          :portdecls (list out-portdecl in-portdecl idx-portdecl)
                          :vardecls  (list out-vardecl in-vardecl idx-vardecl)
                          :modinsts  (list inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          coremods)))


;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 2))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 3))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 4))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 75))


(def-vl-modgen vl-make-n-bit-dynamic-bitselect-m ((n posp)
                                                  (m posp))
   :short "Generate a dynamic bit-selection module for an N bit wire and an M
bit select."

   :long "<p>We produce @('VL_N_BIT_DYNAMIC_BITSELECT_M(out, in, idx)'), a
conservative approximation of @('out = in[idx]') where @('in') has width @('N')
and @('idx') has width @('M').</p>

<p>Prerequisite: see @(see vl-make-n-bit-dynamic-bitselect), which can be used
to introduce a module @('VL_N_BIT_DYNAMIC_BITSELECT(out, in, idx)'), where
@('in') has width @('N') and @('idx') has width @('W') where W is the the
smallest number W such that N &lt;= 2^W.</p>

<p>The problem with just using @('VL_N_BIT_DYNAMIC_BITSELECT') directly to
synthesize expressions of the form @('in[idx]') is that, in practice, the width
of @('idx') may be smaller or larger than W.  When smaller, we need to pad it
with zeros.  When larger, we need to do additional out-of-bounds checking.</p>"

; BOZO consider adding a warning when M > K.  The user could chop down the
; index to be the right number of bits.

   :body
   (b* ((n         (lposfix n))
        (m         (lposfix m))
        (coremods  (vl-make-n-bit-dynamic-bitselect n))
        (coremod   (car coremods))

        ;; K is the width of the "index" port on our core module.  We could
        ;; probably clean this up and prove that it's equal to something or
        ;; other.
        (k (b* ((portdecls (vl-module->portdecls coremod))
                (idx       (vl-find-portdecl "idx" portdecls))
                ((unless idx) ;; Should never happen
                 (raise "coremod has no index port?")
                 m)
                (type    (vl-portdecl->type idx))
                ((unless (eq (vl-datatype-kind type) :vl-coretype))
                 (raise "coremod port isn't a coretype?")
                 m)
                ((vl-coretype type))
                ((unless (and (atom type.udims)
                              (or (atom type.pdims)
                                  (and (atom (cdr type.pdims))
                                       (not (eq (car type.pdims) :vl-unsized-dimension))))))
                 (raise "coremod index unexpected array dims")
                 m)
                (range   (and (consp type.pdims) (car type.pdims)))
                ((unless (vl-maybe-range-resolved-p range)) ;; Should never happen
                 (raise "coremod index range not resolved?")
                 m))
             (vl-maybe-range-size range)))

        ((when (eql k m))
         ;; No need to do anything special, the width of the select is already
         ;; correct.
         coremods)

        ;; Else, we need a new module.
        (name (cat "VL_" (natstr n) "_BIT_DYNAMIC_BITSELECT_" (natstr m)))

        ((mv out-expr out-port out-portdecl out-vardecl) (vl-primitive-mkport "out" :vl-output))
        ((mv in-expr in-port in-portdecl in-vardecl)     (vl-occform-mkport "in" :vl-input n))
        ((mv idx-expr idx-port idx-portdecl idx-vardecl) (vl-occform-mkport "idx" :vl-input m))

        ((when (< k m))
         ;; Case 1.  Our idx port is larger than the idx port on the core
         ;; module.  Need to (1) chop it down and send only the least
         ;; significant bits into the core module, and (2) return X when any of
         ;; the high bits are nonzero.
         (b* ((lowbits  (vl-make-partselect idx-expr (- k 1) 0)) ;; idx[k-1:0], width k
              (highbits (vl-make-partselect idx-expr (- m 1) k)) ;; idx[m-1:k], width m-k

              ;; wire main = in[lowbits];
              ;; VL_N_BIT_DYNAMIC_BITSELECT core (main, in, lowbits);
              ((mv main-expr main-vardecl) (vl-primitive-mkwire "main"))
              (core-inst (vl-simple-inst (car coremods) "core" main-expr in-expr lowbits))

              ;; wire any_extra = |highbits;
              ((cons extra-mod extra-support) (vl-make-n-bit-reduction-op :vl-unary-bitor (- m k)))
              ((mv extra-expr extra-vardecl)  (vl-primitive-mkwire "any_extra"))
              (extra-inst (vl-simple-inst extra-mod "mk_any_extra" extra-expr highbits))

              ;; this is effectively out = any_extra ? 1'bx : main;
              ;;
              ;; wire a, b, no_extra;
              ;; not(no_extra, any_extra);
              ;; and(a, no_extra, main);
              ;; and(b, any_extra, 1'bx);
              ;; or(out, a, b);
              ((mv noextra-expr noextra-vardecl) (vl-primitive-mkwire "no_extra"))
              ((mv a-expr a-vardecl)             (vl-primitive-mkwire "a"))
              ((mv b-expr b-vardecl)             (vl-primitive-mkwire "b"))
              (noextra-inst (vl-simple-inst *vl-1-bit-not* "mk_no_extra" noextra-expr extra-expr))
              (a-inst       (vl-simple-inst *vl-1-bit-and* "mk_a"        a-expr       noextra-expr main-expr))
              (b-inst       (vl-simple-inst *vl-1-bit-and* "mk_b"        b-expr       extra-expr   |*sized-1'bx*|))
              (out-inst     (vl-simple-inst *vl-1-bit-or*  "mk_out"      out-expr     a-expr       b-expr))

              (mod (make-vl-module :name      name
                                   :origname  name
                                   :ports     (list out-port in-port idx-port)
                                   :portdecls (list out-portdecl in-portdecl idx-portdecl)
                                   :vardecls  (list out-vardecl in-vardecl idx-vardecl main-vardecl extra-vardecl
                                                    noextra-vardecl a-vardecl b-vardecl)
                                   :modinsts  (list core-inst extra-inst noextra-inst a-inst b-inst out-inst)
                                   :minloc    *vl-fakeloc*
                                   :maxloc    *vl-fakeloc*)))
           (list* mod extra-mod (append coremods extra-support))))

        ;; Case 2.  k > m.  That is, the index port on the core module is bigger
        ;; than our index port.  That's fine, we just need to pad the index with
        ;; zeroes to make it fit.
        (padsize    (- k m))
        (pad-expr   (make-vl-atom :guts (make-vl-constint :value 0 :origwidth padsize :origtype :vl-unsigned)
                                  :finalwidth padsize :finaltype :vl-unsigned))
        (padded-idx (make-vl-nonatom :op :vl-concat
                                     :args (list pad-expr idx-expr)
                                     :finalwidth k
                                     :finaltype :vl-unsigned))

        ;; VL_N_BIT_DYNAMIC_BITSELECT core (out, in, pad);
        (core-inst (vl-simple-inst (car coremods) "core" out-expr in-expr padded-idx)))

     (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port idx-port)
                           :portdecls (list out-portdecl in-portdecl idx-portdecl)
                           :vardecls  (list out-vardecl in-vardecl idx-vardecl)
                           :modinsts  (list core-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           *vl-1-bit-not* *vl-1-bit-and* *vl-1-bit-or*
           coremods)))

;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 4 2))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 1 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 1 2))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 1 3))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 1 4))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 1 100))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 4 2))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 6 15))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 2 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 3 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 4 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect-m 5 1))

