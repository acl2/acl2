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
(include-book "../../util/next-power-of-2")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

; gen-select.lisp -- functions that generate dynamic bit-select modules


(defsection *vl-1-bit-dynamic-bitselect*
  :parents (occform)
  :short "Degenerate 1-bit dynamic bit-selection module."

  :long "<p>The module <tt>VL_1_BIT_DYNAMIC_BITSELECT(out, in, idx)</tt>
implements <tt>assign out = in[idx]</tt> in the (essentially degenerate) case
that <tt>in</tt> is only one-bit wide, and <tt>idx</tt> is only one-bit wide:
if <tt>idx</tt> is zero, we return <tt>in</tt>, otherwise the index is
out-of-bounds and X is returned.</p>

<code>
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
</code>"

  (defconst *vl-1-bit-dynamic-bitselect*
    (b* ((name (hons-copy "VL_1_BIT_DYNAMIC_BITSELECT"))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in"  :vl-input 1))
         ((mv idx-expr idx-port idx-portdecl idx-netdecl) (vl-occform-mkport "idx" :vl-input 1))

         ((mv ~idx-expr ~idx-netdecl) (vl-occform-mkwire "idx_bar" 1))
         ((mv a-expr a-netdecl)       (vl-occform-mkwire "a" 1))
         ((mv b-expr b-netdecl)       (vl-occform-mkwire "b" 1))

         (~idx-gate (vl-make-unary-gateinst  :vl-not ~idx-expr idx-expr                   nil nil))
         (a-gate    (vl-make-binary-gateinst :vl-and a-expr    ~idx-expr in-expr          nil nil))
         (b-gate    (vl-make-binary-gateinst :vl-and b-expr    idx-expr  |*sized-1'bx*|   nil nil))
         (out-gate  (vl-make-binary-gateinst :vl-or  out-expr  a-expr    b-expr           nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list out-port in-port idx-port)
                      :portdecls (list out-portdecl in-portdecl idx-portdecl)
                      :netdecls  (list out-netdecl in-netdecl idx-netdecl ~idx-netdecl a-netdecl b-netdecl)
                      :gateinsts (list ~idx-gate a-gate b-gate out-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(defsection *vl-2-bit-dynamic-bitselect*
  :parents (occform)
  :short "Primitive dynamic bit-selection module."

  :long "<p><tt>VL_2_BIT_DYNAMIC_BITSELECT(out, in, idx)</tt> conservatively
approximates <tt>out = in[idx]</tt> and is used to implement bit-selects where
the index is not fixed.  Its Verilog definition is as follows:</p>

<code>
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
</code>

<p>The only place we this inexactly approximates the real Verilog semantics is
when <tt>in</tt> contains Z's.  In Verilog, such a Z can be selected and
returned, but in our module X is returned instead.  Actually this seems good --
our behavior probably more closely corresponds to what real hardware would do
for a dynamic bit-select, anyway.</p>

<p>The XOR gates at the end are needed to obtain this X behavior.  Without
them, in cases where <tt>in[1] === in[0]</tt>, we might return 0 or 1 even when
idx is <tt>X</tt>.  This wouldn't be okay: the Verilog specification mandates
that if any bit of <tt>idx</tt> is <tt>X</tt>, then <tt>X</tt> is returned from
the bit select.</p>"

  (defconst *vl-2-bit-dynamic-bitselect*
    (b* ((name (hons-copy "VL_2_BIT_DYNAMIC_BITSELECT"))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input 2))
         ((mv idx-expr idx-port idx-portdecl idx-netdecl) (vl-occform-mkport "idx" :vl-input 1))

         ((mv ~idx-expr ~idx-netdecl)   (vl-occform-mkwire "idx_bar" 1))
         ((mv idx_x-expr idx_x-netdecl) (vl-occform-mkwire "idx_x" 1))
         ((mv a-expr a-netdecl)         (vl-occform-mkwire "a" 1))
         ((mv b-expr b-netdecl)         (vl-occform-mkwire "b" 1))
         ((mv main-expr main-netdecl)   (vl-occform-mkwire "main" 1))

         (in[0]-expr  (vl-make-bitselect in-expr 0))
         (in[1]-expr  (vl-make-bitselect in-expr 1))

         ;; not (idx_bar, idx);
         ;; and (a, idx, in[1]) ;
         ;; and (b, idx_bar, in[0]) ;
         ;; or (main, a, b) ;
         ;; xor (idx_x, idx, idx);
         ;; xor (out, idx_x, main);
         (~idx-gate  (vl-make-unary-gateinst  :vl-not ~idx-expr  idx-expr              nil nil))
         (a-gate     (vl-make-binary-gateinst :vl-and a-expr     idx-expr   in[1]-expr nil nil))
         (b-gate     (vl-make-binary-gateinst :vl-and b-expr     ~idx-expr  in[0]-expr nil nil))
         (main-gate  (vl-make-binary-gateinst :vl-or  main-expr  a-expr     b-expr     nil nil))
         (idx_x-gate (vl-make-binary-gateinst :vl-xor idx_x-expr idx-expr   idx-expr   nil nil))
         (out-gate   (vl-make-binary-gateinst :vl-xor out-expr   idx_x-expr main-expr  nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list out-port in-port idx-port)
                      :portdecls (list out-portdecl in-portdecl idx-portdecl)
                      :netdecls  (list out-netdecl in-netdecl idx-netdecl
                                       ~idx-netdecl a-netdecl b-netdecl main-netdecl
                                       idx_x-netdecl)
                      :gateinsts (list ~idx-gate a-gate b-gate main-gate idx_x-gate out-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(def-vl-modgen vl-make-2^n-bit-dynamic-bitselect (n)
  :short "Generates a dynamic bit-selection module for wire widths that are
powers of 2."

  :long "<p>We construct <tt>VL_{2^N}_BIT_DYNAMIC_BITSELECT(out, in, idx)</tt>,
a conservative approximation of <tt>out = in[idx]</tt> where <tt>in</tt> has
width <tt>2^N</tt>.  We generate this module inductively/recursively by using
smaller selectors.</p>

<p>As a basis, when N is 0 or 1, we use the 1-bit or 2-bit selectors that we
pre-define; see @(see *vl-1-bit-dynamic-bitselect*) and @(see
*vl-2-bit-dynamic-bitselect*).</p>

<p>When <tt>N &gt; 1</tt>, let <tt>M</tt> be <tt>2^N</tt> and <tt>K</tt> be
<tt>2^(N-1)</tt>.  We define <tt>VL_M_BIT_DYNAMIC_BITSELECT</tt> in Verilog as
follows:</p>

<code>
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
</code>"

  :guard (natp n)
  :verify-guards nil
  :body
  (b* (((when (zp n))
        (list *vl-1-bit-dynamic-bitselect*))
       ((when (= n 1))
        (list *vl-2-bit-dynamic-bitselect*))

       (m (expt 2 n))
       (k (expt 2 (1- n)))

       (submods (vl-make-2^n-bit-dynamic-bitselect (- n 1)))
       (name (hons-copy (str::cat "VL_" (str::natstr m) "_BIT_DYNAMIC_BITSELECT")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input m))
       ((mv idx-expr idx-port idx-portdecl idx-netdecl) (vl-occform-mkport "idx" :vl-input n))

       ((mv high-expr high-netdecl)   (vl-occform-mkwire "high" 1))
       ((mv low-expr low-netdecl)     (vl-occform-mkwire "low" 1))
       ((mv ~idx-expr ~idx-netdecl)   (vl-occform-mkwire "idx_bar" 1))
       ((mv a-expr a-netdecl)         (vl-occform-mkwire "a" 1))
       ((mv b-expr b-netdecl)         (vl-occform-mkwire "b" 1))
       ((mv main-expr main-netdecl)   (vl-occform-mkwire "main" 1))
       ((mv idx_x-expr idx_x-netdecl) (vl-occform-mkwire "idx_x" 1))

       (|in[m-1]:k|  (vl-make-partselect in-expr (- m 1) k))
       (|in[k-1:0]|  (vl-make-partselect in-expr (- k 1) 0))
       (idx[n-1]     (vl-make-bitselect  idx-expr (- n 1)))
       (|idx[n-2:0]| (vl-make-partselect idx-expr (- n 2) 0))

       ;; VL_K_BIT_DYNAMIC_BITSELECT mk_high (high, in[m-1]:k, idx[N-2:0]);
       ;; VL_K_BIT_DYNAMIC_BITSELECT mk_low (low, in[K-1:0], idx[N-2:0]);

       (high-args    (list (make-vl-plainarg :expr high-expr    :dir :vl-output :portname (hons-copy "out"))
                           (make-vl-plainarg :expr |in[m-1]:k|  :dir :vl-input  :portname (hons-copy "in"))
                           (make-vl-plainarg :expr |idx[n-2:0]| :dir :vl-input  :portname (hons-copy "idx"))))
       (high-inst    (make-vl-modinst :instname  (hons-copy "mk_high")
                                      :modname   (vl-module->name (car submods))
                                      :paramargs (vl-arguments nil nil)
                                      :portargs  (vl-arguments nil high-args)
                                      :loc       *vl-fakeloc*))

       (low-args    (list (make-vl-plainarg :expr low-expr     :dir :vl-output :portname (hons-copy "out"))
                          (make-vl-plainarg :expr |in[k-1:0]|  :dir :vl-input  :portname (hons-copy "in"))
                          (make-vl-plainarg :expr |idx[n-2:0]| :dir :vl-input  :portname (hons-copy "idx"))))
       (low-inst    (make-vl-modinst :instname  (hons-copy "mk_low")
                                     :modname   (vl-module->name (car submods))
                                     :paramargs (vl-arguments nil nil)
                                     :portargs  (vl-arguments nil low-args)
                                     :loc       *vl-fakeloc*))

       ;; not (idx_bar, idx[N-1]);
       ;; and (a, idx[N-1], high) ;
       ;; and (b, idx_bar, low) ;
       ;; or (main, a, b) ;
       ;; xor (idx_x, idx[N-1], idx[N-1]);
       ;; xor (out, idx_x, main);

       (~idx-gate  (vl-make-unary-gateinst  :vl-not ~idx-expr  idx[n-1]             nil nil))
       (a-gate     (vl-make-binary-gateinst :vl-and a-expr     idx[n-1]   high-expr nil nil))
       (b-gate     (vl-make-binary-gateinst :vl-and b-expr     ~idx-expr  low-expr  nil nil))
       (main-gate  (vl-make-binary-gateinst :vl-or  main-expr  a-expr     b-expr    nil nil))
       (idx_x-gate (vl-make-binary-gateinst :vl-xor idx_x-expr idx[n-1]   idx[n-1]  nil nil))
       (out-gate   (vl-make-binary-gateinst :vl-xor out-expr   idx_x-expr main-expr nil nil)))

    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port idx-port)
                          :portdecls (list out-portdecl in-portdecl idx-portdecl)
                          :netdecls  (list out-netdecl in-netdecl idx-netdecl high-netdecl low-netdecl
                                           ~idx-netdecl a-netdecl b-netdecl main-netdecl idx_x-netdecl)
                          :modinsts  (list high-inst low-inst)
                          :gateinsts (list ~idx-gate a-gate b-gate main-gate idx_x-gate out-gate)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          submods)))

(verify-guards vl-make-2^n-bit-dynamic-bitselect)

;(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 0))
;(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 1))
;(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 2))
;(vl-pps-modulelist (vl-make-2^n-bit-dynamic-bitselect 3))



(local (defthm crock
         (implies (and (posp n)
                       (not (equal n (expt 2 (next-power-of-2 n)))))
                  (posp (next-power-of-2 n)))
         :hints(("Goal" :in-theory (enable next-power-of-2)))))


(def-vl-modgen vl-make-n-bit-dynamic-bitselect (n)
  :short "Generate a basic dynamic bit-selection module."

  :long "<p>We construct <tt>VL_N_BIT_DYNAMIC_BITSELECT(out, in, idx)</tt>, a
conservative approximation of <tt>out = in[idx]</tt> where <tt>in</tt> has
width <tt>N</tt> and <tt>idx</tt> has the minimum width necessary to select
from N bits.  In particular, the width of <tt>idx</tt> is the smallest number W
such that N &lt;= 2^W.</p>

<p>When <tt>N</tt> is a power of 2, we simply construct the desired module
using @(see vl-make-2^n-bit-dynamic-bitselect).</p>

<p>Otherwise, the basic strategy is to instantiate the next biggest power
of 2, and then pad <tt>in</tt> with however many X bits are necessary to
obtain an input of this larger size.  As an example, we implement a 6-bit
select by using an 8-bit select as follows:</p>

<code>
module VL_6_BIT_DYNAMIC_BITSELECT(out, in, idx) ;

   output out;
   input [5:0] in;
   input [2:0] idx;

   VL_8_BIT_DYNAMIC_BITSELECT core(out, {2'bxx, in}, idx);

endmodule
</code>"

  :guard (posp n)
  :body
  (b* ( ;; bitlength = min { M : n <= 2^M }
       (bitlength   (next-power-of-2 n))
       (2^bitlength (expt 2 bitlength))

       (coremods (vl-make-2^n-bit-dynamic-bitselect bitlength))
       ((when (= 2^bitlength n))
        ;; Powers of 2 -- don't need to do anything padding, just use the 2^n
        ;; modules directly.
        coremods)

       (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_DYNAMIC_BITSELECT")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))
       ((mv idx-expr idx-port idx-portdecl idx-netdecl) (vl-occform-mkport "idx" :vl-input bitlength))

       ;; pad-expr = { (2^bitlen-n)'bxxx...xxx, in }
       (padlen        (- 2^bitlength n))
       (|padlen'bxxx| (make-vl-atom :guts (make-vl-weirdint :bits (repeat :vl-xval padlen)
                                                            :origwidth padlen :origtype :vl-unsigned)
                                    :finalwidth padlen
                                    :finaltype :vl-unsigned))
       (pad-expr      (make-vl-nonatom :op :vl-concat
                                       :args (list |padlen'bxxx| in-expr)
                                       :finalwidth 2^bitlength
                                       :finaltype :vl-unsigned))

       ;; VL_{2^bitlength}_BIT_DYNAMIC_BITSELECT core(out, pad-expr, idx);
       (inst-args (list (make-vl-plainarg :expr out-expr :dir :vl-output)
                        (make-vl-plainarg :expr pad-expr :dir :vl-input)
                        (make-vl-plainarg :expr idx-expr :dir :vl-input)))
       (inst (make-vl-modinst :instname  "core"
                              :modname   (vl-module->name (car coremods))
                              :paramargs (vl-arguments nil nil)
                              :portargs  (vl-arguments nil inst-args)
                              :loc       *vl-fakeloc*)))
    (cons (make-vl-module :name      name
                          :origname  name
                          :ports     (list out-port in-port idx-port)
                          :portdecls (list out-portdecl in-portdecl idx-portdecl)
                          :netdecls  (list out-netdecl in-netdecl idx-netdecl)
                          :modinsts  (list inst)
                          :minloc    *vl-fakeloc*
                          :maxloc    *vl-fakeloc*)
          coremods)))


;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 1))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 2))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 3))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 4))
;; (vl-pps-modulelist (vl-make-n-bit-dynamic-bitselect 75))



(def-vl-modgen vl-make-n-bit-dynamic-bitselect-m (n m)
   :short "Generate a dynamic bit-selection module for an N bit wire and an M
bit select."

   :long "<p>We produce <tt>VL_N_BIT_DYNAMIC_BITSELECT_M(out, in, idx)</tt>, a
conservative approximation of <tt>out = in[idx]</tt> where <tt>in</tt> has
width <tt>N</tt> and <tt>idx</tt> has width <tt>M</tt>.</p>

<p>Prerequisite: see @(see vl-make-n-bit-dynamic-bitselect), which can be used
to introduce a module <tt>VL_N_BIT_DYNAMIC_BITSELECT(out, in, idx)</tt>, where
<tt>in</tt> has width <tt>N</tt> and <tt>idx</tt> has width <tt>W</tt> where W
is the the smallest number W such that N &lt;= 2^W.</p>

<p>The problem with just using <tt>VL_N_BIT_DYNAMIC_BITSELECT</tt> directly to
synthesize expressions of the form <tt>in[idx]</tt> is that, in practice, the
width of <tt>idx</tt> may be smaller or larger than W.  When smaller, we need
to pad it with zeros.  When larger, we need to do additional out-of-bounds
checking.</p>"

; BOZO consider adding a warning when M > K.  The user could chop down the
; index to be the right number of bits.

   :guard (and (posp n) (posp m))
   :body
   (b* ((coremods  (vl-make-n-bit-dynamic-bitselect n))
        (coremod   (car coremods))

        ;; K is the width of the "index" port on our core module.  We could
        ;; probably clean this up and prove that it's equal to something or
        ;; other.
        (k (b* ((portdecls (vl-module->portdecls coremod))
                (idx       (vl-find-portdecl "idx" portdecls))
                ((unless idx) ;; Should never happen
                 (er hard? 'vl-make-n-bit-dynamic-bitselect "coremod has no index port?")
                 m)
                (range    (vl-portdecl->range idx))
                ((unless (vl-maybe-range-resolved-p range)) ;; Should never happen
                 (er hard? 'vl-make-n-bit-dynamic-bitselect "coremod index range not resolved?")
                 m))
             (vl-maybe-range-size range)))

        ((when (= k m))
         ;; No need to do anything special, the width of the select is already
         ;; correct.
         coremods)

        ;; Else, we need a new module.
        (name (str::cat "VL_" (str::natstr n) "_BIT_DYNAMIC_BITSELECT_" (str::natstr m)))

        ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
        ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input n))
        ((mv idx-expr idx-port idx-portdecl idx-netdecl) (vl-occform-mkport "idx" :vl-input m))

        ((when (< k m))
         ;; Case 1.  Our idx port is larger than the idx port on the core
         ;; module.  Need to (1) chop it down and send only the least
         ;; significant bits into the core module, and (2) return X when any of
         ;; the high bits are nonzero.
         (b* ((lowbits  (vl-make-partselect idx-expr (- k 1) 0)) ;; idx[k-1:0], width k
              (highbits (vl-make-partselect idx-expr (- m 1) k)) ;; idx[m-1:k], width m-k

              ;; wire main = in[lowbits];
              ;; VL_N_BIT_DYNAMIC_BITSELECT core (main, in, lowbits);
              ((mv main-expr main-netdecl) (vl-occform-mkwire "main" 1))
              (core-args (list (make-vl-plainarg :expr main-expr :dir :vl-output :portname (hons-copy "out"))
                               (make-vl-plainarg :expr in-expr   :dir :vl-input  :portname (hons-copy "in"))
                               (make-vl-plainarg :expr lowbits   :dir :vl-input  :portname (hons-copy "idx"))))
              (core-inst (make-vl-modinst :modname   (vl-module->name (car coremods))
                                          :instname  (hons-copy "core")
                                          :paramargs (vl-arguments nil nil)
                                          :portargs  (vl-arguments nil core-args)
                                          :loc       *vl-fakeloc*))

              ;; wire any_extra = |highbits;
              ((cons extra-mod extra-support) (vl-make-n-bit-reduction-op :vl-unary-bitor (- m k)))
              ((mv extra-expr extra-netdecl) (vl-occform-mkwire "any_extra" 1))
              (extra-args (list (make-vl-plainarg :expr extra-expr :dir :vl-output :portname (hons-copy "out"))
                                (make-vl-plainarg :expr highbits   :dir :vl-input  :portname (hons-copy "in"))))
              (extra-inst (make-vl-modinst :modname   (vl-module->name extra-mod)
                                           :instname  (hons-copy "mk_any_extra")
                                           :paramargs (vl-arguments nil nil)
                                           :portargs  (vl-arguments nil extra-args)
                                           :loc       *vl-fakeloc*))

              ;; this is effectively out = any_extra ? 1'bx : main;
              ;;
              ;; wire a, b, no_extra;
              ;; not(no_extra, any_extra);
              ;; and(a, no_extra, main);
              ;; and(b, any_extra, 1'bx);
              ;; or(out, a, b);
              ((mv noextra-expr noextra-netdecl) (vl-occform-mkwire "no_extra" 1))
              ((mv a-expr a-netdecl) (vl-occform-mkwire "a" 1))
              ((mv b-expr b-netdecl) (vl-occform-mkwire "b" 1))
              (noextra-gate (vl-make-unary-gateinst  :vl-not noextra-expr extra-expr                   nil nil))
              (a-gate       (vl-make-binary-gateinst :vl-and a-expr       noextra-expr main-expr       nil nil))
              (b-gate       (vl-make-binary-gateinst :vl-and b-expr       extra-expr   |*sized-1'bx*|  nil nil))
              (out-gate     (vl-make-binary-gateinst :vl-or  out-expr     a-expr       b-expr          nil nil))

              (mod (make-vl-module :name      name
                                   :origname  name
                                   :ports     (list out-port in-port idx-port)
                                   :portdecls (list out-portdecl in-portdecl idx-portdecl)
                                   :netdecls  (list out-netdecl in-netdecl idx-netdecl main-netdecl extra-netdecl
                                                    noextra-netdecl a-netdecl b-netdecl)
                                   :gateinsts (list noextra-gate a-gate b-gate out-gate)
                                   :modinsts  (list core-inst extra-inst)
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
        (core-args    (list (make-vl-plainarg :expr out-expr   :dir :vl-output :portname (hons-copy "out"))
                            (make-vl-plainarg :expr in-expr    :dir :vl-input  :portname (hons-copy "in"))
                            (make-vl-plainarg :expr padded-idx :dir :vl-input  :portname (hons-copy "idx"))))
        (core-inst    (make-vl-modinst :instname  (hons-copy "core")
                                       :modname   (vl-module->name (car coremods))
                                       :paramargs (vl-arguments nil nil)
                                       :portargs  (vl-arguments nil core-args)
                                       :loc       *vl-fakeloc*)))

     (cons (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port idx-port)
                           :portdecls (list out-portdecl in-portdecl idx-portdecl)
                           :netdecls  (list out-netdecl in-netdecl idx-netdecl)
                           :modinsts  (list core-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
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

