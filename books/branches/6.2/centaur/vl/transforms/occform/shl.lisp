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
(include-book "xdet")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

(make-event

; Disabling waterfall parallelism because this book allegedly uses memoization
; while performing its proofs.  

 (if (and (ACL2::hons-enabledp state) 
          (f-get-global 'ACL2::parallel-execution-enabled state)) 
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))

(local (defthm car-of-vl-make-list-of-bitselects-under-iff
         (implies (force (vl-expr-p expr))
                  (iff (car (vl-make-list-of-bitselects expr low high))
                       t))
         :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects)))))

(local (defthm vl-maybe-expr-p-of-car-when-vl-exprlist-p
         (implies (vl-exprlist-p x)
                  (vl-maybe-expr-p (car x)))))

(local (defthm len-of-cdr
         (implies (consp x)
                  (equal (len (cdr x))
                         (1- (len x))))))



; Basic idea: a << b is the same as
;
;   temp0 =     a << (b[0] * 2^0)          "place 0"
;   temp1 = temp0 << (b[1] * 2^1)          "place 1"
;   temp2 = temp1 << (b[2] * 2^2)          "place 2"
;   ...

(def-vl-modgen vl-make-n-bit-shl-place-p (n p)
  :short "Generate a module that conditionally shifts an @('N') bit number by
@('2**(P-1)') bits to the left."

  :long "<p>We generate a gate-based module that is semantically equivalent
to:</p>

@({
module VL_N_BIT_SHL_PLACE_P (out, in, shiftp) ;
  output [n-1:0] out;
  input [n-1:0] in;
  input shiftp;

  assign out = shiftp ? (in << 2**(p-1)) : in;

endmodule
})

<p>These \"place shifters\" can be combined to form a full shifter that
operates on O(log_2 n) muxes.</p>"

  :guard (and (posp n) (posp p))
  :body
  (b* ((shift-amount (expt 2 (- p 1)))
       (name  (hons-copy (cat "VL_" (natstr n) "_BIT_SHL_PLACE_" (natstr p))))

       ((mv out-expr out-port out-portdecl out-netdecl)             (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr in-port in-portdecl in-netdecl)                 (vl-occform-mkport "in" :vl-input n))
       ((mv shiftp-expr shiftp-port shiftp-portdecl shiftp-netdecl) (vl-primitive-mkport "shiftp" :vl-input))

       ;; we can only shift as many places as there are bits in n.
       (places      (min n shift-amount))
       (|places'b0| (make-vl-atom :guts (make-vl-constint :value 0
                                                          :origwidth places
                                                          :origtype :vl-unsigned)
                                  :finalwidth places :finaltype :vl-unsigned))

       (shifted-expr
        (if (<= n shift-amount)
            |places'b0|
          ;; {in[(N-1)-places:0], places'b0}
          (make-vl-nonatom :op :vl-concat
                           :args (list (make-vl-nonatom :op :vl-partselect-colon
                                                        :args (list in-expr
                                                                    (vl-make-index (- n (+ 1 places)))
                                                                    (vl-make-index 0))
                                                        :finalwidth (- n places)
                                                        :finaltype :vl-unsigned)
                                       |places'b0|)
                           :finalwidth n
                           :finaltype :vl-unsigned)))

       ;; VL_N_BIT_APPROX_MUX mux(out, shiftp, shifted-expr, in);
       ((cons mux-mod mux-support) (vl-make-n-bit-mux n t))
       (mux-inst (vl-simple-inst mux-mod "mux" out-expr shiftp-expr shifted-expr in-expr)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port in-port shiftp-port)
                           :portdecls (list out-portdecl in-portdecl shiftp-portdecl)
                           :netdecls  (list out-netdecl in-netdecl shiftp-netdecl)
                           :modinsts  (list mux-inst)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           mux-mod
           mux-support)))

#||
(vl-pps-modulelist (vl-make-n-bit-shl-place-p 10 3))
||#

(define vl-make-n-bit-shl-place-ps ((n posp)
                                    (p natp))
  :returns (mv (shift-mods vl-modulelist-p :hyp :fguard)
               (support-mods vl-modulelist-p :hyp :fguard))
  :parents (occform)
  :short "Generate a list of place-shifters, counting down from P to 1."
  (b* (((when (zp p))
        (mv nil nil))
       ((cons car-shifter car-support) (vl-make-n-bit-shl-place-p n p))
       ((mv cdr-shifters cdr-support) (vl-make-n-bit-shl-place-ps n (- p 1))))
    (mv (cons car-shifter cdr-shifters)
        (append car-support cdr-support)))
  ///
  (defmvtypes vl-make-n-bit-shl-place-ps (true-listp true-listp))

  (defthm len-of-vl-make-n-bit-shl-place-ps-0
    (equal (len (mv-nth 0 (vl-make-n-bit-shl-place-ps n p)))
           (nfix p))))


(define vl-make-list-of-netdecls
  ((n        "how many wires to generate"     natp)
   (basename "generate wires like basename_3" stringp)
   (range    "range for each generated wire"  vl-maybe-range-p))
  :returns (wires vl-netdecllist-p :hyp :fguard)
  :parents (occform)
  :short "Generate a list of distinct wires with a particular range."

  (if (zp n)
      nil
    (cons (make-vl-netdecl :name  (cat basename "_" (natstr n))
                           :type  :vl-wire
                           :range range
                           :loc   *vl-fakeloc*)
          (vl-make-list-of-netdecls (- n 1) basename range)))
  ///
  (defthm len-of-vl-make-list-of-netdecls
    (equal (len (vl-make-list-of-netdecls n basename range))
           (nfix n)))

  (defthm consp-of-vl-make-list-of-netdecls
    (iff (vl-make-list-of-netdecls n basename range)
         (posp n))))


(define vl-make-modinsts-for-shl
  ((name-index natp)
   (mods       vl-modulelist-p)
   (outs       vl-exprlist-p)
   (as         vl-exprlist-p)
   (bs         vl-exprlist-p))
  :guard (and (same-lengthp mods outs)
              (same-lengthp mods as)
              (same-lengthp mods bs))
  :returns (insts vl-modinstlist-p :hyp :fguard)
  (b* (((when (atom mods))
        nil)
       (modinst (vl-simple-inst (car mods) (cat "shift_" (natstr name-index))
                                (car outs) (car as) (car bs))))
    (cons modinst
          (vl-make-modinsts-for-shl (+ 1 name-index)
                                    (cdr mods) (cdr outs) (cdr as) (cdr bs))))
  ///
  (defthm len-of-vl-make-modinsts-for-shl
    (equal (len (vl-make-modinsts-for-shl name-index mods outs as bs))
           (len mods))))


(local (defthm l0
         (implies (vl-exprlist-p x)
                  (iff (car (last x))
                       (consp x)))))

(local (defthm l1
         (implies (vl-exprlist-p x)
                  (iff (car (last (rev x)))
                       (consp x)))
         :hints(("Goal"
                 :in-theory (disable l0)
                 :use ((:instance l0 (x (rev x))))))))

(def-vl-modgen vl-make-n-bit-shl-by-m-bits (n m)
  :short "Generate a module that shifts an @('N') bit number left by an @('M')
bit number."

  :long "<p>We generate a gate-based module that is semantically equivalent
to:</p>

@({
module VL_N_BIT_SHL_BY_M_BITS (out, a, b) ;
  output [n-1:0] out;
  input [n-1:0] a;
  input [m-1:0] b;
  assign out = a << b;
endmodule
})"

  :guard (and (posp n)
              (posp m))

  :body
  (b* ((name (hons-copy (cat "VL_" (natstr n) "_BIT_SHL_BY_" (natstr m) "_BITS")))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv a-expr a-port a-portdecl a-netdecl)         (vl-occform-mkport "a" :vl-input n))
       ((mv b-expr b-port b-portdecl b-netdecl)         (vl-occform-mkport "b" :vl-input m))

       ;; We'll have K place-shifters, one that shifts by 2**0, one by 2**1, etc.
       ;; The actual number of shifters is constrained in two ways.
       ;;
       ;;  - We don't need more than 1+log2(n) shifters because A only has N
       ;;    bits so shifting by more than 2**{1+log2(n)} just zeroes out A.
       ;;
       ;;  - We don't need more than M shifters because there are only M bits
       ;;    of B, so there are only M places to consider shifting.
       ;;
       ;; The basic idea is to set:
       ;;
       ;;  wire [n-1:0] temp1 =          a << (b[0] * 2^0);
       ;;  wire [n-1:0] temp2 =     temp_1 << (b[1] * 2^1)
       ;;    ...
       ;;  wire [n-1:0] tempK = temp_{k-1} << (b[k-1] * 2^{k-1})

       (k (min (+ (integer-length n) 1) m))

       ((mv pshift-mods pshift-support) (vl-make-n-bit-shl-place-ps n k))
       (pshift-mods (reverse pshift-mods)) ;; for place_1 ... place_k order

       (temp-netdecls (reverse (vl-make-list-of-netdecls k "temp" (vl-make-n-bit-range n))))      ;; temp_1 ... temp_k
       (temp-exprs    (vl-make-idexpr-list (vl-netdecllist->names temp-netdecls) n :vl-unsigned))
       (last-temp     (car (last temp-exprs)))

       ;; We'll drive the temp wires in a moment.  But first, we'll put in our X
       ;; detection stuff.

       ((cons xdet-mod xdet-support)   (vl-make-n-bit-xdetect m))
       ((cons xeach-mod xeach-support) (vl-make-n-bit-xor-each n))
       (supporting-mods (list* xdet-mod xeach-mod (append xdet-support xeach-support pshift-mods pshift-support)))

       ((mv bx-expr bx-netdecl) (vl-occform-mkwire "bx" 1))
       (bx-modinst  (vl-simple-inst xdet-mod  "mk_bx"  bx-expr  b-expr))
       (out-modinst (vl-simple-inst xeach-mod "mk_out" out-expr bx-expr last-temp))

       ;; The right-hand sides depend on how many bits we have in B.  But
       ;; in either case, much is the same:

       (lhs-exprs (cons a-expr (butlast temp-exprs 1)))
       (b-wires (vl-make-list-of-bitselects b-expr 0 (- m 1)))

       ((when (= m k))
        ;; We have exactly the right number of bits in B, so we can give one
        ;; bit to each shifter.
        (b* ((pshift-insts (vl-make-modinsts-for-shl 1 pshift-mods temp-exprs lhs-exprs b-wires)))
          (cons (make-vl-module :name      name
                                :origname  name
                                :ports     (list out-port a-port b-port)
                                :portdecls (list out-portdecl a-portdecl b-portdecl)
                                :netdecls  (list* out-netdecl a-netdecl b-netdecl bx-netdecl temp-netdecls)
                                :modinsts  (append pshift-insts (list bx-modinst out-modinst))
                                :minloc    *vl-fakeloc*
                                :maxloc    *vl-fakeloc*)
                supporting-mods)))

       ;; Otherwise, m > k.  We want to take the upper bits of B and xor them
       ;; all together for use in the final shift.  If any of them is high, we
       ;; get a zero.

       ;; wire merged_high = |(b[m-1:k-1]);
       (diff (+ 1 (- m k)))
       ((cons merged-mod merged-support) (vl-make-n-bit-reduction-op :vl-unary-bitor diff))
       ((mv merged-expr merged-netdecl)  (vl-primitive-mkwire "merged_high"))

       (high-bits (make-vl-nonatom :op :vl-partselect-colon
                                   :args (list b-expr
                                               (vl-make-index (- m 1))
                                               (vl-make-index (- k 1)))
                                   :finalwidth diff
                                   :finaltype :vl-unsigned))
       (merged-inst (vl-simple-inst merged-mod "merge_high" merged-expr high-bits))

       ;; Okay, now we're ready to build the rhses.  We just use merged-expr
       ;; as the arg to the final shifter.

       (lower-wires  (take (- k 1) b-wires))  ;; b[0], b[1], ..., b[k-2]
       (rhs-exprs    (append lower-wires (list merged-expr)))
       (pshift-insts (vl-make-modinsts-for-shl 1 pshift-mods temp-exprs lhs-exprs rhs-exprs)))

    (list* (make-vl-module :name      name
                           :origname  name
                           :ports     (list out-port a-port b-port)
                           :portdecls (list out-portdecl a-portdecl b-portdecl)
                           :netdecls  (list* out-netdecl a-netdecl b-netdecl bx-netdecl merged-netdecl temp-netdecls)
                           :modinsts  (cons merged-inst (append pshift-insts (list bx-modinst out-modinst)))
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*)
           merged-mod
           (append merged-support supporting-mods))))
