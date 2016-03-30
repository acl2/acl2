; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
(include-book "../parsetree")
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (non-parallel-book))
(local (in-theory (enable acl2::arith-equiv-forwarding)))

(defxdoc expr-building
  :parents (mlib)
  :short "Basic functions for generating expressions and gates."

  :long "<h3>WARNING</h3>

<p>Many of these functions generate sized expressions so you have to be really
careful that you're using them in the proper way.</p>")

(local (xdoc::set-default-parents expr-building))

(local (defthm vl-bit-p-of-nth
         (implies (and (force (< (nfix n) (len x)))
                       (force (vl-bitlist-p x)))
                  (vl-bit-p (nth n x)))))


(define vl-make-bitselect
 :short "Safely create the bit-select @('expr[n]')."
 ((expr vl-expr-p "Should be an sized identifier.")
  (n    natp))
  :returns (expr[n] vl-expr-p)
  :long "<p>Historic note.  We used to (incorrectly) check whether N was less
than the final-width of the expression, and also optimize so that when FOO had
width 1, we would create FOO instead of FOO[0].  This did not cause problems
since this function was only used in occform (where the wires we were
generating always started at index 0), but is more generally incorrect since a
wire's finalwidth need not be related to the valid bits that can be selected
from it, e.g., wire [7:5] w; should allow us to select w[7], w[6], and w[5],
but the width of w is only 2.</p>

<p>We no longer try to do any bounds-checking here, since it is really not
possible to do it correctly without knowing the bounds of the wire, which is
not available to us here.  You can hence use this function to create an invalid
expression like foo[n]; garbage in, garbage out.</p>"

  (b* (((unless (vl-fast-atom-p expr))
        ;; BOZO it would probably be cleaner to have vl-idexpr-p as a guard,
        ;; instead of having this check.
        (raise "Trying to select from non-atom: ~x0." expr)
        |*sized-1'b0*|)

       ((unless (posp (vl-expr->finalwidth expr)))
        ;; This may not be necessary, now that our sizing code is better.
        (raise "Trying to select from unwidthed expr: ~x0" expr)
        |*sized-1'b0*|)

       (guts (vl-atom->guts expr))

       ((unless (vl-id-p guts))
        ;; BOZO it would probably be cleaner to have vl-idexpr-p as a guard,
        ;; instead of having this check.
        (raise "Not implemented: bitselect from ~x0." (tag guts))
        |*sized-1'b0*|))

    (hons-copy
     (make-vl-nonatom :op :vl-bitselect
                      :args (acl2::hons-list (vl-expr-fix expr) (vl-make-index n))
                      :finalwidth 1
                      :finaltype :vl-unsigned)))
  ///
  (defthm vl-expr->finalwidth-of-vl-make-bitselect
    (equal (vl-expr->finalwidth (vl-make-bitselect expr n))
           1))

  (defthm vl-expr->finaltype-of-vl-make-bitselect
    (equal (vl-expr->finaltype (vl-make-bitselect expr n))
           :vl-unsigned)))


(define vl-make-list-of-bitselects ((expr vl-expr-p)
                                    (low  natp)
                                    (high natp))
  :short "Build a list of expressions, @('(expr[low] ... expr[high])')."
  :guard (<= low high)
  :returns (exprs vl-exprlist-p)
  :measure (nfix (- (nfix high) (nfix low)))
  (if (mbe :logic (zp (- (nfix high) (nfix low)))
           :exec (eql high low))
      (list (vl-make-bitselect expr low))
    (cons (vl-make-bitselect expr low)
          (vl-make-list-of-bitselects expr (+ (nfix low) 1) high)))
  ///
  (defthm len-of-vl-make-list-of-bitselects
    (equal (len (vl-make-list-of-bitselects expr low high))
           (+ 1 (nfix (- (nfix high) (nfix low))))))

  (defthm vl-exprlist->finalwidths-of-vl-make-list-of-bitselects
    (equal (vl-exprlist->finalwidths (vl-make-list-of-bitselects expr low high))
           (replicate (+ 1 (nfix (- (nfix high) (nfix low)))) 1))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm vl-exprlist->finaltypes-of-vl-make-list-of-bitselects
    (equal (vl-exprlist->finaltypes (vl-make-list-of-bitselects expr low high))
           (replicate (+ 1 (nfix (- (nfix high) (nfix low)))) :vl-unsigned))
    :hints(("Goal" :in-theory (enable replicate)))))


(define vl-make-msb-to-lsb-bitselects ((expr vl-expr-p)
                                       (msb  natp)
                                       (lsb  natp))
  :short "Build a list of expressions, @('(expr[msb] ... expr[lsb])')."
  :returns (selects vl-exprlist-p)
  (b* ((msb  (lnfix msb))
       (lsb  (lnfix lsb))
       (left-right-p (>= msb lsb))
       (low  (if left-right-p lsb msb))
       (high (if left-right-p msb lsb))
       (list (vl-make-list-of-bitselects expr low high)))
    (if left-right-p
        (reverse list)
      list))
  ///
  (defthm true-listp-of-vl-make-msb-to-lsb-bitselects
    (true-listp (vl-make-msb-to-lsb-bitselects expr msb lsb))
    :rule-classes :type-prescription)

  (defthm len-of-vl-make-msb-to-lsb-bitselects
    (equal (len (vl-make-msb-to-lsb-bitselects expr msb lsb))
           (+ 1 (abs (- (nfix msb) (nfix lsb))))))

  (defthm vl-exprlist->finalwidths-of-vl-make-msb-to-lsb-bitselects
    (equal (vl-exprlist->finalwidths (vl-make-msb-to-lsb-bitselects expr msb lsb))
           (replicate (+ 1 (abs (- (nfix msb) (nfix lsb)))) 1))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm vl-exprlist->finaltypes-of-vl-make-msb-to-lsb-bitselects
    (equal (vl-exprlist->finaltypes (vl-make-msb-to-lsb-bitselects expr msb lsb))
           (replicate (+ 1 (abs (- (nfix msb) (nfix lsb)))) :vl-unsigned))
    :hints(("Goal" :in-theory (enable replicate)))))


(define vl-default-n-bit-expr ((n posp))
  :returns (expr vl-expr-p)
  :short "Build an arbitrary expression of some particular width."
  (let ((n (mbe :logic (pos-fix n)
                :exec n)))
    (make-vl-atom :guts (make-vl-constint :value 0
                                          :origwidth n
                                          :origtype :vl-unsigned)
                  :finalwidth n
                  :finaltype :vl-unsigned))
  ///
  (defthm vl-expr->finalwidth-of-vl-default-n-bit-expr
    (equal (vl-expr->finalwidth (vl-default-n-bit-expr n))
           (pos-fix n)))

  (defthm vl-expr-widthsfixed-p-of-vl-default-n-bit-expr
    (vl-expr-widthsfixed-p (vl-default-n-bit-expr n))
    :hints(("Goal" :in-theory (enable vl-expr-widthsfixed-p)))))



(define vl-make-partselect
  :short "Safely creates expr[msb:lsb]."

  ((expr vl-expr-p)
   (msb  natp)
   (lsb  natp))
  :returns (|expr[msb:lsb]| vl-expr-p)

  :long "<p>We ensure that expr is an identifier and that @('msb >= lsb').
Moreover, if @('msb = lsb'), we create the bitselect @('expr[msb]')
instead.</p>

<p>Historic note.  This used to have the same problem as @(see
vl-make-bitselect), and checked whether the msb was less than the final-width
of expression.  See the discussion there.</p>

<p>We no longer try to prevent you from creating part-selects with invalid
ranges, since it's just not possible to do that correctly here.  Garbage in,
garbage out.</p>"

  (b* ((msb (lnfix msb))
       (lsb (lnfix lsb))

       ((when (> lsb msb))
        (raise "LSB, ~x0, is larger than MSB, ~x1." lsb msb)
        (vl-default-n-bit-expr 1))

       (width     (+ 1 (- msb lsb)))
       (msb-index (vl-make-index msb))
       (lsb-index (vl-make-index lsb))

       ((unless (and (vl-fast-atom-p expr)
                     (vl-fast-id-p (vl-atom->guts expr))))
        ;; BOZO it might be nicer to use a vl-idexpr-p guard.
        (raise "Trying to select from a non-identifier: ~x0" expr)
        (vl-default-n-bit-expr width))

       ((when (= lsb msb))
        (make-vl-nonatom :op :vl-bitselect
                         :args (list expr msb-index)
                         :finalwidth 1
                         :finaltype :vl-unsigned)))

    (make-vl-nonatom :op :vl-partselect-colon
                     :args (list expr msb-index lsb-index)
                     :finalwidth width
                     :finaltype :vl-unsigned))
  ///
  (defthm vl-expr->finalwidth-of-vl-make-partselect
    (equal (vl-expr->finalwidth (vl-make-partselect expr msb lsb))
           (+ 1 (nfix (- (nfix msb) (nfix lsb))))))

  (defthm vl-expr-widthsfixed-p-of-vl-make-partselect
    (implies (force (vl-expr-widthsfixed-p expr))
             (vl-expr-widthsfixed-p (vl-make-partselect expr msb lsb)))
    :hints(("Goal"
            :in-theory (enable vl-expr-widthsfixed-p)
            :expand ((:free (a b c d e)
                      (vl-expr-widthsfixed-p (vl-nonatom a b c d e))))))))


; BOZO the stuff below doesn't belong in a library about expressions.  It's about
; making instances.

(define vl-make-unary-gateinst
  :short "Make a unary (buf or not) gate instance."
  ((type vl-gatetype-p)
   (out  vl-expr-p)
   (in   vl-expr-p)
   &key
   (atts vl-atts-p)
   ((loc vl-location-p) '*vl-fakeloc*))
  :guard (member type (list :vl-buf :vl-not))
  :returns (inst vl-gateinst-p)
  (progn$
   ;; Quick sanity check.
   (or (and (equal (vl-expr->finalwidth out) 1)
            (equal (vl-expr->finalwidth in) 1))
       (raise "Expected expressions of width 1."))
   (make-vl-gateinst :type type
                     :args (list (make-vl-plainarg :expr (vl-expr-fix out) :dir :vl-output)
                                 (make-vl-plainarg :expr (vl-expr-fix in) :dir :vl-input))
                     :atts atts
                     :loc loc)))

(define vl-make-unary-gateinstlist
  :short "Make a list of unary (buf or not) gate instances."
  ((type vl-gatetype-p)
   (outs vl-exprlist-p)
   (ins  vl-exprlist-p)
   &key
   (atts vl-atts-p)
   ((loc vl-location-p) '*vl-fakeloc*))
  :guard (and (member type (list :vl-buf :vl-not))
              (same-lengthp outs ins))
  :returns (insts vl-gateinstlist-p)
  (if (atom outs)
      nil
    (cons (vl-make-unary-gateinst type (car outs) (car ins)
                                  :atts atts :loc loc)
          (vl-make-unary-gateinstlist type (cdr outs) (cdr ins)
                                      :atts atts :loc loc))))

(define vl-make-binary-gateinst
  :short "Make a basic binary gate instance, e.g., an AND, OR, XOR, NAND, NOR, or XNOR gate."
  ((type vl-gatetype-p)
   (out  vl-expr-p)
   (a    vl-expr-p)
   (b    vl-expr-p)
   &key
   (atts vl-atts-p)
   ((loc vl-location-p) '*vl-fakeloc*))
  :guard
  (member-eq type (list :vl-and :vl-nand :vl-nor :vl-or :vl-xor :vl-xnor))
  :returns (inst vl-gateinst-p)
  (prog2$
   ;; Quick sanity check.
   (or (and (equal (vl-expr->finalwidth out) 1)
            (equal (vl-expr->finalwidth a) 1)
            (equal (vl-expr->finalwidth b) 1))
       (raise "Expected expressions of width 1."))

   ;; Per Section 7.2 (Page 80), the first terminal is the output and the
   ;; remaining terminals are inputs.
   (make-vl-gateinst
    :type type
    :args (list (make-vl-plainarg :expr (vl-expr-fix out) :dir :vl-output)
                (make-vl-plainarg :expr (vl-expr-fix a) :dir :vl-input)
                (make-vl-plainarg :expr (vl-expr-fix b) :dir :vl-input))
    :atts atts
    :loc loc)))

(define vl-make-binary-gateinstlist
  :short "Make a list of basic binary gate instances, e.g., AND, OR, XOR, NAND, NOR, or XNOR gates."
  ((type vl-gatetype-p)
   (outs vl-exprlist-p)
   (as   vl-exprlist-p)
   (bs   vl-exprlist-p)
   &key
   (atts vl-atts-p)
   ((loc vl-location-p) '*vl-fakeloc*))
  :guard (and (member-eq type (list :vl-and :vl-nand :vl-nor :vl-or :vl-xor :vl-xnor))
              (same-lengthp outs as)
              (same-lengthp outs bs))
  :returns (insts vl-gateinstlist-p)
  (if (atom outs)
      nil
    (cons (vl-make-binary-gateinst type (car outs) (car as) (car bs)
                                   :atts atts :loc loc)
          (vl-make-binary-gateinstlist type (cdr outs) (cdr as) (cdr bs)
                                       :atts atts :loc loc)))
  ///
  (defthm len-of-vl-make-binary-gateinstlist
    (equal (len (vl-make-binary-gateinstlist type outs as bs :atts atts :loc loc))
           (len outs))))

