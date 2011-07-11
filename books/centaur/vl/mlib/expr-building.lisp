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
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))


(defxdoc expr-building
  :parents (mlib)
  :short "Basic functions for generating expressions and gates.")


; WARNING WARNING WARNING!!!
;
; Many of these functions generate sized expressions so you have to be really
; careful that you're using them in the proper way.

(local (defthm vl-bit-p-of-nth
         (implies (and (force (< (nfix n) (len x)))
                       (force (vl-bitlist-p x)))
                  (vl-bit-p (nth n x)))))


(defsection vl-make-bitselect

; Historic note.  We used to (incorrectly) check whether N was less than the
; final-width of the expression, and also optimize so that when FOO had width
; 1, we would create FOO instead of FOO[0].  This did not cause problems since
; this function was only used in occform (where the wires we were generating
; always started at index 0), but is more generally incorrect since a wire's
; finalwidth need not be related to the valid bits that can be selected from
; it, e.g., wire [7:5] w; should allow us to select w[7], w[6], and w[5], but
; the width of w is only 2.
;
; We now do not try to do any bounds-checking here, since it is really not
; possible to do it correctly without knowing the bounds of the wire, which is
; not available to us here.  You can hence use this function to create an
; invalid expression like foo[n]; garbage in, garbage out.

  (defund vl-make-bitselect (expr n)
    (declare (xargs :guard (and (vl-expr-p expr)
                                (natp n))))

; Safely create the bit-select, expr[n].  Expr should be an identifier.

    (b* (((unless (vl-fast-atom-p expr))
          ;; BOZO it would probably be cleaner to have vl-idexpr-p as a guard,
          ;; instead of having this check.
          (er hard? 'vl-make-bitselect "Trying to select from non-atom: ~x0." expr)
          |*sized-1'b0*|)

         ((unless (posp (vl-expr->finalwidth expr)))
          ;; This may not be necessary, now that our sizing code is better.
          (er hard? 'vl-make-bitselect "Trying to select from unwidthed expr: ~x0" expr)
          |*sized-1'b0*|)

         (guts (vl-atom->guts expr))

         ((unless (vl-id-p guts))
          ;; BOZO it would probably be cleaner to have vl-idexpr-p as a guard,
          ;; instead of having this check.
          (er hard? 'vl-make-bitselect "Not implemented: bitselect from ~x0." (tag guts))
          |*sized-1'b0*|))

      (make-honsed-vl-nonatom :op :vl-bitselect
                              :args (acl2::hons-list expr (vl-make-index n))
                              :finalwidth 1
                              :finaltype :vl-unsigned)))

  (local (in-theory (enable vl-make-bitselect)))

  (defthm vl-expr-p-of-vl-make-bitselect
    (implies (force (vl-expr-p expr))
             (vl-expr-p (vl-make-bitselect expr n))))

  (defthm vl-expr->finalwidth-of-vl-make-bitselect
    (equal (vl-expr->finalwidth (vl-make-bitselect expr n))
           1))

  (defthm vl-expr->finaltype-of-vl-make-bitselect
    (equal (vl-expr->finaltype (vl-make-bitselect expr n))
           :vl-unsigned)))



(defsection vl-make-list-of-bitselects

  (defund vl-make-list-of-bitselects (expr low high)
    "Returns ( expr[low] ... expr[high] )"
    (declare (xargs :guard (and (vl-expr-p expr)
                                (natp low)
                                (natp high)
                                (<= low high))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (if (mbe :logic (zp (- (nfix high) (nfix low)))
             :exec (= high low))
        (list (vl-make-bitselect expr low))
      (cons (vl-make-bitselect expr low)
            (vl-make-list-of-bitselects expr (+ (nfix low) 1) high))))

  (local (in-theory (enable vl-make-list-of-bitselects)))

  (defthm vl-exprlist-p-of-vl-make-list-of-bitselects
    (implies (force (vl-expr-p expr))
             (vl-exprlist-p (vl-make-list-of-bitselects expr low high))))

  (defthm len-of-vl-make-list-of-bitselects
    (equal (len (vl-make-list-of-bitselects expr low high))
           (+ 1 (nfix (- (nfix high) (nfix low))))))

  (defthm vl-exprlist->finalwidths-of-vl-make-list-of-bitselects
    (equal (vl-exprlist->finalwidths (vl-make-list-of-bitselects expr low high))
           (repeat 1 (+ 1 (nfix (- (nfix high) (nfix low))))))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm vl-exprlist->finaltypes-of-vl-make-list-of-bitselects
    (equal (vl-exprlist->finaltypes (vl-make-list-of-bitselects expr low high))
           (repeat :vl-unsigned (+ 1 (nfix (- (nfix high) (nfix low))))))
    :hints(("Goal" :in-theory (enable repeat)))))





(defsection vl-default-n-bit-expr

  (defund vl-default-n-bit-expr (n)
    (declare (xargs :guard (posp n)))
    (make-vl-atom :guts (make-vl-constint :value 0
                                          :origwidth n
                                          :origtype :vl-unsigned)
                  :finalwidth n
                  :finaltype :vl-unsigned))

  (local (in-theory (enable vl-default-n-bit-expr)))

  (defthm vl-expr-p-of-vl-default-n-bit-expr
    (implies (force (posp n))
             (equal (vl-expr-p (vl-default-n-bit-expr n))
                    t)))

  (defthm vl-expr->finalwidth-of-vl-default-n-bit-expr
    (equal (vl-expr->finalwidth (vl-default-n-bit-expr n))
           n))

  (defthm vl-expr-widthsfixed-p-of-vl-default-n-bit-expr
    (implies (posp n)
             (vl-expr-widthsfixed-p (vl-default-n-bit-expr n)))
    :hints(("Goal" :in-theory (enable vl-expr-widthsfixed-p)))))



(defsection vl-make-partselect

; Safely creates expr[msb:lsb].  We ensure that expr is an identifier and that
; msb >= lsb.  Moreover, if msb = lsb, we create the bitselect expr[msb]
; instead.

; Historic note.  This used to have the same problem as vl-make-bitselect, and
; checked whether the msb was less than the final-width of expression.  See the
; comments there for more discussion.  We no longer try to prevent you from
; creating part-selects with invalid ranges, since it's just not possible to do
; that correctly here.  Garbage in, garbage out.

  (defund vl-make-partselect (expr msb lsb)
    (declare (xargs :guard (and (vl-expr-p expr)
                                (natp msb)
                                (natp lsb))))


    (b* ((msb       (mbe :logic (nfix msb) :exec msb))
         (lsb       (mbe :logic (nfix lsb) :exec lsb))

         ((when (> lsb msb))
          (er hard? 'vl-make-partselect "LSB, ~x0, is larger than MSB, ~x1." lsb msb)
          (vl-default-n-bit-expr 1))

         (width     (+ 1 (- msb lsb)))
         (msb-index (vl-make-index msb))
         (lsb-index (vl-make-index lsb))

         ((unless (and (vl-fast-atom-p expr)
                       (vl-fast-id-p (vl-atom->guts expr))))
          ;; BOZO it might be nicer to use a vl-idexpr-p guard.
          (er hard? 'vl-make-partselect "Trying to select from a non-identifier: ~x0" expr)
          (vl-default-n-bit-expr width))

         ((when (= lsb msb))
          (make-vl-nonatom :op :vl-bitselect
                           :args (list expr msb-index)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))

      (make-vl-nonatom :op :vl-partselect-colon
                       :args (list expr msb-index lsb-index)
                       :finalwidth width
                       :finaltype :vl-unsigned)))

  (local (in-theory (enable vl-make-partselect)))

  (defthm vl-expr-p-of-vl-make-partselect
    (implies (force (vl-expr-p expr))
             (vl-expr-p (vl-make-partselect expr msb lsb))))

  (defthm vl-expr->finalwidth-of-vl-make-partselect
    (equal (vl-expr->finalwidth (vl-make-partselect expr msb lsb))
           (+ 1 (nfix (- (nfix msb) (nfix lsb))))))

  (defthm vl-expr-widthsfixed-p-of-vl-make-partselect
    (implies (force (vl-expr-widthsfixed-p expr))
             (vl-expr-widthsfixed-p (vl-make-partselect expr msb lsb)))
    :hints(("Goal" :in-theory (enable vl-expr-widthsfixed-p)))))




#||


;; BOZO clean this up.  Why both?  What's the deal?

(defund vl-maybe-zero-extend (expr n)
  (declare (xargs :guard (and (vl-expr-p expr)
                              (natp n))))
  (let ((width (vl-expr->width expr)))
    (cond ((not (posp width))
           (prog2$ (er hard? 'vl-maybe-zero-extend "Expected a width on ~x0." expr)
                   expr))

          ((< n width)
           (prog2$ (er hard? 'vl-maybe-zero-extend "Cannot extend ~x0-bit expr to ~x1 bits: ~x2."
                       width n expr)
                   expr))

          ((= n width)
           ;; Nothing to do.
           expr)

          (t
           (let* ((difference (- n width))
                  (zero-int  (make-vl-constint :value 0
                                               :width difference
                                               :signedp nil))
                  (zero-atom (make-vl-atom :guts zero-int
                                           :width difference
                                           :sign :vl-unsigned)))
             (make-vl-nonatom :op :vl-concat
                              :args (list zero-atom expr)
                              :width n
                              :sign :vl-unsigned
                              :atts (list (list "ZERO_EXTENSION"))))))))

(defthm vl-expr-p-of-vl-maybe-zero-extend
  (implies (and (force (vl-expr-p expr))
                (force (natp n)))
           (vl-expr-p (vl-maybe-zero-extend expr n)))
  :hints(("Goal" :in-theory (enable vl-maybe-zero-extend))))



(defund vl-zero-extend (n expr)
  (declare (xargs :guard (and (natp n)
                              (vl-expr-p expr)
                              (natp (vl-expr->width expr))
                              (> n (vl-expr->width expr)))))

; Expr is an arbitrary expression whose width should be strictly less than n.
; Our goal is to produce a new expression which represents the zero-extension
; of expr to n bits.  To do this, we just make a concatenation with a zero of
; the appropriate size.

  (let* ((m    (vl-expr->width expr))
         (zero (make-vl-atom
                :guts (make-vl-constint :width (- n m)
                                        :signedp nil
                                        :value 0)
                :width (- n m)
                :sign :vl-unsigned)))
    (make-vl-nonatom :op :vl-concat
                     :atts (list (list "VL_ZERO_EXTENSION"))
                     :args (list zero expr)
                     :width n
                     :sign :vl-unsigned)))

(defthm vl-expr-p-of-vl-zero-extend
  (implies (and (force (natp n))
                (force (vl-expr-p expr))
                (force (natp (vl-expr->width expr)))
                (force (> n (vl-expr->width expr))))
           (vl-expr-p (vl-zero-extend n expr)))
  :hints(("Goal" :in-theory (enable vl-zero-extend))))

(defthm vl-expr->width-of-vl-zero-extend
  (equal (vl-expr->width (vl-zero-extend n expr))
         n)
  :hints(("Goal" :in-theory (enable vl-zero-extend))))

(defthm vl-expr->sign-of-vl-zero-extend
  (equal (vl-expr->sign (vl-zero-extend n expr))
         :vl-unsigned)
  :hints(("Goal" :in-theory (enable vl-zero-extend))))

||#





; BOZO the stuff below doesn't belong in a library about expressions.  It's about
; making instances.


(defsection vl-make-unary-gateinst

  (defund vl-make-unary-gateinst (type out in atts loc)
    "Make a gate: type(out, in);"
    (declare (xargs :guard (and (member-eq type (list :vl-buf :vl-not))
                                (vl-expr-p out)
                                (vl-expr-p in)
                                (vl-atts-p atts)
                                (or (not loc) (vl-location-p loc)))))
    (prog2$
     ;; Quick sanity check.
     (or (and (equal (vl-expr->finalwidth out) 1)
              (equal (vl-expr->finalwidth in) 1))
         (er hard? 'vl-make-unary-gateinst "Expected expressions of width 1."))
     (make-vl-gateinst
      :type type
      :args (list (make-vl-plainarg :expr out :dir :vl-output)
                  (make-vl-plainarg :expr in :dir :vl-input))
      :atts atts
      :loc (or loc *vl-fakeloc*))))

  (local (in-theory (enable vl-make-unary-gateinst)))

  (defthm vl-gateinst-p-of-vl-make-unary-gateinst
    (implies (and (force (member-eq type (list :vl-buf :vl-not)))
                  (force (vl-expr-p out))
                  (force (vl-expr-p in))
                  (force (vl-atts-p atts))
                  (force (or (not loc) (vl-location-p loc))))
             (vl-gateinst-p (vl-make-unary-gateinst type out in atts loc)))))


(defsection vl-make-unary-gateinstlist

  (defund vl-make-unary-gateinstlist (type outs ins loc)
    "Make a list of gates, [type(out1, in), ..., type(outN, inN)]"
    (declare (xargs :guard (and (member-eq type (list :vl-buf :vl-not))
                                (vl-exprlist-p outs)
                                (vl-exprlist-p ins)
                                (same-lengthp outs ins)
                                (or (not loc) (vl-location-p loc)))))
    (if (atom outs)
        nil
      (cons (vl-make-unary-gateinst type (car outs) (car ins) nil loc)
            (vl-make-unary-gateinstlist type (cdr outs) (cdr ins) loc))))

  (local (in-theory (enable vl-make-unary-gateinstlist)))

  (defthm vl-gateinstlist-p-of-vl-make-unary-gateinstlist
    (implies (and (force (member-eq type (list :vl-buf :vl-not)))
                  (force (vl-exprlist-p outs))
                  (force (vl-exprlist-p ins))
                  (force (equal (len outs) (len ins)))
                  (force (or (not loc) (vl-location-p loc))))
             (vl-gateinstlist-p (vl-make-unary-gateinstlist type outs ins loc)))))


(defsection vl-make-binary-gateinst

  (defund vl-make-binary-gateinst (type out a b atts loc)
    "Makes a gate: type(out, a, b);"
    (declare (xargs :guard (and (member-eq type (list :vl-and :vl-nand :vl-nor
                                                      :vl-or :vl-xor :vl-xnor))
                                (vl-expr-p out)
                                (vl-expr-p a)
                                (vl-expr-p b)
                                (vl-atts-p atts)
                                (or (not loc) (vl-location-p loc)))))
    (prog2$
     ;; Quick sanity check.
     (or (and (equal (vl-expr->finalwidth out) 1)
              (equal (vl-expr->finalwidth a) 1)
              (equal (vl-expr->finalwidth b) 1))
         (er hard? 'vl-make-binary-gateinst "Expected expressions of width 1."))

     ;; Per Section 7.2 (Page 80), the first terminal is the output and the
     ;; remaining terminals are inputs.
     (make-vl-gateinst
      :type type
      :args (list (make-vl-plainarg :expr out :dir :vl-output)
                  (make-vl-plainarg :expr a :dir :vl-input)
                  (make-vl-plainarg :expr b :dir :vl-input))
      :atts atts
      :loc (or loc *vl-fakeloc*))))

  (local (in-theory (enable vl-make-binary-gateinst)))

  (defthm vl-gateinst-p-of-vl-make-binary-gateinst
    (implies (and (force (member-eq type (list :vl-and :vl-nand :vl-nor
                                               :vl-or :vl-xor :vl-xnor)))
                  (force (vl-expr-p out))
                  (force (vl-expr-p a))
                  (force (vl-expr-p b))
                  (force (vl-atts-p atts))
                  (force (or (not loc) (vl-location-p loc))))
             (vl-gateinst-p (vl-make-binary-gateinst type out a b atts loc)))
    :hints(("Goal" :in-theory (enable vl-make-binary-gateinst)))))


(defsection vl-make-binary-gateinstlist

  (defund vl-make-binary-gateinstlist (type outs as bs loc)
    "Make a list of gates, [type(out1, a1, b1), ..., type(outN, aN, bN)]"
    (declare (xargs :guard (and (member-eq type (list :vl-and :vl-nand :vl-nor
                                                      :vl-or :vl-xor :vl-xnor))
                                (vl-exprlist-p outs)
                                (vl-exprlist-p as)
                                (vl-exprlist-p bs)
                                (same-lengthp outs as)
                                (same-lengthp outs bs)
                                (or (not loc) (vl-location-p loc)))))
    (if (atom outs)
        nil
      (cons (vl-make-binary-gateinst type (car outs) (car as) (car bs) nil loc)
            (vl-make-binary-gateinstlist type (cdr outs) (cdr as) (cdr bs) loc))))

  (local (in-theory (enable vl-make-binary-gateinstlist)))

  (defthm vl-gateinstlist-p-of-vl-make-binary-gateinstlist
    (implies (and (force (member-eq type (list :vl-and :vl-nand :vl-nor
                                               :vl-or :vl-xor :vl-xnor)))
                  (force (vl-exprlist-p outs))
                  (force (vl-exprlist-p as))
                  (force (vl-exprlist-p bs))
                  (force (equal (len outs) (len as)))
                  (force (equal (len outs) (len bs)))
                  (force (or (not loc) (vl-location-p loc))))
             (vl-gateinstlist-p (vl-make-binary-gateinstlist type outs as bs loc))))

  (defthm len-of-vl-make-binary-gateinstlist
    (equal (len (vl-make-binary-gateinstlist type outs as bs loc))
           (len outs))))





;; This all appears to be unused now.


;; (defund vl-qmark-expr (x y z)

;;   (declare (xargs :guard (and (vl-expr-p x)
;;                               (vl-expr-p y)
;;                               (vl-expr-p z))))

;; ; Safely construct an expression which corresponds to "x ? y : z", performing
;; ; trivial optimizations where possible.

;;   (cond ((or (not (posp (vl-expr->width x)))
;;              (not (posp (vl-expr->width y)))
;;              (not (posp (vl-expr->width z))))
;;          (prog2$ (er hard? 'vl-qmark-expr "Expected posp width.")
;;                  x))

;;         ((or (not (equal (vl-expr->width y)
;;                          (vl-expr->width z))))
;;          (prog2$ (er hard? 'vl-qmark-expr "Expected equal widths.")
;;                  x))

;;         ;; Some simple optimizations.
;;         ((vl-obviously-true-expr-p x)
;;          y)
;;         ((vl-obviously-false-expr-p x)
;;          z)
;;         ((equal y z)
;;          y)

;;         (t
;;          (let* ((x-sign      (vl-expr->sign x))
;;                 (y-sign      (vl-expr->sign y))
;;                 (z-sign      (vl-expr->sign z))
;;                 (result-sign (cond ((and (eq x-sign :vl-signed)
;;                                          (eq y-sign :vl-signed)
;;                                          (eq z-sign :vl-signed))
;;                                     :vl-signed)
;;                                    ((or (eq x-sign :vl-unsigned)
;;                                         (eq y-sign :vl-unsigned)
;;                                         (eq z-sign :vl-unsigned))
;;                                     :vl-unsigned)
;;                                    (t
;;                                     (cw "; Warning in vl-qmark-expr: expected signs to be computed"))))

;;                 ;; We fix up the first arg to be width 1, as in oprewrite.
;;                 (test-fixed (if (= (vl-expr->width x) 1)
;;                                 x
;;                               ;; |x
;;                               (make-vl-nonatom :op :vl-unary-bitor
;;                                                :args (list x)
;;                                                :width 1
;;                                                :sign x-sign))))
;;            (make-vl-nonatom :op :vl-qmark
;;                             :args (list test-fixed y z)
;;                             :width (vl-expr->width y)
;;                             :sign result-sign)))))

;; (defthm vl-expr-p-of-vl-qmark-expr
;;   (implies (and (force (vl-expr-p x))
;;                 (force (vl-expr-p y))
;;                 (force (vl-expr-p z)))
;;            (vl-expr-p (vl-qmark-expr x y z)))
;;   :hints(("Goal" :in-theory (enable vl-qmark-expr))))



;; (defund vl-lognot-expr (x)
;;   ;; We build an expression which is the negation of x, with appropriate widths
;;   ;; and sign.  X is expected to have a sign and width already computed.
;;   (declare (xargs :guard (vl-expr-p x)))
;;   (cond ((not (posp (vl-expr->width x)))
;;          (prog2$ (er hard? 'vl-lognot-expr "Expected posp width.")
;;                  x))
;;         ((not (eq (vl-expr->sign x) :vl-unsigned))
;;          (prog2$ (er hard? 'vl-lognot-expr "Expected unsigned.")
;;                  x))
;;         (t
;;          ;; It would be most natural to use :vl-unary-lognot of x, but we
;;          ;; prefer (see oprewrite) to use ~(|x), which is equivalent.  We
;;          ;; know that this produces an unsigned, one-bit value.
;;          (let ((or-x (make-vl-nonatom :op :vl-unary-bitor
;;                                       :args (list x)
;;                                       :width 1
;;                                       :sign :vl-unsigned)))
;;            (make-vl-nonatom :op :vl-unary-bitnot
;;                             :args (list or-x)
;;                             :width 1
;;                             :sign :vl-unsigned)))))

;; (defthm vl-expr-p-of-vl-lognot-expr
;;   (implies (force (vl-expr-p x))
;;            (vl-expr-p (vl-lognot-expr x)))
;;   :hints(("Goal" :in-theory (enable vl-lognot-expr))))





;; (defund vl-logand-exprs (x y)
;;   ;; We build an expression which is equivalent to x && y, with appropriate
;;   ;; widths and sign.  X and Y are expected to have a sign and width already
;;   ;; computed.
;;   (declare (xargs :guard (and (vl-expr-p x)
;;                               (vl-expr-p y))))
;;   (cond ((or (not (posp (vl-expr->width x)))
;;              (not (posp (vl-expr->width y))))
;;          (prog2$ (er hard? 'vl-logand-exprs "Expected posp width.")
;;                  x))
;;         ((or (not (eq (vl-expr->sign x) :vl-unsigned))
;;              (not (eq (vl-expr->sign y) :vl-unsigned)))
;;          (prog2$ (er hard? 'vl-logand-exprs "Expected unsigned.")
;;                  x))
;;         (t
;;          ;; It would be most natural to build x && y here.  But instead we are
;;          ;; going to write (|x) & (|y), as in oprewrite, since this is our
;;          ;; preferred form.
;;          (let* ((or-x (make-vl-nonatom :op :vl-unary-bitor
;;                                        :args (list x)
;;                                        :width 1
;;                                        :sign :vl-unsigned))
;;                 (or-y (make-vl-nonatom :op :vl-unary-bitor
;;                                        :args (list y)
;;                                        :width 1
;;                                        :sign :vl-unsigned)))
;;            (make-vl-nonatom :op :vl-binary-bitand
;;                             :args (list or-x or-y)
;;                             :width 1
;;                             :sign :vl-unsigned)))))

;; (defthm vl-expr-p-of-vl-logand-exprs
;;   (implies (and (force (vl-expr-p x))
;;                 (force (vl-expr-p y)))
;;            (vl-expr-p (vl-logand-exprs x y)))
;;   :hints(("Goal" :in-theory (enable vl-logand-exprs))))



;; (defund vl-logand-exprlist (x)
;;   ;; We build an expression which is the logical and of all the expressions in
;;   ;; x.  Widths and signs should have already been computed.  Our answer is
;;   ;; always one-bit wide and we tolerate the empty list by returning the
;;   ;; constant 1.
;;   (declare (xargs :guard (vl-exprlist-p x)))
;;   (cond ((atom x)
;;          (make-vl-atom :guts (make-vl-constint :width 1
;;                                                :signedp nil
;;                                                :value 1)
;;                        :width 1
;;                        :sign :vl-unsigned))
;;         ((atom (cdr x))
;;          (let ((width (vl-expr->width (car x))))
;;            (cond ((not (posp width))
;;                   (prog2$
;;                    (er hard? 'vl-logand-exprlist "Expected widths to be positive.")
;;                    (car x)))
;;                  ((eql width 1)
;;                   ;; Already one bit wide, no need to do any trickery.
;;                   (car x))
;;                  (t
;;                   ;; Otherwise, we build the expression |(car x) so that our
;;                   ;; result is only one-bit wide.
;;                   (make-vl-nonatom :op :vl-unary-bitor
;;                                    :args (list (car x))
;;                                    :width 1
;;                                    :sign :vl-unsigned)))))
;;         (t
;;          (vl-logand-exprs (car x)
;;                           (vl-logand-exprlist (cdr x))))))

;; (defthm vl-expr-p-of-vl-logand-exprlist
;;   (implies (vl-exprlist-p x)
;;            (vl-expr-p (vl-logand-exprlist x)))
;;   :hints(("Goal" :in-theory (enable vl-logand-exprlist))))
