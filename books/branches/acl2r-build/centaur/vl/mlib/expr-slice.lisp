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
(include-book "range-tools")
(include-book "find-item")
(include-book "welltyped")
(include-book "expr-building")
(include-book "hid-tools")
(local (include-book "../util/arithmetic"))


; BOZO eventually want to integrate slicing properly throughout the whole
; transformation sequence
;
;   - expr-split should use slicability to decide whether to split up
;     expressions
;
;   - occform should use it when deciding how to handle plain assignments
;      (at least partially done with this)
;
;   - wire-alist stuff should probably be switched to use it, make-defm stuff;
;     but this needs to still be efficient so we might want to bypass building
;     bit exprs with some fused version
;
;   - replicate/partition should all be switched to using this
;      (at least partially done with this)


(defxdoc expr-slicing
  :parents (mlib)
  :short "Functions for slicing up expressions into bits or segments."

  :long "<p>We say a Verilog expression @('x') is <b>sliceable</b> when it may
be \"easily\" converted into a concatenation, say @('{ bit_N, bit_N-1, ...,
bit0 }'), where each @('bit_i') is either a one-bit wide constant (i.e.,
@('1'b0'), @('1'b1'), @('1'bX'), or @('1'bZ')), or is a bit-select from a plain
identifier (i.e., @('foo[3]')).</p>

<p>Sliceable expressions are of interest because they can be easily partitioned
into lists of individual bits or broken into segments, without having to
introduce any temporary wires.</p>

<p>@(call vl-expr-sliceable-p) recognizes the expressions we regard as
sliceble.  For the atoms, we allow:</p>

<ul>
 <li><see topic=\"@(url vl-constint-p)\">Constant</see> integers,</li>
 <li><see topic=\"@(url vl-weirdint-p)\">Weird</see> integers, and</li>
 <li><see topic=\"@(url vl-id-p)\">Identifiers</see></li>
</ul>

<p>We do not currently consider <see topic='@(url vl-real-p)'>real
numbers</see> or <see topic='@(url vl-string-p)'>strings</see> to be sliceable,
but in principle we could add support for this.  It doesn't make sense to
regard the other kinds of atoms (HID pieces, function names, and system
function names) as sliceable.</p>

<p>Beyond these atoms, we regard resolved bit- and part-selects from
identifiers as sliceable.  It is pretty obvious that the indicies of a
part-select need to be resolved for easy partitioning.  But even though we know
that @('foo[i]') is only a single-bit wide, we also insist that bit selects be
resolved because this is useful in functions like @(see vl-msb-bitslice-expr)
which convert sliceable expressions into actual lists of bits, and also in
@(see vl-assign-occform) where we assume we can just use plain assignments on
any sliceable expressions.</p>

<p>We say that concatenations of sliceable arguments as sliceable, as are
replications of sliceable arguments with resolved multiplicities.</p>

<p>Other expressions aren't sliceable.  This seems generally sensible, e.g.,
what are the bits of @('a + b')?  With enough context it would be possible to
slice up hierarchical identifiers, but we don't try to do this since it would
be quite a bit more complex.</p>")





; -----------------------------------------------------------------------------
;
;                     Recognizing Sliceable Expressions
;
; -----------------------------------------------------------------------------

(defsection vl-expr-sliceable-p
  :parents (expr-slicing)
  :short "@(call vl-expr-sliceable-p) determines if the expression @('x') is
sliceable."

  ;; Expressions can be bit/part-selected from if they are IDs or non-atom HIDs.
  (define vl-hid/id-p ((x vl-expr-p))
    (or (vl-idexpr-p x)
        (and (vl-nonatom-p x)
             (vl-hidexpr-p x)))
    ///
    (defthm vl-hid/id-p-when-idexpr
      (implies (vl-idexpr-p x)
               (vl-hid/id-p x)))
    (defthm vl-hid/id-p-when-hidexpr
      (implies (and (vl-nonatom-p x)
                    (vl-hidexpr-p x))
               (vl-hid/id-p x))
      :hints(("Goal" :in-theory (enable vl-hidexpr-p)))))

  (mutual-recursion

   (defund vl-expr-sliceable-p (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (b* ((guts (vl-atom->guts x)))
             (or (vl-fast-constint-p guts)
                 (vl-fast-weirdint-p guts)
                 (vl-fast-id-p guts))))

          ((when (vl-hidexpr-p x)) t)

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((when (eq op :vl-bitselect))
           (and (vl-hid/id-p (first args))
                (vl-expr-resolved-p (second args))))

          ((when (eq op :vl-partselect-colon))
           (and (vl-hid/id-p (first args))
                (vl-expr-resolved-p (second args))
                (vl-expr-resolved-p (third args))))

          ((when (eq op :vl-concat))
           (vl-exprlist-sliceable-p args))

          ((when (eq op :vl-multiconcat))
           (and (vl-expr-resolved-p (first args))
                (vl-expr-sliceable-p (second args)))))

       nil))

   (defund vl-exprlist-sliceable-p (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         t
       (and (vl-expr-sliceable-p (car x))
            (vl-exprlist-sliceable-p (cdr x)))))))


(defsection vl-exprlist-sliceable-p

  (defthm vl-exprlist-sliceable-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-sliceable-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-exprlist-sliceable-p))))

  (defthm vl-exprlist-sliceable-p-of-cons
    (equal (vl-exprlist-sliceable-p (cons a x))
           (and (vl-expr-sliceable-p a)
                (vl-exprlist-sliceable-p x)))
    :hints(("Goal" :in-theory (enable vl-exprlist-sliceable-p))))

  (deflist vl-exprlist-sliceable-p (x)
    (vl-expr-sliceable-p x)
    :elementp-of-nil nil
    :already-definedp t
    :parents (expr-slicing)))


(define vl-find-hid/id-range ((x (and (vl-expr-p x)
                                      (vl-hid/id-p x)))
                              (mod vl-module-p)
                              (ialist (equal ialist (vl-moditem-alist mod))))
  :guard-debug t
  :prepwork ((local (in-theory (enable vl-hid/id-p))))
  :returns (mv successp
               (range vl-maybe-range-p :hyp :fguard))
  (b* (((when (vl-idexpr-p x))
        (vl-find-net/reg-range (vl-idexpr->name x) mod ialist)))
    (vl-hid-range x)))







; -----------------------------------------------------------------------------
;
;                   Slicing Expressions into Bit-Expressions
;
; -----------------------------------------------------------------------------

(defsection vl-msb-bitslice-constint
  :parents (vl-msb-bitslice-expr)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>
@(see vl-constint-p) atom into MSB-ordered, single-bit expressions."

  :long "<p><b>Signature:</b> @(call vl-msb-bitslice-constint) returns a list
of one-bit wide, unsigned expressions.</p>

<p>We require that @('X') is a well-typed constant integer expression, i.e.,
our @(see expression-sizing) transform should have already been run.  Note that
the \"propagation step\" of expression sizing should have already handled any
sign/zero extensions, so we assume here that the atom's @('finalwidth') is
already correct and that no extensions are necessary.</p>"

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
  (local (in-theory (disable acl2::functional-commutativity-of-minus-*-left)))

  (local (defthm logand-1
           (implies (natp value)
                    (equal (logand value 1)
                           (mod value 2)))))


; A logbitp based approach would potentially be more efficient when dealing
; with bignums, since shifting will cause us to generate new bignums.  But it
; would be pretty silly to be worried about things like that.

  (defund vl-lsb-bitslice-constint-aux (len value)
    (declare (xargs :guard (and (natp len)
                                (natp value))
                    :measure (nfix len)))
    (if (mbe :logic (zp len)
             :exec (= len 0))
        nil
      (let* ((floor2 (mbe :logic (floor value 2)
                          :exec (ash value -1)))
             (mod2   (mbe :logic (mod value 2)
                          :exec (logand value 1)))
             (bit    (if (= mod2 0)
                         |*sized-1'b0*|
                       |*sized-1'b1*|)))
        (cons bit
              (vl-lsb-bitslice-constint-aux (mbe :logic (- (nfix len) 1)
                                                 :exec (- len 1))
                                            floor2)))))

  (local (in-theory (enable vl-lsb-bitslice-constint-aux)))

  (defthm true-listp-of-vl-lsb-bitslice-constint
    (true-listp (vl-lsb-bitslice-constint-aux len value))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-lsb-bitslice-constint-aux
    (vl-exprlist-p (vl-lsb-bitslice-constint-aux len value)))

  (defthm len-of-vl-lsb-bitslice-constint-aux
    (equal (len (vl-lsb-bitslice-constint-aux len value))
           (nfix len)))

  (defthm vl-exprlist->finalwidths-of-vl-lsb-bitslice-constint-aux
    (equal (vl-exprlist->finalwidths (vl-lsb-bitslice-constint-aux len value))
           (repeat 1 (nfix len)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm vl-exprlist->finaltypes-of-vl-lsb-bitslice-constint-aux
    (equal (vl-exprlist->finaltypes (vl-lsb-bitslice-constint-aux len value))
           (repeat :vl-unsigned (nfix len)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm vl-exprlist-welltyped-p-of-vl-lsb-bitslice-constint-aux
    (vl-exprlist-welltyped-p (vl-lsb-bitslice-constint-aux len value)))


  (defund vl-msb-bitslice-constint-aux (len value acc)
    "Accumulate lsb's into acc, which produces an MSB-ordered list."
    (declare (xargs :guard (and (natp len)
                                (natp value))
                    :measure (nfix len)))
    (mbe :logic
         (revappend (vl-lsb-bitslice-constint-aux len value) acc)
         :exec
         (if (mbe :logic (zp len)
                  :exec (= len 0))
             acc
           (let* ((floor2 (mbe :logic (floor value 2)
                               :exec (ash value -1)))
                  (mod2   (mbe :logic (mod value 2)
                               :exec (logand value 1)))
                  (bit    (if (= mod2 0)
                              |*sized-1'b0*|
                            |*sized-1'b1*|)))
             (vl-msb-bitslice-constint-aux (mbe :logic (- (nfix len) 1)
                                                :exec (- len 1))
                                           floor2
                                           (cons bit acc))))))

  (local (in-theory (enable vl-atom-welltyped-p
                            vl-msb-bitslice-constint-aux)))

  (defund vl-msb-bitslice-constint (x)
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-atom-welltyped-p x)
                                (vl-fast-constint-p (vl-atom->guts x)))))
    (vl-msb-bitslice-constint-aux (vl-atom->finalwidth x)
                                  (vl-constint->value (vl-atom->guts x))
                                  nil))

  (local (in-theory (enable vl-msb-bitslice-constint)))

  (defthm true-listp-of-vl-msb-bitslice-constint
    (true-listp (vl-msb-bitslice-constint x))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-msb-bitslice-constint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x))))
             (vl-exprlist-p (vl-msb-bitslice-constint x))))

  (defthm len-of-vl-msb-bitslice-constint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x))))
             (equal (len (vl-msb-bitslice-constint x))
                    (vl-atom->finalwidth x))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-constint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x))))
             (equal (vl-exprlist->finalwidths (vl-msb-bitslice-constint x))
                    (repeat 1 (vl-atom->finalwidth x)))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-constint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x))))
             (equal (vl-exprlist->finaltypes (vl-msb-bitslice-constint x))
                    (repeat :vl-unsigned (vl-atom->finalwidth x)))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-constint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-constint-p (vl-atom->guts x))))
             (vl-exprlist-welltyped-p (vl-msb-bitslice-constint x))))

  (local
   (assert!
    (equal
     (vl-msb-bitslice-constint (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                                     :origtype :vl-signed
                                                                     :value 7)
                                             :finalwidth 5
                                             :finaltype :vl-signed))
     (list |*sized-1'b0*| |*sized-1'b0*| |*sized-1'b1*| |*sized-1'b1*| |*sized-1'b1*|))))

  (local
   (assert!
    (equal
     (vl-msb-bitslice-constint (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                                     :origtype :vl-unsigned
                                                                     :value 15)
                                             :finalwidth 5
                                             :finaltype :vl-unsigned))
     (list |*sized-1'b0*| |*sized-1'b1*| |*sized-1'b1*| |*sized-1'b1*| |*sized-1'b1*|)))))




(defsection vl-msb-bitslice-weirdint
  :parents (vl-msb-bitslice-expr)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>,
@(see vl-weirdint-p) atom into MSB-ordered, single-bit expressions."

  :long "<p><b>Signature:</b> @(call vl-msb-bitslice-weirdint) returns a list
of one-bit wide expressions.</p>

<p>We require that @('X') is a well-typed constant integer expression, i.e.,
our @(see expression-sizing) transform should have already been run.  Note that
the \"propagation step\" of expression sizing should have already handled any
sign/zero extensions, so we assume here that the atom's @('finalwidth') is
already correct and that no extensions are necessary.</p>"

; The bits of a weirdint are already in msb-first order, so we just need to
; convert them into individual bits in the same order.

  (defund vl-bit-to-sized-expr (x)
    (declare (xargs :guard (vl-bit-p x)))
    (case x
      (:vl-0val |*sized-1'b0*|)
      (:vl-1val |*sized-1'b1*|)
      (:vl-xval |*sized-1'bx*|)
      (:vl-zval |*sized-1'bz*|)))

  (defprojection vl-bitlist-to-sized-exprs (x)
    (vl-bit-to-sized-expr x)
    :guard (vl-bitlist-p x))

  (local (in-theory (enable vl-bit-p
                            vl-bit-to-sized-expr
                            vl-atom-welltyped-p)))

  (defthm vl-exprlist-p-of-vl-bitlist-to-sized-exprs
    (implies (force (vl-bitlist-p x))
             (vl-exprlist-p (vl-bitlist-to-sized-exprs x)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-exprlist->finalwidths-of-vl-bitlist-to-sized-exprs
    (implies (force (vl-bitlist-p x))
             (equal (vl-exprlist->finalwidths (vl-bitlist-to-sized-exprs x))
                    (repeat 1 (len x))))
    :hints(("Goal"
            :in-theory (enable repeat)
            :induct (len x))))

  (defthm vl-exprlist->finaltypes-of-vl-bitlist-to-sized-exprs
    (implies (force (vl-bitlist-p x))
             (equal (vl-exprlist->finaltypes (vl-bitlist-to-sized-exprs x))
                    (repeat :vl-unsigned (len x))))
    :hints(("Goal"
            :in-theory (enable repeat)
            :induct (len x))))

  (defthm vl-exprlist-welltyped-p-of-vl-bitlist-to-sized-exprs
    (implies (force (vl-bitlist-p x))
             (vl-exprlist-welltyped-p (vl-bitlist-to-sized-exprs x)))
    :hints(("Goal" :induct (len x))))



  (defund vl-msb-bitslice-weirdint (x)
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-atom-welltyped-p x)
                                (vl-fast-weirdint-p (vl-atom->guts x)))))
    (vl-bitlist-to-sized-exprs (vl-weirdint->bits (vl-atom->guts x))))

  (local (in-theory (enable vl-msb-bitslice-weirdint)))

  (defthm true-listp-of-vl-msb-bitslice-weirdint
    (true-listp (vl-msb-bitslice-weirdint x))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-msb-bitslice-weirdint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x))))
             (vl-exprlist-p (vl-msb-bitslice-weirdint x))))

  (defthm len-of-vl-msb-bitslice-weirdint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x))))
             (equal (len (vl-msb-bitslice-weirdint x))
                    (vl-atom->finalwidth x))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-weirdint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x))))
             (equal (vl-exprlist->finalwidths (vl-msb-bitslice-weirdint x))
                    (repeat 1 (vl-atom->finalwidth x)))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-weirdint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x))))
             (equal (vl-exprlist->finaltypes (vl-msb-bitslice-weirdint x))
                    (repeat :vl-unsigned (vl-atom->finalwidth x)))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-weirdint
    (implies (and (force (vl-atom-p x))
                  (force (vl-atom-welltyped-p x))
                  (force (vl-weirdint-p (vl-atom->guts x))))
             (vl-exprlist-welltyped-p (vl-msb-bitslice-weirdint x))))

  (local
   (assert!
    (equal
     (vl-msb-bitslice-weirdint
      (make-vl-atom :finalwidth 5
                    :finaltype :vl-signed
                    :guts
                    (make-vl-weirdint
                     :origwidth 5
                     :origtype :vl-signed
                     :bits '(:vl-zval :vl-0val :vl-1val :vl-1val :vl-xval))))
     (list |*sized-1'bz*| |*sized-1'b0*| |*sized-1'b1*| |*sized-1'b1*| |*sized-1'bx*|)))))


(defsection vl-msb-bitslice-name
  (local (in-theory (enable vl-maybe-range-p
                            vl-maybe-range-resolved-p
                            vl-maybe-range-size)))

  (define vl-msb-bitslice-name ((x        stringp)
                                (mod      vl-module-p)
                                (ialist   (equal ialist (vl-moditem-alist mod)))
                                (warnings vl-warninglist-p))
    (b* (((mv successp range)
          (vl-find-net/reg-range x mod ialist))
         ((unless successp)
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Expected a net/reg declaration for ~a0."
                     :args (list x))
              nil))

         ((unless (vl-maybe-range-resolved-p range))
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Expected the range of ~a0 to be resolved, but it ~
                           is ~a1."
                     :args (list x range))
              nil))

         (msb-index (if range (vl-resolved->val (vl-range->msb range)) 0))
         (lsb-index (if range (vl-resolved->val (vl-range->lsb range)) 0))
         ;; Main-bits are, e.g., (foo[5] ... foo[3]) for wire [5:3] foo;
         ;; We now try to avoid introducing bitselects for wires that do
         ;; not have a range, since some Verilog implementations complain
         ;; about that sort of thing.  It's okay to force the width/type
         ;; here to 1-bit unsigned because the spec is that we're producing
         ;; a list of 1-bit, unsigned expressions that are semantically
         ;; equivalent to the input expression, and we're going to make any
         ;; sign/zero extension explicit immediately below.
         (main-bits (if range
                        (vl-make-msb-to-lsb-bitselects
                         (vl-idexpr x (vl-range-size range) :vl-unsigned)
                         msb-index lsb-index)
                      (list (vl-idexpr x 1 :vl-unsigned)))))
      (mv t warnings main-bits)))

  (local (in-theory (enable vl-msb-bitslice-name)))

  (defmvtypes vl-msb-bitslice-name (booleanp nil true-listp))

  (defthm vl-warninglist-p-of-vl-msb-bitslice-name
    (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
      (implies (vl-warninglist-p warnings)
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-exprlist-p-of-vl-msb-bitslice-name
    (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
      (implies (and (force (stringp x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-make-msb-to-lsb-bitselects))))

  (encapsulate nil
    (local (defthm nonempty-by-len-of-vl-make-msb-to-lsb-bitselects-asdfaf
             (let ((x (vl-make-msb-to-lsb-bitselects expr msb lsb)))
               (iff x
                    (< 0 (len x))))))

    (defthm nonempty-of-vl-msb-bitslice-name
      (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
        (implies (mv-nth 0 ret)
                 (mv-nth 2 ret)))))


  ;; Ugh, the proof that all the widths are 1 is pretty awkward, but it's
  ;; essentially just a matter of chaining together stupid properties.


  (local (defthm vl-make-list-of-bitselects-degenerate
           (equal (vl-make-list-of-bitselects x n n)
                  (list (vl-make-bitselect x n)))
           :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects)))))

  (local (defthm promote-vl-expr->finalwidth
           (implies (vl-atom-p x)
                    (equal (vl-expr->finalwidth x)
                           (vl-atom->finalwidth x)))
           :hints(("Goal" :in-theory (enable vl-expr->finalwidth)))))

  (local (defthm j1
           (equal (equal (append x (list a)) (list b))
                  (and (equal a b)
                       (atom x)))
           :hints(("Goal" :in-theory (enable append)))))

  (local (defun cdr-dec-induct (x n)
           (if (zp n)
               (list x n)
             (cdr-dec-induct (cdr x) (- n 1)))))

  (local (defthm j2
           (equal (equal (append x (list y))
                         (repeat a n))
                  (and (posp n)
                       (equal y a)
                       (equal (list-fix x) (repeat a (- n 1)))))
           :hints(("Goal"
                   :induct (cdr-dec-induct x n)
                   :in-theory (enable repeat)))))

  (local (defthm c0
           (all-equalp 1 (vl-exprlist->finalwidths
                          (vl-make-list-of-bitselects expr low high)))))

  (local (defthm c1
           (iff (member-equal (first (rev x)) x)
                (consp x))
           :hints(("Goal" :in-theory (enable rev)))))

  (local (defthm c2
           (implies (and (all-equalp a x)
                         (member-equal b x))
                    (equal a b))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (disable all-equalp)))
           :rule-classes nil))

  (local (defthm c4
           (equal (vl-expr->finalwidth
                   (first (rev (vl-make-list-of-bitselects expr low high))))
                  1)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finalwidths-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finalwidth
                                        (first (rev (vl-make-list-of-bitselects expr low high)))))
                                    (a 1)
                                    (x (vl-exprlist->finalwidths
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm c5
           (equal (vl-expr->finalwidth
                   (first (vl-make-list-of-bitselects expr low high)))
                  1)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finalwidths-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finalwidth
                                        (first (vl-make-list-of-bitselects expr low high))))
                                    (a 1)
                                    (x (vl-exprlist->finalwidths
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm main
           (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
             (all-equalp 1 (vl-exprlist->finalwidths (mv-nth 2 ret))))
           :hints(("Goal" :in-theory (e/d (vl-make-msb-to-lsb-bitselects)
                                          (all-equalp))))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-name
    (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
      (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
             (repeat 1 (len (mv-nth 2 ret)))))
    :hints (("goal" :in-theory (disable vl-msb-bitslice-name main)
             :use main)))


  (local (defthm vl-exprlist->finaltypes-of-repeat
           (equal (vl-exprlist->finaltypes (repeat a n))
                  (repeat (vl-expr->finaltype a) n))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm d0
           (all-equalp :vl-unsigned (vl-exprlist->finaltypes
                                     (vl-make-list-of-bitselects expr low high)))))

  (local (defthm d4
           (equal (vl-expr->finaltype
                   (first (rev (vl-make-list-of-bitselects expr low high))))
                  :vl-unsigned)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finaltypes-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finaltype
                                        (first (rev (vl-make-list-of-bitselects expr low high)))))
                                    (a :vl-unsigned)
                                    (x (vl-exprlist->finaltypes
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm d5
           (equal (vl-expr->finaltype
                   (first (vl-make-list-of-bitselects expr low high)))
                  :vl-unsigned)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finaltypes-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finaltype
                                        (first (vl-make-list-of-bitselects expr low high))))
                                    (a :vl-unsigned)
                                    (x (vl-exprlist->finaltypes
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm main2
           (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
             (all-equalp :vl-unsigned (vl-exprlist->finaltypes (mv-nth 2 ret))))
           :hints(("Goal" :in-theory (e/d (vl-make-msb-to-lsb-bitselects)
                                          (all-equalp))))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-name
    (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
      (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
             (repeat :vl-unsigned (len (mv-nth 2 ret)))))
    :hints (("goal" :in-theory (disable vl-msb-bitslice-name main2)
             :use main2)))



  (defthm vl-expr-welltyped-p-of-vl-make-bitselect
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp n)))
             (vl-expr-welltyped-p (vl-make-bitselect expr n)))
    :hints(("Goal" :in-theory (enable vl-make-bitselect
                                      vl-make-index
                                      vl-atom-welltyped-p
                                      vl-expr-welltyped-p))))

  (defthm vl-expr-welltyped-p-of-vl-idexpr
    (implies (and (vl-exprtype-p finaltype)
                  (posp finalwidth)
                  (stringp name))
             (vl-expr-welltyped-p (vl-idexpr name finalwidth finaltype)))
    :hints(("Goal" :in-theory (e/d (vl-idexpr
                                    vl-expr-welltyped-p
                                    vl-atom-welltyped-p)))))

  (defthm vl-exprlist-welltyped-p-of-vl-make-list-of-bitselects
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp low))
                  (force (natp high))
                  (force (<= low high)))
             (vl-exprlist-welltyped-p (vl-make-list-of-bitselects expr low high)))
    :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-name
    (let ((ret (vl-msb-bitslice-name x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (stringp x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-make-msb-to-lsb-bitselects)))))



(defsection vl-msb-bitslice-hid
  (local (in-theory (enable vl-maybe-range-p
                            vl-maybe-range-resolved-p
                            vl-maybe-range-size
                            vl-hidexpr-welltyped-p)))

  (define vl-msb-bitslice-hid ((x        (and (vl-expr-p x)
                                              (vl-nonatom-p x)
                                              (vl-hidexpr-p x)
                                              (vl-expr-welltyped-p x)))
                               (warnings vl-warninglist-p))
    (b* (((mv ok range) (vl-hid-range x))
         ((unless (and ok (vl-maybe-range-resolved-p range)))
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Expected the range of ~a0 to be resolved"
                     :args (list x))
              nil))

         ((unless range)
          (mv t warnings (list x)))

         (msb-index (vl-resolved->val (vl-range->msb range)))
         (lsb-index (vl-resolved->val (vl-range->lsb range)))
         ;; Main-bits are, e.g., (foo[5] ... foo[3]) for wire [5:3] foo;
         ;; We now try to avoid introducing bitselects for wires that do
         ;; not have a range, since some Verilog implementations complain
         ;; about that sort of thing.  It's okay to force the width/type
         ;; here to 1-bit unsigned because the spec is that we're producing
         ;; a list of 1-bit, unsigned expressions that are semantically
         ;; equivalent to the input expression, and we're going to make any
         ;; sign/zero extension explicit immediately below.
         (main-bits (vl-make-msb-to-lsb-bitselects
                     x msb-index lsb-index)))
      (mv t warnings main-bits)))

  (local (in-theory (enable vl-msb-bitslice-hid)))

  (defmvtypes vl-msb-bitslice-hid (booleanp nil true-listp))

  (defthm vl-warninglist-p-of-vl-msb-bitslice-hid
    (let ((ret (vl-msb-bitslice-hid x warnings)))
      (implies (vl-warninglist-p warnings)
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-exprlist-p-of-vl-msb-bitslice-hid
    (let ((ret (vl-msb-bitslice-hid x warnings)))
      (implies (and (force (vl-expr-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-make-msb-to-lsb-bitselects))))

  (encapsulate nil
    (local (defthm nonempty-by-len-of-vl-make-msb-to-lsb-bitselects-asdfaf
             (let ((x (vl-make-msb-to-lsb-bitselects expr msb lsb)))
               (iff x
                    (< 0 (len x))))))

    (defthm nonempty-of-vl-msb-bitslice-hid
      (let ((ret (vl-msb-bitslice-hid x warnings)))
        (implies (mv-nth 0 ret)
                 (mv-nth 2 ret)))))


  ;; Ugh, the proof that all the widths are 1 is pretty awkward, but it's
  ;; essentially just a matter of chaining together stupid properties.


  (local (defthm vl-make-list-of-bitselects-degenerate
           (equal (vl-make-list-of-bitselects x n n)
                  (list (vl-make-bitselect x n)))
           :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects)))))

  (local (defthm promote-vl-expr->finalwidth
           (implies (vl-atom-p x)
                    (equal (vl-expr->finalwidth x)
                           (vl-atom->finalwidth x)))
           :hints(("Goal" :in-theory (enable vl-expr->finalwidth)))))

  (local (defthm j1
           (equal (equal (append x (list a)) (list b))
                  (and (equal a b)
                       (atom x)))
           :hints(("Goal" :in-theory (enable append)))))

  (local (defun cdr-dec-induct (x n)
           (if (zp n)
               (list x n)
             (cdr-dec-induct (cdr x) (- n 1)))))

  (local (defthm j2
           (equal (equal (append x (list y))
                         (repeat a n))
                  (and (posp n)
                       (equal y a)
                       (equal (list-fix x) (repeat a (- n 1)))))
           :hints(("Goal"
                   :induct (cdr-dec-induct x n)
                   :in-theory (enable repeat)))))

  (local (defthm c0
           (all-equalp 1 (vl-exprlist->finalwidths
                          (vl-make-list-of-bitselects expr low high)))))

  (local (defthm c1
           (iff (member-equal (first (rev x)) x)
                (consp x))
           :hints(("Goal" :in-theory (enable rev)))))

  (local (defthm c2
           (implies (and (all-equalp a x)
                         (member-equal b x))
                    (equal a b))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (disable all-equalp)))
           :rule-classes nil))

  (local (defthm c4
           (equal (vl-expr->finalwidth
                   (first (rev (vl-make-list-of-bitselects expr low high))))
                  1)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finalwidths-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finalwidth
                                        (first (rev (vl-make-list-of-bitselects expr low high)))))
                                    (a 1)
                                    (x (vl-exprlist->finalwidths
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm c5
           (equal (vl-expr->finalwidth
                   (first (vl-make-list-of-bitselects expr low high)))
                  1)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finalwidths-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finalwidth
                                        (first (vl-make-list-of-bitselects expr low high))))
                                    (a 1)
                                    (x (vl-exprlist->finalwidths
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm main
           (implies (and (vl-expr-p x)
                         (vl-nonatom-p x)
                         (vl-hidexpr-p x)
                         (vl-expr-welltyped-p x))
                    (let ((ret (vl-msb-bitslice-hid x warnings)))
                      (all-equalp 1 (vl-exprlist->finalwidths (mv-nth 2 ret)))))
           :hints(("Goal" :in-theory (e/d (vl-make-msb-to-lsb-bitselects
                                           vl-expr->finalwidth)
                                          (all-equalp))
                   :expand ((vl-hidexpr-p x)
                            (vl-expr-welltyped-p x))))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-hid
    (implies (and (vl-expr-p x)
                  (vl-nonatom-p x)
                  (vl-hidexpr-p x)
                  (vl-expr-welltyped-p x))
             (let ((ret (vl-msb-bitslice-hid x warnings)))
               (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
                      (repeat 1 (len (mv-nth 2 ret))))))
    :hints (("goal" :in-theory (disable vl-msb-bitslice-hid main)
             :use main)))


  (local (defthm vl-exprlist->finaltypes-of-repeat
           (equal (vl-exprlist->finaltypes (repeat a n))
                  (repeat (vl-expr->finaltype a) n))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm d0
           (all-equalp :vl-unsigned (vl-exprlist->finaltypes
                                     (vl-make-list-of-bitselects expr low high)))))

  (local (defthm d4
           (equal (vl-expr->finaltype
                   (first (rev (vl-make-list-of-bitselects expr low high))))
                  :vl-unsigned)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finaltypes-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finaltype
                                        (first (rev (vl-make-list-of-bitselects expr low high)))))
                                    (a :vl-unsigned)
                                    (x (vl-exprlist->finaltypes
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm d5
           (equal (vl-expr->finaltype
                   (first (vl-make-list-of-bitselects expr low high)))
                  :vl-unsigned)
           :hints(("Goal"
                   :in-theory (disable vl-exprlist->finaltypes-of-vl-make-list-of-bitselects)
                   :use ((:instance c2
                                    (b (vl-expr->finaltype
                                        (first (vl-make-list-of-bitselects expr low high))))
                                    (a :vl-unsigned)
                                    (x (vl-exprlist->finaltypes
                                        (vl-make-list-of-bitselects expr low high)))))))))

  (local (defthm main2
           (implies (and (vl-expr-p x)
                         (vl-nonatom-p x)
                         (vl-hidexpr-p x)
                         (vl-expr-welltyped-p x))
                    (let ((ret (vl-msb-bitslice-hid x warnings)))
                      (all-equalp :vl-unsigned (vl-exprlist->finaltypes (mv-nth 2 ret)))))
           :hints(("Goal" :in-theory (e/d (vl-make-msb-to-lsb-bitselects
                                           vl-expr->finaltype)
                                          (all-equalp))
                   :expand ((vl-hidexpr-p x)
                            (vl-expr-welltyped-p x))))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-hid
    (implies (and (vl-expr-p x)
                  (vl-nonatom-p x)
                  (vl-hidexpr-p x)
                  (vl-expr-welltyped-p x))
             (let ((ret (vl-msb-bitslice-hid x warnings)))
               (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
                      (repeat :vl-unsigned (len (mv-nth 2 ret))))))
    :hints (("goal" :in-theory (disable vl-msb-bitslice-hid main2)
             :use main2)))



  (defthm vl-expr-welltyped-p-of-vl-make-bitselect
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp n)))
             (vl-expr-welltyped-p (vl-make-bitselect expr n)))
    :hints(("Goal" :in-theory (enable vl-make-bitselect
                                      vl-make-index
                                      vl-atom-welltyped-p
                                      vl-expr-welltyped-p))))

  (defthm vl-expr-welltyped-p-of-vl-idexpr
    (implies (and (vl-exprtype-p finaltype)
                  (posp finalwidth)
                  (stringp name))
             (vl-expr-welltyped-p (vl-idexpr name finalwidth finaltype)))
    :hints(("Goal" :in-theory (e/d (vl-idexpr
                                    vl-expr-welltyped-p
                                    vl-atom-welltyped-p)))))

  (defthm vl-exprlist-welltyped-p-of-vl-make-list-of-bitselects
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp low))
                  (force (natp high))
                  (force (<= low high)))
             (vl-exprlist-welltyped-p (vl-make-list-of-bitselects expr low high)))
    :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-hid
    (let ((ret (vl-msb-bitslice-hid x warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (vl-hidexpr-p x))
                    (force (vl-expr-welltyped-p x)))
               (vl-exprlist-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-make-msb-to-lsb-bitselects))))

  (defthm len-of-vl-msb-bitslice-hid
    (let ((ret (vl-msb-bitslice-hid x warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (vl-hidexpr-p x))
                    (force (vl-expr-welltyped-p x)))
               (equal (len (mv-nth 2 ret))
                      (vl-expr->finalwidth x))))
    :hints (("goal" :in-theory (enable vl-expr->finalwidth
                                       vl-width-from-difference
                                       vl-range-size)
             :expand ((vl-hidexpr-p x)
                      (vl-expr-welltyped-p x))))))



(defsection vl-msb-bitslice-id
  :parents (vl-msb-bitslice-expr)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>,
@(see vl-id-p) atom into MSB-ordered, single-bit expressions."

  :long "<p><b>Signature:</b> @(call vl-msb-bitslice-id) returns @('(mv
successp warnings bits)'), where @('bits') is a list of one-bit wide
expressions on success.</p>

<p>We require that @('X') is a well-typed identifier expression, i.e., our
@(see expression-sizing) transform should have already been run.  See also the
discussion in @(see vl-atom-welltyped-p) and note that the finalwidth and
finaltype of the identifier may differ from its declaration.  We expect these
widths to be at least as large as the identifier's width, and differences here
are used to indicate zero/sign extensions.</p>

<p>The list of bits we want to return here depends on the order of the msb
and lsb indices for the wire.  For instance, if the wire is declared as:</p>

@({
wire [3:0] w;
})

<p>Then we want to return @('{w[3], w[2], w[1], w[0]}').  But if the wire is
instead declared as:</p>

@({
wire [0:3] w;
})

<p>Then we will want to return @('{w[0], w[1], w[2], w[3]}') instead.</p>"

  (local (in-theory (enable vl-atom-welltyped-p
                            vl-maybe-range-p
                            vl-maybe-range-resolved-p
                            vl-maybe-range-size)))


  (define vl-msb-bitslice-id (x mod ialist warnings)
    "Returns (MV SUCCESSP WARNINGS BITS)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-atom-welltyped-p x)
                                (vl-fast-id-p (vl-atom->guts x))
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))
                    :guard-debug t))
    (b* (((vl-atom x) x)
         (name (vl-id->name x.guts))
         ((mv successp warnings main-bits)
          (vl-msb-bitslice-name name mod ialist warnings))
         ((unless successp)
          (mv nil warnings nil))

         (nwires (len main-bits))
         ((when (< x.finalwidth nwires))
          (mv nil
              (fatal :type :vl-programming-error
                     :msg "Found a plain, atomic identifier expression for ~
                           ~a0 with width ~x1, which is smaller than ~x2, the ~
                           size of its range.  Expected all occurrences of ~
                           plain identifiers to have widths that are at least ~
                           as large as their declarations."
                     :args (list x x.finalwidth nwires))
              nil))

         ((when (= nwires x.finalwidth))
          ;; There's no sign/zero extension so this is straightforward:
          (mv t warnings main-bits))

         ;; Otherwise, there's an extension being done here.
         (extension-bit (if (eq x.finaltype :vl-signed)
                            (car main-bits) ;; sign extension
                          |*sized-1'b0*|))  ;; zero extension
         (bits (append (repeat extension-bit (- x.finalwidth nwires))
                       main-bits)))
      (mv t warnings bits)))

  (local (in-theory (enable vl-msb-bitslice-id)))

  (defmvtypes vl-msb-bitslice-id (booleanp nil true-listp))

  (defthm vl-warninglist-p-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (vl-warninglist-p warnings)
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-exprlist-p-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (and (force (vl-atom-p x))
                    (force (vl-atom-welltyped-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-make-msb-to-lsb-bitselects))))

  (defthm len-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-atom-welltyped-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (len (mv-nth 2 ret))
                      (vl-atom->finalwidth x)))))


  (local (defthm vl-exprlist->finalwidths-of-repeat
           (equal (vl-exprlist->finalwidths (repeat a n))
                  (repeat (vl-expr->finalwidth a) n))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (in-theory (disable car-of-vl-exprlist->finalwidths)))
  (local (defthm vl-expr->finalwidth-of-first
           (equal (vl-expr->finalwidth (first x))
                  (first (vl-exprlist->finalwidths x)))))

  (local (defthm first-repeat
           (implies (not (zp len))
                    (equal (first (repeat v len)) v))
           :hints(("Goal" :in-theory (enable repeat)))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-atom-welltyped-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
                      (repeat 1 (vl-atom->finalwidth x))))))

  (local (defthm vl-exprlist->finaltypes-of-repeat
           (equal (vl-exprlist->finaltypes (repeat a n))
                  (repeat (vl-expr->finaltype a) n))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (in-theory (disable car-of-vl-exprlist->finaltypes)))
  (local (defthm vl-expr->finaltype-of-first
           (equal (vl-expr->finaltype (first x))
                  (first (vl-exprlist->finaltypes x)))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-atom-welltyped-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
                      (repeat :vl-unsigned (vl-atom->finalwidth x))))))



  (defthm vl-expr-welltyped-p-of-vl-make-bitselect
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp n)))
             (vl-expr-welltyped-p (vl-make-bitselect expr n)))
    :hints(("Goal" :in-theory (enable vl-make-bitselect
                                      vl-make-index
                                      vl-expr-welltyped-p))))

  (defthm vl-exprlist-welltyped-p-of-vl-make-list-of-bitselects
    (implies (and (force (vl-expr-p expr))
                  (force (vl-expr-welltyped-p expr))
                  (force (natp low))
                  (force (natp high))
                  (force (<= low high)))
             (vl-exprlist-welltyped-p (vl-make-list-of-bitselects expr low high)))
    :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-id
    (let ((ret (vl-msb-bitslice-id x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-atom-welltyped-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-make-msb-to-lsb-bitselects)))))



(defsection vl-msb-bitslice-partselect
  :parents (vl-msb-bitslice-expr)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>,
part-select into into MSB-ordered, single-bit expressions."

  :long "<p><b>Signature:</b> @(call vl-msb-bitslice-partselect) returns @('(mv
successp warnings bits)'), where @('bits') is a list of one-bit wide
expressions on success.</p>

<p>We require that @('X') is a well-typed, and also @(see vl-expr-sliceable-p)
part-select expression, i.e., our @(see expression-sizing) transform should
have already been run.</p>

<p>The list of bits we want to return here depends on the order of the msb and
lsb indices for the wire.  To consider the cases, imagine:</p>

@({
wire [3:0] a;
wire [0:3] b;
})

<p>There are four kinds of selects we might encounter, basically:</p>

<ul>
<li>@('a[2:0]'), which should become @('{a[2], a[1], a[0]}')</li>
<li>@('b[0:2]'), which should become @('{b[0], b[1], b[2]}')</li>
<li>@('a[0:2]') or @('b[2:0]'), which should be disallowed.</li>
</ul>"

  (local (in-theory (enable vl-expr-sliceable-p
                            vl-expr-welltyped-p
                            vl-maybe-range-p
                            vl-maybe-range-resolved-p
                            vl-maybe-range-size)))

  (define vl-msb-bitslice-partselect (x mod ialist warnings)
    "Returns (MV SUCCESSP WARNINGS BITS)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-nonatom-p x)
                                (equal (vl-nonatom->op x) :vl-partselect-colon)
                                (vl-expr-welltyped-p x)
                                (vl-expr-sliceable-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))
                    :guard-debug t))
    (b* ((args  (vl-nonatom->args x))

         (from  (first args))
         (left  (second args))
         (right (third args))

         ;;(name      (vl-idexpr->name from))
         (left-val  (vl-resolved->val left))
         (right-val (vl-resolved->val right))

         ((mv successp range)
          (vl-find-hid/id-range from mod ialist))
         ((unless successp)
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Expected a net/reg declaration for ~a0."
                     :args (list x))
              nil))

         ((unless (vl-maybe-range-resolved-p range))
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Expected the range of ~a0 to be resolved, but it ~
                           is ~a1."
                     :args (list x range))
              nil))

         ((unless range)
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Trying to do a part-select, ~a0, but ~a1 does not ~
                           have a range."
                     :args (list x from))
              nil))

         ((vl-range range) range)
         (wire-msb-val (vl-resolved->val range.msb))
         (wire-lsb-val (vl-resolved->val range.lsb))

         (wire-is-msb-first-p   (>= wire-msb-val wire-lsb-val))
         (select-is-msb-first-p (>= left-val right-val))
         (select-is-trivial-p   (= left-val right-val))

         ((unless (or (equal wire-is-msb-first-p select-is-msb-first-p)
                      select-is-trivial-p))
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Trying to do a part-select, ~a0, in the opposite ~
                           order of the range from ~a1 (~a2)."
                     :args (list x from range))
              nil))

         ;; Sure, why not do another bounds check.
         (wire-max (max wire-msb-val wire-lsb-val))
         (wire-min (min wire-msb-val wire-lsb-val))
         (sel-max  (max left-val right-val))
         (sel-min  (min left-val right-val))
         ((unless (and (<= wire-min sel-min)
                       (<= sel-max wire-max)))
          (mv nil
              (fatal :type :vl-slicing-fail
                     :msg "Part select ~a0 is out of bounds; the range of ~a1 ~
                           is only ~a2."
                     :args (list x from range))
              nil))

         (bits (vl-make-msb-to-lsb-bitselects from left-val right-val)))
      (mv t warnings bits)))

  (local (in-theory (enable vl-msb-bitslice-partselect)))

  (defmvtypes vl-msb-bitslice-partselect (booleanp nil true-listp))

  (defthm vl-warninglist-p-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (vl-warninglist-p warnings)
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-exprlist-p-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (and (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (equal (vl-nonatom->op x) :vl-partselect-colon))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-p (mv-nth 2 ret)))))

  (defthm len-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (equal (vl-nonatom->op x) :vl-partselect-colon))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (len (mv-nth 2 ret))
                      (vl-nonatom->finalwidth x)))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (equal (vl-nonatom->op x) :vl-partselect-colon))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
                      (repeat 1 (vl-nonatom->finalwidth x))))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (equal (vl-nonatom->op x) :vl-partselect-colon))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
                      (repeat :vl-unsigned (vl-nonatom->finalwidth x))))))

  (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-partselect
    (let ((ret (vl-msb-bitslice-partselect x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-nonatom-p x))
                    (force (equal (vl-nonatom->op x) :vl-partselect-colon))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-make-msb-to-lsb-bitselects)))))





(defsection vl-msb-bitslice-expr
  :parents (expr-slicing)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>,
<see topic='@(url vl-expr-sliceable-p)'>sliceable</see> expression into a list
of MSB-ordered, single-bit expressions."

  :long "<p><b>Signature:</b> @(call vl-msb-bitslice-expr) returns @('(mv
successp warnings bits)'), where @('bits') is a list of one-bit wide
expressions on success.</p>

<p>We require that @('X') is a well-typed expression, i.e., our @(see
expression-sizing) transform should have already been run.  On success, we
split the expression into its individual bits, and as basic correctness
properties, we prove that on success the resulting @('bits') is a list of
well-typed expressions where:</p>

<ul>
 <li>@('(len bits)') is the @('finalwidth') of @('x'), and</li>
 <li>each @('bit_i') is unsigned and has a @('finalwidth') of 1.</li>
</ul>

<p>The only reason this function will fail is if some identifier within @('x')
is not declared in the module or has a @('finalwidth') that is smaller than its
declared width.  These situations should not arise in practice if the
expressions have been sized correctly.</p>"

  (defxdoc vl-msb-bitslice-exprlist
    :parents (expr-slicing)
    :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>,
<see topic='@(url vl-expr-sliceable-p)'>sliceable</see> expression list into
a flat list of MSB-ordered, single-bit expressions."

    :long "<p>See @(see vl-msb-bitslice-expr)</p>")

  (mutual-recursion
   (defund vl-msb-bitslice-expr (x mod ialist warnings)
     "Returns (MV SUCCESSP WARNINGS BITS)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-expr-sliceable-p x)
                                 (vl-expr-welltyped-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (b* ((guts (vl-atom->guts x))
                ((when (vl-fast-constint-p guts))
                 (mv t warnings (vl-msb-bitslice-constint x)))
                ((when (vl-fast-weirdint-p guts))
                 (mv t warnings (vl-msb-bitslice-weirdint x))))
             ;; Else, must be an id.
             (vl-msb-bitslice-id x mod ialist warnings)))

          ((when (mbe :logic (atom x)
                      :exec nil))
           (er hard 'vl-msb-bitslice-expr "Impossible.")
           (mv nil warnings nil))

          (op   (vl-nonatom->op x))

          ((when (or (eq op :vl-hid-dot)
                     (eq op :vl-hid-arraydot)))
           (vl-msb-bitslice-hid x warnings))

          (args (vl-nonatom->args x))

          ((when (eq op :vl-bitselect))
           ;; Since we assume X is well-typed, it already has width 1 and is
           ;; unsigned, so we don't need to do anything.
           (mv t warnings (list x)))

          ((when (eq op :vl-partselect-colon))
           ;; From sliceable we get that it's an idexpr, and from welltyped
           ;; we know it has the right sizes, etc.
           (vl-msb-bitslice-partselect x mod ialist warnings))

          ((when (eq op :vl-concat))
           ;; From sliceable, we know all the args are sliceable; from welltyped
           ;; we know the sizes are all fine.
           (vl-msb-bitslice-exprlist args mod ialist warnings))

          ;; else, a multiconcat
          (mult   (first args))
          (concat (second args))
          ((mv successp warnings concat-bits)
           (vl-msb-bitslice-expr concat mod ialist warnings))
          ((unless successp)
           (mv nil warnings nil))
          (full-bits (flatten (repeat concat-bits (vl-resolved->val mult)))))
       (mv successp warnings full-bits)))

   (defund vl-msb-bitslice-exprlist (x mod ialist warnings)
     "Returns (MV SUCCESSP WARNINGS BITS)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-exprlist-sliceable-p x)
                                 (vl-exprlist-welltyped-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv t warnings nil))
          ((mv successp warnings bits1)
           (vl-msb-bitslice-expr (car x) mod ialist warnings))
          ((unless successp)
           (mv nil warnings nil))
          ((mv successp warnings bits2)
           (vl-msb-bitslice-exprlist (cdr x) mod ialist warnings))
          ((unless successp)
           (mv nil warnings nil)))
       (mv t warnings (append bits1 bits2)))))

  (flag::make-flag vl-flag-msb-bitslice-expr
                   vl-msb-bitslice-expr
                   :flag-mapping
                   ((vl-msb-bitslice-expr . expr)
                    (vl-msb-bitslice-exprlist . list)))

  (local (defun my-induct (x mod ialist warnings)
           (b* (((when (atom x))
                 (mv t warnings nil))
                ((mv successp warnings bits1)
                 (vl-msb-bitslice-expr (car x) mod ialist warnings))
                ((unless successp)
                 (mv nil warnings nil))
                ((mv successp warnings bits2)
                 (my-induct (cdr x) mod ialist warnings))
                ((unless successp)
                 (mv nil warnings nil)))
             (mv t warnings (append bits1 bits2)))))

  (defthm true-listp-of-vl-msb-bitslice-exprlist
    (true-listp (mv-nth 2 (vl-msb-bitslice-exprlist x mod ialist warnings)))
    :rule-classes :type-prescription
    :hints(("Goal"
            :expand ((vl-msb-bitslice-exprlist x mod ialist warnings))
            :induct (my-induct x mod ialist warnings))))

  (defthm true-listp-of-vl-msb-bitslice-expr
    (true-listp (mv-nth 2 (vl-msb-bitslice-expr x mod ialist warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :expand ((vl-msb-bitslice-expr x mod ialist warnings)))))

  (defthm-vl-flag-msb-bitslice-expr
    (defthm vl-warninglist-p-of-vl-msb-bitslice-expr
      (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-msb-bitslice-exprlist
      (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                     (vl-msb-bitslice-exprlist x mod ialist warnings)))))

  (local (in-theory (enable vl-expr-sliceable-p
                            vl-expr-welltyped-p)))

  (verify-guards vl-msb-bitslice-expr)

  (defthm-vl-flag-msb-bitslice-expr
    (defthm vl-exprlist-p-of-vl-msb-bitslice-expr
      (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
        (implies (and (force (vl-expr-p x))
                      (force (vl-expr-sliceable-p x))
                      (force (vl-expr-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-p (mv-nth 2 ret))))
      :flag expr)
    (defthm vl-exprlist-p-of-vl-msb-bitslice-exprlist
      (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
        (implies (and (force (vl-exprlist-p x))
                      (force (vl-exprlist-sliceable-p x))
                      (force (vl-exprlist-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-p (mv-nth 2 ret))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                     (vl-msb-bitslice-exprlist x mod ialist warnings)))))

  (local (defthm len-of-flatten-of-repeat
           (equal (len (flatten (repeat a n)))
                  (* (nfix n) (len a)))
           :hints(("Goal" :in-theory (enable repeat)))))

  (defthm-vl-flag-msb-bitslice-expr
    (defthm len-of-vl-msb-bitslice-expr
      (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-expr-p x))
                      (force (vl-expr-sliceable-p x))
                      (force (vl-expr-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (equal (len (mv-nth 2 ret))
                        (vl-expr->finalwidth x))))
      :flag expr)
    (defthm len-of-vl-msb-bitslice-exprlist
      (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-exprlist-p x))
                      (force (vl-exprlist-sliceable-p x))
                      (force (vl-exprlist-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (equal (len (mv-nth 2 ret))
                        (sum-nats (vl-exprlist->finalwidths x)))))
      :flag list)
    :hints(("Goal"
            :in-theory (enable vl-expr->finalwidth)
            :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                     (vl-msb-bitslice-exprlist x mod ialist warnings)))))



  (local (defthm all-equalp-of-vl-exprlist->finalwidths-of-flatten-repeat
           (equal (all-equalp a (vl-exprlist->finalwidths (flatten (repeat x n))))
                  (or (zp n)
                      (all-equalp a (vl-exprlist->finalwidths x))))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm-vl-flag-msb-bitslice-expr
           (defthm l0
             (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
               (implies (and (mv-nth 0 ret)
                             (force (vl-expr-p x))
                             (force (vl-expr-sliceable-p x))
                             (force (vl-expr-welltyped-p x))
                             (force (vl-module-p mod))
                             (force (equal ialist (vl-moditem-alist mod))))
                        (all-equalp 1 (vl-exprlist->finalwidths (mv-nth 2 ret)))))
             :flag expr)
           (defthm l1
             (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
               (implies (and (mv-nth 0 ret)
                             (force (vl-exprlist-p x))
                             (force (vl-exprlist-sliceable-p x))
                             (force (vl-exprlist-welltyped-p x))
                             (force (vl-module-p mod))
                             (force (equal ialist (vl-moditem-alist mod))))
                        (all-equalp 1 (vl-exprlist->finalwidths (mv-nth 2 ret)))))
             :flag list)
           :hints(("Goal"
                   :in-theory (e/d (vl-expr->finalwidth)
                                   (all-equalp))
                   :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                            (vl-msb-bitslice-exprlist x mod ialist warnings))))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-expr
    (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
                      (repeat 1 (vl-expr->finalwidth x)))))
    :hints(("Goal"
            :in-theory (disable l0)
            :use ((:instance l0)))))

  (defthm vl-exprlist->finalwidths-of-vl-msb-bitslice-exprlist
    (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-exprlist-p x))
                    (force (vl-exprlist-sliceable-p x))
                    (force (vl-exprlist-welltyped-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finalwidths (mv-nth 2 ret))
                      (repeat 1 (sum-nats (vl-exprlist->finalwidths x))))))
    :hints(("Goal"
            :in-theory (disable l1)
            :use ((:instance l1)))))




  (local (defthm all-equalp-of-vl-exprlist->finaltypes-of-flatten-repeat
           (equal (all-equalp a (vl-exprlist->finaltypes (flatten (repeat x n))))
                  (or (zp n)
                      (all-equalp a (vl-exprlist->finaltypes x))))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm-vl-flag-msb-bitslice-expr
           (defthm m0
             (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
               (implies (and (mv-nth 0 ret)
                             (force (vl-expr-p x))
                             (force (vl-expr-sliceable-p x))
                             (force (vl-expr-welltyped-p x))
                             (force (vl-module-p mod))
                             (force (equal ialist (vl-moditem-alist mod))))
                        (all-equalp :vl-unsigned (vl-exprlist->finaltypes (mv-nth 2 ret)))))
             :flag expr)
           (defthm m1
             (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
               (implies (and (mv-nth 0 ret)
                             (force (vl-exprlist-p x))
                             (force (vl-exprlist-sliceable-p x))
                             (force (vl-exprlist-welltyped-p x))
                             (force (vl-module-p mod))
                             (force (equal ialist (vl-moditem-alist mod))))
                        (all-equalp :vl-unsigned (vl-exprlist->finaltypes (mv-nth 2 ret)))))
             :flag list)
           :hints(("Goal"
                   :in-theory (e/d (vl-expr->finaltype)
                                   (all-equalp))
                   :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                            (vl-msb-bitslice-exprlist x mod ialist warnings))))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-expr
    (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-expr-sliceable-p x))
                    (force (vl-expr-welltyped-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
                      (repeat :vl-unsigned (vl-expr->finalwidth x)))))
    :hints(("Goal"
            :in-theory (disable m0)
            :use ((:instance m0)))))

  (defthm vl-exprlist->finaltypes-of-vl-msb-bitslice-exprlist
    (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-exprlist-p x))
                    (force (vl-exprlist-sliceable-p x))
                    (force (vl-exprlist-welltyped-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprlist->finaltypes (mv-nth 2 ret))
                      (repeat :vl-unsigned (sum-nats (vl-exprlist->finalwidths x))))))
    :hints(("Goal"
            :in-theory (disable m1)
            :use ((:instance m1)))))



  (local (defthm vl-exprlist-welltyped-p-of-flatten-of-repeat
           (equal (vl-exprlist-welltyped-p (flatten (repeat x n)))
                  (or (zp n)
                      (vl-exprlist-welltyped-p x)))
           :hints(("Goal" :in-theory (enable repeat)))))

  (defthm-vl-flag-msb-bitslice-expr
    (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-expr
      (let ((ret (vl-msb-bitslice-expr x mod ialist warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-expr-p x))
                      (force (vl-expr-sliceable-p x))
                      (force (vl-expr-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-welltyped-p (mv-nth 2 ret))))
      :flag expr)
    (defthm vl-exprlist-welltyped-p-of-vl-msb-bitslice-exprlist
      (let ((ret (vl-msb-bitslice-exprlist x mod ialist warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-exprlist-p x))
                      (force (vl-exprlist-sliceable-p x))
                      (force (vl-exprlist-welltyped-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-welltyped-p (mv-nth 2 ret))))
      :flag list)
    :hints(("Goal"
            :in-theory (e/d )
            :expand ((vl-msb-bitslice-expr x mod ialist warnings)
                     (vl-msb-bitslice-exprlist x mod ialist warnings))))))


