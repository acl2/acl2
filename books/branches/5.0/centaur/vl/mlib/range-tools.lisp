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
(include-book "find-item")
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))


(defxdoc range-tools
  :parents (mlib)
  :short "Basic functions for working with ranges."
  :long "<p>In Verilog, ranges are used in net and register declarations, and
also in module- and gate-instance declarations to describe arrays of modules
or gates.</p>

<p>For gate and module instances, the spec is pretty clear.  7.1.5 covers gate
instances and 12.1.2 says that module instances have the same rules.  In short,
neither side has to be larger than the other, neither side has to be zero, and
it always specifies abs(left-right)+1 occurrences (so that if they're the same
it means one gate).</p>

<p>BOZO consider \"negative\" numbers and what they might mean.</p>

<p>There specification doesn't give similarly crisp semantics to net and reg
ranges.  Verilog-XL is horribly permissive, allowing even negative indexes and
such.  But Verilog-XL indeed seems to treat w[1:1] as a single bit, and in the
Centaur design there are occurrences of [0:0] and [1:1] and such.  So it may be
that the semantics are supposed to be the same?  It turns out that there are at
least some differences, e.g., you're not allowed to select bit 0 from a plain
wire, but you can select bit 0 from w[0:0], etc.</p>

<p>Historically, VL required the msb index is not smaller than the lsb index.
But we now try to permit designs that use ranges that go from both high to low
and low to high.</p>

<p>The difference is that for a wire like <tt>wire [5:0] w</tt>, the most
significant bit is <tt>w[5]</tt> and the least significant is <tt>w[0]</tt>,
whereas for <tt>wire [0:5] v</tt>, the most significant bit is <tt>v[0]</tt>
and the least significant is <tt>v[5]</tt>.</p>

<p>Regardless of how the range is written, the wire behaves the same as far as
operations like addition, concatenation, and so forth are concerned.  This
might seem pretty surprising.  For instance,</p>

<code>
wire [3:0] a = 4'b0001;
wire [0:3] b = 4'b1000;
wire [7:0] c = {a, b};
</code>

<p>Results in <tt>c</tt> having the value <tt>8'b 0001_1000</tt>.  Basically
the way that the bits of <tt>b</tt> are represented doesn't affect its value as
an integer, and when we just write <tt>b</tt> we're referring to that
value.</p>

<p>Where it <i>does</i> matter is when bits or parts are selected from the
wire.  That is, <tt>b[0]</tt> is 1 since its indices go from low to high.</p>")


(defsection vl-range-resolved-p
  :parents (range-tools)
  :short "Determine if a range's indices have been resolved to constants."

; Historically we required x.msb >= x.lsb, but now we try to handle both cases.

  (defund vl-range-resolved-p (x)
    (declare (xargs :guard (vl-range-p x)
                    :guard-hints (("Goal" :in-theory (enable vl-expr-resolved-p)))))
    (b* (((vl-range x) x))
      (and (vl-expr-resolved-p x.msb)
           (vl-expr-resolved-p x.lsb))))

  (local (in-theory (enable vl-range-resolved-p)))

  (defthm vl-expr-resolved-p-of-vl-range->msb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->msb x))))

  (defthm vl-expr-resolved-p-of-vl-range->lsb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->lsb x))))

  (defthm natp-of-vl-resolved->val-of-vl-range->lsb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p range)
             (natp (vl-resolved->val (vl-range->lsb range)))))

  (defthm natp-of-vl-resolved->val-of-vl-range->msb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p range)
             (natp (vl-resolved->val (vl-range->msb range))))))



(defsection vl-maybe-range-resolved-p

  (definlined vl-maybe-range-resolved-p (x)
    (declare (xargs :guard (vl-maybe-range-p x)))
    (or (not x)
        (vl-range-resolved-p x)))

  (local (in-theory (enable vl-maybe-range-resolved-p)))

  (defthm vl-maybe-range-resolved-p-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-maybe-range-resolved-p x)))

  (defthm vl-range-resolved-p-when-vl-maybe-range-resolved-p
    (implies (vl-maybe-range-resolved-p x)
             (equal (vl-range-resolved-p x)
                    (if x t nil)))))



(defsection vl-make-n-bit-range
  :parents (range-tools)
  :short "Create the range <tt>[n-1:0]</tt>, but only if necessary.  That is,
if <tt>n</tt> is <tt>1</tt>, we just return <tt>nil</tt>, which is still valid
for use in any net or reg declaration."

  (defund vl-make-n-bit-range (n)
    "Returns MAYBE-RANGE"
    (declare (xargs :guard (posp n)))
    ;;(if (= n 1)
    ;;    nil
      (make-vl-range :msb (vl-make-index (- n 1))
                     :lsb (vl-make-index 0)))

  (local (in-theory (enable vl-make-n-bit-range)))

  (defthm vl-maybe-range-p-of-vl-make-n-bit-range
    (vl-maybe-range-p (vl-make-n-bit-range n))))




(defund vl-slow-find-net/reg-range (name mod)
  "Returns (MV SUCCESSP MAYBE-RANGE)"
  (declare (xargs :guard (and (stringp name)
                              (vl-module-p mod))))

; We look up the range for a wire or register declaration.  SUCCESSP is true as
; long as NAME is the name of a wire or register.

  (b* ((find (or (vl-find-netdecl name (vl-module->netdecls mod))
                 (vl-find-regdecl name (vl-module->regdecls mod))))
       ((when (not find))
        (mv nil nil))
       (tag (tag find))
       ((when (and (not (eq tag :vl-netdecl))
                   (not (eq tag :vl-regdecl))))
        (mv nil nil))
       (range (if (eq tag :vl-netdecl)
                  (vl-netdecl->range find)
                (vl-regdecl->range find))))
      (mv t range)))

(defthm vl-range-p-of-vl-slow-find-net/reg-range
  (implies (and (force (stringp name))
                (force (vl-module-p mod)))
           (equal (vl-range-p (mv-nth 1 (vl-slow-find-net/reg-range name mod)))
                  (if (mv-nth 1 (vl-slow-find-net/reg-range name mod))
                      t
                    nil)))
   :hints(("Goal" :in-theory (enable vl-slow-find-net/reg-range))))

(defthm vl-maybe-range-p-of-vl-slow-find-net/reg-range
  (implies (and (force (stringp name))
                (force (vl-module-p mod)))
           (vl-maybe-range-p (mv-nth 1 (vl-slow-find-net/reg-range name mod))))
  :hints(("Goal" :in-theory (enable vl-slow-find-net/reg-range))))




(defun vl-find-net/reg-range (name mod ialist)
  "Returns (MV SUCCESSP MAYBE-RANGE)"
  (declare (xargs :guard (and (stringp name)
                              (vl-module-p mod)
                              (equal ialist (vl-moditem-alist mod)))
                  :verify-guards nil))
  (mbe :logic (vl-slow-find-net/reg-range name mod)
       :exec
       (b* ((find (vl-fast-find-moduleitem name mod ialist))
            ((when (not find))
             (mv nil nil))
            (tag (tag find))
            ((when (and (not (eq tag :vl-netdecl))
                        (not (eq tag :vl-regdecl))))
             (mv nil nil))
            (range (if (eq tag :vl-netdecl)
                       (vl-netdecl->range find)
                     (vl-regdecl->range find))))
           (mv t range))))

(verify-guards vl-find-net/reg-range
               :hints(("Goal" :in-theory (enable vl-slow-find-net/reg-range
                                                 vl-find-moduleitem))))




(defund vl-range-size (x)
  (declare (xargs :guard (and (vl-range-p x)
                              (vl-range-resolved-p x))))

; The size of a range is one more than the difference between its high and low
; components.  For example [3:0] has size 4.  Notice that this definition still
; works in the case of [1:1] and so on.

  (let ((left  (vl-resolved->val (vl-range->msb x)))
        (right (vl-resolved->val (vl-range->lsb x))))
    (+ 1 (abs (- left right)))))

(defthm posp-of-vl-range-size
  (posp (vl-range-size x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-range-size))))



(definlined vl-maybe-range-size (x)
  (declare (xargs :guard (and (vl-maybe-range-p x)
                              (vl-maybe-range-resolved-p x))))

; If x is the range of a net declaration or register declaration, this function
; returns its width.  That is, if there is a range then the width of this wire
; or register is the size of the range.  And otherwise, it is a single-bit wide.

  (if (not x)
      1
    (vl-range-size x)))

(defthm posp-of-vl-maybe-range-size
  (posp (vl-maybe-range-size x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-maybe-range-size))))

