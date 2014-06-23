; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(local (std::add-default-post-define-hook :fix))

(defxdoc range-tools
  :parents (mlib)
  :short "Basic functions for working with ranges."
  :long "<p>In Verilog, ranges are used in net and register declarations, and
also in module- and gate-instance declarations to describe arrays of modules
or gates.</p>

<p>For gate and module instances, the Verilog-2005 standard is pretty clear.
7.1.5 covers gate instances and 12.1.2 says that module instances have the same
rules.  In short, neither side has to be larger than the other, neither side
has to be zero, and it always specifies abs(left-right)+1 occurrences (so that
if they're the same it means one gate).</p>

<p>BOZO consider \"negative\" numbers and what they might mean.</p>

<p>The specification doesn't give similarly crisp semantics to net and reg
ranges.  Verilog-XL is horribly permissive, allowing even negative indexes and
such.  But Verilog-XL indeed seems to treat w[1:1] as a single bit, and in the
Centaur design there are occurrences of [0:0] and [1:1] and such.  So it may be
that the semantics are supposed to be the same?  It turns out that there are at
least some differences, e.g., you're not allowed to select bit 0 from a plain
wire, but you can select bit 0 from w[0:0], etc.</p>

<p>Historically, VL required the msb index is not smaller than the lsb index.
But we now try to permit designs that use ranges that go from both high to low
and low to high.</p>

<p>The difference is that for a wire like @('wire [5:0] w'), the most
significant bit is @('w[5]') and the least significant is @('w[0]'), whereas
for @('wire [0:5] v'), the most significant bit is @('v[0]') and the least
significant is @('v[5]').</p>

<p>Regardless of how the range is written, the wire behaves the same as far as
operations like addition, concatenation, and so forth are concerned.  This
might seem pretty surprising.  For instance,</p>

@({
wire [3:0] a = 4'b0001;
wire [0:3] b = 4'b1000;
wire [7:0] c = {a, b};
})

<p>Results in @('c') having the value @('8'b 0001_1000').  Basically the way
that the bits of @('b') are represented doesn't affect its value as an integer,
and when we just write @('b') we're referring to that value.</p>

<p>Where it <i>does</i> matter is when bits or parts are selected from the
wire.  That is, @('b[0]') is 1 since its indices go from low to high.</p>")

(local (xdoc::set-default-parents range-tools))

(define vl-range-resolved-p ((x vl-range-p))
  :short "Determine if a range's indices have been resolved to constants."
  :long "<p>Historically we required @('x.msb >= x.lsb'), but now we try to
handle both cases.</p>"
  (b* (((vl-range x) x))
    (and (vl-expr-resolved-p x.msb)
         (vl-expr-resolved-p x.lsb)))
  ///
  (defthm vl-expr-resolved-p-of-vl-range->msb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->msb x))))

  (defthm vl-expr-resolved-p-of-vl-range->lsb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->lsb x)))))


(define vl-maybe-range-resolved-p ((x vl-maybe-range-p))
  :inline t
  (or (not x)
      (vl-range-resolved-p x))
  ///
  (defthm vl-maybe-range-resolved-p-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-maybe-range-resolved-p x)))

  (defthm vl-range-resolved-p-when-vl-maybe-range-resolved-p
    (implies (and (vl-maybe-range-resolved-p x)
                  x)
             (vl-range-resolved-p x))))


(define vl-make-n-bit-range ((n posp))
  :returns (maybe-range vl-maybe-range-p)
  :short "Create the range @('[n-1:0]')."
  (let ((n (mbe :logic (pos-fix n) :exec n)))
    (make-vl-range :msb (vl-make-index (- n 1))
                   :lsb (vl-make-index 0))))


;; BOZO horrible hack.  For now, we'll make find-net/reg-range only succeed for
;; regs, not for other kinds of variables.  Eventually we will want to extend
;; this code to deal with other kinds of variables, but for now, e.g., we don't
;; want any confusion w.r.t. the range of integers, reals, etc.

(define vl-slow-find-net/reg-range ((name stringp)
                                    (mod vl-module-p))
  :short "Look up the range for a wire or variable declaration."
  :returns (mv (successp    booleanp :rule-classes :type-prescription
                            "True when @('name') is the name of a wire or variable.")
               (maybe-range vl-maybe-range-p
                            "The range of the wire, on success."))
  :hooks ((:fix :args ((mod vl-module-p))))
  (b* ((find (or (vl-find-netdecl name (vl-module->netdecls mod))
                 (vl-find-vardecl name (vl-module->vardecls mod))))
       ((when (not find))
        (mv nil nil))
       (tag (tag find))
       ((when (eq tag :vl-netdecl))
        (mv t (vl-netdecl->range find)))
       ((when (and (eq tag :vl-vardecl)
                   (eq (vl-vardecl->type find) :vl-reg)))
        (mv t (vl-vardecl->range find))))
    (mv nil nil))
  ///
  (defthm vl-range-p-of-vl-slow-find-net/reg-range
    (equal (vl-range-p (mv-nth 1 (vl-slow-find-net/reg-range name mod)))
           (if (mv-nth 1 (vl-slow-find-net/reg-range name mod))
               t
             nil))))

(define vl-find-net/reg-range ((name   stringp)
                               (mod    vl-module-p)
                               (ialist (equal ialist (vl-moditem-alist mod))))
  :returns (mv successp maybe-range)
  :enabled t
  :hooks ((:fix :args ((mod vl-module-p))))
  :guard-hints(("Goal" :in-theory (enable vl-slow-find-net/reg-range
                                          vl-find-moduleitem)))
  (mbe :logic (vl-slow-find-net/reg-range name mod)
       :exec
       (b* ((find (vl-fast-find-moduleitem name mod ialist))
            ((when (not find))
             (mv nil nil))
            (tag (tag find))
            ((when (eq tag :vl-netdecl))
             (mv t (vl-netdecl->range find)))
            ((when (and (eq tag :vl-vardecl)
                        (eq (vl-vardecl->type find) :vl-reg)))
             (mv t (vl-vardecl->range find))))
         (mv nil nil))))

(define vl-range-size ((x vl-range-p))
  :guard (vl-range-resolved-p x)
  :returns (size posp :rule-classes :type-prescription)
  :short "The size of a range is one more than the difference between its msb
and lsb.  For example [3:0] has size 4."
  :long "<p>Notice that this definition still works in the case of [1:1] and so
on.</p>"
  (b* (((vl-range x) x)
       (left  (vl-resolved->val x.msb))
       (right (vl-resolved->val x.lsb)))
    (+ 1 (abs (- left right)))))

(define vl-maybe-range-size ((x vl-maybe-range-p))
  :guard (vl-maybe-range-resolved-p x)
  :returns (size posp :rule-classes :type-prescription)
  :short "Usual way to compute the width of a net/reg, given its range."
  :long "<p>If @('x') is the range of a net declaration or register
declaration, this function returns its width.  That is, if there is a range
then the width of this wire or register is the size of the range.  And
otherwise, it is a single-bit wide.</p>"
  (if (not x)
      1
    (vl-range-size x)))

