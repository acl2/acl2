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
(include-book "scopestack")
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

(define vl-simpletype-p ((x vl-datatype-p))
  (vl-datatype-case x
    :vl-coretype
    (and (or (eq x.name :vl-reg)
             (eq x.name :vl-logic))
         (atom x.udims)
         (or (atom x.pdims)
             (and (atom (cdr x.pdims))
                  (mbe :logic (vl-range-p (car x.pdims))
                       :exec (not (eq (car x.pdims) :vl-unsized-dimension))))))
    :otherwise nil))

(define vl-simpletype->range ((x vl-datatype-p))
  :guard (vl-simpletype-p x)
  :returns (range vl-maybe-range-p)
  :guard-hints (("Goal" :in-theory (enable vl-simpletype-p)))
  (b* (((vl-coretype x)))
    (and (consp x.pdims)
         (mbt (vl-range-p (car x.pdims)))
         (car x.pdims))))

(define vl-simpletype->signedp ((x vl-datatype-p))
  :guard (vl-simpletype-p x)
  :returns (signedp booleanp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-simpletype-p)))
  (b* (((vl-coretype x)))
    x.signedp))

(acl2::def-b*-binder vl-simpletype
  :body
  (std::da-patbind-fn 'vl-simpletype
                      '((range . vl-simpletype->range)
                        (signedp . vl-simpletype->signedp))
                      acl2::args acl2::forms acl2::rest-expr))


(define vl-simplereg-p ((x vl-vardecl-p))
  ;; Horrible hack to try to help with porting existing code.
  ;;
  ;; This will recognize only variables that are either basic reg (or logic)
  ;; wires, signed or unsigned, perhaps with a single range, but not with any
  ;; more complex dimensions.
  (b* (((vl-vardecl x) x))
    (and (not x.constp)
         (not x.varp)
         (not x.lifetime)
         (eq (vl-datatype-kind x.type) :vl-coretype)
         (b* (((vl-coretype x.type) x.type))
           (and (or (eq x.type.name :vl-reg)
                    (eq x.type.name :vl-logic))
                (atom x.type.udims)
                (or (atom x.type.pdims)
                    (and (atom (cdr x.type.pdims))
                         (mbe :logic (vl-range-p (car x.type.pdims))
                              :exec (not (eq (car x.type.pdims) :vl-unsized-dimension))))))))))

(deflist vl-simplereglist-p (x)
  :guard (vl-vardecllist-p x)
  (vl-simplereg-p x))

(define vl-simplereg->signedp ((x vl-vardecl-p))
  :returns (signedp booleanp :rule-classes :type-prescription)
  :guard (vl-simplereg-p x)
  :guard-hints (("Goal" :in-theory (enable vl-simplereg-p)))
  (b* (((vl-vardecl x) x)
       ((vl-coretype x.type) x.type))
    x.type.signedp))

(define vl-simplereg->range ((x vl-vardecl-p))
  :returns (range vl-maybe-range-p)
  :guard (vl-simplereg-p x)
  :prepwork ((local (in-theory (enable vl-simplereg-p vl-maybe-range-p))))
  (b* (((vl-vardecl x) x)
       ((vl-coretype x.type) x.type))
    (and (consp x.type.pdims)
         (vl-range-fix (car x.type.pdims))))
  ///
  (more-returns
   (range (equal (vl-range-p range) (if range t nil))
          :name vl-range-p-of-vl-simplereg->range)))

(acl2::def-b*-binder vl-simplereg
  :body
  (std::da-patbind-fn 'vl-simplereg
                      '((range . vl-simplereg->range)
                        (signedp . vl-simplereg->signedp))
                      acl2::args acl2::forms acl2::rest-expr))



(define vl-simplenet-p ((x vl-vardecl-p))
  ;; Horrible hack to try to help with porting existing code.
  ;;
  ;; This will recognize only variables that are nets: signed or unsigned, of
  ;; any type, perhaps with a single range, but not with any more complex
  ;; dimensions.
  (b* (((vl-vardecl x) x)
       ((unless x.nettype) nil)
       ((unless (eq (vl-datatype-kind x.type) :vl-coretype)) nil)
       ((vl-coretype x.type)))
    (and (eq x.type.name :vl-logic)
         (atom x.type.udims)
         (or (atom x.type.pdims)
             (and (not (eq (car x.type.pdims) :vl-unsized-dimension))
                  (atom (cdr x.type.pdims)))))))

(define vl-simplenet->range ((x vl-vardecl-p))
  :returns (range vl-maybe-range-p)
  :guard (vl-simplenet-p x)
  :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
  (b* (((vl-vardecl x) x)
       ((vl-coretype x.type) x.type))
    (and (consp x.type.pdims)
         (vl-range-fix (car x.type.pdims))))
  ///
  (more-returns
   (range (equal (vl-range-p range) (if range t nil))
          :name vl-range-p-of-vl-simplenet->range)))

(define vl-simplenet->signedp ((x vl-vardecl-p))
  :returns (signedp booleanp :rule-classes :type-prescription)
  :guard (vl-simplenet-p x)
  :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
  (b* (((vl-vardecl x) x)
       ((vl-coretype x.type) x.type))
    x.type.signedp))

(define vl-simplenet->nettype ((x vl-vardecl-p))
  :returns (nettype vl-nettypename-p)
  :guard (vl-simplenet-p x)
  :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
  (b* (((vl-vardecl x) x))
    (vl-nettypename-fix x.nettype)))

(acl2::def-b*-binder vl-simplenet
  :body
  (std::da-patbind-fn 'vl-simplenet
                      '((range . vl-simplenet->range)
                        (signedp . vl-simplenet->signedp)
                        (nettype . vl-simplenet->nettype))
                      acl2::args acl2::forms acl2::rest-expr))



(define vl-simplevar-p ((x vl-vardecl-p))
  :returns (bool)
  (or (vl-simplenet-p x)
      (vl-simplereg-p x))
  ///
  (defthm vl-simpletype-p-of-simplevar-type
    (implies (vl-simplevar-p x)
             (vl-simpletype-p (vl-vardecl->type x)))
    :hints(("Goal" :in-theory (enable vl-simpletype-p
                                      vl-simplevar-p
                                      vl-simplenet-p
                                      vl-simplereg-p)))))

(define vl-simplevar->signedp ((x vl-vardecl-p))
  :returns (signedp booleanp :rule-classes :type-prescription)
  :guard (vl-simplevar-p x)
  :prepwork ((local (in-theory (enable vl-simplevar-p))))
  (vl-simpletype->signedp (vl-vardecl->type x)))

(define vl-simplevar->range ((x vl-vardecl-p))
  :returns (range vl-maybe-range-p)
  :guard (vl-simplevar-p x)
  :prepwork ((local (in-theory (enable vl-simplevar-p))))
  (vl-simpletype->range (vl-vardecl->type x))
  ///
  (more-returns
   (range (equal (vl-range-p range) (if range t nil))
          :name vl-range-p-of-vl-simplevar->range)))

(acl2::def-b*-binder vl-simplevar
  :body
  (std::da-patbind-fn 'vl-simplevar
                      '((range . vl-simplevar->range)
                        (signedp . vl-simplevar->signedp))
                      acl2::args acl2::forms acl2::rest-expr))



;; BOZO horrible hack.  For now, we'll make find-net/reg-range only succeed for
;; simple regs, not for other kinds of variables.  Eventually we will want to
;; extend this code to deal with other kinds of variables, but for now, e.g.,
;; we don't want any confusion w.r.t. the range of integers, reals, etc.

(define vl-ss-find-range ((name   stringp) (ss vl-scopestack-p))
  :returns (mv successp
               (maybe-range vl-maybe-range-p))
  :enabled t
  (b* ((find (vl-scopestack-find-item name ss))
       ((unless (and find
                     (eq (tag find) :vl-vardecl)
                     (vl-simplevar-p find)))
        (mv nil nil)))
    (mv t (vl-simplevar->range find)))
  ///
  (more-returns
   (maybe-range (iff (vl-range-p maybe-range) maybe-range)
                :name vl-range-p-of-vl-ss-find-range)))

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



;; BOZO horrible hack.  For now, we'll make find-net/reg-range only succeed for
;; simple regs, not for other kinds of variables.  Eventually we will want to
;; extend this code to deal with other kinds of variables, but for now, e.g.,
;; we don't want any confusion w.r.t. the range of integers, reals, etc.

(define vl-slow-find-net/reg-range ((name stringp)
                                    (mod vl-module-p))
  :short "Look up the range for a wire or variable declaration."
  :returns (mv (successp    booleanp :rule-classes :type-prescription
                            "True when @('name') is the name of a wire or variable.")
               (maybe-range vl-maybe-range-p
                            "The range of the wire, on success."))
  :hooks ((:fix :args ((mod vl-module-p))))
  (b* ((find (vl-find-vardecl name (vl-module->vardecls mod)))
       ((unless (and find
                     (vl-simplevar-p find)))
        (mv nil nil)))
    (mv t (vl-simplevar->range find)))
  ///
  (more-returns
   (maybe-range (equal (vl-range-p maybe-range) (if maybe-range t nil))
                :name vl-range-p-of-vl-slow-find-net/reg-range)))

