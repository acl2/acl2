; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")

(include-book "datatype-tools")
(include-book "coretypes")
(local (std::add-default-post-define-hook :fix))


(defenum vl-arithclass-p
  (:vl-signed-int-class
   :vl-unsigned-int-class
   :vl-shortreal-class
   :vl-real-class
   :vl-other-class
   :vl-error-class)
  :parents (vl-expr-typedecide)
  :short "Classification of expressions (or datatypes) as signed or unsigned
integral, shortreal, real, or of some other kind."
  :long "<p>These classifications are used in the description of expression
types (signedness) found in SystemVerilog-2012 Sections 11.7-11.8.</p>

<p>It isn't entirely clear to me whether @('shortreal') should be regarded as a
different type than @('real'), but it seems possibly useful to keep them
separated.</p>

<p>We use ``other'' class to describe things that are valid but of some
non-arithmetic type, for instance: unpacked structures, void, chandles, etc.</p>

<p>We use ``error'' class to describe the case where we really did have some
kind of error determining the type.</p>")

(local (xdoc::set-default-parents vl-arithclass-p))

(define vl-coretype-arithclass ((typinfo vl-coredatatype-info-p)
                                (signedp booleanp))
  :returns (class vl-arithclass-p)
  :parents (vl-datatype-arithclass)
  :short "We factor this out of @(see vl-datatype-arithclass) so we can reuse
          it in places like @(see vl-syscall-typedecide)."
  (b* (((vl-coredatatype-info typinfo)))
    (cond (typinfo.takes-signingp
           ;; Any integer atom/vector type takes a signing
           (if signedp
               :vl-signed-int-class
             :vl-unsigned-int-class))
          ((or (vl-coretypename-equiv typinfo.coretypename :vl-real)
               ;; See SystemVerilog-2012 Section 6.12: realtime is synonymous
               ;; with real.
               (vl-coretypename-equiv typinfo.coretypename :vl-realtime))
           :vl-real-class)
          ((vl-coretypename-equiv typinfo.coretypename :vl-shortreal)
           :vl-shortreal-class)
          (t
           ;; Some crazy type like void, string, event, etc.
           :vl-other-class))))

(define vl-datatype-arithclass ((x vl-datatype-p))
  :short "Decide whether the datatype is signed/unsigned/real/other."

  :long "<p>Returns an @(see vl-arithclass-p) that describes the kind of this
datatype.  This function never fails, as such, but in some cases where
implementations disagree on the correct signedness, we return a flag to signal
that there is a caveat about that signedness.</p>

<p>This caveat occurs when we have packed dimensions on a usertype that is
declared as signed.  In this case, NCV treats the array as unsigned, but VCS
treats it as signed.  The SV spec only touches on this to say (from Sec. 7.4.1,
Packed Arrays):</p>

<blockquote> If a packed array is declared as signed, then the array viewed as
a single vector shall be signed. The individual elements of the array are
unsigned unless they are of a named type declared as signed. A partselect of a
packed array shall be unsigned.</blockquote>

<p>An example:</p>

@({
    typedef logic signed [3:0] squad;

    squad [3:0] b;
    assign b = 16'hffff;

    logic [20:0] btest;
    assign btest = b;
})

<p>In NCVerilog, btest has the value @('0ffff'), indicating that @('b') (as a
whole) is considered unsigned; in VCS, btest has the value @('fffff'),
indicating that @('b') is considered signed.</p>"
  :guard (vl-datatype-resolved-p x)
  :measure (vl-datatype-count x)
  :returns (mv (caveat-flag)
               (class vl-arithclass-p))
  (b* (((when (consp (vl-datatype->udims x)))
        ;; Unpacked array has no sensible arith class
        (mv nil :vl-other-class)))
    (vl-datatype-case x
      :vl-coretype
      (mv nil (vl-coretype-arithclass (vl-coretypename->info x.name) x.signedp))

      :vl-struct
      (mv nil (cond ((not x.packedp) :vl-other-class)
                    (x.signedp       :vl-signed-int-class)
                    (t               :vl-unsigned-int-class)))
      :vl-union
      (mv nil (cond ((not x.packedp) :vl-other-class)
                    (x.signedp       :vl-signed-int-class)
                    (t               :vl-unsigned-int-class)))
      :vl-enum
      (vl-datatype-arithclass x.basetype)
      :vl-usertype
      (b* (((unless (mbt (and x.res t)))
            (mv (impossible) :vl-other-class))
           ((mv caveat ans1) (vl-datatype-arithclass x.res))
           ((when (and (consp (vl-datatype->pdims x))
                       (eq ans1 :vl-signed-int-class)))
            ;; Packed array of some signed usertype -- special caveat case
            ;; described above.
            (mv t :vl-unsigned-int-class)))
        (mv caveat ans1)))))


(define vl-exprsign->arithclass ((x vl-exprsign-p))
  :returns (class vl-arithclass-p)
  :inline t
  (if (vl-exprsign-equiv x :vl-signed)
      :vl-signed-int-class
    :vl-unsigned-int-class))

(define vl-arithclass-rank ((x vl-arithclass-p))
  :parents (vl-arithclass-max)
  :short "Rankings of @(see vl-arithclass-p)s used in @(see vl-arithclass-max)."
  :returns (rank natp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-arithclass-p)))
  :inline t
  (case (vl-arithclass-fix x)
    (:vl-signed-int-class   1)
    (:vl-unsigned-int-class 2)
    (:vl-shortreal-class    3)
    (:vl-real-class         4)
    (:vl-other-class        5)
    (:vl-error-class        6)
    (otherwise (nfix (impossible)))))

(defsection vl-arithclass-max
  :short "@(call vl-arithclass-max) computes the arithmetic class for a non
self-determined operand, given the classes of the arguments."

  :long "<p>See SystemVerilog-2012 Section 11.8.1, Expression Evaluation Rules.
This function loosely corresponds to the case for non self-determined operands,
where ``the following rules apply:</p>
<ul>
 <li>If any operand is real, the result is real.</li>
 <li>If any operand is unsigned, the result is unsigned, regardless of the operator.</li>
 <li>If all operands are signed, the result will be signed, regardless of operator,
     except when specified otherwise.''</li>
</ul>

<p>These rules seem pretty incomplete because not all expressions fit nicely
into these types: for instance what is the result from a @('mintypmax')
expression or a tagged union type or an unpacked type or that sort of thing.
But at any rate we imagine a hierarchy, where:</p>

@({
     signed < unsigned < shortreal < real < other
})

<p>And the maximum class of an argument becomes the class for the operator.
For example, if we're computing the type of @('a + b') and @('a') is a unsigned
but @('b') is a shortreal, then the sum should be a shortreal.</p>

<p>We assign the ``other'' class to anything that is valid but doesn't seem
like a sensible arithmetic type.  For instance, an unpacked structure or weird
operator like a mintypmax.</p>

<p>We use the ``error'' class only for cases where we truly cannot determine
the type of something because of an error (e.g., undeclared identifier,
etc.)</p>"

  (defund vl-arithclass-max-fn (x y)
    (declare (xargs :guard (and (vl-arithclass-p x)
                                (vl-arithclass-p y))))
    (b* ((x (vl-arithclass-fix x))
         (y (vl-arithclass-fix y)))
      (if (< (vl-arithclass-rank x) (vl-arithclass-rank y))
          y
        x)))

  (defmacro vl-arithclass-max (x y &rest rst)
    (xxxjoin 'vl-arithclass-max-fn (cons x (cons y rst))))

  (add-binop vl-arithclass-max vl-arithclass-max-fn)

  (local (in-theory (enable vl-arithclass-max-fn)))

  (defthm vl-arithclass-p-of-vl-arithclass-max
    (vl-arithclass-p (vl-arithclass-max x y)))

  (defthm vl-arithclass-max-of-vl-arithclass-max
    (equal (vl-arithclass-max (vl-arithclass-max x y) z)
           (vl-arithclass-max x (vl-arithclass-max y z))))

  (deffixequiv vl-arithclass-max-fn :args ((x vl-arithclass-p) (y vl-arithclass-p))))


(define vl-integer-arithclass-p ((x vl-arithclass-p))
  :inline t
  (or (vl-arithclass-equiv x :vl-signed-int-class)
      (vl-arithclass-equiv x :vl-unsigned-int-class))
  ///
  (defthm vl-integer-arithclass-p-of-vl-exprsign->arithclass
    (vl-integer-arithclass-p (vl-exprsign->arithclass x))
    :hints(("Goal" :in-theory (enable vl-exprsign->arithclass))))


  (define vl-integer-arithclass->exprsign ((x vl-arithclass-p))
    :guard (vl-integer-arithclass-p x)
    :returns (sign vl-exprsign-p)
    :inline t
    (if (vl-arithclass-equiv x :vl-signed-int-class)
        :vl-signed
      :vl-unsigned))


  (defthm symbolp-of-vl-datatype-arithclass
    (let ((ret (mv-nth 1 (vl-datatype-arithclass x))))
      (and (symbolp ret)
           (not (equal ret t))
           (not (equal ret nil))))
    :rule-classes :type-prescription
    :hints(("Goal"
            :in-theory (disable type-when-vl-arithclass-p)
            :use ((:instance type-when-vl-arithclass-p
                   (x (mv-nth 1 (vl-datatype-arithclass x))))))))

  (defthm vl-integer-arithclass-p-of-vl-arithclass-max
    (implies (and (vl-integer-arithclass-p x)
                  (vl-integer-arithclass-p y))
             (vl-integer-arithclass-p (vl-arithclass-max x y)))
    :hints(("Goal" :in-theory (enable vl-arithclass-max
                                      vl-arithclass-rank
                                      vl-integer-arithclass-p)))))
