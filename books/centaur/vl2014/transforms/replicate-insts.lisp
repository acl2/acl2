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
(include-book "../mlib/expr-slice")
(include-book "../mlib/port-tools")
(include-book "../mlib/namefactory")
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

; BOZO now that we have VL primitive modules for other gates, it might make the
; most sense to try to just eliminate all gates in one fell swoop early in the
; transformation sequence, replacing them with their VL module equivalents,
; then only deal with module instances instead of gate instances here.

(defxdoc replicate-insts
  :parents (transforms)
  :short "Eliminate arrays of gate and module instances."

  :long "<p>We now introduce a transformation which eliminates \"ranges\" from
gate and module instances.  The basic idea is to transform things like this:</p>

@({
   type instname [N:0] (arg1, arg2, ..., argM) ;
})

<p>Into things like this:</p>

@({
   type instname_0 (arg1-0, arg2-0, ..., argM-0);
   type instname_1 (arg1-1, arg2-1, ..., argM-1);
   ...
   type instname_N (arg1-N, arg2-N, ..., argM-N);
})

<p>Here, @('type') might be a gate type (e.g., @('not'), @('xor'), etc.) or a
module name, @('instname') is the name of this instance array, and the
arguments are expressions which represent the inputs and outputs.</p>

<p><b>Ordering Notes</b>.  We require that (1) @(see argresolve) has been
applied so there are only plain argument lists to deal with, that (2) all
expressions have been sized so we can determine the sizes of arguments and
ports, and (3) that @(see drop-blankports) has been run so that there are no
blank ports.  We expect that all of the actuals are <see topic='@(url
expr-slicing)'>sliceable</see> expressions.  However, this transformation
should be run before @(see blankargs), so there may be blank arguments (but not
blank ports.)</p>

<p>The semantics of instance arrays are covered in Section 7.1.5 and 7.1.6, and
per Section 12.1.2 they hold for both gate instances and module instances.</p>

<p>One minor issue to address is that the names of all instances throughout a
module need to be unique, and so we need to take care that the instance names
we are generating (i.e., instname_0, etc.) do not clash with other names in the
module; we discuss this further in @(see vl-replicated-instnames).</p>

<p>But the most complicated thing about splitting instances is how to come up
with the new arguments for each new instance we are generating.  This is
addressed in @(see argument-partitioning).</p>")

(local (xdoc::set-default-parents replicate-insts))

(define vl-preferred-replicate-names
  :parents (vl-replicated-instnames)
  :short "Preferred names from low to high, inclusive, e.g., (foo_3 foo_4 foo_5)"
  ((low natp)
   (high natp)
   (instname stringp))
  :guard (<= low high)
  :returns (names string-listp)
  :measure (nfix (- (nfix high) (nfix low)))
  (b* ((low  (lnfix low))
       (high (lnfix high))
       (name (cat instname "_" (natstr low)))
       ((when (mbe :logic (zp (- high low))
                   :exec (eql low high)))
        (list name)))
    (cons name (vl-preferred-replicate-names (+ 1 low) high instname)))
  ///
  (defthm len-of-vl-preferred-replicate-names
    (equal (len (vl-preferred-replicate-names low high instname))
           (+ 1 (nfix (- (nfix high) (nfix low)))))))

(define vl-bad-replicate-names
  :parents (vl-replicated-instnames)
  :short "Fallback names in case our preferred names aren't available.  Only
          called if there is a name conflict that prevents us from using good
          names."
  ((n        natp)
   (basename stringp)
   (nf       vl-namefactory-p))
  :returns (mv (names string-listp)
               (nf    vl-namefactory-p))
  (b* (((when (zp n))
        (mv nil (vl-namefactory-fix nf)))
       ((mv name nf)   (vl-namefactory-indexed-name basename nf))
       ((mv others nf) (vl-bad-replicate-names (- n 1) basename nf)))
    (mv (cons name others) nf))
  ///
  (defthm len-of-vl-bad-replicate-names
    (equal (len (mv-nth 0 (vl-bad-replicate-names n basename nf)))
           (nfix n))))

(local (in-theory (enable vl-range-resolved-p)))

(define vl-replicated-instnames
  :short "Generate the new names that we'll use for replicated instances."
  ((instname  maybe-stringp     "Name of the instance array we are replicating.")
   (instrange vl-range-p        "Its associated range.")
   (nf        vl-namefactory-p  "For generating fresh names.")
   (ctx       vl-modelement-p   "Context for warnings.")
   (warnings  vl-warninglist-p  "Ordinary @(see warnings) accumulator."))
  :guard (vl-range-resolved-p instrange)
  :returns
  (mv (warnings vl-warninglist-p)
      (names    "The names to be used for the new instances."
                string-listp)
      (nf       vl-namefactory-p))

  :long "<p>This function is responsible for naming the new gate or module
instances that are going to be created when we split up an instance array.  We
really want these new names to correspond to the original instance name and the
instance numbers, since otherwise it can be hard to understand the relationship
of the transformed module's state to the original module.</p>

<p>Suppose we are transforming an instance like this:</p>

@({
   type foo [N:0] (arg1, arg2, ..., argM);
})

<p>We produce a list of @('N+1') names that are to be used as the instance
names for the split up arguments.  We try to use names of the form
@('instname_index') if they are available, e.g., for the above we would
generate names like @('foo_N, ..., foo_0').</p>

<p>We want to return the names so that the name corresponding to the most
significant bits comes first.  If the range is like @('[N:0]'), then we return
@('foo_N, ..., foo_0').  If the range goes the other way, i.e., @('[0:N]'),
then we return @('foo_0, ..., foo_N').</p>"

  (b* ((instname (maybe-string-fix instname))
       (ctx      (vl-modelement-fix ctx))
       (left     (vl-resolved->val (vl-range->msb instrange)))
       (right    (vl-resolved->val (vl-range->lsb instrange)))
       (low      (min left right))
       (high     (max left right))
       (instname (or instname "unnamed"))
       (names-low-to-high (vl-preferred-replicate-names low high instname))
       (names-msb-first   (if (>= left right)
                              (reverse names-low-to-high)
                            names-low-to-high))
       ((mv fresh nf)
        (vl-namefactory-plain-names names-msb-first nf))
       ((when (equal names-msb-first fresh))
        ;; Great -- we can use exactly what we want to use.
        (mv (ok) names-msb-first nf))
       ;; Use bad names.  We don't care what order them come in.
       ((mv fresh nf)
        (vl-bad-replicate-names (+ 1 (- high low))
                                (cat "vl_badname_" instname)
                                nf)))
    (mv (warn :type :vl-warn-replicate-name
              :msg "~a0: preferred names for instance array ~s1 are not ~
                    available, so using lousy vl_badname_* naming scheme ~
                    instead.  This conflict is caused by ~&2."
              :args (list ctx instname
                          (difference (mergesort names-msb-first)
                                      (mergesort fresh))))
        (rev fresh)
        nf))
  ///
  (defthm len-of-vl-replicated-instnames
    (implies (and (force (vl-range-resolved-p instrange))
                  (force (vl-namefactory-p nf)))
             (equal
              (len (mv-nth 1 (vl-replicated-instnames instname instrange
                                                      nf ctx warnings)))
              (vl-range-size instrange)))
    :hints(("Goal" :in-theory (e/d (vl-range-size))))))

(define vl-replicate-orig-instnames1
  :parents (vl-replicate-orig-instnames)
  ((low natp)
   (high natp)
   (instname stringp))
  :guard (<= low high)
  :returns (names string-listp "Verilog-style names in <i>lowest-first order</i>,
                                e.g., @('(\"foo[3]\" \"foo[4]\" \"foo[5]\")').")
  :measure (nfix (- (nfix high) (nfix low)))
  (b* ((low  (lnfix low))
       (high (lnfix high))
       (name (cat instname "[" (natstr low) "]"))
       ((when (mbe :logic (zp (- high low))
                   :exec (eql low high)))
        (list name)))
    (cons name (vl-replicate-orig-instnames1 (+ 1 low) high instname)))
  ///
  (defthm len-of-vl-replicate-orig-instnames1
    (equal (len (vl-replicate-orig-instnames1 low high instname))
           (+ 1 (nfix (- (nfix high) (nfix low))))))
  (assert! (equal (vl-replicate-orig-instnames1 3 5 "foo")
                  '("foo[3]" "foo[4]" "foo[5]"))))

(define vl-replicate-orig-instnames
  :short "Generate the Verilog-style names of the original instances (e.g.,
          names with square-bracketed indices)."
  ((instname maybe-stringp)
   (instrange vl-range-p))
  :guard (vl-range-resolved-p instrange)
  :returns (names string-listp "Verilog-style names in <i>highest-first order</i>,
                                e.g., @('(\"foo[5]\" \"foo[4]\" \"foo[3]\")').")
  :long "<p>These names are just going to be attributes for the new instances,
         which allow you to relate the original Verilog with the simplified
         Verilog.  The order must match @(see vl-replicated-instnames).</p>"
  (b* ((left  (vl-resolved->val (vl-range->msb instrange)))
       (right (vl-resolved->val (vl-range->lsb instrange)))
       (low   (min left right))
       (high  (max left right))
       (instname
        ;; Sol asked if the instname can really be nil.  Yes, but it's pretty
        ;; unusual.  The reason is that VL uses the same modinst representation
        ;; for both module instances and user-defined primitive instances (but
        ;; we don't actually support UDP's yet), and UDP's aren't required to
        ;; have instance names.  Go figure.
        (or instname "unnamed"))
       (low-to-high (vl-replicate-orig-instnames1 low high instname)))
    (if (>= left right)
        (reverse low-to-high)
      low-to-high))
  ///
  (defthm len-of-vl-replicate-orig-instnames
    (equal (len (vl-replicate-orig-instnames instname instrange))
           (vl-range-size instrange))
    :hints(("Goal" :in-theory (enable vl-range-size)))))

(defxdoc argument-partitioning
  :short "How arguments to instance arrays are split up and given to the
individual instances."

  :long "<p>Recall that in the @(see replicate-insts) transform we are
basically rewriting instance arrays like this:</p>

@({
   type instname [N:0] (arg1, arg2, ..., argM) ;
})

<p>Into things like this:</p>

@({
   type instname_0 (arg1-0, arg2-0, ..., argM-0);
   type instname_1 (arg1-1, arg2-1, ..., argM-1);
   ...
   type instname_N (arg1-N, arg2-N, ..., argM-N);
})

<p>Let us consider a particular, non-blank argument, @('ArgI'), whose width is
@('ArgI-W').  Suppose this argument is connected to a non-blank port with width
@('P-W').</p>

<p>Let's be clear on what we mean by @('P-W').  If we are talking about module
instances then this is quite straightforward: the module has a list of ports,
and we can see how wide these ports are supposed to be by looking at the widths
of their port expressions; see @(see vl-port-p).  The argument @('ArgI')
corresponds to some particular port, and so the width of that port is what
@('P-W') is going to be.  If we are talking about gates, then P-W is always
1.</p>

<p>According to the semantics laid forth in 7.1.6, there are only two valid
cases.</p>

<p><b>Case 1.</b> @('ArgI-W = P-W.') In this case, the argument is simply to be
replicated, verbatim, across all of the new instances.</p>

<p><b>Case 2.</b> @('ArgI-W = P-W * K'), where @('K') is the number of
instances specified by this array.  That is, if our instance array declaration
is:</p>

@({
    type instname [N:0] (arg1, arg2, ...);
})

<p>then @('K') is @('N+1').  In this case, we are going to slice up @('ArgI')
into @('K') segments of @('P-W') bits each, and send them off to the instances.
For example, in the code:</p>

@({
    wire w[3:0];
    not g [3:0] (w, 4'b0011);
})

<p>The @('ArgI-W') of both @('w') and @('4'b0011') is four, while the @('P-W')
is 1.  In this case, we create four one-bit slices of @('w'), and four one-bit
slices of @('4'b0011'), and connect them with four separate not-gates.</p>

<p>When we are dealing with gates, @('P-W') is always 1.  But when we talk
about modules, @('P-W') might be larger.  For example, consider the module:</p>

@({
   module two_bit_and (o, a, b) ;
      output [1:0] o;
      input [1:0] a;
      input [1:0] b;
      assign o = a & b;
   endmodule
})

<p>And here we have an array of these two_bit_and modules:</p>

@({
   wire [7:0] j;
   two_bit_and myarray [3:0] (j, 8'b 11_00_10_01, 2'b 01);
})

<p>This array is equivalent to:</p>

@({
   two_bit_and myarray_0 (j[7:6], 2'b 11, 2'b 01) ;
   two_bit_and myarray_1 (j[5:4], 2'b 00, 2'b 01) ;
   two_bit_and myarray_2 (j[3:2], 2'b 10, 2'b 01) ;
   two_bit_and myarray_3 (j[1:0], 2'b 01, 2'b 01) ;
})

<p>And so the value of @('j') will be @('8'b 0100_0001').</p>

<p>That is, since all of the ports of two_bit_and are 2 bits, and we are
creating four instances, each of the array arguments can only be 2 or 8 bits
long.  Any 8-bit arguments are split into 2-bit slices, and any 2-bit arguments
are replicated.</p>")

(define vl-partition-msb-bitslices
  :parents (argument-partitioning)
  :short "Group up a list of bits into N-bit concatenations."

  ((n "A positive number that must evenly divide @('(len x)')." posp)
   (x "A list of 1-bit unsigned expressions." vl-exprlist-p))
  :guard (and (eql (mod (len x) n) 0)
              (all-equalp 1 (vl-exprlist->finalwidths x)))
  :returns (new-exprs vl-exprlist-p "Concatenations of @('n') successive bits of @('x').")
  :measure (len x)

  :long "<p>The basic way that we partition an expression into @('N')-bit
slices is to break it up into individual bits with @(see vl-msb-bitslice-expr),
then group these bits together into @('N')-bit concatenations.  Typically we
expect that @('x') is the result of calling @(see vl-msb-bitslice-expr) to
slice up an expression into such bits.</p>

<p>We return a new list of expressions, each of is a concatenation of @('n')
successive bits of @('x').  For instance, if</p>

<ul>
 <li>@('x') is @('(bit_99 bit_98 ... bit_0)'), and</li>
 <li>@('n') is @('5'),</li>
</ul>

<p>Then the resulting list of expressions will be:</p>

<ul>
 <li>@('{bit_99, bit_98, bit_97, bit_96, bit_95}')</li>
 <li>@('{bit_94, bit_93, bit_92, bit_91, bit_90}')</li>
 <li>...</li>
 <li>@('{bit_4,  bit_3,  bit_2,  bit_1,  bit_0}')</li>
</ul>

<p>We prove that the resulting expressions all have width @('n'), that there
are the right number of resulting expressions, and that they are all well-typed
assuming that the input bit-expressions are well-typed.</p>

<h3>Aesthetic Notes</h3>

<p>An arguably unfortunate consequence of our partitioning approach is that the
resulting concatenations of bits can be large and ugly in certain cases.  For
instance, part selects like @('foo[31:0]') will get blown up into things like
@('{ foo[31], foo[30], ..., foo[0] }'), which is overly verbose and perhaps
hard to read.</p>

<p>My original implementation of partitioning also had a \"cleaning\" phase
that tried to correct for this, essentially by identifying these descending
sequences of bit-selects and re-assembling them into part-selects.  But I no
longer to implement such a cleaning phase.  My rationale is that:</p>

<ol>

<li>Aesthetics here are not very important because instance arrays are not that
common in the first place, so we are not going to be breaking up very many
expressions in this potentially bad way, and</li>

<li>Not cleaning avoids any potential errors in the cleaning code.  This is not
much of an argument since the cleaning code is relatively simple, but it still
has some merit.</li>

</ol>

<p>NOTE: we now have @(see expr-cleaning) code that can do this cleaning.  We
don't currently use it here, in case it has any bugs, but perhaps we should
re-integrate it.</p>"

  (b* ((n (lposfix n))
       ((when (eql n 0))
        nil)
       ((when (< (len x) n))
        nil))
    (cons (make-vl-nonatom :op :vl-concat
                           :args (first-n n x)
                           :finalwidth n
                           :finaltype :vl-unsigned
                           :atts nil)
          (vl-partition-msb-bitslices n (rest-n n x))))

  :prepwork
  ((local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
   (local (defthm l0
            (implies (and (equal (vl-exprlist->finalwidths x) (replicate (len x) 1))
                          (natp n)
                          (<= n (len x)))
                     (equal (vl-exprlist->finalwidths (nthcdr n x))
                            (replicate (- (len x) n) 1)))
            :hints(("Goal" :in-theory (enable replicate nthcdr))))))
  ///
  (local (in-theory (enable vl-partition-msb-bitslices)))

  (defthm len-of-vl-partition-msb-bitslices
    (equal (len (vl-partition-msb-bitslices n x))
           (floor (len x) (pos-fix n))))

  (defthm vl-exprlist->finalwidths-of-vl-partition-msb-bitslices
    (equal (vl-exprlist->finalwidths (vl-partition-msb-bitslices n x))
           (replicate (floor (len x) (pos-fix n))
                      (pos-fix n)))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm vl-exprlist->finaltypes-of-vl-partition-msb-bitslices
    (equal (vl-exprlist->finaltypes (vl-partition-msb-bitslices n x))
           (replicate (floor (len x) (pos-fix n)) :vl-unsigned))
    :hints(("Goal" :in-theory (enable replicate))))

  (local (defthm c0
           (implies (and (all-equalp 1 (vl-exprlist->finalwidths x))
                         (natp n)
                         (<= n (len x)))
                    (all-equalp 1 (vl-exprlist->finalwidths (take n x))))
           :hints(("goal"
                   :in-theory (e/d (acl2::take)
                                   (all-equalp))))))

  (local (defthm c1
           (implies (all-equalp 1 (vl-exprlist->finalwidths x))
                    (all-equalp 1 (vl-exprlist->finalwidths (nthcdr n x))))))

  (local (defthm c2
           (implies (all-equalp 1 (vl-exprlist->finalwidths x))
                    (not (member-equal nil (vl-exprlist->finalwidths x))))))

  (defthm vl-exprlist-welltyped-p-of-vl-partition-msb-bitslices
    (implies (and (force (vl-exprlist-welltyped-p x))
                  (force (all-equalp 1 (vl-exprlist->finalwidths x))))
             (vl-exprlist-welltyped-p (vl-partition-msb-bitslices n x)))
    :hints(("Goal" :in-theory (e/d (vl-expr-welltyped-p)
                                   (all-equalp
                                    vl-exprlist->finalwidths-of-take))))))


(define vl-partition-plainarg
  :parents (argument-partitioning)
  :short "Partition a plain argument into slices."

  ((arg        vl-plainarg-p    "An argument we need to replicate.")
   (port-width posp             "Width of the port this argument is connected to.")
   (insts      posp             "Number of instances in this instance array.")
   (ss         vl-scopestack-p)
   (elem       vl-modelement-p  "Context for warnings.")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))

  :verbosep t

  :returns
  (mv (okp       booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (plainargs vl-plainarglist-p))

  :long "<p>Our goal is to create a list of the @('insts')-many plainargs which
this port is to be partitioned into.  On success, @('plainargs') will be a list
of @('insts') arguments, each of which has width @('port-width').  The
arguments are in \"msb-first\" order, i.e., the \"msb-most slice\" of @('arg')
comes first.</p>

<p>We might fail with a fatal warning if there is some problem with the actual;
we expect the actual to be already sized, <see topic='@(url
vl-expr-welltyped-p)'>well-typed</see>, and <see topic='@(url
expr-slicing)'>sliceable</see>), and its width must be compatible with the
width of the port, as described in @(see argument-partitioning).</p>"

  (b* ((arg        (vl-plainarg-fix arg))
       (port-width (lposfix port-width))
       (insts      (lposfix insts))
       (ss         (vl-scopestack-fix ss))
       (elem       (vl-modelement-fix elem))
       (warnings   (vl-warninglist-fix warnings))

       ((vl-plainarg arg) arg)

       ((unless arg.expr)
        ;; Special case for blanks: If we have a blank in an array of
        ;; instances, we just want to send blank to each member of the
        ;; instance.
        (mv t (ok) (replicate insts arg)))

       (expr-width (vl-expr->finalwidth arg.expr))
       ((unless (posp expr-width))
        (mv nil
            (fatal :type :vl-bad-argument
                   :msg "~a0: expected argument widths to be computed, but ~
                         found argument ~a1 without any width assigned."
                   :args (list elem arg.expr))
            nil))

       ((when (eql expr-width port-width))
        ;; The port is exactly as wide as the argument being given to it.
        ;; We are to replicate the argument, verbatim, across all of the
        ;; instances we are creating.
        (mv t (ok) (replicate insts arg)))

       ;; Otherwise, the port is not the same width as the argument.  In this
       ;; case, the argument's width should be a multiple of the port's
       ;; width.

       ((unless (eql expr-width (* port-width insts)))
        (mv nil
            (fatal :type :vl-bad-argument
                   :msg "~a0: argument ~a1 has width ~x2, which is not ~
                         compatible with this array instance.  (Since the ~
                         port has width ~x3, the only acceptable widths are ~
                         ~x3 and ~x4.)"
                   :args (list elem arg.expr expr-width port-width
                               (* port-width insts)))
            nil))

       ((unless (vl-expr-sliceable-p arg.expr))
        (mv nil
            (fatal :type :vl-bad-argument
                   :msg "~a0: trying to slice an unsliceable argument, ~a1."
                   :args (list elem arg.expr))
            nil))

       ((unless (vl-expr-welltyped-p arg.expr))
        (mv nil
            (fatal :type :vl-bad-argument
                   :msg "~a0: trying to slice up ill-typed argument ~a1."
                   :args (list elem arg.expr))
            nil))

       ;; Everything is looking good, try to slice the expression into bits.
       ((mv successp warnings bits)
        (vl-msb-bitslice-expr arg.expr ss warnings))

       ((unless successp)
        ;; This shouldn't really occur in practice, but if it does occur we've
        ;; already given a warning.
        (mv nil warnings nil))

       ;; At this point, bits are provably a list of expr-width many
       ;; expressions, each of which is well-typed, 1-bit wide, and unsigned.
       ;; We now need to gather these expressions up into port-width bit
       ;; concatenations.  This is always successful and results in
       ;; insts-many port-width bit expressions.
       (partitions (vl-partition-msb-bitslices port-width bits))

       ;; Now we just have to turn all these expressions into new plainargs,
       ;; instead of just expressions.
       (plainargs (vl-exprlist-to-plainarglist partitions
                                               :dir arg.dir
                                               :atts arg.atts)))

    (mv t warnings plainargs))
  ///
  (defthm len-of-vl-partition-plainarg
    (let ((ret (vl-partition-plainarg arg port-width insts ss elem warnings)))
      (implies (mv-nth 0 ret)
               (equal (len (mv-nth 2 ret))
                      (pos-fix insts)))))

  ;; hrmn, blank handling ruins nice theorms about width/type...
  ;; could write a nice predicate, but whatever.
  )


(define vl-partition-plainarglist
  :parents (argument-partitioning)
  :short "Extend @(see vl-partition-plainarg) across a list of arguments."

  ((args        vl-plainarglist-p  "Arguments to some submodule.")
   (port-widths pos-listp          "Corresponding widths of the submodule's ports.")
   (insts       posp               "How many instances there are.")
   (ss vl-scopestack-p)
   (elem        vl-modelement-p    "Context for warnings.")
   (warnings    vl-warninglist-p   "Ordinary @(see warnings) accumulator."))
  :guard (same-lengthp args port-widths)
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (plainarglists vl-plainarglistlist-p))

  :long "<p>Supposing that @('args') has length <i>N</i>, the @('result') we
return on success is a list of <i>N</i> plainarglists (one for each argument),
and each of these lists has @('insts')-many plainargs.  That is, each element
of the @('result') is the partitioning of the corresponding argument.</p>"

  (b* (((when (atom args))
        (mv t (ok) nil))
       ((mv successp warnings car-result)
        (vl-partition-plainarg (car args) (car port-widths)
                               insts ss elem warnings))
       ((unless successp)
        (mv nil warnings nil))
       ((mv successp warnings cdr-result)
        (vl-partition-plainarglist (cdr args) (cdr port-widths)
                                   insts ss elem warnings))
       ((unless successp)
        (mv nil warnings nil)))
    (mv t warnings (cons car-result cdr-result)))
  ///
  (defmvtypes vl-partition-plainarglist (booleanp nil true-listp))

  (defthm all-have-len-of-vl-partition-plainarglist
    (let ((ret (vl-partition-plainarglist args port-widths insts ss elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (equal len (pos-fix insts)))
               (all-have-len (mv-nth 2 ret) len)))))


(define vl-reorient-partitioned-args
  :parents (argument-partitioning)
  :short "Group arguments for instances after @(see vl-partition-plainarglist)."
  ((lists true-listp)
   (n     natp))
  :guard (all-have-len lists n)
  (if (zp n)
      nil
    (cons (strip-cars lists)
          (vl-reorient-partitioned-args (strip-cdrs lists) (- n 1))))

  :long "<p>We are given @('lists'), which should be a @(see
vl-plainarglistlist-p) formed by calling @(see vl-partition-plainarglist), and
@('n'), the number of instances we are trying to generate.  Note that every
list in @('lists') has length @('n').</p>

<p>At this point, the args are bundled up in a bad order.  That is, to create
the new instances, we want to have lists of the form</p>

@({
   (arg1-slice1 arg2-slice1 arg3-slice1 ...) for the first instance,
   (arg1-slice2 arg2-slice2 arg3-slice2 ...) for the second instance,
   etc.
})

<p>But instead, what @(see vl-partition-plainarglist) does is create lists
of the slices, e.g., </p>

@({
   (arg1-slice1 arg1-slice2 arg1-slice3 ...)
   (arg2-slice1 arg2-slice2 arg2-slice3 ...)
   etc.
})

<p>So our goal is simply to simply transpose this matrix and aggregate the data
by slice, rather than by argument.</p>"
  ///
  (defthm vl-plainarglistlist-p-of-vl-reorient-partitioned-args
    (implies (and (force (vl-plainarglistlist-p lists))
                  (force (all-have-len lists n)))
             (vl-plainarglistlist-p (vl-reorient-partitioned-args lists n))))

  (defthm all-have-len-of-vl-reorient-partitioned-args
    (all-have-len (vl-reorient-partitioned-args lists n)
                  (len lists)))

  (defthm len-of-vl-reorient-partitioned-args
    (equal (len (vl-reorient-partitioned-args lists n))
           (nfix n))))

#||

;; Here's a quick little example:

(defconst *matrix*
  '((a1 a2 a3)
    (b1 b2 b3)
    (c1 c2 c3)
    (d1 d2 d3)))

(vl-reorient-partitioned-args *matrix* 3)

||#


(define vl-assemble-gateinsts
  :parents (argument-partitioning)
  :short "Build @(see vl-gateinst-p)'s from the sliced-up arguments."

  ((names string-listp "Names to give to the new gate instances.")
   (args  vl-plainarglistlist-p
          "The arguments for each instance, already reoriented; see @(see
           vl-partition-plainarglist) and @(see
           vl-reorient-partitioned-args).")
   (idx     integerp "Current index, used only for annotations.")
   (idxincr integerp "How to compute the next index, typically +/-1 depending
                      on whether this is an MSB-first or LSB-first range.")
   (type vl-gatetype-p)
   (strength vl-maybe-gatestrength-p)
   (delay vl-maybe-gatedelay-p)
   (atts vl-atts-p)
   (loc vl-location-p))
  :guard (same-lengthp names args)
  :returns (gates vl-gateinstlist-p)
  :hooks nil

  (if (atom args)
      nil
    (cons (make-vl-gateinst :type type
                            :name (car names)
                            :range nil
                            :strength strength
                            :delay delay
                            :args (car args)
                            :atts
                            (cons (cons "VL_REPLICATE_INDEX"
                                        (vl-make-index idx))
                                  atts)
                            :loc loc)
          (vl-assemble-gateinsts (cdr names) (cdr args)
                                 (+ idx idxincr) idxincr
                                 type strength delay atts loc))))


(define vl-replicate-gateinst
  :short "Convert a gate array instance into a list of gates (if necessary)."

  ((x        vl-gateinst-p     "Some gate, which may or may not be an instance array.")
   (nf       vl-namefactory-p  "For fresh name generation.")
   (ss vl-scopestack-p)
   (warnings vl-warninglist-p  "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (warnings      vl-warninglist-p)
      (new-gateinsts vl-gateinstlist-p "New gates that will replace @('x').")
      (nf            vl-namefactory-p))
  :long "<p>If @('x') has a range, i.e., it is an array of gate instances, then
we try to split it into a list of @('nil')-ranged, simple gates.  The
@('new-gateinsts') should replace @('x') in the module.</p>"

  (b* ((x  (vl-gateinst-fix x))
       (nf (vl-namefactory-fix nf))
       ((vl-gateinst x) x)
       ((unless x.range)
        ;; There is no range, so this is not an array of gates; we don't
        ;; need to do anything.
        (mv (ok) (list x) nf))

       ((unless (vl-range-resolved-p x.range))
        (mv (fatal :type :vl-bad-gate
                   :msg "~a0: expected range of instance array to be ~
                         resolved, but found ~a1."
                   :args (list x x.range))
            (list x)
            nf))

       ;; We add an annotation saying that these instances are from a gate
       ;; array.
       (x.atts (cons (list "VL_FROM_GATE_ARRAY") x.atts))

       ;; We previously checked that size was positive, but via the theorem
       ;; posp-of-vl-range-size this check was not necessary; size is always
       ;; positive.
       (size (vl-range-size x.range))

       ;; Claim: The port widths for gates are always 1.  BOZO is there any
       ;; evidence to support this claim, from the Verilog spec?
       (port-widths (replicate (len x.args) 1))

       ;; Partition the args into their slices, then transpose the slices to
       ;; form the new argument lists for the instances we are going to
       ;; generate.
       ((mv successp warnings slices)
        (vl-partition-plainarglist x.args port-widths size ss x warnings))

       ((unless successp)
        ;; Already added warnings
        (mv warnings (list x) nf))

       (transpose (vl-reorient-partitioned-args slices size))

       ;; Come up with names for these instances.
       ((mv warnings names nf)
        (vl-replicated-instnames x.name x.range nf x warnings))

       ;; Put the origname on the atts if the inst was named.
       (new-atts (if x.name
                     (cons (cons "VL_REPLICATE_ORIGNAME"
                                 (make-vl-atom :guts (vl-string x.name)))
                           x.atts)
                   x.atts))

       (left-idx (vl-resolved->val (vl-range->msb x.range)))
       (right-idx (vl-resolved->val (vl-range->lsb x.range)))
       (idx-incr (if (>= left-idx right-idx) -1 1))

       ;; Finally, assemble the gate instances.
       (new-gates
        (vl-assemble-gateinsts names transpose left-idx idx-incr
                               x.type x.strength x.delay new-atts x.loc)))

    ;; And that's it!
    (mv warnings new-gates nf))
  ///
  (defmvtypes vl-replicate-gateinst (nil true-listp nil)))


(define vl-replicate-gateinstlist
  :short "Extend @(see vl-replicate-gateinst) across a @(see
vl-gateinstlist-p)."
  ((x        vl-gateinstlist-p)
   (nf       vl-namefactory-p)
   (ss vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings      vl-warninglist-p)
      (new-gateinsts vl-gateinstlist-p "Replacements for @('x').")
      (nf            vl-namefactory-p))
  (b* (((when (atom x))
        (mv (ok) nil (vl-namefactory-fix nf)))
       ((mv warnings car-prime nf)
        (vl-replicate-gateinst (car x) nf ss warnings))
       ((mv warnings cdr-prime nf)
        (vl-replicate-gateinstlist (cdr x) nf ss warnings))
       (new-gateinsts (append car-prime cdr-prime)))
    (mv warnings new-gateinsts nf))
  ///
  (defmvtypes vl-replicate-gateinstlist (nil true-listp nil)))


(define vl-plainarglists-to-arguments
  :parents (argument-partitioning)
  :short "Convert each plainarglist in a @(see vl-plainarglistlist-p) into an
@(see vl-arguments-p)."
  ((x vl-plainarglistlist-p))
  :returns (args vl-argumentlist-p)
  (if (consp x)
      (cons (make-vl-arguments-plain :args (car x))
            (vl-plainarglists-to-arguments (cdr x)))
    nil)
  ///
  (defthm len-of-vl-plainarglists-to-arguments
    (equal (len (vl-plainarglists-to-arguments x))
           (len x))))


(define vl-replicate-arguments
  :short "Partition arguments for a module instance"

  ((args        vl-arguments-p  "Arguments to a module instance.  Should already
                                 be resolved, i.e. should be plainargs, and sized.")
   (port-widths pos-listp       "Widths of the corresponding ports.")
   (insts       posp            "Number of instances we're splitting these args into.")
   (ss vl-scopestack-p)
   (elem        vl-modelement-p  "Context for warnings.")
   (warnings    vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :hooks nil
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (arg-lists (and (vl-argumentlist-p arg-lists)
                      (implies (and successp
                                    (equal len (pos-fix insts)))
                               (equal (len arg-lists)
                                      len)))
                 "The new arguments to give to each (split up) module instance."))

  (b* ((insts (pos-fix insts))
       ((when (eq (vl-arguments-kind args) :vl-arguments-named))
        (mv nil
            (fatal :type :vl-bad-arguments
                   :msg "~a0: Expected only plain argument lists, but found ~
                         named args instead."
                   :args (list elem))
            nil))

       (actuals (vl-arguments-plain->args args))
       ((unless (same-lengthp actuals port-widths))
        (mv nil
            (fatal :type :vl-bad-arguments
                   :msg "~a0: Expected ~x1 arguments but found ~x2."
                   :args (list elem (len port-widths) (len actuals)))
            nil))

       ;; Slice up the arguments...
       ((mv successp warnings slices)
        (vl-partition-plainarglist actuals port-widths insts ss elem warnings))
       ((unless successp)
        ;; Already added warnings
        (mv nil warnings nil))

       ;; Transpose the matrix into slice-order
       (transpose (vl-reorient-partitioned-args slices insts))

       ;; Turn the plainarglists into vl-arguments-p structures
       (arg-lists (vl-plainarglists-to-arguments transpose)))
    (mv t (ok) arg-lists)))


(define vl-module-port-widths
  :short "Determine the widths of a module's ports."
  ((ports    vl-portlist-p "The module's ports.")
   (inst     vl-modinst-p  "The module instance we're trying to replicate;
                            serves merely as a context for warnings.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (port-widths (implies successp
                            (and (pos-listp port-widths)
                                 (equal (len port-widths)
                                        (len ports))))))
  :long "<p>We fail and cause fatal errors if any port is blank or does not have
         a positive width.</p>"
  :measure (len ports)
  (b* ((ports    (vl-portlist-fix ports))
       (warnings (vl-warninglist-fix warnings))
       (inst     (vl-modinst-fix inst))

       ((when (atom ports))
        (mv t warnings nil))
       (port1 (vl-port-fix (car ports)))
       ((when (eq (tag port1) :vl-interfaceport))
        (mv nil
            (fatal :type :vl-replicate-fail
                   :msg "~a0: bozo need to implement interface ports.~%"
                   :args (list inst))
            nil))
       (expr1  (vl-regularport->expr port1))
       (width1 (and expr1 (vl-expr->finalwidth expr1)))
       ((unless (posp width1))
        (mv nil
            (fatal :type :vl-replicate-fail
                   :msg "~a0: width of ~a1 is ~x2; expected a positive number."
                   :args (list inst port1
                               (and expr1 (vl-expr->finalwidth expr1))))
            nil))
       ((mv successp warnings cdr-sizes)
        (vl-module-port-widths (cdr ports) inst warnings))
       ((unless successp)
        (mv nil warnings nil)))
    (mv t warnings (cons width1 cdr-sizes))))


(define vl-assemble-modinsts
  :short "Build @(see vl-modinst-p)'s from the sliced-up arguments."
  ((names     string-listp      "Names to give to each instance.")
   (args      vl-argumentlist-p "Arguments to use for each instance.")
   (idx       integerp          "Index number, used in attributes.")
   (idxincr   integerp          "Typically +/-1, whether to count up or down.")
   (modname   stringp           "Module being instantiated.")
   (str       vl-maybe-gatestrength-p)
   (delay     vl-maybe-gatedelay-p)
   (paramargs vl-paramargs-p)
   (atts      vl-atts-p)
   (loc       vl-location-p))
  :guard (same-lengthp names args)
  :returns (modinsts vl-modinstlist-p)
  :hooks nil
  (if (atom args)
      nil
    (cons (make-vl-modinst :instname (car names)
                           :modname modname
                           :str str
                           :delay delay
                           :atts
                           (cons (cons "VL_REPLICATE_INDEX" (vl-make-index idx))
                                 atts)
                           :portargs (car args)
                           :paramargs paramargs
                           :loc loc)
          (vl-assemble-modinsts (cdr names) (cdr args) (+ idx idxincr)
                                idxincr modname str delay paramargs atts loc))))


(define vl-modinst-origname
  :short "Retrieve the original name of a module instance if it was modified by
          the replicate transform."
  ((x vl-modinst-p))
  :returns (orig-name maybe-stringp :rule-classes :type-prescription)
  (b* (((vl-modinst x) x)
       (x.instname (mbe :logic (and (stringp x.instname)
                                    x.instname)
                        :exec x.instname))
       (look (assoc-equal "VL_REPLICATE_ORIGNAME" x.atts))
       ((when (not (cdr look))) x.instname)
       ((when (not (and (vl-atom-p (cdr look))
                        (vl-string-p (vl-atom->guts (cdr look))))))
        (raise "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
        x.instname))
    (vl-string->value (vl-atom->guts (cdr look)))))

(define vl-modinst-origidx
  :short "Retrieve the original index of a module instance if it was modified by
          the replicate transform."
  ((x vl-modinst-p))
  :returns (index maybe-natp :rule-classes :type-prescription)
  (b* (((vl-modinst x) x)
       (look (assoc-equal "VL_REPLICATE_INDEX" x.atts))
       ((when (not (cdr look))) nil)
       ((when (not (vl-expr-resolved-p (cdr look))))
        (raise "Malformed VL_REPLICATE_INDEX attribute: ~x0~%" (cdr look))
        nil))
    (vl-resolved->val (cdr look))))

(define vl-modinst-origname/idx
  :short "Retrieve the Verilog-style name for this module instance, like foo[3],
          if it was modified by the @('replicate') transform."
  ((x vl-modinst-p))
  :returns (verilog-name maybe-stringp :rule-classes :type-prescription)
  (b* ((origname (vl-modinst-origname x))
       ((unless origname) nil)
       (origidx (vl-modinst-origidx x)))
    (if origidx
        (cat origname "[" (natstr origidx) "]")
      origname)))

(define vl-gateinst-origname
  :short "Retrieve the original name of a gate instance if it was modified by
          the replicate transform."
  ((x vl-gateinst-p))
  :returns (origname maybe-stringp :rule-classes :type-prescription)
  (b* (((vl-gateinst x) x)
       (x.name (mbe :logic (and (stringp x.name) x.name)
                    :exec x.name))
       (look (assoc-equal "VL_REPLICATE_ORIGNAME" x.atts))
       ((when (not (cdr look))) x.name)
       ((when (not (and (vl-atom-p (cdr look))
                        (vl-string-p (vl-atom->guts (cdr look))))))
        (er hard? 'vl-gateinst-origname
            "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
        x.name))
    (vl-string->value (vl-atom->guts (cdr look)))))

(define vl-gateinst-origidx
  :short "Retrieve the Verilog-style name for this gate instance, like foo[3],
          if it was modified by the @('replicate') transform."
  ((x vl-gateinst-p))
  :returns (index maybe-natp :rule-classes :type-prescription)
  (b* (((vl-gateinst x) x)
       (look (assoc-equal "VL_REPLICATE_INDEX" x.atts))
       ((when (not (cdr look))) nil)
       ((when (not (vl-expr-resolved-p (cdr look))))
        (raise "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
        nil))
    (vl-resolved->val (cdr look))))

(define vl-gateinst-origname/idx
  :short "Retrieve the Verilog-style name for this gate instance, like foo[3],
          if it was modified by the @('replicate') transform."
  ((x vl-gateinst-p))
  :returns (verilog-name maybe-stringp :rule-classes :type-prescription)
  (b* ((origname (vl-gateinst-origname x))
       ((unless origname) nil)
       (origidx (vl-gateinst-origidx x)))
    (if origidx
        (cat origname "[" (natstr origidx) "]")
      origname)))

(define vl-replicate-modinst
  :short "Convert a module instance into a list of simpler instances, if
necessary."
  ((x        vl-modinst-p     "A module instance, perhaps an instance array.")
   (nf       vl-namefactory-p "For generating fresh names.")
   (ss vl-scopestack-p)
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :hooks nil
  :returns
  (mv (warnings     vl-warninglist-p)
      (new-modinsts vl-modinstlist-p :hyp :fguard "Replacements for @('x').")
      (nf           vl-namefactory-p :hyp :fguard))
  :long "<p>If @('x') has a range, i.e., it is an array of module instances,
then we try to split it into a list of @('nil')-ranged, simple instances.  If
@('x') is a regular (non-array) instance, we just keep it.</p>"

  (b* (((vl-modinst x) x)

       ((unless x.range)
        ;; There isn't a range, so this is already an ordinary, non-array
        ;; instance.  We don't need to do anything, so return early.
        (mv (ok) (list x) nf))

       ((unless (vl-range-resolved-p x.range))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: instance array with unresolved range: ~a1."
                   :args (list x x.range))
            (list x)
            nf))

       ((unless (vl-paramargs-empty-p x.paramargs))
        ;; Probably unnecessary, but I don't really want to think about
        ;; parameters here.
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: instance array still has parameters?  This ~
                         should have been taken care of during ~
                         unparameterization."
                   :args (list x))
            (list x)
            nf))

       ;; We add an annotation saying that these instances are from an array.
       (x.atts (cons (list "VL_FROM_INST_ARRAY") x.atts))
       (size   (vl-range-size x.range))

       (target (vl-scopestack-find-definition x.modname ss))
       ((unless (and target (eq (tag target) :vl-module)))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: instance of undefined module ~m1."
                   :args (list x x.modname))
            (list x)
            nf))

       ((mv successp warnings port-widths)
        (vl-module-port-widths (vl-module->ports target) x warnings))
       ((unless successp)
        ;; Already added a warning.
        (mv warnings (list x) nf))

       ((mv successp warnings new-args)
        (vl-replicate-arguments x.portargs port-widths size ss x warnings))
       ((unless successp)
        (mv warnings (list x) nf))

       ((mv warnings names nf)
        (vl-replicated-instnames x.instname x.range nf x warnings))

       ;; Put the origname on the atts if the inst was named.
       (new-atts (if x.instname
                     (cons (cons "VL_REPLICATE_ORIGNAME"
                                 (make-vl-atom :guts (vl-string x.instname)))
                           x.atts)
                   x.atts))

       (left-idx  (vl-resolved->val (vl-range->msb x.range)))
       (right-idx (vl-resolved->val (vl-range->lsb x.range)))
       (idx-incr (if (>= left-idx right-idx) -1 1))

       (new-modinsts
        (vl-assemble-modinsts names new-args left-idx idx-incr x.modname x.str
                              x.delay x.paramargs new-atts x.loc)))

    (mv warnings new-modinsts nf))
  ///
  (defmvtypes vl-replicate-modinst (nil true-listp nil)))


(define vl-replicate-modinstlist
  :short "Extend @(see vl-replicate-modinst) across a @(see vl-modinstlist-p)"
  ((x        vl-modinstlist-p)
   (nf       vl-namefactory-p)
   (ss vl-scopestack-p)
   (warnings vl-warninglist-p))
  :hooks nil
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinstlist-p :hyp :fguard)
               (nf       vl-namefactory-p :hyp :fguard))
  (b* (((when (atom x))
        (mv (ok) nil nf))
       ((mv warnings car-insts nf)
        (vl-replicate-modinst (car x) nf ss warnings))
       ((mv warnings cdr-insts nf)
        (vl-replicate-modinstlist (cdr x) nf ss warnings)))
    (mv warnings (append car-insts cdr-insts) nf))
  ///
  (defmvtypes vl-replicate-modinstlist (nil true-listp nil)))


(define vl-some-gateinst-array-p ((x vl-gateinstlist-p))
  :short "Are there any gate instance arrays?"
  (if (atom x)
      nil
    (or (vl-gateinst->range (car x))
        (vl-some-gateinst-array-p (cdr x)))))

(define vl-some-modinst-array-p ((x vl-modinstlist-p))
  :short "Are there any module instance arrays?"
  (if (atom x)
      nil
    (or (vl-modinst->range (car x))
        (vl-some-modinst-array-p (cdr x)))))

(define vl-module-replicate
  :short "Eliminate gate and module instance arrays from a module."
  ((x        vl-module-p                           "Module to simplify.")
   (ss vl-scopestack-p))
  :returns (new-x vl-module-p
                  "Rewritten version of X, where any gate or module instance
                   arrays have been replaced by an explicit list of
                   instances.")
  (b* ((x    (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)

       (ss   (vl-scopestack-push x ss))

       ((vl-module x) x)

       ((unless (or (vl-some-gateinst-array-p x.gateinsts)
                    (vl-some-modinst-array-p x.modinsts)))
        ;; Optimization.  Avoid constructing ialist, etc., when there aren't
        ;; any arrays to replicate anyway.
        x)

       (nf         (vl-starting-namefactory x))

       (warnings   x.warnings)

       ((mv warnings new-gateinsts nf)
        (vl-replicate-gateinstlist x.gateinsts nf ss warnings))

       ((mv warnings new-modinsts nf)
        (vl-replicate-modinstlist x.modinsts nf ss warnings))

       (- (vl-free-namefactory nf))

       (x-prime (change-vl-module x
                                  :modinsts new-modinsts
                                  :gateinsts new-gateinsts
                                  :warnings warnings)))
    x-prime))

(defprojection vl-modulelist-replicate ((x        vl-modulelist-p)
                                        (ss vl-scopestack-p))
  :short "Extend @(see vl-module-replicate) across the list of modules."
  :returns (new-x vl-modulelist-p)
  (vl-module-replicate x ss))

(define vl-design-replicate
  :short "Top-level @(see replicate-insts) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-replicate x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
