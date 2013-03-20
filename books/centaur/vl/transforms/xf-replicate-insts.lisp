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
(include-book "../mlib/expr-slice")
(include-book "../mlib/namefactory")
(include-book "../mlib/find-module")
(include-book "../mlib/context")
(local (include-book "../util/arithmetic"))


(defxdoc replicate
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



(defsection vl-replicated-instnames
  :parents (replicate)
  :short "Safely generate the instance names for @(see replicate)d instances."

  :long "<p>This function is responsible for naming the new module instances
that are going to be created when we split up an instance array.  We really
want these new names to correspond to the original instance name and the
instance numbers, since otherwise it can be hard to understand the relationship
of the transformed module's state to the original module.</p>

<p>Suppose we are transforming an instance like this:</p>

@({
   type foo [N:0] (arg1, arg2, ..., argM);
})

<p><b>Signature:</b> @(call vl-replicated-instnames) returns @('(MV WARNINGS'
NAMES NF')').</p>

<p>We are given:</p>

<ul>

<li>@('instname'), a string that is the name of the instance array, e.g.,
@('foo').</li>

<li>@('instrange'), the associated range, e.g., @('[N:0]').</li>

<li>@('nf'), a @(see vl-namefactory-p) for generating new names.</li>

<li>@('warnings'), a @(see warnings) accumulator that we may extend with a
non-fatal warning if our preferred names are unavailable.</li>

<li>@('inst'), the whole instance, which is semantically irrelevant and used
only as a context for warnings.</li>

</ul>

<p>We produce @('names'), a list of @('N+1') names that are to be used as the
instance names for the split up arguments.</p>

<p>We try to use names of the form @('instname_index') if they are available,
e.g., for a range like [N:0], we would prefer to generate names like @('foo_N,
..., foo_0').</p>

<p>We want to return the names so that the name corresponding to the most
significant bits comes first.  If the range is like @('[N:0]'), then we return
@('foo_N, ..., foo_0').  But if the range goes the other way, i.e., @('[0:N]'),
then we return @('foo_0, ..., foo_N').</p>"

(defund vl-preferred-replicate-names (low high instname)
    ;; Preferred names from low to high, inclusive, e.g., (foo_3 foo_4 foo_5)
    (declare (xargs :guard (and (natp low)
                                (natp high)
                                (<= low high)
                                (stringp instname))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (let ((low  (lnfix low))
          (high (lnfix high))
          (name (cat instname "_" (natstr low))))
      (if (mbe :logic (zp (- high low))
               :exec (= low high))
          (list name)
        (cons name (vl-preferred-replicate-names (+ 1 low) high instname)))))

(defthm string-listp-of-vl-preferred-replicate-names
    (string-listp (vl-preferred-replicate-names low high instname))
    :hints(("Goal" :in-theory (enable vl-preferred-replicate-names))))

(defthm len-of-vl-preferred-replicate-names
    (equal (len (vl-preferred-replicate-names low high instname))
           (+ 1 (nfix (- (nfix high) (nfix low)))))
    :hints(("Goal" :in-theory (enable vl-preferred-replicate-names))))


(defund vl-bad-replicate-names (n basename nf)
    ;; Fallback names in case our preferred names aren't available.  Only called
    ;; if there is a name conflict that prevents us from using good names.
    "Returns (MV NAMES NF')."
    (declare (xargs :guard (and (natp n)
                                (stringp basename)
                                (vl-namefactory-p nf))))
    (b* (((when (zp n))
          (mv nil nf))
         ((mv name nf)
          (vl-namefactory-indexed-name basename nf))
         ((mv others nf)
          (vl-bad-replicate-names (- n 1) basename nf)))
      (mv (cons name others) nf)))

(defthm vl-bad-replicate-names-props
    (implies (and (force (stringp basename))
                  (force (vl-namefactory-p nf)))
             (and (string-listp (mv-nth 0 (vl-bad-replicate-names n basename nf)))
                  (vl-namefactory-p (mv-nth 1 (vl-bad-replicate-names n basename nf)))))
    :hints(("Goal" :in-theory (enable vl-bad-replicate-names))))

(defthm len-of-vl-bad-replicate-names
    (equal (len (mv-nth 0 (vl-bad-replicate-names n basename nf)))
           (nfix n))
    :hints(("Goal" :in-theory (enable vl-bad-replicate-names))))


(local (in-theory (enable vl-range-resolved-p)))

(defund vl-replicated-instnames (instname instrange nf inst warnings)
    "Returns (MV WARNINGS NAMES NF')"
    (declare (xargs :guard (and (vl-maybe-string-p instname)
                                (vl-range-p instrange)
                                (vl-range-resolved-p instrange)
                                (vl-namefactory-p nf)
                                (or (vl-modinst-p inst)
                                    (vl-gateinst-p inst))
                                (vl-warninglist-p warnings))))
    (b* ((left     (vl-resolved->val (vl-range->msb instrange)))
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
          (mv warnings names-msb-first nf))

         ;; Use bad names.  We don't care what order them come in.
         ((mv fresh nf)
          (vl-bad-replicate-names (+ 1 (- high low))
                                  (cat "vl_badname_" instname)
                                  nf))
         (warnings
          (cons (make-vl-warning
                 :type :vl-warn-replicate-name
                 :msg "~a0: preferred names for instance array ~s1 are not ~
                     available, so using lousy vl_badname_* naming scheme ~
                     instead.  This conflict is caused by ~&2."
                 :args (list inst instname
                             (difference (mergesort names-msb-first)
                                         (mergesort fresh)))
                 :fatalp nil
                 :fn 'vl-replicated-instnames)
                warnings)))
      (mv warnings (rev fresh) nf)))

  (local (in-theory (enable vl-replicated-instnames)))

  (defthm vl-warninglist-p-of-vl-replicated-instnames
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-replicated-instnames instname instrange nf inst warnings)))))

  (defthm string-listp-of-vl-replicated-instnames
    (implies (and (force (vl-maybe-string-p instname))
                  (force (vl-namefactory-p nf)))
             (string-listp
              (mv-nth 1 (vl-replicated-instnames instname instrange nf inst warnings)))))

  (defthm len-of-vl-replicated-instnames
    (implies (and (force (vl-range-resolved-p instrange))
                  (force (vl-namefactory-p nf)))
             (equal
              (len (mv-nth 1 (vl-replicated-instnames instname instrange nf inst warnings)))
              (vl-range-size instrange)))
    :hints(("Goal" :in-theory (e/d (vl-range-size)))))

  (defthm vl-namefactory-p-of-vl-replicated-instnames
    (implies (and (force (vl-maybe-string-p instname))
                  (force (vl-range-p instrange))
                  (force (vl-range-resolved-p instrange))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p
              (mv-nth 2 (vl-replicated-instnames instname instrange nf inst
                                                 warnings))))))


(defsection vl-replicate-orig-instnames
  :parents (replicate)
  :short "Generate the original instance names (with square-bracketed indices)
for replicated instances."

  :long "<p>These names are just going to be attributes for the new instances,
which allow you to relate the original Verilog with the simplified Verilog.</p>

<p>The names are returned in msb-first order to agree with @(see
vl-replicated-instnames).</p>"

  (defund vl-replicate-orig-instnames1 (low high instname)
    ;; Preferred names in lowest-first order, e.g., (foo_3 foo_4 foo_5)
    (declare (xargs :guard (and (natp low)
                                (natp high)
                                (<= low high)
                                (stringp instname))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (let ((low  (lnfix low))
          (high (lnfix high))
          (name (cat instname "[" (natstr low) "]")))
      (if (mbe :logic (zp (- high low))
               :exec (= low high))
          (list name)
        (cons name (vl-replicate-orig-instnames1 (+ 1 low) high instname)))))

  (defthm string-listp-of-vl-replicate-orig-instnames1
    (string-listp (vl-replicate-orig-instnames1 low high instname))
    :hints(("Goal" :in-theory (enable vl-replicate-orig-instnames1))))

  (defthm len-of-vl-replicate-orig-instnames1
    (equal (len (vl-replicate-orig-instnames1 low high instname))
           (+ 1 (nfix (- (nfix high) (nfix low)))))
    :hints(("Goal" :in-theory (enable vl-replicate-orig-instnames1))))



  (defund vl-replicate-orig-instnames (instname instrange)
    (declare (xargs :guard (and (vl-maybe-string-p instname)
                                (vl-range-p instrange)
                                (vl-range-resolved-p instrange))))
    (b* ((left  (vl-resolved->val (vl-range->msb instrange)))
         (right (vl-resolved->val (vl-range->lsb instrange)))
         (low   (min left right))
         (high  (max left right))

; Sol asked if the instname can really be nil.  Yes, but it's pretty unusual.
; The reason is that VL uses the same modinst representation for both module
; instances and user-defined primitive instances (but we don't actually support
; UDP's yet), and UDP's aren't required to have instance names.  Go figure.

         (instname (or instname "unnamed"))

         (low-to-high (vl-replicate-orig-instnames1 low high instname)))
      (if (>= left right)
          (reverse low-to-high)
        low-to-high)))

  (defthm string-listp-of-vl-replicate-orig-instnames
    (string-listp (vl-replicate-orig-instnames instname instrange))
    :hints(("Goal" :in-theory (enable vl-replicate-orig-instnames))))

  (defthm len-of-vl-replicate-orig-instnames
    (equal (len (vl-replicate-orig-instnames instname instrange))
           (vl-range-size instrange))
    :hints(("Goal" :in-theory (enable vl-replicate-orig-instnames
                                      vl-range-size)))))




(defxdoc argument-partitioning
  :parents (replicate)
  :short "How arguments to instance arrays are split up and given to the
individual instances."

  :long "<p>Recall that in the @(see replicate) transform we are basically
rewriting instance arrays like this:</p>

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



(defsection vl-partition-msb-bitslices
  :parents (argument-partitioning)
  :short "Group up a list of bits into N-bit concatenations."

  :long "<p>The basic way that we partition an expression into @('N')-bit
slices is to break it up into individual bits with @(see vl-msb-bitslice-expr),
then group these bits together into @('N')-bit concatenations.</p>

<p><b>Signature:</b> @(call vl-partition-msb-bitslices) returns a @(see
vl-exprlist-p).</p>

<ul>

<li>@('n') must be a positive number that must evenly divide @('(len x)').</li>

<li>@('x') must be a list of 1-bit, unsigned expressions.  Typically we expect
that @('x') is the result of calling @(see vl-msb-bitslice-expr) to slice up an
expression into such bits.</li>

</ul>

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

<li>Aesthetics here are not very important because instance arrays are not
    that common in the first place, so we are not going to be breaking up
    very many expressions in this potentially bad way, and</li>

<li>Not cleaning avoids any potential errors in the cleaning code.  This is
    not much of an argument since the cleaning code is relatively simple,
    but it still has some merit.</li>

</ol>

<p>NOTE: we now have the function vl-expr-clean-concats in
mlib/clean-concats.lisp, which does this cleaning.  It's currently not used, in
case there are any bugs, but perhaps we should re-integrate it.</p>"

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (local (defthm l0
           (implies (and (equal (vl-exprlist->finalwidths x) (repeat 1 (len x)))
                         (natp n)
                         (<= n (len x)))
                    (equal (vl-exprlist->finalwidths (nthcdr n x))
                           (repeat 1 (- (len x) n))))
           :hints(("Goal" :in-theory (enable repeat nthcdr)))))

  (defund vl-partition-msb-bitslices (n x)
    (declare (xargs :guard (and (posp n)
                                (= (mod (len x) n) 0)
                                (vl-exprlist-p x)
                                (true-listp x)
                                (all-equalp 1 (vl-exprlist->finalwidths x)))
                    :measure (len x)))
    (let ((n (lnfix n)))
      (cond ((= n 0)
             nil)
            ((< (len x) n)
             nil)
            (t
             (cons (make-vl-nonatom :op :vl-concat
                                    :args (take n x)
                                    :finalwidth n
                                    :finaltype :vl-unsigned
                                    :atts nil)
                   (vl-partition-msb-bitslices n (nthcdr n x)))))))

  (local (in-theory (enable vl-partition-msb-bitslices)))

  (defthm vl-exprlist-p-of-vl-partition-msb-bitslices
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-partition-msb-bitslices n x))))

  (defthm len-of-vl-partition-msb-bitslices
    (implies (force (posp n))
             (equal (len (vl-partition-msb-bitslices n x))
                    (floor (len x) n))))

  (defthm vl-exprlist->finalwidths-of-vl-partition-msb-bitslices
    (implies (force (posp n))
             (equal (vl-exprlist->finalwidths (vl-partition-msb-bitslices n x))
                    (repeat n (floor (len x) n))))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm vl-exprlist->finaltypes-of-vl-partition-msb-bitslices
    (implies (force (posp n))
             (equal (vl-exprlist->finaltypes (vl-partition-msb-bitslices n x))
                    (repeat :vl-unsigned (floor (len x) n))))
    :hints(("Goal" :in-theory (enable repeat))))

  (local (defthm c0
           (implies (and (all-equalp 1 (vl-exprlist->finalwidths x))
                         (<= (nfix n) (len x)))
                    (all-equalp 1 (vl-exprlist->finalwidths (take n x))))
           :hints(("goal"
                   :in-theory (e/d (acl2::take-redefinition)
                                   (all-equalp))))))

  (local (defthm c1
           (implies (all-equalp 1 (vl-exprlist->finalwidths x))
                    (all-equalp 1 (vl-exprlist->finalwidths (nthcdr n x))))))

  (local (defthm c2
           (implies (all-equalp 1 (vl-exprlist->finalwidths x))
                    (not (member-equal nil (vl-exprlist->finalwidths x))))))

  (defthm vl-exprlist-welltyped-p-of-vl-partition-msb-bitslices
    (implies (and (force (vl-exprlist-p x))
                  (force (vl-exprlist-welltyped-p x))
                  (force (all-equalp 1 (vl-exprlist->finalwidths x))))
             (vl-exprlist-welltyped-p (vl-partition-msb-bitslices n x)))
    :hints(("Goal" :in-theory (e/d (vl-expr-welltyped-p)
                                   (all-equalp))))))




(defsection vl-partition-plainarg
  :parents (argument-partitioning)
  :short "Partition a plain argument into slices."

  :long "<p><b>Signature:</b> @(call vl-partition-plainarg) returns @('(mv
successp warnings plainargs)').</p>

<p>As inputs,</p>

<ul>

<li>@('arg') is a plainarg which we may need to replicate,</li>

<li>@('port-width') is the width of the port this argument is connected
to.</li>

<li>@('insts') is the number of instances in this array,</li>

<li>@('mod') is the superior module that the instance array occurs in, which is
needed for proper bit-splitting,</li>

<li>@('ialist') is the @(see vl-moditem-alist) for @('mod'), for fast wire
lookups,</li>

<li>@('elem') is a @(see vl-modelement-p) for good error messages,</li>

<li>@('warnings') is an accumulator for warnings, and may be extended with
fatal warnings.</li>

</ul>

<p>Our goal is to create a list of the @('insts')-many plainargs which this
port is to be partitioned into.  On success, @('plainargs') will be a list of
@('insts') arguments, each of which has width @('port-width').  The arguments
are in \"msb-first\" order, i.e., the \"msb-most slice\" of @('arg') comes
first.</p>

<p>We might fail with a fatal warning if there is some problem with the actual;
we expect the actual to be already sized, <see url='@(url
vl-expr-welltyped-p)'>well-typed</see>, and <see url='@(url
expr-slicing)'>sliceable</see>), and its width must be compatible with the
width of the port, as described in @(see argument-partitioning).</p>"

  (defund vl-partition-plainarg (arg port-width insts mod ialist elem warnings)
    "Returns (MV WARNINGS PLAINARGS)"
    (declare (xargs :guard (and (vl-plainarg-p arg)
                                (posp port-width)
                                (posp insts)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))

    (b* ((expr (vl-plainarg->expr arg))
         ((unless expr)
          ;; Special case for blanks: If we have a blank in an array of
          ;; instances, we just want to send blank to each member of the
          ;; instance.
          (mv t warnings (repeat arg insts)))

         (expr-width (vl-expr->finalwidth expr))
         ((unless (posp expr-width))
          (b* ((w (make-vl-warning
                   :type :vl-bad-argument
                   :msg "~a0: expected argument widths to be computed, but ~
                         found argument ~a1 without any width assigned."
                   :args (list elem expr)
                   :fatalp t
                   :fn 'vl-partition-plainarg)))
            (mv nil (cons w warnings) nil)))

         ((when (= expr-width port-width))
          ;; The port is exactly as wide as the argument being given to it.
          ;; We are to replicate the argument, verbatim, across all of the
          ;; instances we are creating.
          (mv t warnings (repeat arg insts)))

         ;; Otherwise, the port is not the same width as the argument.  In this
         ;; case, the argument's width should be a multiple of the port's
         ;; width.

         ((unless (= expr-width (* port-width insts)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-argument
                   :msg "~a0: argument ~a1 has width ~x2, which is not ~
                         compatible with this array instance.  (Since the ~
                         port has width ~x3, the only acceptable widths are ~
                         ~x3 and ~x4.)"
                   :args (list elem expr expr-width port-width (* port-width insts))
                   :fatalp t
                   :fn 'vl-partition-plainarg)))
            (mv nil (cons w warnings) nil)))

         ((unless (vl-expr-sliceable-p expr))
          (b* ((w (make-vl-warning
                   :type :vl-bad-argument
                   :msg "~a0: trying to slice an unsliceable argument, ~a1."
                   :args (list elem expr)
                   :fatalp t
                   :fn 'vl-partition-plainarg)))
            (mv nil (cons w warnings) nil)))

         ((unless (vl-expr-welltyped-p expr))
          (b* ((w (make-vl-warning
                   :type :vl-bad-argument
                   :msg "~a0: trying to slice up ill-typed argument ~a1."
                   :args (list elem expr)
                   :fatalp t
                   :fn 'vl-partition-plainarg)))
            (mv nil (cons w warnings) nil)))

         ;; Everything is looking good, try to slice the expression into bits.
         ((mv successp warnings bits)
          (vl-msb-bitslice-expr expr mod ialist warnings))

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
                                                 :dir (vl-plainarg->dir arg)
                                                 :atts (vl-plainarg->atts arg))))

      (mv t warnings plainargs)))

  (local (in-theory (enable vl-partition-plainarg)))

  (defthm vl-warninglist-p-of-vl-partition-plainarg
    (let ((ret (vl-partition-plainarg arg port-width insts mod ialist elem warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-plainarglist-p-of-vl-partition-plainarg
    (let ((ret (vl-partition-plainarg arg port-width insts mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-plainarg-p arg))
                    (force (posp port-width))
                    (force (posp insts))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-plainarglist-p (mv-nth 2 ret)))))

  (defthm len-of-vl-partition-plainarg
    (let ((ret (vl-partition-plainarg arg port-width insts mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-plainarg-p arg))
                    (force (posp port-width))
                    (force (posp insts))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (len (mv-nth 2 ret))
                      insts))))

  ;; hrmn, blank handling ruins nice theorms about width/type...
  ;; could write a nice predicate, but whatever.
  )


(defsection vl-partition-plainarglist
  :parents (argument-partitioning)
  :short "Extend @(see vl-partition-plainarg) across a list of arguments."

  :long "<p><b>Signature:</b> @(call vl-partition-plainarglist) returns @('(mv
successp warnings result)'), where @('result') is a @(see
vl-plainarglistlist-p).</p>

<p>Supposing that @('args') has length <i>N</i>, the @('result') we return on
success is a list of <i>N</i> plainarglists (one for each argument), and each
of these lists has @('insts')-many plainargs.  That is, each element of the
@('result') is the partitioning of the corresponding argument.</p>"

  (defund vl-partition-plainarglist (args port-widths insts mod ialist elem warnings)
    "Returns (MV SUCCESSP WARNINGS PLAINARGLISTS)"
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (pos-listp port-widths)
                                (same-lengthp args port-widths)
                                (posp insts)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom args))
          (mv t warnings nil))
         ((mv successp warnings car-result)
          (vl-partition-plainarg (car args) (car port-widths) insts mod ialist elem warnings))
         ((unless successp)
          (mv nil warnings nil))
         ((mv successp warnings cdr-result)
          (vl-partition-plainarglist (cdr args) (cdr port-widths) insts mod ialist elem warnings))
         ((unless successp)
          (mv nil warnings nil)))
      (mv t warnings (cons car-result cdr-result))))

  (defmvtypes vl-partition-plainarglist (booleanp nil true-listp))

  (local (in-theory (enable vl-partition-plainarglist)))

  (defthm vl-warninglist-p-of-vl-partition-plainarglist
    (let ((ret (vl-partition-plainarglist args port-widths insts mod ialist elem warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-plainarglistlist-p-of-vl-partition-plainarglist
    (let ((ret (vl-partition-plainarglist args port-widths insts mod ialist elem warnings)))
      (implies (and (force (vl-plainarglist-p args))
                    (force (pos-listp port-widths))
                    (force (same-lengthp args port-widths))
                    (force (posp insts))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-plainarglistlist-p (mv-nth 2 ret)))))

  (defthm all-have-len-of-vl-partition-plainarglist
    (let ((ret (vl-partition-plainarglist args port-widths insts mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-plainarglist-p args))
                    (force (pos-listp port-widths))
                    (force (same-lengthp args port-widths))
                    (force (posp insts))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (all-have-len (mv-nth 2 ret) insts)))))




(defsection vl-reorient-partitioned-args
  :parents (argument-partitioning)
  :short "Group arguments for instances after @(see vl-partition-plainarglist)."

  :long "<p><b>Signature:</b> @(call vl-reorient-partitioned-args) returns a
@(see vl-plainarglistlist-p).</p>

<p>We are given @('lists'), which should be a @(see vl-plainarglistlist-p)
formed by calling @(see vl-partition-plainarglist), and @('n'), the number of
instances we are trying to generate.  Note that every list in @('lists') has
length @('n').</p>

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

<p>So our goal is simply to simply transpose this matrix and aggregate the
data by slice, rather than by argument.</p>"

  (defund vl-reorient-partitioned-args (lists n)
    (declare (xargs :guard (and (all-have-len lists n)
                                (true-listp lists)
                                (natp n))))
    (if (zp n)
        nil
      (cons (strip-cars lists)
            (vl-reorient-partitioned-args (strip-cdrs lists) (- n 1)))))

  (local (in-theory (enable vl-reorient-partitioned-args)))

  (defthm vl-plainarglistlist-p-of-vl-reorient-partitioned-args
    (implies (and (vl-plainarglistlist-p lists)
                  (all-have-len lists n))
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



(defsection vl-assemble-gateinsts
  :parents (argument-partitioning)
  :short "Build @(see vl-gateinst-p)'s from the sliced-up arguments."

  :long "<p><b>Signature:</b> @(call vl-assemble-gateinsts) returns a @(see
vl-gateinstlist-p).</p>

<p>@('names') are the names to give the instances and @('args') are the
reoriented, partitioned arguments (see @(see vl-partition-plainarglist) and
@(see vl-reorient-partitioned-args); the other arguments are replicated from
the gate instance.  We create the new gates.</p>"

  (defund vl-assemble-gateinsts (names args idx idxincr type strength delay atts loc)
    (declare (xargs :guard (and (string-listp names)
                                (vl-plainarglistlist-p args)
                                (same-lengthp names args)
                                (integerp idx)
                                (integerp idxincr)
                                (vl-gatetype-p type)
                                (vl-maybe-gatestrength-p strength)
                                (vl-maybe-gatedelay-p delay)
                                (vl-atts-p atts)
                                (vl-location-p loc))))
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
            (vl-assemble-gateinsts (cdr names) (cdr args) (+ idx idxincr) idxincr type strength delay atts loc))))

  (local (in-theory (enable vl-assemble-gateinsts)))

  (defthm vl-gateinstlist-p-of-vl-assemble-gateinsts
    (implies (and (force (string-listp names))
                  (force (vl-plainarglistlist-p args))
                  (force (same-lengthp names args))
                  (force (vl-gatetype-p type))
                  (force (vl-maybe-gatestrength-p strength))
                  (force (vl-maybe-gatedelay-p delay))
                  (force (vl-atts-p atts))
                  (force (vl-location-p loc)))
             (vl-gateinstlist-p
              (vl-assemble-gateinsts names args idx idxincr type strength delay
                                     atts loc)))
    :hints(("Goal" :in-theory (disable stringp-when-true-listp
                                       vl-location-p-when-wrong-tag)))))




; BOZO now that we have VL primitive modules for other gates, it might make the
; most sense to try to just eliminate all gates in one fell swoop early in the
; transformation sequence, replacing them with their VL module equivalents,
; then only deal with module instances instead of gate instances here.

(defsection vl-replicate-gateinst
  :parents (replicate)
  :short "Convert a gate into a list of simpler gates, if necessary."

  :long "<p><b>Signature:</b> @(call vl-replicate-gateinst) returns @('(mv
warnings new-gateinsts new-nf)').</p>

<ul>

<li>@('x') is some gate</li>

<li>@('warnings') is an accumulator for warnings,</li>

<li>@('mod') is the module that @('x') occurs in, and @('ialist') is its @(see
vl-moditem-alist),</li>

<li>@('nf') is a @(see vl-namefactory-p) for generating names.</li>

</ul>

<p>If @('x') has a range, i.e., it is an array of gate instances, then we try
to split it into a list of @('nil')-ranged, simple gates.  The
@('new-gateinsts') should replace @('x') in the module.</p>"


  (defund vl-replicate-gateinst (x nf mod ialist warnings)
    "Returns (MV WARNINGS' NEW-GATEINSTS NF')"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-namefactory-p nf)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))))
    (b* (((vl-gateinst x) x)

         ((unless x.range)
          ;; There is no range, so this is not an array of gates; we don't
          ;; need to do anything.
          (mv warnings (list x) nf))

         ((unless (vl-range-resolved-p x.range))
          (b* ((w (make-vl-warning
                   :type :vl-bad-gate
                   :msg "~a0: expected range of instance array to be ~
                         resolved, but found ~a1."
                   :args (list x x.range)
                   :fatalp t
                   :fn 'vl-replicate-gateinst)))
            (mv (cons w warnings) (list x) nf)))

         ;; We add an annotation saying that these instances are from a gate
         ;; array.
         (x.atts      (cons (list "VL_FROM_GATE_ARRAY") x.atts))

         ;; We previously checked that size was positive, but via the theorem
         ;; posp-of-vl-range-size this check was not necessary; size is always
         ;; positive.
         (size        (vl-range-size x.range))

         ;; Claim: The port widths for gates are always 1.  BOZO is there any
         ;; evidence to support this claim, from the Verilog spec?
         (port-widths (repeat 1 (len x.args)))

         ;; Partition the args into their slices, then transpose the slices to
         ;; form the new argument lists for the instances we are going to
         ;; generate.
         ((mv successp warnings slices)
          (vl-partition-plainarglist x.args port-widths size mod ialist x warnings))

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
          (vl-assemble-gateinsts names transpose left-idx idx-incr x.type x.strength x.delay new-atts x.loc)))

      ;; And that's it!
      (mv warnings new-gates nf)))

  (defmvtypes vl-replicate-gateinst (nil true-listp nil))

  (local (in-theory (enable vl-replicate-gateinst)))

  (defthm vl-warninglist-p-of-vl-replicate-gateinst
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-replicate-gateinst x nf mod ialist warnings)))))

  (defthm vl-gateinstlist-p-of-vl-replicate-gateinst
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-gateinstlist-p (mv-nth 1 (vl-replicate-gateinst x nf mod ialist warnings)))))

  (defthm vl-namefactory-p-of-vl-replicate-gateinst
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-namefactory-p (mv-nth 2 (vl-replicate-gateinst x nf mod ialist warnings))))))



(defsection vl-replicate-gateinstlist
  :parents (replicate)
  :short "Extend @(see vl-replicate-gateinst) across a @(see
vl-gateinstlist-p)."

  :long "<p><b>Signature</b>: @(call vl-replicate-gateinstlist) returns @('(mv
warnings new-gateinsts new-nf)').</p>

<p>@('new-gateinsts') is a list of new gates, which should replace @('x') in
the module.</p>"

  (defund vl-replicate-gateinstlist (x nf mod ialist warnings)
    "Returns (MV WARNINGS NEW-GATEINSTS NEW-NF)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-namefactory-p nf)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nf))
         ((mv warnings car-prime nf)
          (vl-replicate-gateinst (car x) nf mod ialist warnings))
         ((mv warnings cdr-prime nf)
          (vl-replicate-gateinstlist (cdr x) nf mod ialist warnings))
         (new-gateinsts (append car-prime cdr-prime)))
        (mv warnings new-gateinsts nf)))

  (defmvtypes vl-replicate-gateinstlist (nil true-listp nil))

  (local (in-theory (enable vl-replicate-gateinstlist)))

  (defthm vl-warninglist-p-of-vl-replicate-gateinstlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-replicate-gateinstlist x nf mod ialist warnings)))))

  (defthm vl-gateinstlist-p-of-vl-replicate-gateinstlist
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-gateinstlist-p (mv-nth 1 (vl-replicate-gateinstlist x nf mod ialist warnings)))))

  (defthm vl-namefactory-p-of-vl-replicate-gateinstlist
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-namefactory-p (mv-nth 2 (vl-replicate-gateinstlist x nf mod ialist warnings))))))




(defsection vl-plainarglists-to-arguments
  :parents (argument-partitioning)
  :short "Convert each plainarglist in a @(see vl-plainarglistlist-p) into an
@(see vl-argument-p)."

  (defund vl-plainarglists-to-arguments (x)
    (declare (xargs :guard (vl-plainarglistlist-p x)))
    (if (consp x)
        (cons (vl-arguments nil (car x))
              (vl-plainarglists-to-arguments (cdr x)))
      nil))

  (local (in-theory (enable vl-plainarglists-to-arguments)))

  (defthm vl-argumentlist-p-of-vl-plainarglists-to-arguments
    (implies (force (vl-plainarglistlist-p x))
             (vl-argumentlist-p (vl-plainarglists-to-arguments x))))

  (defthm len-of-vl-plainarglists-to-arguments
    (equal (len (vl-plainarglists-to-arguments x))
           (len x))))




(defsection vl-replicate-arguments
  :parents (replicate)
  :short "Partition arguments for a module instance"

  :long "<p><b>Signature:</b> @(call vl-replicate-arguments) returns @('(mv
successp warnings arg-lists)').</p>

<ul>

<li>@('args') is a single @(see vl-arguments-p) object, which should be the
@('portargs') from a @(see vl-modinst-p).  We expect that the arguments have
already been resolved, so that @('args') contains a plainarglist rather than
named arguments.</li>

<li>@('port-widths') are the widths from the corresponding ports, and we check
to ensure that there are as many @('port-widths') as there are arguments in
@('args').</li>

<li>@('insts') is the number of instances that we are splitting these arguments
into.</li>

<li>@('mod') is the module we are working in, and @('ialist') is its @(see
vl-moditem-alist).</li>

<li>@('elem') is a @(see vl-modelement-p) for better warnings, and
@('warnings') is an accumulator for warnings.</li>

</ul>

<p>The @('arg-lists') we produce is a @(see vl-argumentslist-p) of length
@('insts'), and contains the new arguments to use in the split up module
instances.</p>"

  (defund vl-replicate-arguments (args port-widths insts mod ialist elem warnings)
    "Returns (MV SUCCESSP WARNINGS ARG-LISTS)"
    (declare (xargs :guard (and (vl-arguments-p args)
                                (pos-listp port-widths)
                                (posp insts)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((namedp  (vl-arguments->namedp args))
         (actuals (vl-arguments->args args))

         ((when namedp)
          (b* ((w (make-vl-warning
                   :type :vl-bad-arguments
                   :msg "~a0: Expected only plain argument lists, but found ~
                         named args instead."
                   :args (list elem)
                   :fatalp t
                   :fn 'vl-replicate-arguments)))
            (mv nil (cons w warnings) nil)))

         ((unless (same-lengthp actuals port-widths))
          (b* ((w (make-vl-warning
                   :type :vl-bad-arguments
                   :msg "~a0: Expected ~x1 arguments but found ~x2."
                   :args (list elem (len port-widths) (len actuals))
                   :fatalp t
                   :fn 'vl-replicate-arguments)))
            (mv nil (cons w warnings) nil)))

         ;; Slice up the arguments...
         ((mv successp warnings slices)
          (vl-partition-plainarglist actuals port-widths insts mod ialist elem warnings))
         ((unless successp)
          ;; Already added warnings
          (mv nil warnings nil))

         ;; Transpose the matrix into slice-order
         (transpose (vl-reorient-partitioned-args slices insts))

         ;; Turn the plainarglists into vl-arguments-p structures
         (arg-lists (vl-plainarglists-to-arguments transpose)))
      (mv t warnings arg-lists)))

  (local (in-theory (enable vl-replicate-arguments)))

  (defthm vl-warninglist-p-of-vl-replicate-arguments
    (let ((ret (vl-replicate-arguments args port-widths insts mod ialist elem warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-argumentlist-p-of-vl-replicate-arguments
    (let ((ret (vl-replicate-arguments args port-widths insts mod ialist elem warnings)))
      (implies (and (force (vl-arguments-p args))
                    (force (pos-listp port-widths))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod)))
                    (force (posp insts)))
               (vl-argumentlist-p (mv-nth 2 ret)))))

  (defthm len-of-vl-replicate-arguments
    (let ((ret (vl-replicate-arguments args port-widths insts mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-arguments-p args))
                    (force (pos-listp port-widths))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod)))
                    (force (posp insts)))
               (equal (len (mv-nth 2 (vl-replicate-arguments args port-widths insts mod ialist elem warnings)))
                      insts)))))




(defsection vl-module-port-widths
  :parents (replicate)
  :short "Determine the widths of a module's ports."

  :long "<p><b>Signature:</b> @(call vl-module-port-widths) returns a @('(mv
successp warnings widths)'), where @('widths') is a list of positive
numbers.</p>

<ul>

<li>@('ports') are the module's ports.</li>

<li>@('inst') is the module instance that we are trying to replicate, and is
only used to generate more useful error messages.</li>

<li>@('warnings') is an ordinary @(see warnings) accumulator.</li>

</ul>

<p>We fail and cause fatal errors if any port is blank or does not have a
positive width.</p>"

  (defund vl-module-port-widths (ports inst warnings)
    (declare (xargs :guard (and (vl-portlist-p ports)
                                (vl-modinst-p inst)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom ports))
          (mv t warnings nil))

         (expr1  (vl-port->expr (car ports)))
         (width1 (and expr1 (vl-expr->finalwidth expr1)))
         ((unless (posp width1))
          (mv nil
              (cons (make-vl-warning
                     :type :vl-replicate-fail
                     :msg "~a0: width of ~a1 is ~x2; expected a positive ~
                           number."
                     :args (list inst (car ports)
                                 (and expr1 (vl-expr->finalwidth expr1)))
                     :fatalp t
                     :fn 'vl-module-port-widths)
                    warnings)
              nil))

         ((mv successp warnings cdr-sizes)
          (vl-module-port-widths (cdr ports) inst warnings))
         ((unless successp)
          (mv nil warnings nil)))

      (mv t warnings (cons width1 cdr-sizes))))

  (local (in-theory (enable vl-module-port-widths)))

  (defthm vl-warninglist-p-of-vl-module-port-widths
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-module-port-widths ports inst warnings)))))

  (defthm vl-module-port-widths-basics
    (let ((ret (vl-module-port-widths ports inst warnings)))
      (implies (mv-nth 0 ret)
               (and (pos-listp (mv-nth 2 ret))
                    (equal (len (mv-nth 2 ret)) (len ports)))))))




(defsection vl-assemble-modinsts
  :parents (replicate)
  :short "Build @(see vl-modinst-p)'s from the sliced-up arguments."

  :long "<p><b>Signature:</b> @(call vl-assemble-modinsts) returns a @(see
vl-modinstlist-p).</p>

<ul>

<li>@('names') are the names to give to the module instances.</li>

<li>@('args') are the sliced up arguments (see @(see
vl-replicate-arguments)).</li>

<li>The other arguments are taken from the original module instance that we are
slicing up.</li>

</ul>"

  (defund vl-assemble-modinsts (names args idx idxincr modname str delay paramargs atts loc)
    (declare (xargs :guard (and (string-listp names)
                                (vl-argumentlist-p args)
                                (same-lengthp names args)
                                (integerp idx)
                                (integerp idxincr)
                                (stringp modname)
                                (vl-maybe-gatestrength-p str)
                                (vl-maybe-gatedelay-p delay)
                                (vl-arguments-p paramargs)
                                (vl-atts-p atts)
                                (vl-location-p loc))))
    (if (atom args)
        nil
      (cons (make-vl-modinst :instname (car names)
                             :modname modname
                             :str str
                             :delay delay
                             :atts
                             (cons (cons "VL_REPLICATE_INDEX"
                                         (vl-make-index idx))
                                   atts)
                             :portargs (car args)
                             :paramargs paramargs
                             :loc loc)
            (vl-assemble-modinsts (cdr names) (cdr args) (+ idx idxincr) idxincr modname str delay paramargs atts loc))))

  (local (in-theory (enable vl-assemble-modinsts)))

  (defthm vl-modinstlist-p-of-vl-assemble-modinsts
    (implies (and (force (string-listp names))
                  (force (vl-argumentlist-p args))
                  (force (same-lengthp names args))
                  (force (stringp modname))
                  (force (vl-maybe-gatestrength-p str))
                  (force (vl-maybe-gatedelay-p delay))
                  (force (vl-arguments-p paramargs))
                  (force (vl-atts-p atts))
                  (force (vl-location-p loc)))
             (vl-modinstlist-p
              (vl-assemble-modinsts names args idx idxincr modname str delay
                                    paramargs atts loc)))
    :hints (("goal" :induct (vl-assemble-modinsts names args idx idxincr modname
                                                  str delay paramargs atts loc)
             :in-theory (e/d (string-listp)
                             (stringp-when-true-listp
                              vl-modinst-p-by-tag-when-vl-modelement-p
                              vl-string-p-by-tag-when-vl-atomguts-p
                              vl-location-p-when-wrong-tag))))))

(defsection vl-modinst-origname
  :parents (replicate)
  :short "Retrieve the original name of a module instance if it was modified by
the replicate transform."

  (defund vl-modinst-origname (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* (((vl-modinst x) x)
         (x.instname (mbe :logic (and (stringp x.instname)
                                      x.instname)
                          :exec x.instname))
         (look (assoc-equal "VL_REPLICATE_ORIGNAME" x.atts))
         ((when (not (cdr look))) x.instname)
         ((when (not (and (vl-atom-p (cdr look))
                          (vl-string-p (vl-atom->guts (cdr look))))))
          (er hard? 'vl-modinst-origname
              "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
          x.instname))
      (vl-string->value (vl-atom->guts (cdr look)))))

  (defthm vl-maybe-string-p-of-vl-modinst-origname
    (vl-maybe-string-p (vl-modinst-origname x))
    :hints(("Goal" :in-theory (enable vl-modinst-origname))))

  (defund vl-modinst-origidx (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* (((vl-modinst x) x)
         (look (assoc-equal "VL_REPLICATE_INDEX" x.atts))
         ((when (not (cdr look))) nil)
         ((when (not (vl-expr-resolved-p (cdr look))))
          (er hard? 'vl-modinst-origname
              "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
          nil))
      (vl-resolved->val (cdr look))))

  (defthm vl-maybe-natp-of-vl-modinst-origidx
    (vl-maybe-natp (vl-modinst-origidx x))
    :hints(("Goal" :in-theory (enable vl-modinst-origidx))))

  (defund vl-modinst-origname/idx (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* ((origname (vl-modinst-origname x))
         ((unless origname) nil)
         (origidx (vl-modinst-origidx x)))
      (if origidx
          (cat origname "[" (natstr origidx) "]")
        origname)))

  (defthm vl-maybe-string-p-of-vl-modinst-origname/idx
    (vl-maybe-string-p (vl-modinst-origname/idx x))
    :hints(("Goal" :in-theory (enable vl-modinst-origname/idx)))))

(defsection vl-gateinst-origname
  :parents (replicate)
  :short "Retrieve the original name of a module instance if it was modified by
the replicate transform."

  (defund vl-gateinst-origname (x)
    (declare (xargs :guard (vl-gateinst-p x)))
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

  (defthm vl-maybe-string-p-of-vl-gateinst-origname
    (vl-maybe-string-p (vl-gateinst-origname x))
    :hints(("Goal" :in-theory (enable vl-gateinst-origname))))


  (defund vl-gateinst-origidx (x)
    (declare (xargs :guard (vl-gateinst-p x)))
    (b* (((vl-gateinst x) x)
         (look (assoc-equal "VL_REPLICATE_INDEX" x.atts))
         ((when (not (cdr look))) nil)
         ((when (not (vl-expr-resolved-p (cdr look))))
          (er hard? 'vl-gateinst-origname
              "Malformed VL_REPLICATE_ORIGNAME attribute: ~x0~%" (cdr look))
          nil))
      (vl-resolved->val (cdr look))))

  (defthm vl-maybe-natp-of-vl-gateinst-origidx
    (vl-maybe-natp (vl-gateinst-origidx x))
    :hints(("Goal" :in-theory (enable vl-gateinst-origidx))))

  (defund vl-gateinst-origname/idx (x)
    (declare (xargs :guard (vl-gateinst-p x)))
    (b* ((origname (vl-gateinst-origname x))
         ((unless origname) nil)
         (origidx (vl-gateinst-origidx x)))
      (if origidx
          (cat origname "[" (natstr origidx) "]")
        origname)))

  (defthm vl-maybe-string-p-of-vl-gateinst-origname/idx
    (vl-maybe-string-p (vl-gateinst-origname/idx x))
    :hints(("Goal" :in-theory (enable vl-gateinst-origname/idx)))))

(defsection vl-replicate-modinst
  :parents (replicate)
  :short "Convert a module instance into a list of simpler instances, if
necessary."

  :long "<p><b>Signature:</b> @(call vl-replicate-modinst) returns @('(mv
warnings new-modinsts new-nf)').</p>

<ul>

<li>@('x') is some module instance, which may have a range that we want to
eliminate.</li>

<li>@('mods') and @('modalist') are the global list of modules and its
corresponding @(see vl-modalist) for fast module lookups; we need this to be
able to determine the sizes of ports when we are slicing arguments.</li>

<li>@('nf') is a @(see vl-namefactory-p) for generating fresh names.</li>

<li>@('warnings') is an accumulator for warnings.</li>

</ul>

<p>If @('x') has a range, i.e., it is an array of module instances, then we try
to split it into a list of @('nil')-ranged, simple instances.  The
@('new-modinsts') should replace @('x') in the module.</p>"

  (defund vl-replicate-modinst (x mods modalist nf mod ialist warnings)
    "Returns (MV WARNINGS NEW-MODINSTS NF-PRIME)"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-modulelist-p mods)
                                (equal (vl-modalist mods) modalist)
                                (vl-namefactory-p nf)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))))

    (b* (((vl-modinst x) x)

         ((unless x.range)
          ;; There isn't a range, so this is already an ordinary, non-array
          ;; instance.  We don't need to do anything, so return early.
          (mv warnings (list x) nf))

         ((unless (vl-range-resolved-p x.range))
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: instance array with unresolved range: ~a1."
                   :args (list x x.range)
                   :fatalp t
                   :fn 'vl-replicate-modinst)))
            (mv (cons w warnings) (list x) nf)))

         ((when (vl-arguments->args x.paramargs))
          ;; Probably unnecessary, but I don't really want to think about
          ;; parameters here.
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: instance array still has parameters?  This ~
                         should have been taken care of during ~
                         unparameterization."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-replicate-modinst)))
            (mv (cons w warnings) (list x) nf)))

         ;; We add an annotation saying that these instances are from an array.
         (x.atts (cons (list "VL_FROM_INST_ARRAY") x.atts))
         (size   (vl-range-size x.range))

         (target (vl-fast-find-module x.modname mods modalist))
         ((unless target)
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: instance of undefined module ~m1."
                   :args (list x x.modname)
                   :fatalp t
                   :fn 'vl-replicate-modinst)))
            (mv (cons w warnings) (list x) nf)))

         ((mv successp warnings port-widths)
          (vl-module-port-widths (vl-module->ports target) x warnings))
         ((unless successp)
          ;; Already added a warning.
          (mv warnings (list x) nf))

         ((mv successp warnings new-args)
          (vl-replicate-arguments x.portargs port-widths size mod ialist x warnings))
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

      (mv warnings new-modinsts nf)))

  (defmvtypes vl-replicate-modinst (nil true-listp nil))

  (local (in-theory (enable vl-replicate-modinst)))

  (defthm vl-warninglist-p-of-vl-replicate-modinst
    (let ((ret (vl-replicate-modinst x mods modalist nf mod ialist warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 ret)))))

  (defthm vl-modinstlist-p-of-vl-replicate-modinst
    (let ((ret (vl-replicate-modinst x mods modalist nf mod ialist warnings)))
      (implies (and (force (vl-modinst-p x))
                    (force (vl-modulelist-p mods))
                    (force (equal (vl-modalist mods) modalist))
                    (force (vl-namefactory-p nf))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-modinstlist-p (mv-nth 1 ret)))))

  (defthm vl-namefactory-p-of-vl-replicate-modinst
    (let ((ret (vl-replicate-modinst x mods modalist nf mod ialist warnings)))
      (implies (and (force (vl-modinst-p x))
                    (force (vl-modulelist-p mods))
                    (force (equal (vl-modalist mods) modalist))
                    (force (vl-namefactory-p nf))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-namefactory-p (mv-nth 2 ret))))))



(defsection vl-replicate-modinstlist
  :parents (replicate)
  :short "Extend @(see vl-replicate-modinst) across a @(see vl-modinstlist-p)"

  :long "<p><b>Signature:</b> @(call vl-replicate-modinstlist) returns @('(mv
warnings x-prime nf-prime)').</p>"

  (defund vl-replicate-modinstlist (x mods modalist nf mod ialist warnings)
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-modulelist-p mods)
                                (equal (vl-modalist mods) modalist)
                                (vl-namefactory-p nf)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nf))
         ((mv warnings car-insts nf)
          (vl-replicate-modinst (car x) mods modalist nf mod ialist warnings))
         ((mv warnings cdr-insts nf)
          (vl-replicate-modinstlist (cdr x) mods modalist nf mod ialist warnings)))
        (mv warnings (append car-insts cdr-insts) nf)))

  (defmvtypes vl-replicate-modinstlist (nil true-listp nil))

  (local (in-theory (enable vl-replicate-modinstlist)))

  (defthm vl-warninglist-p-of-vl-replicate-modinstlist
    (let ((ret (vl-replicate-modinstlist x mods modalist nf mod ialist warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 ret)))))

  (defthm vl-modinstlist-p-of-vl-replicate-modinstlist
    (let ((ret (vl-replicate-modinstlist x mods modalist nf mod ialist warnings)))
      (implies (and (force (vl-modinstlist-p x))
                    (force (vl-modulelist-p mods))
                    (force (equal (vl-modalist mods) modalist))
                    (force (vl-namefactory-p nf))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-modinstlist-p (mv-nth 1 ret)))))

  (defthm vl-namefactory-p-of-vl-replicate-modinstlist
    (let ((ret (vl-replicate-modinstlist x mods modalist nf mod ialist warnings)))
      (implies (and (force (vl-modinstlist-p x))
                    (force (vl-modulelist-p mods))
                    (force (equal (vl-modalist mods) modalist))
                    (force (vl-namefactory-p nf))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-namefactory-p (mv-nth 2 ret))))))



(defund vl-some-gateinst-array-p (x)
  (declare (xargs :guard (vl-gateinstlist-p x)))
  (cond ((atom x)
         nil)
        ((vl-gateinst->range (car x))
         t)
        (t
         (vl-some-gateinst-array-p (cdr x)))))

(defund vl-some-modinst-array-p (x)
  (declare (xargs :guard (vl-modinstlist-p x)))
  (cond ((atom x)
         nil)
        ((vl-modinst->range (car x))
         t)
        (t
         (vl-some-modinst-array-p (cdr x)))))

(defsection vl-module-replicate
  :parents (replicate)
  :short "Eliminate gate and module instance arrays from a module."

  :long "<p><b>Signature:</b> @(call vl-module-replicate) returns an updated
module.</p>

<p>@('x') is the module to alter, @('mods') is the global list of modules, and
@('modalist') is the @(see vl-modalist) for @('mods') for fast lookups.  We
produce a new version of @('x') by eliminating any gate or module instance
arrays, and replacing them with explicit lists of instances.</p>"

  (defund vl-module-replicate (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((when (vl-module->hands-offp x))
          x)

         ((vl-module x) x)

         ((unless (or (vl-some-gateinst-array-p x.gateinsts)
                      (vl-some-modinst-array-p x.modinsts)))
          ;; Optimization.  Avoid constructing ialist, etc., when there aren't
          ;; any arrays to replicate anyway.
          x)

         (nf         (vl-starting-namefactory x))
         (ialist     (vl-moditem-alist x))

         (warnings   x.warnings)

         ((mv warnings new-gateinsts nf)
          (vl-replicate-gateinstlist x.gateinsts nf x ialist warnings))

         ((mv warnings new-modinsts nf)
          (vl-replicate-modinstlist x.modinsts mods modalist nf x ialist warnings))

         (- (vl-free-namefactory nf))
         (- (fast-alist-free ialist))

         (x-prime (change-vl-module x
                                    :modinsts new-modinsts
                                    :gateinsts new-gateinsts
                                    :warnings warnings)))
        x-prime))

  (local (in-theory (enable vl-module-replicate)))

  (defthm vl-module-p-of-vl-module-replicate
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (vl-module-replicate x mods modalist))))

  (defthm vl-module->name-of-vl-module-replicate
    (equal (vl-module->name (vl-module-replicate x mods modalist))
           (vl-module->name x))))


(defprojection vl-modulelist-replicate-aux (x mods modalist)
  (vl-module-replicate x mods modalist)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :result-type vl-modulelist-p
  :parents (replicate)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-replicate-aux
     (equal (vl-modulelist->names (vl-modulelist-replicate-aux x mods modalist))
            (vl-modulelist->names x)))))


(defsection vl-modulelist-replicate
  :parents (replicate)
  :short "Extend @(see vl-module-replicate) across the list of modules."

  (defund vl-modulelist-replicate (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (result   (vl-modulelist-replicate-aux x x modalist))
         (-        (flush-hons-get-hash-table-link modalist)))
        result))

  (local (in-theory (enable vl-modulelist-replicate)))

  (defthm vl-modulelist-p-of-vl-modulelist-replicate
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-replicate x))))

  (defthm vl-modulelist->names-of-vl-modulelist-replicate
    (equal (vl-modulelist->names (vl-modulelist-replicate x))
           (vl-modulelist->names x))))

