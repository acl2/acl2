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
(include-book "../mlib/range-tools")
(include-book "../util/sum-nats")
(include-book "../mlib/context")
(include-book "../mlib/welltyped")
(include-book "../mlib/lvalues")
(local (include-book "clause-processors/autohide" :dir :system))
(local (include-book "../util/arithmetic"))


(defxdoc expression-sizing
  :parents (transforms)
  :short "Calculate the widths and types of expressions."

  :long "<p>Expression sizing and typing is <b>possibly the most complex,
error-prone, and subtle aspect</b> of processing Verilog expressions.  One
reason for this is that the size and signedness of subexpressions depends upon
the other terms in the expressions that contain them.  For instance, the result
of @('((4'd14 + 4'd3) >> 4'd1)') might be either 8 or 0, depending on where it
is being used.  Another reason is just how elaborate the rules for sizing are,
and how many corner cases there are.</p>

<p>These issues mean that great care must be taken even when writing
simple-looking reductions like constant folding.  Moreover, you really need to
understand how sizing works if you are going to safely write any code that
generates Verilog expressions.</p>

<p>I have put together a gentle @(see expression-sizing-intro) which describes
Verilog's basic algorithm for how sizes and types are determined.  You may also
wish to familiarize yourself with the VL notion of <see topic=\"@(url
vl-expr-welltyped-p)\">well-typed</see> expressions.</p>

<p>The expression-sizing transformation attempts to determine expression sizes
and types throughout a module.  Prerequisite transformations:</p>

<ul>
 <li>@(see portdecl-sign), so we get can signedness right,</li>
 <li>@(see unparameterization), so there are no paramterized widths, and</li>
 <li>@(see rangeresolve), so the ranges of wires and selects have been
     determined.</li>
</ul>

<p>BOZO follow-hids might also be a prerequisite when we add support for
HIDs.</p>

<p>It is valid to run this transformation any time after the above transforms
have been run.  It is also \"idempotent,\" so it is perfectly valid to run the
transform more than once on the same module (e.g., perhaps your subsequent
transformation wishes to add some assignment statements, and subsequently wants
to determine their sizes.</p>")


(defxdoc expression-sizing-intro
  :parents (expression-sizing)
  :short "Introduction to Verilog's expression sizing/typing algorithm."

  :long "<p>Sizing expressions in Verilog is a <b>two-phase process</b>.</p>

<ol>

<li>We inspect the expression to determine what final size and signedness it
should have.  To a first approximation: the final size of the expression will
be the maximum size of any of its operands, and the final signedness will be
unsigned unless all operands are signed.  But the real story involves many
operand-specific rules and corner cases.</li>

<li>We then \"propagate\" the final size and signedness down to the operands.
Approximately true: if the final signedness is signed, then we globally
sign-extend every operand to the final width; if the final signedness is
unsigned, we instead always zero-extend the operands.  After this extension,
the operands all agree on a size, and the inputs to operators like @('+') will
have the same width, and the output of the operator will also have this same
width.  But again, the real story has many rules and corner cases to
cover.</li>

</ol>

<p><b>Stop!</b> Carefully read the above steps again.  Understanding the two
phases is a critical first step to making any sense of the rules.</p>

<p>Let us now begin making these steps more precise.</p>

<h4>Final-Size Computation</h4>

<p>First, the claim that \"final size of the expression is the maximum size of
any of its operands\" is basically true for expressions like @('a + b').  But
it is completely wrong for, e.g., @('|foo') or @('foo == bar'), which basically
produce one-bit wide answers.  Another example is concatenations like @('{foo,
bar}') where the width should be the sum of its arguments widths.</p>

<p>The actual rules for computing the final width of an expression are given in
Table 5-22 of the Verilog spec, which we now reproduce: </p>

@({
 Expression                     Bit Length         Notes
 -----------------------------------------------------------------------------
 Unsized constants              \"Same as integer\"  (see ** below)
 Sized constants                As given
 i [+ - * / % & | ^ ^~ ~^] j    max{L(i),L(j)}
 [+ - ~] i                      L(i)
 i [=== !== == != > >= < <=] j  1 bit              i,j sized to max(L(i),L(j))
 i [&& ||] j                    1 bit              i,j self-determined
 [& ~& | ~| ^ ~^ ^~ !] i        1 bit              i self-determined
 i [>> << ** >>> <<<] j         L(i)               j self-determined
 i ? j : k                      max(L(j),L(k))     i self-determined
 {i, ..., j}                    L(i)+...+L(j)      all self-determined
 {i {j, ..., k}}                i*(L(j)+...+L(k))  all self-determined
 -----------------------------------------------------------------------------
})

<p>(**) What does \"same as integer\" mean?  From Section 4.8: Verilog
implementations may limit the size of integer variables.  The limit must be at
least 32 bits, but is not otherwise unconstrained.  Hence, expressions
involving unsized constants may have implementation-dependent sizes (and can in
fact have implementation-dependent results).</p>

<p>VL acts like a 32-bit implementation, so effectively any unsized constant is
treated as if it has size 32.  I historically tried to directly support
abstract \"integer-sized\" expressions so that we could warn about expressions
whose behavior might be implementation-dependent.  But I eventually decided
that this approach overly complicated the sizing code.  Today, the VL @(see
lexer) automatically treats unsized constants as if they were 32 bits so the
whole matter of \"how large is integer-size?\" is effectively settle a priori.
But the lexer also marks any unsized constants with the @(':wasunsized')
property, which allows us to still carry out this compatibility checking.</p>

<p>At any rate, the \"bit length\" column in the above table gives an almost
full story about how to determine the finalwidth of an expression.  But as a
final twist, when assignment statements are sized, the bit-length of the
left-hand side of the assignment also plays a role in the finalwidth
computation.  Essentially, the finalwidth of @('rhs') in @('assign lhs = rhs')
is @('max{L(lhs), L(rhs)}').</p>

<p>Our main function for computing the desired finalwidth of an expression is
@(see vl-expr-selfsize).</p>


<h4>Signedness Computation</h4>

<p>The above claim that \"the final signedness will be unsigned unless all
operands are signed\" is basically true for expressions like @('a + b').  For
instance, if the full expression is @('(3 + 4) + 0'), then its final signedness
is signed because all of its operands are signed.  On the other hand, if we
change this to @('(3 + 4) + 1'b0'), then the final signedness is unsigned
because @('1'b0') is unsigned.</p>

<p>The Verilog rules for signedness are covered in Section 5.5.1 and 5.5.4.
We summarize these rules here:</p>

<ul>

<li>Constants are either signed or unsigned depending upon how they are written
in the source code, e.g., plain numbers like @('5') are signed, and otherwise
the signedness is controlled by the base specifier, e.g., @('10'b0') is
unsigned but @('10'sb0') is signed.  (All of this is handled by our @(see
lexer) and built into the @(':origtype') field of our @(see vl-constint-p) and
@(see vl-weirdint-p) atomguts.)</li>

<li>Bit-selects, part-selects, concatenations (and presumably multiple
concatenations), and comparison results (e.g., from @('a == b')) are always
unsigned.</li>

<li>Reals converted to integers are signed (but we don't handle reals, so
this doesn't affect us).</li>

<li>The signedness of self-determined subexpressions is determined by the
subexpression itself, and doesn't depend on any other terms from the
expression, e.g., @('{ 3, 1'b0 }') is a concatenation with one signed and one
unsigned subexpression.</li>

<li>For nonself-determined operands, if any operand is real the result is real;
if any operand is unsigned the result is unsigned; otherwise all operands are
signed and the result is \"signed, regardless of operator, except when
specified otherwise.\" (This is particularly unclear).</li>

</ul>

<p>Another rule is found in 5.1.12, which says the right-hand side of a shift
is always treated as unsigned.</p>

<p>Some additional technical questions and investigations may be found in @(see
expression-sizing-minutia).</p>

<p>In VL, our main function for computing the final signedness of an expression
is @(see vl-expr-typedecide).</p>

<h4>Propagating the Context</h4>

<p>BOZO document this.</p>")


(defxdoc expression-sizing-minutia
  :parents (expression-sizing)
  :short "Specific issues and questions related to the expression sizing and
typing of expressions."

  :long "<p>There are several ways in which the spec seems unclear or seems to
contradict what Verilog implementations do.</p>

<h2>Q1.  Does a self-determined operand affect the types of the expressions in
which it is involved?</h2>

<p>I ask this question only about the shifting operators, power operator, and
conditional operators; the other operators that have self-determined operands
are: concatenation and multiple-concatenation operators (which are
unambiguously defined to be unsigned in 5.5.1), and logical/reduction
operations which are discussed below in Q2.</p>

<p>What does the spec say?  In 5.5.1, we are told <em>The sign and size of any
self-determined operand are determined by the operand itself and independent of
the remainder of the expression.</em>.  From this, and from the discussion of
what it means to be a self-determined expression in 5.4.1, I think it is clear
that we are supposed to compute the size/type of the subexpression without
considering the sizes and types of other operands in the containing expression.
But what is <b>not</b> clear is: does the resulting size and type of the
subexpression have any bearing on the width/type of the containing
expression?</p>

<p>The width question is unambiguously answered \"no\" in all cases by Table
5-22.  The type question is unambiguously answered \"no\" by for shift
operators in Section 5.1.12, where we are told <em>the right operand is always
treated as an unsigned number and has no effect on the signedness of the
result.</em> But the type question is not addressed in 5.1.13 for the
conditional operator, and while there is some discussion in 5.1.5 about the
type of a power operator when its operands are real, the section just refers us
to 5.4.1 and 5.5.1 for the integer cases.</p>

<p>Well, 5.4.1 doesn't really say anything about types, except that it contains
Table 5-22 that says which operands are self-determined, and 5.5.1 is back
where we started.  So the only things we have to go on for the conditional
operator and power operator are:</p>

<ul>

<li><b>R1.</b> The sign and size of any self-determined operand are determined by the operand
itself and independent of the remainder of the expression.</li>

<li><b>R2.</b> For nonself-determined operands, the following rules apply:
<ul>
 <li>If any operand is real, the result is real</li>
 <li>If any operand is unsigned, the result is unsigned, regardless of the
     operator</li>
 <li>If all operands are signed, the result will be signed, regardless of operator,
     except when specified otherwise.</li>
</ul></li>

</ul>

<p>We have already looked at the R1---indeed, we're trying to figure out just
what it means by <em>independent</em>.  So, we are left with R2, which
<em>almost</em> seems to provide a clear answer.  In particular, if <em>any
operand</em> really means <em>any</em> operand then it is clear that we should
include the types of these self-determined operands really do affect the results.</p>

<p>But there is this damn header, <em>For nonself-determined operands</em>,
which suggests this maybe <em>any operand</em> here only refers to any
nonself-determined operand.  And if this is the case, then we still have no
idea what we are supposed to do with conditional and power operations, which
have a mixture of self and nonself-determined operands.</p>

<p>We conclude that the spec is ambiguous and revert to testing with other
Verilog implementations to see what they seem to do.</p>

<h4>Conditional Operator</h4>

<p>Verilog-XL and NCVerilog agree that the answer for both of the following
expressions are @('1111101').  This can only happen if the branch operands are
being sign-extended.  Hence, it seems that these implementations treat the sign
of the condition as irrelevant to the result type.</p>

@({
wire [6:0] y0 = 1'b0 ? 3'sb 100 : 3'sb 101;
wire [6:0] y1 = 1'sb0 ? 3'sb 100 : 3'sb 101;
})

<h4>Power Operator</h4>

<p>Unfortunately Verilog-XL does not seem to support the power operator, so we
only are able to test with NCVerilog.  NCVerilog reports 1984 (-64) as the
result for both of the following,</p>

@({
wire [10:0] p2 = (3'sb100 ** 2'b11);
wire [10:0] p3 = (3'sb100 ** 2'sb11);
})

<p>Hence it seems that the type of the exponent is not relevant to the result
type.  If it were, then in p2 we would have to zero-extend the base to 4,
rather than sign-extend it to -4, and the result for p2 would be 64 instead of
1984.</p>

<h4>Shift Operators</h4>

<p>For good measure we also tried a shift-operator, even though we think the
spec is clear here.</p>

@({
wire [4:0] v1 = 1'sd 1 >> 1'b0;
})

<p>Here, ignoring the sign of the right-hand side would produce @('11111'),
since the left-hand side would be sign-extended to 5 bits and then unchanged by
the shift.  On the other hand, if we allow the right-hand side to play a role,
then the result is unsigned and we would zero-extend the left-hand side
instead, producing a final result of 1.  Both Verilog-XL and NCVerilog get
@('11111'), which we think is correct.</p>

<h4>Conclusions</h4>

<p>The implementations seem to agree that the types of these operands should
not matter.  Since we think the spec is vague and does not say one way or
another, we mimick their behavior.  However, we also issue warnings when we
encounter one of these operands with an unsigned self-determined operand and
signed nonself-determined operands, since this is a case that other
implementations might be confused about.  See @(see vl-expr-typedecide-aux) for
details.</p>


<h3>Q2.  What is the type of a reduction or logical operation?</h3>

<p>The ambiguity in Q1 is also a problem for:</p>
<ul>

<li>the logical operators (@('&&'), @('||'), and @('!')) and</li>

<li>the reduction operators (@('&'), @('~&'), @('|'), @('~|'), @('^'), @('~^'),
and @('^~')).</li>

</ul>

<p>In these cases, there are no nonself-determined operators that R2 might
allow us to use to get an answer.  5.1.11 (reduction operators) doesn't provide
any help, and neither does 5.1.9 (logical operators).  So, we are again reduced
to testing.  Here are some simple cases:</p>

@({
wire [4:0] q0 = | 17;
wire [4:0] q1 = ! 3'sd 0;
wire [4:0] q2 = & 5'sb11111;
wire [4:0] q3 = 3 && 5;
})

<p>In Verilog-XL and NCVerilog, all of these expressions produce @('00001'),
meaning that in each case they are being zero-extended instead of sign
extended.  This is somewhat further evidence that R2 is not supposed to apply
to self-determined operands.</p>

<p>Some internet searching revealed <a
href=\"http://www.eda.org/svdb/bug_view_page.php?bug_id=0001072\">Issue
1072</a> at the EDA.org \"mantis\" site, which seems to suggests that the spec
is wrong and should say reduction operators and logical operators produce
unsigned 1-bit values.</p>

<p>We therefore treat these as unsigned 1-bit values, but we take special care
to generate warnings if this treatment affects the final signedness of an
expression.  See @(see vl-expr-typedecide) for details.</p>


<h3>Q3.  What does shifting by a negative number mean?</h3>

<p>This question is silly because it seems that the Verilog specification
somewhat clearly says in 5.1.12 that <em>the right operand is always treated as
an unsigned number</em>.</p>

<p>Unfortunately, Verilog-XL and NCVerilog produce different results for:</p>

@({
wire [9:0] v0 = 10'b 0000_11_0000 >> ( 2'sd 0 + 1'sd 1 );
})

<p>In Verilog-XL, the answer is @('0001_10_0000'), i.e., the result appears to
have been left-shifted by one place; in NCVerilog, the answer is
@('0000_00_0110'), i.e., the result appears to have been right-shifted by 3
places.</p>

<p>In both cases, the right-hand side seems to indeed be self-determined and
yields 2'sd 3.  And, since we are supposed to \"treat the right-hand side as an
unsigned number,\" it seems like we should shift the left-hand side by 3 places
to the right like NCVerilog.</p>

<p>I found some discussion from the IEEE 1364 Behavioral Task Force Mailing
List Archives, specifically a <a
href=\"http://www.boydtechinc.com/btf/archive/btf_1999/0642.html\">signed shift
errata?</a> thread started by Stuart Sutherland on Monday, July 19, 1999, the
followup to which suggests that Verilog-XL is in the wrong and that this is one
area where NCVerilog was designed to match the standard instead of
Verilog-XL.</p>

<p>We follow NCVerilog's behavior, but issue a warning if we see a signed
right-hand side (unless it is a signed constant whose sign-bit is zero) so that
the difference does not matter.  See @(see vl-expr-typedecide-aux) for
details.</p>")



; -----------------------------------------------------------------------------
;
;                       DETERMINATION OF FINAL SIZES
;
; -----------------------------------------------------------------------------

(defsection vl-atom-selfsize
  :parents (vl-expr-selfsize)
  :short "Compute the self-determined size of an atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-atom-selfsize) returns @('(mv warnings
size)')</p>

<p>We attempt to compute the \"self-determined size\" of the atom @('x').
Another way to look at this function is as an extension of \"origwidth\" from
constint/weirdint atoms to include identifiers.</p>

<p>We have taken special care in our @(see lexer) to ensure that every
constant, whether it is a @(see vl-weirdint-p) or @(see vl-constint-p), has a
determined width.  As a result, it is easy to determine the self-determined
size of a constant, and we never fail to do so.</p>

<p>For identifiers, we must look up the identifier in the module to try to
determine its size.  This can fail if the identifier is not declared in the
module, or if its size is not resolved.  In these cases, we add a fatal warning
to @('warnings') and return @('nil') as the size.</p>

<p>We do not try to size other atoms, such as strings, real numbers, individual
HID pieces, function names, etc.; instead we just return @('nil') as the size.
But we do not issue a warning in this case, because it seems like these things
are not really supposed to have sizes.</p>"

  (defund vl-atom-selfsize (x mod ialist elem warnings)
    "Returns (MV WARNINGS SIZE)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))

         ((when (vl-fast-constint-p guts))
          (mv warnings (vl-constint->origwidth guts)))

         ((when (vl-fast-weirdint-p guts))
          (mv warnings (vl-weirdint->origwidth guts)))

         ((when (vl-fast-string-p guts))
          (mv warnings (* 8 (length (vl-string->value guts)))))

         ((unless (vl-fast-id-p guts))
          ;; Reals, function names, hierarchical identifier pieces, etc., for which
          ;; a size is not applicable.
          (mv warnings nil))

         (name (vl-id->name guts))
         (item (vl-fast-find-moduleitem name mod ialist))

         ((unless item)
          ;; Shouldn't happen if the module is well-formed and all used names
          ;; are declared.
          (b* ((w (make-vl-warning
                   :type :vl-bad-identifier
                   :msg "~a0: cannot size ~w1 because it is not declared."
                   :args (list elem name)
                   :fatalp t
                   :fn 'vl-atom-selfsize)))
            (mv (cons w warnings) nil)))

         ((when (mbe :logic (or (vl-netdecl-p item)
                                (vl-regdecl-p item))
                     :exec (or (eq (tag item) :vl-netdecl)
                               (eq (tag item) :vl-regdecl))))
          (b* (((mv arrdims range)
                (if (eq (tag item) :vl-netdecl)
                    (mv (vl-netdecl->arrdims item) (vl-netdecl->range item))
                  (mv (vl-regdecl->arrdims item) (vl-regdecl->range item))))
               ((when (consp arrdims))
                ;; Shouldn't happen unless the module directly uses the name of
                ;; an array in an expression; if we've properly converted
                ;; bitselects to array-references, our expression-sizing code
                ;; should not try to size its name.
                (b* ((w (make-vl-warning
                         :type :vl-bad-identifier
                         :msg "~a0: cannot size w1 because it is an array."
                         :args (list elem name)
                         :fatalp t
                         :fn 'vl-atom-selfsize)))
                  (mv (cons w warnings) nil)))
               ((unless (vl-maybe-range-resolved-p range))
                ;; Shouldn't happen unless we had a problem resolving ranges
                ;; earlier.
                (b* ((w (make-vl-warning
                         :type :vl-bad-range
                         :msg "~a0: cannot size ~w1 because its range is not ~
                               resolved: ~a2."
                         :args (list elem name range)
                         :fatalp t
                         :fn 'vl-atom-selfsize)))
                  (mv (cons w warnings) nil)))
               (size (vl-maybe-range-size range)))
            (mv warnings size)))

         ((when (and (mbe :logic (vl-vardecl-p item)
                          :exec (eq (tag item) :vl-vardecl))))
          (b* (((unless (eq (vl-vardecl->type item) :vl-integer))
                ;; We don't try to size real, realtime, or time variables.
                (mv warnings nil))
               ((when (consp (vl-vardecl->arrdims item)))
                ;; Analogous to the netdecl/regdecl array case.
                (b* ((w (make-vl-warning
                         :type :vl-bad-identifier
                         :msg "~a0: cannot size ~w1 because it is an array."
                         :args (list elem name)
                         :fatalp t
                         :fn 'vl-atom-selfsize)))
                  (mv (cons w warnings) nil))))
            ;; Regular integer variables just have size 32.
            (mv warnings 32)))

         ;; It would be surprising if we get here -- this is an identifier that
         ;; refers to something in the module, maybe an event, parameter, or
         ;; instance?  It seems like we shouldn't hit this case unless the
         ;; module contains something really strange.
         (w (make-vl-warning
             :type :vl-bad-identifier
             :msg "~a0: cannot size ~w1 because it is a ~x2; we expected to ~
                   only need to size nets, registers, and variables."
             :args (list elem name (tag item))
             :fatalp t
             :fn 'vl-atom-selfsize)))
      (mv (cons w warnings) nil)))

  (local (in-theory (enable vl-atom-selfsize)))

  (defthm vl-warninglist-p-of-vl-atom-selfsize
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-atom-selfsize x mod ialist elem warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm maybe-natp-of-vl-atom-selfsize
    (maybe-natp (mv-nth 1 (vl-atom-selfsize x mod ialist elem warnings)))
    :rule-classes ((:type-prescription)))

  (defthm warning-irrelevance-of-vl-atom-selfsize
    (let ((ret1 (vl-atom-selfsize x mod ialist elem warnings))
          (ret2 (vl-atom-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))





(defsection vl-syscall-selfsize
  :parents (vl-expr-selfsize)
  :short "Compute the self-determined size of an system call."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>This might as well have been part of @(see vl-op-selfsize).  I decided to
separate it out so that it can be more easily managed if it grows into a
complex function.  At the moment we only support @('$random').</p>

<h3>$random</h3>

<p>From Section 17.9.1 on page 311, <i>\"The system function
@('$random')... returns a new 32-bit random number each time it is called.  The
random number is a signed integer; it can be positive or negative...</i> This
is rather vague, but I think it probably means two separate things.  First,
that the values produced by @('$random') are in the range @('[-2^31, 2^31)').
Second, that the \"return type\" of @('$random') is @('integer'), which of
course has an implementation-dependent size which some implementation might
treat as 64-bits.  But since we emulate a 32-bit implementation, we just regard
the size of @('$random') as 32.</p>"

  (defund vl-syscall-selfsize (args arg-sizes context elem warnings)
    "Returns (MV WARNINGS SIZE)"
    (declare (xargs :guard (and (vl-exprlist-p args)
                                (nat-listp arg-sizes)
                                (same-lengthp args arg-sizes)
                                (vl-expr-p context)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings)))
             (ignorable arg-sizes context elem))
    (b* ((expr (make-vl-nonatom :op :vl-syscall :args args))
         ((when (vl-$random-expr-p expr))
          (mv warnings 32)))
      (mv warnings nil)))

  (local (in-theory (enable vl-syscall-selfsize)))

  (defthm vl-warninglist-p-of-vl-syscall-selfsize
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-syscall-selfsize args arg-sizes context elem warnings)))))

  (defthm maybe-natp-of-vl-syscall-selfsize
    (maybe-natp
     (mv-nth 1 (vl-syscall-selfsize args arg-sizes context elem warnings)))
    :rule-classes ((:type-prescription)))

  (defthm warning-irrelevance-of-vl-syscall-selfsize
    (let ((ret1 (vl-syscall-selfsize args arg-sizes context elem warnings))
          (ret2 (vl-syscall-selfsize args arg-sizes context elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))





(defsection vl-expr-interesting-size-atoms

; This is used to tweak fussy size warnings.  See below.
;
; Our basic goal is to gather all the atoms throughout an expression that are
; sort of meaningful to the current self-size computation.  Obviously you
; should never use this for anything semantically meaningful, it's only meant
; as a heuristic for warning generation.

  (mutual-recursion

   (defund vl-expr-interesting-size-atoms (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (b* (((when (vl-fast-atom-p x))
           (list x))
          (op (vl-nonatom->op x))
          (args (vl-nonatom->args x)))
       (case op
         ((:vl-bitselect :vl-unary-bitand :vl-unary-nand :vl-unary-bitor
                         :vl-unary-nor :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
                         :vl-binary-logand :vl-binary-logor
                         :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
                         :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
                         :vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
                         :vl-syscall :vl-funcall :vl-mintypmax :vl-hid-dot :vl-hid-arraydot
                         :vl-array-index)
          ;; Don't gather anything from here.
          nil)

         ((:vl-binary-power
           :vl-unary-plus :vl-unary-minus :vl-unary-bitnot
           :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
          ;; Second arg doesn't affect selfsize
          (vl-expr-interesting-size-atoms (first args)))

         ((:vl-qmark :vl-multiconcat)
          ;; First arg is special, don't consider it
          (vl-exprlist-interesting-size-atoms (cdr args)))

         ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
                           :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor
                           :vl-concat)
          ;; All args affect size
          (vl-exprlist-interesting-size-atoms args))

         (otherwise
          ;; To make us account for all ops
          (er hard 'vl-expr-interesting-size-atoms
              "Impossible")))))

   (defund vl-exprlist-interesting-size-atoms (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (append (vl-expr-interesting-size-atoms (car x))
                 (vl-exprlist-interesting-size-atoms (cdr x)))
       nil)))

  (defthm true-listp-of-vl-expr-interesting-size-atoms
    (true-listp (vl-expr-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-interesting-size-atoms
    (true-listp (vl-exprlist-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (FLAG::make-flag vl-flag-expr-interesting-size-atoms
                   vl-expr-interesting-size-atoms
                   :flag-mapping ((vl-expr-interesting-size-atoms . expr)
                                  (vl-exprlist-interesting-size-atoms . list)))

  (verify-guards vl-expr-interesting-size-atoms
    :hints(("Goal"
            :use ((:instance return-type-of-vl-nonatom->op (x x)))
            :in-theory (e/d (vl-op-p vl-op-arity)
                            (return-type-of-vl-nonatom->op)))))

  (defthm-vl-flag-expr-interesting-size-atoms
    (defthm vl-atomlist-p-of-vl-expr-interesting-size-atoms
      (implies (force (vl-expr-p x))
               (vl-atomlist-p (vl-expr-interesting-size-atoms x)))
      :flag expr)
    (defthm vl-atomlist-p-of-vl-exprlist-interesting-size-atoms
      (implies (force (vl-exprlist-p x))
               (vl-atomlist-p (vl-exprlist-interesting-size-atoms x)))
      :flag list)
    :hints(("Goal"
            :expand ((vl-expr-interesting-size-atoms x)
                     (vl-exprlist-interesting-size-atoms x)))))

  (defthm-vl-flag-expr-interesting-size-atoms
    (defthm vl-exprlist-p-of-vl-expr-interesting-size-atoms
      (implies (force (vl-expr-p x))
               (vl-exprlist-p (vl-expr-interesting-size-atoms x)))
      :flag expr)
    (defthm vl-exprlist-p-of-vl-exprlist-interesting-size-atoms
      (implies (force (vl-exprlist-p x))
               (vl-exprlist-p (vl-exprlist-interesting-size-atoms x)))
      :flag list)
    :hints(("Goal"
            :expand ((vl-expr-interesting-size-atoms x)
                     (vl-exprlist-interesting-size-atoms x))))))



(defsection vl-collect-unsized-ints

  (defund vl-collect-unsized-ints (x)
    (declare (xargs :guard (vl-exprlist-p x)))
    (cond ((atom x)
           nil)
          ((and (vl-fast-atom-p (car x))
                (vl-fast-constint-p (vl-atom->guts (car x)))
                (vl-constint->wasunsized (vl-atom->guts (car x))))
           (cons (car x) (vl-collect-unsized-ints (cdr x))))
          (t
           (vl-collect-unsized-ints (cdr x)))))

  (defthm vl-exprlist-p-of-vl-collect-unsized-ints
    (implies (vl-exprlist-p x)
             (vl-exprlist-p (vl-collect-unsized-ints x)))
    :hints(("Goal" :in-theory (enable vl-collect-unsized-ints))))

  (defthm vl-exprlist-resolved-p-of-vl-collect-unsized-ints
    (implies (vl-exprlist-p x)
             (vl-exprlist-resolved-p (vl-collect-unsized-ints x)))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p vl-collect-unsized-ints)))))


(defund nats-below-p (max x)
  (declare (xargs :guard (and (natp max)
                              (nat-listp x))))
  (if (atom x)
      t
    (and (< (car x) max)
         (nats-below-p max (cdr x)))))



(defsection vl-tweak-fussy-warning-type

; This function is called when we've just noticed that A and B have different
; self-sizes but are used in an expression like A == B, A & B, C ? A : B, or
; similar, and hence one or the other is going to be implicitly extended.
; We're going to issue a fussy size warning, and we want to decide what type to
; give it.  I.e., is this a minor warning, or a normal warning?
;
; Here, ASIZE and BSIZE are just the self-sizes of A and B, respectively, and
; OP is the operator that is relating A and B.  In the case of a ?: operator,
; note that A and B are the then/else branches.
;
; My original approach was just to say, "It's minor if ASIZE or BSIZE is 32."
; This happens in many very common cases where unsized numbers are used, such
; as:
;
;     foo[3:0] == 7;          //  4 bits == 32 bits
;     foo[0] ? bar[3:0] : 0;  //  foo[0] ? 4 bits : 32 bits
;
; But over time I have added many additional tweaks, described in the comments
; below.  At any rate, this function is either supposed to return NIL to say,
; "I don't actually want to issue a warning," or else should return the :type
; for the warning to be issued, so that one can filter out the probably
; important and probably minor warnings.

  (defund vl-tweak-fussy-warning-type (type a b asize bsize op)
    "Returns NIL (meaning, do not warn) or a Warning Type derived from TYPE."
    (declare (xargs :guard (and (symbolp type)
                                (vl-expr-p a)
                                (vl-expr-p b)
                                (natp asize)
                                (natp bsize)
                                (vl-op-p op))))
    (b* (((when (and (or (and (vl-expr-resolved-p a)
                              (< (vl-resolved->val a) (ash 1 bsize)))
                         (and (vl-expr-resolved-p b)
                              (< (vl-resolved->val b) (ash 1 asize))))
                     (member op '(:vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
                                  :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
                                  :vl-binary-xnor :vl-qmark))))
          ;; Always suppress warnings in the case where one argument or the
          ;; other is a constant and even though its size isn't quite right, it
          ;; is not *really* wrong.  For instance, if foo was once a three-bit
          ;; wire but now is a five-bit wire, we might run into an expression
          ;; like "foo == 3'b7," which isn't really any kind of problem.
          nil)

         (a32p (= asize 32))
         (b32p (= bsize 32))
         ((unless (or a32p b32p))
          ;; Neither op is 32 bits, so this doesn't seem like it's related to
          ;; unsized numbers, go ahead and warn.
          type)

         ;; Figure out which one is 32-bit and which one is not.  We assume
         ;; they aren't both 32 bits, since otherwise we shouldn't be called.
         ((mv expr-32 size-other) (if a32p (mv a bsize) (mv b asize)))

         ;; Collect up interesting unsized ints in the 32-bit expression.  If
         ;; it has unsized ints, they're probably the reason it's 32 bits.
         ;; After collecting them, see if they fit into the size of the other
         ;; expr.
         (atoms         (vl-expr-interesting-size-atoms expr-32))
         (unsized       (vl-collect-unsized-ints atoms))
         (unsized-fit-p (nats-below-p (ash 1 size-other)
                                      (vl-exprlist-resolved->vals unsized)))
         ((unless unsized-fit-p)
          ;; Well, hrmn, there's some integer here that doesn't fit into the
          ;; size of the other argument.  This is especially interesting
          ;; because there's likely to be some kind of truncation here.  Give
          ;; it a new type.
          (intern-in-package-of-symbol (cat (symbol-name type) "-CONST-TOOBIG") type))

         ((when (consp unsized))
          ;; What does this mean?  Well, there are at least some unsized
          ;; numbers in positions that are affecting our selfsize, and every
          ;; such unsized number does fit into the new size we're going into,
          ;; so it seems pretty safe to make this a minor warning.
          (intern-in-package-of-symbol (cat (symbol-name type) "-MINOR") type)))

      ;; Otherwise, we didn't find any unsized atoms, so just go ahead and do the
      ;; warning.
      type))

  (local (in-theory (enable vl-tweak-fussy-warning-type)))

  (defthm symbolp-of-vl-tweak-fussy-warning-type
    (implies (force (symbolp type))
             (symbolp (vl-tweak-fussy-warning-type type a b asize bsize op)))
    :rule-classes :type-prescription))



(defsection vl-op-selfsize
  :parents (vl-expr-selfsize)
  :short "Main function for computing self-determined expression sizes."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-op-selfsize) returns @('(mv warnings size)')</p>

<p>We attempt to determine the size of the expression formed by applying some
operator, @('op'), to some arguments, @('args').  We assume that each argument
has already had its self-size computed successfully and that the results of
these computations are given as the @('arg-sizes').</p>

<p>The @('context') is irrelevant and is only used to form better error
messages; it is supposed to be the expression we are trying to size.  The
@('elem') is similarly irrelevant, and gives the broader context for this
expression.</p>

<p>This function basically implements Table 5-22; see @(see
expression-sizing).</p>"

  (local (in-theory (enable maybe-natp)))

  (defund vl-op-selfsize (op args arg-sizes context elem warnings)
    "Returns (MV WARNINGS SIZE)"
    (declare (xargs :guard (and (vl-op-p op)
                                (vl-exprlist-p args)
                                (or (not (vl-op-arity op))
                                    (equal (len args) (vl-op-arity op)))
                                (nat-listp arg-sizes)
                                (same-lengthp args arg-sizes)
                                (vl-expr-p context)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))
                    :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity)))))

    (case op

      ((:vl-bitselect
        :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
        :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
        :vl-binary-logand :vl-binary-logor)
       ;; All of these operations have one-bit results, and we have no
       ;; expectations that their argument sizes should agree or anything like
       ;; that.
       (mv warnings 1))

      ((:vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte)
       ;; These were previously part of the above case.  They all also return
       ;; one-bit results.  However, we now add warnings if an implicit size
       ;; extension will occur.
       (b* ((type (and (/= (first arg-sizes) (second arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-1
                                                    (first args)
                                                    (second args)
                                                    (first arg-sizes)
                                                    (second arg-sizes)
                                                    op)))
            (warnings (if (not type)
                          warnings
                        (cons (make-vl-warning
                               :type type
                               :msg "~a0: arguments to a comparison operator ~
                                     have different \"self-sizes\" (~x1 ~
                                     versus ~x2).  The smaller argument will ~
                                     be implicitly widened to match the ~
                                     larger argument.  The sub-expression in ~
                                     question is: ~a3."
                               :args (list elem (first arg-sizes) (second arg-sizes) context)
                               :fatalp nil
                               :fn 'vl-op-selfsize)
                              warnings))))
         (mv warnings 1)))

      ((:vl-binary-power
        :vl-unary-plus :vl-unary-minus :vl-unary-bitnot
        :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
       ;; All of these operations keep the size of their first operands.
       (mv warnings (lnfix (first arg-sizes))))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem)
       ;; All of these operations take the max size of either operand.
       ;; Practically speaking we will probably never see times, div, or rem
       ;; operators.  However, plus and minus are common.  We probably do not
       ;; want to issue any size warnings in the case of plus or minus, since
       ;; one argument or the other often needs to be expanded.
       (mv warnings (max (lnfix (first arg-sizes))
                         (lnfix (second arg-sizes)))))

      ((:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       ;; All of these operations take the max size of either operand.  But
       ;; this is a place where implicit widening could be bad.  I mean, you
       ;; probably don't want to be doing A & B when A and B are different
       ;; sizes, right?
       (b* ((max (max (lnfix (first arg-sizes))
                      (lnfix (second arg-sizes))))
            (type (and (/= (first arg-sizes) (second arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-2
                                                    (first args)
                                                    (second args)
                                                    (first arg-sizes)
                                                    (second arg-sizes)
                                                    op)))
            (warnings (if (not type)
                          warnings
                        (cons (make-vl-warning
                               :type type
                               :msg "~a0: arguments to a bitwise operator ~
                                     have different self-sizes (~x1 versus ~
                                     ~x2).  The smaller argument will be ~
                                     implicitly widened to match the larger ~
                                     argument.  The sub-expression in ~
                                     question is: ~a3."
                               :args (list elem (first arg-sizes) (second arg-sizes) context)
                               :fatalp nil
                               :fn 'vl-op-selfsize)
                              warnings))))
         (mv warnings max)))

      ((:vl-qmark)
       ;; The conditional takes the max size of its true and false branches.
       ;; We now warn if the branches don't agree on their size and hence will
       ;; be widened.
       (b* ((max (max (lnfix (second arg-sizes))
                      (lnfix (third arg-sizes))))
            (type (and (/= (second arg-sizes) (third arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-3
                                                    (second args)
                                                    (third args)
                                                    (second arg-sizes)
                                                    (third arg-sizes)
                                                    op)))
            (warnings (if (not type)
                          warnings
                        (cons (make-vl-warning
                               :type type
                               :msg "~a0: branches of a ?: operator have ~
                                     different self-sizes (~x1 versus ~x2).  ~
                                     The smaller branch will be implicitly ~
                                     widened to match the larger argument.  ~
                                     The sub-expression in question is: ~a3."
                               :args (list elem (second arg-sizes) (third arg-sizes) context)
                               :fatalp nil
                               :fn 'vl-op-selfsize)
                              warnings))))
         (mv warnings max)))

      ((:vl-concat)
       ;; Concatenations have the sum of their arguments' widths
       (mv warnings (sum-nats arg-sizes)))

      ((:vl-syscall)
       ;; We do all syscall sizing in a separate function.
       (vl-syscall-selfsize args arg-sizes context elem warnings))

      ((:vl-multiconcat)
       ;; For multiple concatenations, the size is its multiplicity times the
       ;; size of the concatenation-part.  The multiplicity can be zero.
       (b* ((multiplicity (first args))
            (concat-width (mbe :logic (nfix (second arg-sizes))
                               :exec (second arg-sizes)))
            ((unless (vl-expr-resolved-p multiplicity))
             (b* ((w (make-vl-warning
                      :type :vl-unresolved-multiplicity
                      :msg "~a0: cannot size ~a1 because its multiplicity has ~
                            not been resolved."
                      :args (list elem context)
                      :fatalp t
                      :fn 'vl-op-selfsize)))
               (mv (cons w warnings) nil)))
            (size (* (vl-resolved->val multiplicity) concat-width)))
         (mv warnings size)))

      ((:vl-partselect-colon)
       ;; A part-select's width is one greater than the difference in its
       ;; indices.  For instance, a[3:0] is 4 bits, while a[3:3] is one bit.
       (b* ((left  (second args))
            (right (third args))
            ((unless (and (vl-expr-resolved-p left)
                          (vl-expr-resolved-p right)))
             (b* ((w (make-vl-warning
                      :type :vl-unresolved-select
                      :msg "~a0: cannot size ~a1 since it does not have ~
                            resolved indices."
                      :args (list elem context)
                      :fatalp t
                      :fn 'vl-op-selfsize)))
               (mv (cons w warnings) nil)))
            (left-val  (vl-resolved->val left))
            (right-val (vl-resolved->val right))
            (size      (+ 1 (abs (- left-val right-val)))))
         (mv warnings size)))

      ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
       ;; foo[base_expr +: width_expr] has the width specified by width_expr,
       ;; which must be a positive constant. (See Section 5.2.1)
       (b* ((width-expr (second args))
            ((unless (and (vl-expr-resolved-p width-expr)
                          (> (vl-resolved->val width-expr) 0)))
             (b* ((w (make-vl-warning
                      :type :vl-unresolved-select
                      :msg "~a0: cannot size ~a1 since its width expression ~
                            is not a resolved, positive constant."
                      :args (list elem context)
                      :fatalp t
                      :fn 'vl-op-selfsize)))
               (mv (cons w warnings) nil)))
            (size (vl-resolved->val width-expr)))
         (mv warnings size)))

      ((:vl-funcall)
       ;; BOZO we don't currently try to support function calls.  Eventually it
       ;; should be easy to support sizing these, since it looks like functions
       ;; are returned with a syntax like "function [7:0] getbyte;" -- we'll
       ;; just need to look up the function and return the size of its range.
       (mv warnings nil))

      ((:vl-mintypmax)
       ;; I do not think it makes any sense to think about the size of a
       ;; mintypmax expression.  We just return nil and cause no warnings since
       ;; the width is basically "inapplicable."
       (mv warnings nil))

      ((:vl-hid-dot :vl-hid-arraydot :vl-array-index)
       ;; We don't handle these here.  They should be handled in
       ;; vl-expr-selfsize specially, because unlike all of the other
       ;; operators, we can't assume that their subexpressions' sizes can be
       ;; computed.  Instead, we need to only try to determine the size of
       ;; "top-level" HIDs, and also specially handle array indexes.
       (b* ((w (make-vl-warning
                :type :vl-programming-error
                :msg "~a0: vl-op-selfsize should not encounter ~a1"
                :args (list elem context)
                :fatalp t
                :fn 'vl-op-selfsize)))
         (mv (cons w warnings) nil)))

      (otherwise
       (mv warnings
           (er hard 'vl-op-selfsize
               "All operators must be accounted for.  This er forces us to prove ~
                that this is the case, in the guard-verification proof.")))))

  (local (in-theory (enable vl-op-selfsize)))

  (defthm vl-warninglist-p-of-vl-op-selfsize
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-op-selfsize op args arg-sizes context elem warnings)))))

  (defthm maybe-natp-of-vl-op-selfsize
    (maybe-natp (mv-nth 1 (vl-op-selfsize op args arg-sizes context elem warnings)))
    :rule-classes :type-prescription)

  (defthm warning-irrelevance-of-vl-op-selfsize
    (let ((ret1 (vl-op-selfsize op args arg-sizes context elem warnings))
          (ret2 (vl-op-selfsize op args arg-sizes context elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))

(define vl-hidexpr-selfsize ((x (and (vl-expr-p x)
                                     (vl-nonatom-p x)
                                     (or (eq (vl-nonatom->op x) :vl-hid-dot)
                                         (eq (vl-nonatom->op x) :vl-hid-arraydot))))
                             (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p :hyp (vl-warninglist-p warnings))
               (size maybe-natp :hints(("Goal" :in-theory (enable maybe-natp)))))
  (b* ((width (vl-hid-width x))
       ((unless width)
        (mv (cons (make-vl-warning :type :vl-hid-size-failed
                                   :msg "Range of HID ~a0 not resolved"
                                   :args (list x)
                                   :fatalp t)
                  warnings)
            nil)))
    (mv warnings width))
  ///
  (defthm vl-hidexpr-selfsize-normalize-warnings
    (implies (syntaxp (not (equal warnings ''nil)))
             (equal (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                    (mv-nth 1 (vl-hidexpr-selfsize x nil)))))

  (defthm vl-hidexpr-welltyped-p-of-selfsize
    (implies (and (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                  (or (equal op :vl-hid-dot)
                      (equal op :vl-hid-arraydot))
                  (equal type :vl-unsigned)
                  (force (vl-expr-p x))
                  (force (vl-nonatom-p x)))
             (vl-hidexpr-welltyped-p
              (vl-nonatom op (vl-nonatom->atts x) (vl-nonatom->args x)
                          (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                          type)))
    :hints(("Goal" :in-theory (enable vl-hidexpr-welltyped-p)))))


(defsection vl-expr-selfsize
  :parents (vl-expr-size)
  :short "Computation of self-determined expression sizes."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature: </b> @(call vl-expr-selfsize) returns @('(mv warnings
size)').</p>

<p>As inputs:</p>

<ul>

<li>@('x') is the expression whose size we wish to compute.</li>

<li>@('mod') is the module that contains this expression; we use it to look up
expression sizes from their declarations.</li>

<li>@('ialist') is the precomputed @(see vl-moditem-alist) for @('mod'); we use
it for fast wire lookups.</li>

<li>@('elem') is a semantically irrelevant; it is a @(see vl-modelement-p) that
provides a context for @(see warnings).</li>

</ul>

<p>The @('size') we return is a @(see maybe-natp); a @('size') of @('nil')
indicates that we had some problem determining the expression's size.</p>

<p>Some failures are expected, e.g., we do not know how to size some system
calls.  In these cases we do not cause any warnings.  But in other cases, a
failure might mean that the expression is malformed in some way, e.g., maybe it
references an undefined wire or contains a raw, \"unindexed\" reference to an
array.  In these cases we generate fatal warnings.</p>

<p>BOZO we might eventually add as inputs the full list of modules and a
modalist so that we can look up HIDs.  An alternative would be to use the
annotations left by @(see vl-modulelist-follow-hids) like (e.g.,
@('VL_HID_RESOLVED_RANGE_P')) to see how wide HIDs are.</p>"

  (mutual-recursion

   (defund vl-expr-selfsize (x mod ialist elem warnings)
     "Returns (MV WARNINGS SIZE)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (vl-atom-selfsize x mod ialist elem warnings))

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((when (or (eq op :vl-hid-dot)
                     (eq op :vl-hid-arraydot)))

           (vl-hidexpr-selfsize x warnings))


          ((when (eq op :vl-array-index))
           ;; BOZO we should try to size array-indexing here.  For now I'm
           ;; skipping this so I can press on.
           (mv warnings nil))

          ((mv warnings arg-sizes)
           (vl-exprlist-selfsize args mod ialist elem warnings))

          ((when (member nil arg-sizes))
           ;; Some subexpression was not given its size.  We don't try to
           ;; produce a size.
           (mv warnings nil))

          ;; Otherwise, all subexpressions sized successfully.  Call
          ;; vl-op-selfsize to do all the work.
          ((mv warnings size)
           (vl-op-selfsize op args arg-sizes x elem warnings)))

       (mv warnings size)))

   (defund vl-exprlist-selfsize (x mod ialist elem warnings)
     "Returns (MV WARNINGS SIZE-LIST)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-size)
           (vl-expr-selfsize (car x) mod ialist elem warnings))
          ((mv warnings cdr-sizes)
           (vl-exprlist-selfsize (cdr x) mod ialist elem warnings))
          (sizes (cons car-size cdr-sizes)))
       (mv warnings sizes))))

  (defthm vl-exprlist-selfsize-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-selfsize x mod ialist elem warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-selfsize))))

  (defthm vl-exprlist-selfsize-when-of-cons
    (equal (vl-exprlist-selfsize (cons a x) mod ialist elem warnings)
           (b* (((mv warnings car-size) (vl-expr-selfsize a mod ialist elem warnings))
                ((mv warnings cdr-sizes) (vl-exprlist-selfsize x mod ialist elem warnings)))
             (mv warnings (cons car-size cdr-sizes))))
    :hints(("Goal" :in-theory (enable vl-exprlist-selfsize))))

  (local (defun my-induct (x mod ialist elem warnings)
           (b* (((when (atom x))
                 (mv nil nil))
                ((mv warnings car-size)
                 (vl-expr-selfsize (car x) mod ialist elem warnings))
                ((mv warnings cdr-sizes)
                 (my-induct (cdr x) mod ialist elem warnings))
                (sizes    (cons car-size cdr-sizes)))
             (mv warnings sizes))))

  (defthm len-of-vl-exprlist-selfsize-1
    (equal (len (mv-nth 1 (vl-exprlist-selfsize x mod ialist elem warnings)))
           (len x))
    :hints(("Goal" :induct (my-induct x mod ialist elem warnings))))

  (defthm true-listp-of-vl-exprlist-selfsize-1
    (true-listp (mv-nth 1 (vl-exprlist-selfsize x mod ialist elem warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induct x mod ialist elem warnings))))

  (FLAG::make-flag vl-flag-expr-selfsize
                   vl-expr-selfsize
                   :flag-mapping ((vl-expr-selfsize . expr)
                                  (vl-exprlist-selfsize . list)))

  (defthm-vl-flag-expr-selfsize
    (defthm vl-warninglist-p-of-vl-expr-selfsize
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-expr-selfsize x mod ialist elem warnings))))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-selfsize
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-exprlist-selfsize x mod ialist elem warnings))))
      :flag list)
    :hints(("Goal" :expand (vl-expr-selfsize x mod ialist elem warnings))))

  (defthm-vl-flag-expr-selfsize
    (defthm maybe-natp-of-vl-expr-selfsize
      (maybe-natp
       (mv-nth 1 (vl-expr-selfsize x mod ialist elem warnings)))
      :rule-classes :type-prescription
      :flag expr)
    (defthm vl-maybe-nat-listp-of-vl-exprlist-selfsize
      (vl-maybe-nat-listp
       (mv-nth 1 (vl-exprlist-selfsize x mod ialist elem warnings)))
      :flag list)
    :hints(("Goal" :expand (vl-expr-selfsize x mod ialist elem warnings))))

  (verify-guards vl-expr-selfsize)

  (local
   (defthm-vl-flag-expr-selfsize
     ;; This is pretty subtle.  The induction scheme that the flag function would
     ;; generate if we tried to directly use warnings and NIL isn't right in the
     ;; list case.  We have to generalize this to an arbitrary warnings1 and
     ;; warnings2.  Then, ACL2's induction heuristic is smart enough to get the
     ;; right scheme, but only when we tell it to consider the flag function for
     ;; both warnings1 and warnings2.  Ugh.  This took a long time to figure out.
     (defthm l0
       (let ((ret1 (vl-expr-selfsize x mod ialist elem warnings1))
             (ret2 (vl-expr-selfsize x mod ialist elem warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag expr)

     (defthm l1
       (let ((ret1 (vl-exprlist-selfsize x mod ialist elem warnings1))
             (ret2 (vl-exprlist-selfsize x mod ialist elem warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag list)

     :hints(("Goal"
             :do-not '(generalize fertilize)

             :induct (and (vl-flag-expr-selfsize flag x mod ialist elem warnings1)
                          (vl-flag-expr-selfsize flag x mod ialist elem warnings2))
             :expand ((vl-expr-selfsize x mod ialist elem warnings1)
                      (vl-expr-selfsize x mod ialist elem warnings2))))))

  (defthm warning-irrelevance-of-vl-expr-selfsize
    (let ((ret1 (vl-expr-selfsize x mod ialist elem warnings))
          (ret2 (vl-expr-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :hints(("Goal" :use ((:instance l0
                                    (warnings1 warnings)
                                    (warnings2 nil))))))

  (defthm warning-irrelevance-of-vl-exprlist-selfsize
    (let ((ret1 (vl-exprlist-selfsize x mod ialist elem warnings))
          (ret2 (vl-exprlist-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :hints(("Goal" :use ((:instance l1
                                    (warnings1 warnings)
                                    (warnings2 nil)))))))



; -----------------------------------------------------------------------------
;
;                    DETERMINATION OF FINAL SIGNEDNESS
;
; -----------------------------------------------------------------------------

(defsection vl-exprtype-max
  :parents (vl-expr-typedecide)
  :short "@(see vl-exprtype-max) is given @(see vl-exprtype-p)s as arguments;
it returns @(':vl-unsigned') if any argument is unsigned, or @(':vl-signed')
when all arguments are signed."

  (local (in-theory (enable vl-exprtype-p)))

  (defund vl-exprtype-max-fn (x y)
    (declare (xargs :guard (and (vl-exprtype-p x)
                                (vl-exprtype-p y))))
    ;; Goofy MBE stuff is just to make sure this function breaks if we ever add
    ;; support for reals or other types.
    (let ((x-fix (mbe :logic (case x
                               (:vl-signed   :vl-signed)
                               (otherwise    :vl-unsigned))
                      :exec x))
          (y-fix (mbe :logic (case y
                               (:vl-signed   :vl-signed)
                               (otherwise    :vl-unsigned))
                      :exec y)))
      (if (or (eq x-fix :vl-unsigned)
              (eq y-fix :vl-unsigned))
          :vl-unsigned
        :vl-signed)))

  (defmacro vl-exprtype-max (x y &rest rst)
    (xxxjoin 'vl-exprtype-max-fn (cons x (cons y rst))))

  (add-binop vl-exprtype-max vl-exprtype-max-fn)

  (local (in-theory (enable vl-exprtype-max-fn)))

  (defthm vl-exprtype-p-of-vl-exprtype-max
    (vl-exprtype-p (vl-exprtype-max x y)))

  (defthm type-of-vl-exprtype-max
    (and (symbolp (vl-exprtype-max x y))
         (not (equal t (vl-exprtype-max x y)))
         (not (equal nil (vl-exprtype-max x y))))
    :rule-classes :type-prescription)

  (defthm vl-exprtype-max-of-vl-exprtype-max
    (equal (vl-exprtype-max (vl-exprtype-max x y) z)
           (vl-exprtype-max x (vl-exprtype-max y z)))))


(defsection vl-atom-typedecide
  :parents (vl-expr-typedecide)
  :short "Effectively computes the \"self-determined\" type of an atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-atom-typedecide) returns @('(mv warnings
type)').</p>

<p>We compute what the type of the atom @('x') would be if it were in a
self-determined location.  Another way to look at this function is as an
extension of \"origtype\" from constint/weirdint atoms to include identifiers
and strings.</p>

<p>The @('type') we return is a @(see vl-maybe-exprtype-p).  Similarly to @(see
vl-atom-selfsize), we might fail and return @('nil') for the type, perhaps
producing some warnings.</p>"

  (defund vl-atom-typedecide (x mod ialist elem warnings)
    "Returns (MV WARNINGS TYPE)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))
                    :guard-debug t))
    (b* ((guts (vl-atom->guts x))

         ((when (vl-fast-constint-p guts))
          (mv warnings (vl-constint->origtype guts)))

         ((when (vl-fast-weirdint-p guts))
          (mv warnings (vl-weirdint->origtype guts)))

         ((when (vl-fast-string-p guts))
          (mv warnings :vl-unsigned))

         ((unless (vl-fast-id-p guts))
          ;; Other kinds of atoms don't get a type.
          (mv warnings nil))

         (name (vl-id->name guts))
         (item (vl-fast-find-moduleitem name mod ialist))

         ((unless item)
          ;; Shouldn't happen if the module is well-formed and all used names are
          ;; declared.
          (b* ((w (make-vl-warning
                   :type :vl-bad-identifier
                   :msg "~a0: cannot determine the type of ~w1 because it ~
                         is not declared."
                   :args (list elem name)
                   :fatalp t
                   :fn 'vl-atom-typedecide)))
            (mv (cons w warnings) nil)))

         ((when (mbe :logic (or (vl-netdecl-p item)
                                (vl-regdecl-p item))
                     :exec (or (eq (tag item) :vl-netdecl)
                               (eq (tag item) :vl-regdecl))))
          (b* (((mv arrdims signedp)
                (if (eq (tag item) :vl-netdecl)
                    (mv (vl-netdecl->arrdims item)
                        (vl-netdecl->signedp item))
                  (mv (vl-regdecl->arrdims item)
                      (vl-regdecl->signedp item))))
               ((when (consp arrdims))
                ;; Shouldn't happen unless the module directly uses the name of
                ;; an array in an expression.
                (b* ((w (make-vl-warning
                         :type :vl-bad-identifier
                         :msg "~a0: cannot determine the type of ~w1 because ~
                               it is an unindexed reference to an array."
                         :args (list elem name)
                         :fatalp t
                         :fn 'vl-atom-typedecide)))
                  (mv (cons w warnings) nil)))
               (type (if signedp :vl-signed :vl-unsigned)))
            (mv warnings type)))

         ((when (and (mbe :logic (vl-vardecl-p item)
                          :exec (eq (tag item) :vl-vardecl))))
          (b* (((unless (eq (vl-vardecl->type item) :vl-integer))
                ;; We don't try to give types to real, realtime, or time
                ;; variables.
                (mv warnings nil))
               ((when (consp (vl-vardecl->arrdims item)))
                ;; Analogous to the netdecl/regdecl array case.
                (b* ((w (make-vl-warning
                         :type :vl-bad-identifier
                         :msg "~a0: cannot determine the type of ~w1 because ~
                               it is an unindexed reference to an array."
                         :args (list elem name)
                         :fatalp t
                         :fn 'vl-atom-typedecide)))
                  (mv (cons w warnings) nil))))
            ;; Regular integer variables are signed.
            (mv warnings :vl-signed)))

         ;; It would be surprising if we get here -- this is an identifier that
         ;; refers to something in the module, maybe an event, parameter, or
         ;; instance?  It seems like we shouldn't hit this case unless the module
         ;; contains something really strange.
         (w (make-vl-warning
             :type :vl-bad-identifier
             :msg "~a0: cannot determine the type of ~w1 because it is ~
                   a ~x2; we only expected to type net, register, and ~
                   variable declarations."
             :args (list elem name (tag item))
             :fatalp t
             :fn 'vl-atom-typedecide)))
      (mv (cons w warnings) nil)))

  (local (in-theory (enable vl-atom-typedecide)))

  (defthm vl-warninglist-p-of-vl-atom-typedecide
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-atom-typedecide x mod ialist elem warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-maybe-exprtype-p-of-vl-atom-typedecide
    (implies (and (force (vl-atom-p x))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-maybe-exprtype-p
              (mv-nth 1 (vl-atom-typedecide x mod ialist elem warnings))))
    :rule-classes
    ((:rewrite)
     (:rewrite
      :corollary
      (implies (and (force (vl-atom-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprtype-p
                       (mv-nth 1 (vl-atom-typedecide x mod ialist elem warnings)))
                      (if (mv-nth 1 (vl-atom-typedecide x mod ialist elem warnings))
                          t
                        nil))))))

  (defthm warning-irrelevance-of-vl-atom-typedecide
    (let ((ret1 (vl-atom-typedecide x mod ialist elem warnings))
          (ret2 (vl-atom-typedecide x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))


(defsection vl-expr-typedecide-aux
  :parents (vl-expr-typedecide)
  :short "Core of computing expression signedness."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-expr-typedecide-aux) returns @('(mv warnings
type)')</p>

<p>These are the same arguments as @(see vl-expr-typedecide) except for
@('mode').  You should probably read @(see expression-sizing-minutia) to
understand the valid modes:</p>

<ul>

<li>In @(':probably-wrong') mode, we treat reduction/logical operations as if
they produce signed values when their argument is signed, and we allow the
types of self-determined operands in conditional operators, shifts, and so
forth to affect the resulting expression type.  We do not think this is how
sizing is supposed to be done, but a Verilog implementation that was based on a
reading of the specification might mistakenly do it this way.</li>

<li>In @(':probably-right') mode, we try to behave like other Verilog systems
and ignore the type of self-determined operands when computing the resulting
types of expressions, and we also treat reduction/logical operations as if they
produce unsigned values.</li>

</ul>"

  (mutual-recursion

   (defund vl-expr-typedecide-aux (x mod ialist elem warnings mode)
     "Returns (MV WARNINGS TYPE)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings)
                                 (or (eq mode :probably-wrong)
                                     (eq mode :probably-right)))
                     :hints(("Goal" :in-theory (disable (force))))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (vl-atom-typedecide x mod ialist elem warnings))
          (op        (vl-nonatom->op x))
          (args      (vl-nonatom->args x))
          ((when (or (eq op :vl-hid-dot)
                     (eq op :vl-hid-arraydot)))
           (if (assoc-equal "VL_HID_RESOLVED_RANGE_P" (vl-nonatom->atts x))
               ;; this implies it's unsigned
               (mv warnings :vl-unsigned)
             (mv (cons (make-vl-warning :type :vl-bad-hid
                                        :msg "~a0: Couldn't resolve the type of HID ~a1"
                                        :args (list elem x)
                                        :fatalp t)
                       warnings)
                 nil)))

          ((mv warnings arg-types)
           (vl-exprlist-typedecide-aux args mod ialist elem warnings mode)))

       (case op

         ((:vl-bitselect
           :vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
           :vl-concat :vl-multiconcat
           :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
           :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte)
          ;; From 5.5.1, bit-selects, part-selects, concatenations, and
          ;; comparisons always produce unsigned results, no matter the
          ;; signedness of their operands.
          (mv warnings :vl-unsigned))

         ((:vl-unary-plus :vl-unary-minus)
          ;; From 5.5.1, I believe these fall into the "all other operators"
          ;; rule and just take on the signedness of their argument.
          (mv warnings (first arg-types)))

         ((:vl-unary-lognot :vl-unary-bitnot :vl-unary-bitand :vl-unary-bitor
                            :vl-unary-nand :vl-unary-nor :vl-unary-xor :vl-unary-xnor)
          (cond ((eq mode :probably-right)
                 ;; We believe the result is always unsigned; see "minutia".
                 ;; If we ever decide this is not right, review the rules in
                 ;; oprewrite that introduce concatenations like !a -> {~(|a)}
                 ;; since they are not supposed to change signs.
                 (mv warnings :vl-unsigned))
                (t
                 ;; Probably-wrong mode: we act like the operand type matters and
                 ;; treat this like a unary plus or minus.
                 (mv warnings (first arg-types)))))

         ((:vl-binary-logand :vl-binary-logor)
          (cond ((eq mode :probably-right)
                 ;; We believe the result is always unsigned; see "minutia".
                 (mv warnings :vl-unsigned))
                (t
                 ;; Probably wrong mode: we act like the operand types matter and
                 ;; treat this like a regular binary op.
                 (b* ((type1 (first arg-types))
                      (type2 (second arg-types))
                      (type  (and type1 type2 (vl-exprtype-max type1 type2))))
                   (mv warnings type)))))

         ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
                           :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
          ;; Simple context-determined binary ops.
          (b* ((type1 (first arg-types))
               (type2 (second arg-types))
               (type  (and type1 type2 (vl-exprtype-max type1 type2))))
            (mv warnings type)))

         ((:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl :vl-binary-power)
          (cond ((eq mode :probably-right)
                 ;; We believe the second op's type does NOT affect the result
                 ;; type; see "minutia"
                 (mv warnings (first arg-types)))
                (t
                 ;; Probably-wrong mode: we act like the second op's type matters
                 ;; and treat this like a regular binary op.
                 (b* ((type1 (first arg-types))
                      (type2 (second arg-types))
                      (type  (and type1 type2 (vl-exprtype-max type1 type2))))
                   (mv warnings type)))))

         ((:vl-qmark)
          (b* ((type1 (first arg-types))
               (type2 (second arg-types))
               (type3 (third arg-types)))
            (cond ((eq mode :probably-right)
                   ;; We believe the first op's type does NOT affect the result type;
                   ;; see "minutia".
                   (mv warnings (and type1 type2 type3
                                     (vl-exprtype-max type2 type3))))
                  (t
                   ;; Probably-wrong mode: we allow the first op's type to affect the
                   ;; result type.
                   (mv warnings (and type1 type2 type3
                                     (vl-exprtype-max type1 type2 type3)))))))

         ((:vl-syscall)
          (if (vl-$random-expr-p x)
              (mv nil :vl-signed)
            ;; Otherwise, not a supported system call.
            (mv warnings nil)))

         ((:vl-array-index)
          ;; BOZO we should try to determine the type of array indexes.
          (mv warnings nil))

         ((:vl-funcall)
          ;; BOZO eventually add support for function calls.
          (mv warnings nil))

         ((:vl-mintypmax)
          ;; I think it makes no sense to try to assign a type to these.
          (mv warnings nil))

         (otherwise
          (mv warnings (er hard 'vl-expr-typedecide-aux "Provably impossible."))))))

   (defund vl-exprlist-typedecide-aux (x mod ialist elem warnings mode)
     "Returns (MV WARNINGS TYPES)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings)
                                 (or (eq mode :probably-wrong)
                                     (eq mode :probably-right)))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-type)
           (vl-expr-typedecide-aux (car x) mod ialist elem warnings mode))
          ((mv warnings cdr-type)
           (vl-exprlist-typedecide-aux (cdr x) mod ialist elem warnings mode)))
       (mv warnings (cons car-type cdr-type)))))

  (local (in-theory (enable member-equal-when-member-equal-of-cdr-under-iff
                            vl-warninglist-p-when-subsetp-equal
                            sets::double-containment)))

  (defthm vl-exprlist-typedecide-aux-when-atom
    (implies (atom x)
             (equal (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-typedecide-aux))))

  (defthm vl-exprlist-typedecide-aux-of-cons
    (equal (vl-exprlist-typedecide-aux (cons a x) mod ialist elem warnings mode)
           (b* (((mv warnings car-type)
                 (vl-expr-typedecide-aux a mod ialist elem warnings mode))
                ((mv warnings cdr-type)
                 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
             (mv warnings (cons car-type cdr-type))))
    :hints(("Goal" :in-theory (enable vl-exprlist-typedecide-aux))))

  (local (defun my-induct (x mod ialist elem warnings mode)
           (b* (((when (atom x))
                 (mv warnings nil))
                ((mv warnings car-type)
                 (vl-expr-typedecide-aux (car x) mod ialist elem warnings mode))
                ((mv warnings cdr-type)
                 (my-induct (cdr x) mod ialist elem warnings mode)))
             (mv warnings (cons car-type cdr-type)))))

  (defthm len-of-vl-exprlist-typedecide-aux
    (equal (len (mv-nth 1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
           (len x))
    :hints(("Goal" :induct (my-induct x mod ialist elem warnings mode))))

  (defthm true-listp-of-vl-exprlist-typedecide-aux
    (true-listp (mv-nth 1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induct x mod ialist elem warnings mode))))

  (flag::make-flag vl-flag-expr-typedecide-aux
                   vl-expr-typedecide-aux
                   :flag-mapping ((vl-expr-typedecide-aux . expr)
                                  (vl-exprlist-typedecide-aux . list)))

  (defthm-vl-flag-expr-typedecide-aux
    (defthm vl-warninglist-p-of-vl-expr-typedecide-aux
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-expr-typedecide-aux x mod ialist elem warnings mode))))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-typedecide-aux
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode))))
      :flag list)
    :hints(("Goal"
            :expand ((:free (mode)
                            (vl-expr-typedecide-aux x mod ialist elem warnings mode))))))

  (defsection warning-irrel

    (local
     (defthm-vl-flag-expr-selfsize
       ;; This is pretty subtle.  The induction scheme that the flag function would
       ;; generate if we tried to directly use warnings and NIL isn't right in the
       ;; list case.  We have to generalize this to an arbitrary warnings1 and
       ;; warnings2.  Then, ACL2's induction heuristic is smart enough to get the
       ;; right scheme, but only when we tell it to consider the flag function for
       ;; both warnings1 and warnings2.  Ugh.  This took a long time to figure out.
       (defthm w0
         (let ((ret1 (vl-expr-typedecide-aux x mod ialist elem warnings1 mode))
               (ret2 (vl-expr-typedecide-aux x mod ialist elem warnings2 mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag expr)

       (defthm w1
         (let ((ret1 (vl-exprlist-typedecide-aux x mod ialist elem warnings1 mode))
               (ret2 (vl-exprlist-typedecide-aux x mod ialist elem warnings2 mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag list)

       :hints(("Goal"
               :do-not '(generalize fertilize)
               :induct (and (vl-flag-expr-typedecide-aux flag x mod ialist elem warnings1 mode)
                            (vl-flag-expr-typedecide-aux flag x mod ialist elem warnings2 mode))
               :expand ((:free (mode) (vl-expr-typedecide-aux x mod ialist elem warnings1 mode))
                        (:free (mode) (vl-expr-typedecide-aux x mod ialist elem warnings2 mode)))))))

    (defthm warning-irrelevance-of-vl-expr-typedecide-aux
      (let ((ret1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))
            (ret2 (vl-expr-typedecide-aux x mod ialist elem nil mode)))
        (implies (syntaxp (not (equal warnings ''nil)))
                 (equal (mv-nth 1 ret1)
                        (mv-nth 1 ret2))))
      :hints(("Goal" :use ((:instance w0 (warnings1 warnings) (warnings2 nil))))))

    (defthm warning-irrelevance-of-vl-exprlist-typedecide-aux
      (let ((ret1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode))
            (ret2 (vl-exprlist-typedecide-aux x mod ialist elem nil mode)))
        (implies (syntaxp (not (equal warnings ''nil)))
                 (equal (mv-nth 1 ret1)
                        (mv-nth 1 ret2))))
      :hints(("Goal" :use ((:instance w1 (warnings1 warnings) (warnings2 nil)))))))


  (local (deflist vl-maybe-exprtype-list-p (x)
           (vl-maybe-exprtype-p x)
           :guard t
           :elementp-of-nil t))

  (local
   (defthm-vl-flag-expr-typedecide-aux
     (defthm l0
       (implies (and (force (vl-expr-p x))
                     (force (vl-module-p mod))
                     (force (equal ialist (vl-moditem-alist mod))))
                (vl-maybe-exprtype-p
                 (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))))
       :flag expr)

     (defthm l1
       (implies (and (force (vl-exprlist-p x))
                     (force (vl-module-p mod))
                     (force (equal ialist (vl-moditem-alist mod))))
                (vl-maybe-exprtype-list-p
                 (mv-nth 1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode))))
       :flag list)

     :hints(("Goal"
             :expand ((:free (mode)
                             (vl-expr-typedecide-aux x mod ialist elem warnings mode)))))))

  (defthm vl-maybe-exprtype-p-of-vl-expr-typedecide-aux
    (implies (and (force (vl-expr-p x))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-maybe-exprtype-p
              (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))))
    :rule-classes
    ((:rewrite)
     (:rewrite
      :corollary
      (implies (and (force (vl-expr-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprtype-p
                       (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode)))
                      (if (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))
                          t
                        nil))))
     (:type-prescription
      :corollary
      (implies (and (force (vl-expr-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (symbolp (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))))))
    :hints(("Goal" :use ((:instance l0)))))

  (encapsulate
    ()
    (local (in-theory (disable return-type-of-vl-nonatom->op
                               default-car
                               default-cdr)))
    (verify-guards vl-expr-typedecide-aux
      :hints(("Goal"
              :use ((:instance return-type-of-vl-nonatom->op)))
             (and stable-under-simplificationp
                  '(:in-theory (enable vl-op-arity vl-op-p)))))))



(defsection vl-expr-typedecide
  :parents (vl-expr-size)
  :short "Computation of expression signedness (main routine)."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-expr-typedecide) returns @('(mv warnings
type)').  The arguments are as in @(see vl-expr-selfsize).</p>

<p>We determine the signedness of an expression.  This function must
<b>only</b> be used on \"top-level\" and self-determined portions of
expressions.  That is, consider an assignment like:</p>

@({
  assign w = {foo + bar, a + b} | (baz + 1) ;
})

<p>Here, it is legitimate to call @('vl-expr-typedecide') to determine the
signs of:</p>

<ul>
 <li>@('foo + bar'), because it is self-determined,</li>
 <li>@('a + b'), because it is self-determined, and</li>
 <li>@('{foo + bar, a + b} | (baz + 1)'), because it is top-level.</li>
</ul>

<p>But it is <b>not</b> legitimate to try to decide the sign of, @('baz + 1')
in isolation, and doing so could yield an nonsensical result.  For instance, if
@('baz') is signed then, by itself, @('baz + 1') looks like a signed addition.
But concatenations are always unsigned, so in the larger context we can see
that this addition is in fact unsigned.</p>

<p>The @('sign') we return is only a @(see vl-maybe-exprtype-p).  We might
return @('nil') for two reasons.  First, there could be some kind of actual
error with the module or the expression, e.g., the use of a wire which is not
declared; in these cases we add fatal @(see warnings).  But we may also
encounter expressions whose type we do not know how to compute (e.g., perhaps
the expression is an unsupported system call).  In such cases we just return
@('nil') for the sign without adding any warnings.</p>"

  (defund vl-expr-typedecide (x mod ialist elem warnings)
    "Returns (MV WARNINGS TYPE)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))
                    :verify-guards nil
                    :measure (acl2-count x)))
    (b* (((mv warnings right-type)
          (vl-expr-typedecide-aux x mod ialist elem warnings :probably-right))
         ((mv warnings wrong-type)
          (vl-expr-typedecide-aux x mod ialist elem warnings :probably-wrong))
         (warnings
          (if (eq right-type wrong-type)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-vague-spec
                   :msg "~a0: expression ~a1 has a type which is not ~
                         necessarily clear according to the discussion in the ~
                         Verilog standard.  We believe its type should be ~
                         ~s2, but think it would be easy for other Verilog ~
                         systems to mistakenly interpret the expression as ~
                         ~s3.  To reduce any potential confusion, you may ~
                         wish to rewrite this expression to make its ~
                         signedness unambiguous.  Some typical causes of ~
                         signedness are plain decimal numbers like 10, and ~
                         the use of integer variables instead of regs."
                   :args (list elem x right-type wrong-type)
                   :fatalp nil
                   :fn 'vl-expr-typedecide)
                  warnings))))
      (mv warnings right-type)))

  (local (in-theory (enable vl-expr-typedecide)))

  (defthm vl-warninglist-p-of-vl-expr-typedecide
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-expr-typedecide x mod ialist elem warnings)))))

  (defthm warning-irrelevance-of-vl-expr-typedecide
    (let ((ret1 (vl-expr-typedecide x mod ialist elem warnings))
          (ret2 (vl-expr-typedecide x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2)))))

  (defthm vl-maybe-exprtype-p-of-vl-expr-typedecide
    (implies (and (force (vl-expr-p x))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-maybe-exprtype-p
              (mv-nth 1 (vl-expr-typedecide x mod ialist elem warnings))))
    :rule-classes
    ((:rewrite)
     (:rewrite
      :corollary
      (implies (and (force (vl-expr-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-exprtype-p
                       (mv-nth 1 (vl-expr-typedecide x mod ialist elem warnings)))
                      (if (mv-nth 1 (vl-expr-typedecide x mod ialist elem warnings))
                          t
                        nil))))))

  (verify-guards vl-expr-typedecide))




; -----------------------------------------------------------------------------
;
;                PROPAGATION OF FINAL WIDTH/SIGN INTO OPERANDS
;
; -----------------------------------------------------------------------------

(defsection vl-expandsizes-zeroextend
  :parents (vl-expr-expandsizes)
  :short "Safely zero-extend an already-sized, unsigned expression to
finalwidth."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-expandsizes-zeroextend) returns @('(mv successp
warnings expanded-expr)').</p>

<p>The @('finalwidth') must be at least as large as the finalwidth of @('x').
If an extension is needed, we introduce an explicit concatenation, e.g., if we
are expanding @('foo') from 3 to 7 bits, we produce an @('expanded-expr') of
the form @('{ 4'b0, foo }').  When no extension is needed, we just return
@('x') unchanged.</p>"

  (defund vl-expandsizes-zeroextend (x finalwidth elem warnings)
    "Returns (MV SUCCESSP WARNINGS EXPANDED-EXPR)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-expr->finalwidth x)
                                (eq (vl-expr->finaltype x) :vl-unsigned)
                                (natp finalwidth)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((finalwidth   (lnfix finalwidth))
         (x.finalwidth (lnfix (vl-expr->finalwidth x)))

         ((when (> x.finalwidth finalwidth))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: trying to zero-extend ~a1, which has width ~x2, ~
                       to ~x3 bits??? Serious bug in our sizing code."
                   :args (list elem x x.finalwidth finalwidth)
                   :fatalp t
                   :fn 'vl-expandsizes-zeroextend)))
            (mv nil (cons w warnings) x)))

         ((when (= x.finalwidth finalwidth))
          ;; No need to expand.
          (mv t warnings x))

         ;; Otherwise we need to go ahead and do the zero-extension.  We build an
         ;; appropriately-sized constant zero atom and concatenate it onto X.
         (pad-width (- finalwidth x.finalwidth))
         (zero-guts (make-vl-constint :value 0
                                      :origwidth pad-width
                                      :origtype :vl-unsigned
                                      :wasunsized nil))
         (zero-atom (make-vl-atom :guts zero-guts
                                  :finalwidth pad-width
                                  :finaltype :vl-unsigned))
         (atts      (acons (hons-copy "VL_ZERO_EXTENSION") nil nil))
         (concat    (make-vl-nonatom :op :vl-concat
                                     :args (list zero-atom x)
                                     :finalwidth finalwidth
                                     :finaltype :vl-unsigned
                                     :atts atts)))
      (mv t warnings concat)))

  (local (in-theory (enable vl-expandsizes-zeroextend)))

  (defthm vl-warninglist-p-of-vl-expandsizes-zeroextend
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-expandsizes-zeroextend x finalwidth elem warnings)))))

  (defthm warning-irrelevance-of-vl-expandsizes-zeroextend
    (let ((ret1 (vl-expandsizes-zeroextend x finalwidth elem warnings))
          (ret2 (vl-expandsizes-zeroextend x finalwidth elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defthm vl-expr-p-of-vl-expandsizes-zeroextend
    (implies (force (vl-expr-p x))
             (vl-expr-p
              (mv-nth 2 (vl-expandsizes-zeroextend x finalwidth elem warnings)))))

  (defthm vl-expr->finalwidth-of-vl-expandsizes-zeroextend
    (implies (and (force (mv-nth 0 (vl-expandsizes-zeroextend x finalwidth elem warnings)))
                  (force (vl-expr-p x))
                  (force (vl-expr->finalwidth x))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned))
                  (force (natp finalwidth)))
             (equal (vl-expr->finalwidth
                     (mv-nth 2 (vl-expandsizes-zeroextend x finalwidth elem warnings)))
                    (nfix finalwidth))))

  (defthm no-change-loser-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x))))

  (defthm vl-expr->finaltype-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-p x))
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned))
                    (force (natp finalwidth)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      :vl-unsigned))))

  (defthm vl-expr-welltyped-p-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr-p x))
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned))
                    (force (natp finalwidth)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p vl-atom-welltyped-p)))))




(defsection vl-sign-extend-constint
  :parents (vl-expr-expandsizes)
  :short "@(call vl-sign-extend-constint) returns a new value, which is the
sign extension of the @('origwidth')-bit @('value') to @('finalwidth') bits."

  :long "<p>When the MSB is true we need to add the appropriate number of 1
bits.  There are probably any number of ways to do this.  My method is
relatively simple:</p>

@({
                         |---- finalwidth -------------|
                                       |-- origwidth --|
               value  == 0000...0000   1bb...bbbbbbbbbbb
   (logior)    mask   == 1111...1111   000...00000000000
 ----------------------------------------------------------
               result == 1111...1111   1bb...bbbbbbbbbbb
})"

  (defund vl-sign-extend-constint (value origwidth finalwidth)
    (declare (xargs :guard (and (natp value)
                                (posp origwidth)
                                (< value (expt 2 origwidth))
                                (posp finalwidth)
                                (< origwidth finalwidth))))
    (b* (;; Logbitp indexes from 0, so to get the most significant bit of an
         ;; origwidth-wide constant, we get the {origwidth-1}th bit.
         (msb (logbitp (1- origwidth) value))
         ((unless msb)
          ;; MSB is false; sign-extension is zero-extension, no value change.
          value)
         ;; Otherwise, MSB is true.  Add the appropriate number of 1s.
         (finalwidth-many-ones (- (expt 2 finalwidth) 1))
         (origwidth-many-ones  (- (expt 2 origwidth) 1))
         (mask                 (logxor finalwidth-many-ones origwidth-many-ones))
         (result               (logior mask value)))
      result))

  (local
   (progn

     ;; Very basic testing to show it seems to do the right thing

     (assert! (equal (vl-sign-extend-constint #b0010 4 5) #b0010))
     (assert! (equal (vl-sign-extend-constint #b0010 4 6) #b0010))
     (assert! (equal (vl-sign-extend-constint #b0010 4 7) #b0010))
     (assert! (equal (vl-sign-extend-constint #b0010 4 8) #b0010))

     (assert! (equal (vl-sign-extend-constint #b1010 4 5) #b11010))
     (assert! (equal (vl-sign-extend-constint #b1010 4 6) #b111010))
     (assert! (equal (vl-sign-extend-constint #b1010 4 7) #b1111010))
     (assert! (equal (vl-sign-extend-constint #b1010 4 8) #b11111010))))

  (local (include-book "centaur/bitops/ihs-extensions" :dir :system))
  (local (in-theory (enable vl-sign-extend-constint)))

  (defthm natp-of-vl-sign-extend-constint
    (implies (and (force (natp value))
                  (force (posp origwidth))
                  (force (< value (expt 2 origwidth)))
                  (force (posp finalwidth))
                  (force (< origwidth finalwidth)))
             (natp (vl-sign-extend-constint value origwidth finalwidth)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable logxor))))

  (defthm upper-bound-of-vl-sign-extend-constint
    (implies (and (force (natp value))
                  (force (posp origwidth))
                  (force (< value (expt 2 origwidth)))
                  (force (posp finalwidth))
                  (force (< origwidth finalwidth)))
             (< (vl-sign-extend-constint value origwidth finalwidth)
                (expt 2 finalwidth)))
    :rule-classes ((:rewrite) (:linear))))


(defsection vl-constint-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a constant
integer atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-constint-atom-expandsizes) returns @('(mv
successp warnings x-prime)').</p>

<p>We expect that the finalwidth is at least as large as the constant's
original width, and that if the constant was originally unsigned then the
finaltype should also be unsigned.  If these conditions are not met, expansion
fails with fatal warnings.</p>

<p>The new atom we build, @('x-prime') will have a new @(see vl-constint-p) for
its guts, where the origwidth and origtype have been modified to match the
final width and type of the atom.  We have no choice but to do this in the case
of a true sign extension, because the new value might not fit into the original
width.  So for consistency we do it in all cases.  <b>BOZO</b> having
@(':finalwidth') and @(':finaltype') fields for atoms seems somewhat redundant
if we are changing the width and type of the guts.  We could consider forcing
these fields to either be nil or to agree with the constint's width/type (and
similarly for weirdints).  Otherwise we can make this part of well-typed
expressions, but I'm partial to the former.</p>

<h3>Compatibility Warnings</h3>

<p>In certain cases we issue non-fatal \"compatibility warnings\" to say that
an expression might have different values on different Verilog implementations.
It is scary to expand originally-unsized numbers (most frequently plain decimal
numbers) past 32-bits because this could perhaps result in
implementation-dependent behavior.  For instance, consider:</p>

@({
wire signed [47:0] foo, bar;
assign bar = ...;
assign foo = bar + 'h 8000_0000 ;  // bar + 2^31
})

<p>Suppose @('bar') is zero.  On a 32-bit system, the 2^31 represents a
negative number, so when we sign-extend it to 48 bits we get
@('FFFF_8000_0000').  The final value of @('foo') is thus @('FFFF_8000_0000').
But on a 64-bit system, the 2^31 represents a positive number and we would
instead end up sign-extending @('bar') to 64 bits.  The 64-bit addition
produces @('0000_0000_8000_0000') which is then truncated to 48 bits.  The
final value of @('foo') is thus @('0000_8000_0000'), which does not match the
32-bit implementation.</p>

<p>So, when can these kinds of problems arise?</p>

<p>If bar was unsigned, then I think there is no problem because we will need
to zero-extend the 2^31 to 48 bits, which yields @('0000_8000_0000') regardless
of whether we are on a 32-bit, 64-bit, or other-bit implementation.</p>

<p>I once imagined that the sign-bit of the constant had to be 1 to cause
problems, but it is still possible to demonstrate a compatibility problem with
a zero sign bit.  On the other hand, because examples I can think of seem to
rely upon shift operations and hence be relatively unlikely, I mark these as
minor warnings.  Here is an example of such a problem:</p>

@({
wire signed [47:0] foo, bar;
assign bar = ...;
assign foo = (bar + 5) >> 1;
})

<p>Suppose bar is @('FFFF_FFFF_FFFF').  On the 64-bit implementation, the
addition produces is done in 64 bits and produces @('1_0000_0000_0004'), which
is then shifted to obtain @('8000_0000_0002').  On a 32-bit implementation, the
addition is only done in 48 bits and the carry is lost, so the sum is @('4')
and the final result is @('2').</p>"

; BOZO can we push the sanity checks into the guard?

  (local (defthm l0
           (implies (and (< x (expt 2 a))
                         (< a b)
                         (natp a)
                         (natp b)
                         (natp x))
                    (< x (expt 2 b)))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthm l1
           (implies (and (<= (vl-constint->origwidth x) finalwidth)
                         (force (vl-constint-p x))
                         (force (natp finalwidth)))
                    (<= (vl-constint->value x)
                        (expt 2 finalwidth)))
           :rule-classes ((:rewrite) (:linear))))

  (local (include-book "arithmetic-3/bind-free/top" :dir :system))

  (defund vl-constint-atom-expandsizes (x finalwidth finaltype elem warnings)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-fast-constint-p (vl-atom->guts x))
                                (natp finalwidth)
                                (vl-exprtype-p finaltype)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))
         ((vl-constint guts) guts)

         ((when (> guts.origwidth finalwidth))
          ;; Sanity check.  This must never happen because the finalwidth of
          ;; the expression is the maximum of any operand's size.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x)
                   :fatalp t
                   :fn 'vl-constint-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((unless (or (eq guts.origtype finaltype)
                      (and (eq guts.origtype :vl-signed)
                           (eq finaltype :vl-unsigned))))
          ;; Sanity check.  This must never happen because the finaltype of the
          ;; expression must be unsigned if any operand was unsigned.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                         expanding ~a3.  This indicates a serious bug in our ~
                         typing code."
                   :args (list elem guts.origtype finaltype x)
                   :fatalp t
                   :fn 'vl-constint-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((when (= guts.origwidth finalwidth))
          ;; No expansion is necessary.  We build a new guts that has the
          ;; desired type.  This might be converting signed into unsigned, but
          ;; since there's no extension there's no change to the value.
          (b* ((new-guts (if (eq guts.origtype finaltype)
                             guts
                           (change-vl-constint guts
                                               :origwidth finalwidth
                                               :origtype finaltype)))
               (new-x    (change-vl-atom x
                                         :guts new-guts
                                         :finalwidth finalwidth
                                         :finaltype finaltype)))
            (mv t warnings new-x)))

         ;; If we get this far, expansion is necessary.
         ((when (eq finaltype :vl-unsigned))
          ;; Just do a zero-extension.
          (b* ((new-guts (change-vl-constint guts
                                             :origwidth finalwidth
                                             :origtype finaltype))
               (new-x    (change-vl-atom x
                                         :guts new-guts
                                         :finalwidth finalwidth
                                         :finaltype finaltype)))
            (mv t warnings new-x)))

         ;; Else, we want a sign-extension.
         (new-value (vl-sign-extend-constint guts.value guts.origwidth finalwidth))
         (new-guts  (change-vl-constint guts
                                        :value new-value
                                        :origwidth finalwidth))
         (new-x     (change-vl-atom x
                                    :guts new-guts
                                    :finalwidth finalwidth
                                    :finaltype finaltype))

         ((unless guts.wasunsized)
          (mv t warnings new-x))

         ;; Unsized, signed value being extended -- we add a special warning,
         (minorp (= new-value guts.value))
         (w (make-vl-warning
             :type (if minorp
                       :vl-warn-integer-size-minor
                     :vl-warn-integer-size)
             :msg (if minorp
                      "~a0: the unsized integer ~a1 occurs in a context that ~
                      is larger than 32-bits.  In rare cases (particularly ~
                      involving right-shifts), the resulting expression may ~
                      produce different results on Verilog implementations ~
                      with different integer sizes; consider adding an ~
                      explicit size to this number."
                    "~a0: the unsized integer ~a1 occurs in a signed context ~
                    that is larger than 32-bits; it is likely that this could ~
                    cause the expression results to differ between Verilog ~
                    implementations that have different integer sizes.  ~
                    Adding an explicit size to this number is recommended.")
             :args (list elem x)
             :fatalp nil
             :fn 'vl-constint-atom-expandsizes)))
      (mv t (cons w warnings) new-x)))

  (local (in-theory (enable vl-constint-atom-expandsizes)))

  (defthm vl-warninglist-p-of-vl-constint-atom-expandsizes
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-constint-atom-expandsizes x finalwidth finaltype elem
                                                      warnings)))))

  (defthm warning-irrelevance-of-vl-constint-atom-expandsizes
    (let ((ret1 (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-constint-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defthm vl-expr-p-of-vl-constint-atom-expandsizes
    (implies (and (force (vl-atom-p x))
                  (force (vl-constint-p (vl-atom->guts x)))
                  (force (natp finalwidth))
                  (force (vl-exprtype-p finaltype)))
             (vl-expr-p
              (mv-nth 2 (vl-constint-atom-expandsizes x finalwidth finaltype elem
                                                      warnings)))))

  (defthm no-change-loserp-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x))))

  (defthm vl-expr-welltyped-p-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p))))

  (defthm vl-expr->finalwidth-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      finalwidth))))

  (defthm vl-expr->finaltype-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      finaltype)))))




(defsection vl-weirdint-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-weirdint-atom-expandsizes) returns @('(mv
successp warnings x-prime)').</p>

<p>See @(see vl-constint-atom-expandsizes); this function is the same except
that it deals with @(see vl-weirdint-p)s.</p>"

; BOZO can we push the sanity checks into the guard?

  (defund vl-weirdint-atom-expandsizes (x finalwidth finaltype elem warnings)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-fast-weirdint-p (vl-atom->guts x))
                                (natp finalwidth)
                                (vl-exprtype-p finaltype)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))
         ((vl-weirdint guts) guts)

         ((when (> guts.origwidth finalwidth))
          ;; Sanity check.  This must never happen because the finalwidth of
          ;; the expression is the maximum of any operand's size.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x)
                   :fatalp t
                   :fn 'vl-weirdint-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((unless (or (eq guts.origtype finaltype)
                      (and (eq guts.origtype :vl-signed)
                           (eq finaltype :vl-unsigned))))
          ;; Sanity check.  This must never happen because the finaltype of the
          ;; expression must be unsigned if any operand was unsigned.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                         expanding ~a3.  This indicates a serious bug in our ~
                         typing code."
                   :args (list elem guts.origtype finaltype x)
                   :fatalp t
                   :fn 'vl-weirdint-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((when (= guts.origwidth finalwidth))
          ;; No expansion is necessary.  We build a new guts that has the
          ;; desired type.  This might be converting signed into unsigned, but
          ;; since there's no extension there's no change to the value.
          (b* ((new-guts (if (eq guts.origtype finaltype)
                             guts
                           (change-vl-weirdint guts
                                               :origwidth finalwidth
                                               :origtype finaltype)))
               (new-x    (change-vl-atom x
                                         :guts new-guts
                                         :finalwidth finalwidth
                                         :finaltype finaltype)))
            (mv t warnings new-x)))

         ;; If we get this far, expansion is necessary.  If the finaltype is
         ;; signed, then by our above check we know that the origtype is also
         ;; signed, and we want to do a sign-extension.
         ((when (eq finaltype :vl-unsigned))
          ;; Just do a zero-extension.
          (b* ((new-bits (append (repeat :vl-0val (- finalwidth guts.origwidth))
                                 (redundant-list-fix guts.bits)))
               (new-guts (change-vl-weirdint guts
                                             :bits new-bits
                                             :origwidth finalwidth
                                             :origtype finaltype))
               (new-x    (change-vl-atom x
                                         :guts new-guts
                                         :finalwidth finalwidth
                                         :finaltype finaltype)))
            (mv t warnings new-x)))

         ;; Else, we want a sign-extension.
         (sign-bit  (car guts.bits))
         (new-bits  (append (repeat sign-bit (- finalwidth guts.origwidth))
                            (redundant-list-fix guts.bits)))
         (new-guts  (change-vl-weirdint guts
                                        :bits new-bits
                                        :origwidth finalwidth))
         (new-x     (change-vl-atom x
                                    :guts new-guts
                                    :finalwidth finalwidth
                                    :finaltype finaltype))

         ((unless guts.wasunsized)
          (mv t warnings new-x))

         ;; Unsized, signed value being extended -- we add a special warning,

         (minorp (eq sign-bit :vl-0val))
         (w (make-vl-warning
             :type (if minorp
                       :vl-warn-integer-size-minor
                     :vl-warn-integer-size)
             :msg (if minorp
                     "~a0: the unsized integer ~a1 occurs in a context that ~
                      is larger than 32-bits.  In rare cases (particularly ~
                      involving right-shifts), the resulting expression may ~
                      produce different results on Verilog implementations ~
                      with different integer sizes; consider adding an ~
                      explicit size to this number."
                   "~a0: the unsized integer ~a1 occurs in a signed context ~
                    that is larger than 32-bits; it is likely that this could ~
                    cause the expression results to differ between Verilog ~
                    implementations that have different integer sizes.  ~
                    Adding an explicit size to this number is recommended.")
             :args (list elem x)
             :fatalp nil
             :fn 'vl-weirdint-atom-expandsizes)))
      (mv t (cons w warnings) new-x)))

  (local (in-theory (enable vl-weirdint-atom-expandsizes)))

  (defthm vl-warninglist-p-of-vl-weirdint-atom-expandsizes
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem
                                                      warnings)))))

  (defthm warning-irrelevance-of-vl-weirdint-atom-expandsizes
    (let ((ret1 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defthm no-change-loserp-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x))))

  (defthm vl-expr-p-of-vl-weirdint-atom-expandsizes
    (implies (and (force (vl-atom-p x))
                  (force (vl-weirdint-p (vl-atom->guts x)))
                  (force (natp finalwidth))
                  (force (vl-exprtype-p finaltype)))
             (vl-expr-p
              (mv-nth 2 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem
                                                      warnings)))))

  (defthm vl-expr-welltyped-p-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p))))

  (defthm vl-expr->finalwidth-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      finalwidth))))

  (defthm vl-expr->finaltype-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      finaltype)))))




(defsection vl-idatom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into an
identifier atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-idatom-expandsizes) returns @('(mv successp
warnings x-prime)').</p>"

; BOZO can we push the sanity checks into the guard?

  (defund vl-idatom-expandsizes (x finalwidth finaltype mod ialist elem warnings)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-fast-id-p (vl-atom->guts x))
                                (natp finalwidth)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-exprtype-p finaltype)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))
         (name (vl-id->name guts))

         ((mv warnings origwidth) (vl-atom-selfsize x mod ialist elem warnings))
         ((mv warnings origtype)  (vl-atom-typedecide x mod ialist elem warnings))

         ((unless (and origwidth origtype))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: expected to only try to expand sizes for atoms ~
                         whose sizes types can be successfully determined, ~
                         but we failed to determine the size or type of ~w1."
                   :args (list elem name)
                   :fatalp t
                   :fn 'vl-idatom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((when (> origwidth finalwidth))
          ;; Sanity check.  This must never happen because the finalwidth of
          ;; the expression is the maximum of any operand's size.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x)
                   :fatalp t
                   :fn 'vl-idatom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((unless (or (eq origtype finaltype)
                      (and (eq origtype :vl-signed)
                           (eq finaltype :vl-unsigned))))
          ;; Sanity check.  This must never happen because the finaltype of the
          ;; expression must be unsigned if any operand was unsigned.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                         expanding ~a3.  This indicates a serious bug in our ~
                         typing code."
                   :args (list elem origtype finaltype x)
                   :fatalp t
                   :fn 'vl-idatom-expandsizes)))
            (mv nil (cons w warnings) x)))

; BOZO This discussion needs to move into the basic documentation for
; expressions.

         ;; Okay, otherwise some kind of valid extension is taking place.  There
         ;; is nothing to do to the guts (an identifier is just an identifier and
         ;; has no widths of its own).  So, we have two options.
         ;;
         ;;  (1) we can build a new expression that explicitly represents the
         ;;      extension that is taking place, e.g., to zero-extend "foo" from
         ;;      3 bits to 5 bits, we might write an expression like {2'b0,foo},
         ;;      or
         ;;
         ;;  (2) we can just write the final width and type into the atom, and
         ;;      say that each atom involving an identifier implicitly contains
         ;;      a zero-extension or sign-extension to its finalwidth.
         ;;
         ;; Even though it is arguably subtle, we go with option 2 because
         ;; there doesn't seem to be any good way to carry out option 1 for
         ;; signed values.  That is, how do you sign-extend a signed
         ;; identifier?  You might try to write, say, {{{2{foo[3]}, foo}, but
         ;; concatenations in Verilog are always unsigned so the signedness of
         ;; the result is lost.  We could perhaps remedy this by adding more
         ;; operators, but that seems complicated.  So, I prefer to just say
         ;; that the finalwidth of the atom has the final say.

; BOZO add a warning about integer variables getting sign-extended

         (new-x (change-vl-atom x
                                :finalwidth finalwidth
                                :finaltype finaltype)))
      (mv t warnings new-x)))

  (local (in-theory (enable vl-idatom-expandsizes)))

  (defthm vl-warninglist-p-of-vl-idatom-expandsizes
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-idatom-expandsizes x finalwidth finaltype mod ialist
                                               elem warnings)))))

  (defthm warning-irrelevance-of-vl-idatom-expandsizes
    (let ((ret1 (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings))
          (ret2 (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defthm no-change-loserp-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist
                                      elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x))))

  (defthm vl-expr-p-of-vl-idatom-expandsizes
    (implies (and (force (vl-atom-p x))
                  (force (vl-id-p (vl-atom->guts x)))
                  (force (natp finalwidth))
                  (force (vl-exprtype-p finaltype))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-expr-p
              (mv-nth 2 (vl-idatom-expandsizes x finalwidth finaltype mod ialist
                                               elem warnings)))))

  (defthm vl-expr-welltyped-p-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-atom-welltyped-p
                                      vl-expr-welltyped-p
                                      ;; ugly, but we need to see that the atom size
                                      ;; is non-zero.
                                      vl-atom-selfsize))))

  (defthm vl-expr->finalwidth-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      finalwidth))))

  (defthm vl-expr->finaltype-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      finaltype)))))




(defsection vl-string-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-string-atom-expandsizes) returns @('(mv successp
warnings x-prime)').</p>

<p>See @(see vl-constint-atom-expandsizes); this function is the same except
that it deals with @(see vl-string-p)s.</p>"

; BOZO can we push the sanity checks into the guard?

  (defund vl-string-atom-expandsizes (x finalwidth finaltype elem warnings)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (vl-fast-string-p (vl-atom->guts x))
                                (natp finalwidth)
                                (vl-exprtype-p finaltype)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))
         ((vl-string guts) guts)

         (origwidth (* 8 (length guts.value)))

         ((when (> origwidth finalwidth))
          ;; Sanity check.  This must never happen because the finalwidth of
          ;; the expression is the maximum of any operand's size.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x)
                   :fatalp t
                   :fn 'vl-string-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ((unless (eq finaltype :vl-unsigned))
          ;; Sanity check.  This must never happen because the finaltype of the
          ;; expression must be unsigned if any operand was unsigned.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: finaltype is ~s1 when expanding ~a2.  This ~
                         indicates a serious bug in our sizing/typing code."
                   :args (list elem finaltype x)
                   :fatalp t
                   :fn 'vl-string-atom-expandsizes)))
            (mv nil (cons w warnings) x)))

         ;; Otherwise, everything is fine.  The finalwidth that we want is at
         ;; least as large as origwidth.  From 3.6.2, if we need to expand the
         ;; string, we are supposed to basically jam zero-bits (not the '0'
         ;; character) into the left side of it until it's the desired width.
         ;; We'll actually go ahead and leave the atom alone so that it agrees
         ;; with its contents about its width, and use our explicit zero-extend
         ;; function to perform the extension by adding a concatenation, if
         ;; necessary.
         (inner (change-vl-atom x
                                :finalwidth origwidth
                                :finaltype :vl-unsigned))
         ((mv successp warnings new-x)
          (vl-expandsizes-zeroextend inner finalwidth elem warnings))

         ((unless successp)
          (mv nil warnings x)))

      (mv t warnings new-x)))

  (local (in-theory (enable vl-string-atom-expandsizes)))

  (defthm vl-warninglist-p-of-vl-string-atom-expandsizes
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-string-atom-expandsizes x finalwidth finaltype elem
                                                      warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm warning-irrelevance-of-vl-string-atom-expandsizes
    (let ((ret1 (vl-string-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-string-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2)))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm no-change-loserp-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-expr-p-of-vl-string-atom-expandsizes
    (implies (and (force (vl-atom-p x))
                  (force (vl-string-p (vl-atom->guts x)))
                  (force (natp finalwidth))
                  (force (vl-exprtype-p finaltype)))
             (vl-expr-p
              (mv-nth 2 (vl-string-atom-expandsizes x finalwidth finaltype elem
                                                      warnings)))))

  (defthm vl-expr-welltyped-p-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p))))

  (defthm vl-expr->finalwidth-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      finalwidth))))

  (defthm vl-expr->finaltype-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x)))
                    (force (natp finalwidth))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      finaltype)))))


(defsection vl-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into an atom."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p><b>Signature:</b> @(call vl-atom-expandsizes) returns @('(mv successp
warnings x-prime)').</p>"

  (defund vl-atom-expandsizes (x finalwidth finaltype mod ialist elem warnings)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-atom-p x)
                                (natp finalwidth)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-exprtype-p finaltype)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((guts (vl-atom->guts x))
         ((when (vl-fast-constint-p guts))
          (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings))
         ((when (vl-fast-weirdint-p guts))
          (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings))
         ((when (vl-fast-id-p guts))
          (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings))
         ((when (vl-fast-string-p guts))
          (vl-string-atom-expandsizes x finalwidth finaltype elem warnings))
         ;; Otherwise, we shouldn't have tried to size this.
         (w (make-vl-warning
             :type :vl-programming-error
             :msg "~a0: expected to only try to expand sizes for atoms whose ~
                 self-sizes and types can be successfully determined, but we ~
                 are trying to expand an atom of type ~x1: ~a2."
             :args (list elem (tag guts) x)
             :fatalp t
             :fn 'vl-atom-expandsizes)))
      (mv nil (cons w warnings) x)))

  (local (in-theory (enable vl-atom-expandsizes)))

  (defthm vl-warninglist-p-of-vl-atom-expandsizes
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-atom-expandsizes x finalwidth finaltype mod ialist
                                             elem warnings)))))

  (defthm no-change-loserp-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret) x)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-expr-p-of-vl-atom-expandsizes
    (implies (and (force (vl-atom-p x))
                  (force (natp finalwidth))
                  (force (vl-exprtype-p finaltype))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-expr-p
              (mv-nth 2 (vl-atom-expandsizes x finalwidth finaltype mod ialist
                                             elem warnings)))))

  (defthm vl-expr-welltyped-p-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (natp finalwidth))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod)))
                    (force (vl-exprtype-p finaltype)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :hints(("Goal" :in-theory (enable vl-atom-welltyped-p vl-expr-welltyped-p))))

  (defthm vl-expr->finalwidth-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (natp finalwidth))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod)))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      finalwidth))))

  (defthm vl-expr->finaltype-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (natp finalwidth))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod)))
                    (force (vl-exprtype-p finaltype)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      finaltype)))))



(defsection vl-warn-about-signed-shifts
  :parents (vl-expr-typedecide)
  :short "Special warnings about shifting by signed amounts."
  :long "<p>See @(see expression-sizing-minutia); we warn about shifts by
a signed value since Verilog-XL doesn't handle them correctly.</p>"

  (defund vl-warn-about-signed-shifts (rhs elem warnings)
    "Returns WARNINGS'"
    (declare (xargs :guard (and (vl-expr-p rhs)
                                (vl-expr->finaltype rhs)
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings))))
    (b* ((want-to-warn-p
          ;; The idea here is to warn if the RHS is signed, unless it's a plain
          ;; constant whose sign-bit is 0 (since in that case Verilog-XL isn't
          ;; broken, and we don't want tons of noise about "foo >> 1," etc.
          (b* (((unless (eq (vl-expr->finaltype rhs) :vl-signed))
                nil)
               ((unless (vl-fast-atom-p rhs))
                t)
               (guts (vl-atom->guts rhs))
               ((unless (vl-constint-p guts))
                t)
               (val   (vl-constint->value guts))
               (width (vl-constint->origwidth guts)))
            (logbitp (- width 1) val)))

         ((unless want-to-warn-p)
          warnings))

      (cons (make-vl-warning
             :type :vl-warn-signed-shift
             :msg "~a0: found a shift-expression with a signed shift amount, ~
                   ~a1.  This is dangerous because whereas NCVerilog properly ~
                   follows the Verilog standard (5.1.12) and treats the ~
                   right-hand side as unsigned, Verilog-XL incorrectly treats ~
                   negative right-shifts as left-shifts.  We follow the ~
                   standard and mimick NCVerilog, but to ensure ~
                   compatibility, you should probably rewrite this expression ~
                   to ensure that the right-hand side is unsigned.  For ~
                   example, you might wrap the right-hand side in a ~
                   concatnation, e.g., \"a >> {b}\" instead of \"a >> b\"."
             :args (list elem rhs)
             :fatalp nil
             :fn 'vl-warn-about-signed-shifts)
            warnings)))

  (local (in-theory (enable vl-warn-about-signed-shifts)))

  (defthm vl-warninglist-p-of-vl-warn-about-signed-shifts
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-warn-about-signed-shifts rhs elem warnings)))))




(defsection vl-warn-about-implicit-extension

; Extension warnings are very, very good to have, and have found a lot of bugs.
; However, we need to be pretty clever to avoid getting too many trivial,
; nitpicky complaints about assignments that aren't really bugs.
;
; We found that extension warnings were frequently triggered by things like
; "assign {carry,sum} = a + b" where the designer seems to explicitly intend to
; get the carry bit.  We therefore only cause a minor warning if the right-hand
; side is composed only of additions.  Later it turned out we need to permit
; selects, too.  And later we decided to also add subtraction as a permitted
; operation.
;
; Another kind of extension warning that is stupidly minor is when we just have
; assignments like "assign foo[127:0] = 0;".  We now do not even create a minor
; warning for assignments where the rhs is a constant.

  (defund vl-warn-about-implicit-extension (lhs-size x-selfsize x mod ialist elem warnings)
    (declare (xargs :guard (and (natp lhs-size)
                                (natp x-selfsize)
                                (vl-expr-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-modelement-p elem)
                                (vl-warninglist-p warnings)))

             ;; We add these in case we want to look at sizes of subexpressions
             ;; in the future.
             (ignorable lhs-size mod ialist))

; We assume that LHS-SIZE is greater than the size of X, so we are going to
; issue an extension warning.  We need to determine what kind of warning to
; issue.  Note that this can be pretty inefficient since we only call it
; infrequently.

    (b* ((ops     (vl-expr-ops x))

         ((when (and (vl-fast-atom-p x)
                     (vl-constint-p (vl-atom->guts x))
                     (vl-constint->wasunsized (vl-atom->guts x))))
          ;; Completely trivial, don't give any warning.
          warnings)

         (minorp (and (or (member-equal :vl-binary-plus ops)
                          (member-equal :vl-binary-minus ops))
                      (subsetp-equal ops '(:vl-binary-plus
                                           :vl-binary-minus
                                           :vl-partselect-colon
                                           :vl-bitselect))))

         (w (make-vl-warning
             :type (if minorp
                       :vl-warn-extension-minor
                     :vl-warn-extension)
             :msg "~a0: implicit extension from ~x1-bit expression to ~x2-bit ~
                 lvalue.~%     rhs: ~a3"
             :args (list elem x-selfsize lhs-size x)
             :fatalp nil
             :fn 'vl-expr-size)))
      (cons w warnings)))

  (local (in-theory (enable vl-warn-about-implicit-extension)))

  (defthm vl-warninglist-p-of-vl-warn-about-implicit-extension
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-warn-about-implicit-extension
                                lhs-size x-selfsize x mod ialist elem warnings)))))




(defsection vl-expr-size
  :parents (expression-sizing)
  :short "Top-level expression-sizing function."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>This is our main, mutually-recursive collection of functions for sizing
expressions.  Each of these has several arguments in common:</p>

<ul>

<li>@('x'), an expression (or expression list) that we want to size;</li>

<li>@('mod'), the module in which @('x') occurs; we use this to look up wire
widths;</li>

<li>@('ialist'), the @(see vl-moditem-alist) for @('mod'), so that we can
perform fast lookups;</li>

<li>@('elem'), a @(see vl-modelement-p) which is semantically irrelevant and
only provides a context for warnings;</li>

<li>@('warnings'), an ordinary @(see warnings) accumulator, which we may extend
with fatal or non-fatal warnings.</li>

</ul>

<p>And each function returns @('(mv successp warnings x-prime)'), where
@('successp') indicates whether all sizing was successful, @('warnings') is the
updated warnings accumulator, and @('x-prime') is essentially @('(if successp x
sized-x)').  That is, on failure we do not modify @('x'), but on success we
returned a new version of @('x') where all the sizes and types have been
computed.</p>

<p>There are four functions in the recursion.</p>

<dl>

<dt>@(call vl-expr-size)</dt>

<dd>Here, the @('lhs-size') is a @(see maybe-natp).  To size an expression
@('x') which occurs in an assignment such as @('assign lhs = x'), the
@('lhs-size') should be the width of @('lhs').  To size other expressions that
do not occur in assignments, such as a self-determined subexpression, the
@('lhs-size') should be nil.</dd>

<dd>This function implements the two-phase algorithm described in @(see
expression-sizing).  That is, it first determines the maximum size of any
operand in @('x') and the desired type of @('x'), using @(see vl-expr-selfsize)
and @(see vl-expr-typedecide) (which are not part of the mutual recursion).  It
then propagates this size and type into the operands, using
@('vl-expr-expandsizes').</dd>

<dt>@(call vl-expr-expandsizes)</dt>

<dd>This function carries out the propagation phase.  We are given the
@('finalwidth') and @('finaltype') that have been determined by the first phase
of the sizing algorithm, and we must expand every context-determined operand to
match this finalwidth and finaltype.</dd>

<dt>@(call vl-exprlist-size)</dt>

<dd>Here, @('x') should be a list of self-determined expressions.  We use
@('vl-expr-size') (with @('lhs-size = nil')) to size each of the expressions in
@('x').</dd>

<dt>@(call vl-exprlist-expandsizes)</dt>

<dd>Here, @('x') should be a list of context-determined expressions.  We use
@('vl-expr-expandsizes') to expand the operands within each member of @('x') to
the desired @('finalwidth') and @('finaltype').</dd>

</dl>"

  (defxdoc vl-exprlist-size
    :parents (vl-expr-size)
    :short "Size a list of self-determined expressions."
    :long "<p>See @(see vl-expr-size) for documentation.</p>")

  (defxdoc vl-expr-expandsizes
    :parents (vl-expr-size)
    :short "Propagate the final width/type into the operands of a
context-determined expression."
    :long "<p>See @(see vl-expr-size) for documentation.</p>")

  (defxdoc vl-exprlist-expandsizes
    :parents (vl-expr-size)
    :short "Propagate the final width/type into the operands of a list of
context-determined expressions."
    :long "<p>See @(see vl-expr-size) for documentation.</p>")


; BOZO we might be able to strengthen the guards here so that we don't need to
; explicitly check for signed finalwidths in unsigned operators like compares.
; But I'm not sure exactly how this would work, yet.

  (mutual-recursion

 (defund vl-expr-size (lhs-size x mod ialist elem warnings)
   "Determine sizes for a top-level or self-determined expression.
    Returns (MV SUCCESSP WARNINGS X-PRIME)"
   (declare (xargs :guard (and (maybe-natp lhs-size)
                               (vl-expr-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod))
                               (vl-modelement-p elem)
                               (vl-warninglist-p warnings))
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 2)))

   (b* (;; Phase 1, determine maximum size of any operand within X, and the
        ;; final expression type of X.
        ((mv warnings x-selfsize)
         (vl-expr-selfsize x mod ialist elem warnings))
        ((mv warnings finaltype)
         (vl-expr-typedecide x mod ialist elem warnings))
        ((unless (and x-selfsize finaltype))
         (mv nil warnings x))

        ;; The finalwidth we will is either (1) the maximum size of any operand
        ;; in X, which we computed above as x-selfsize, or (2) the size of the
        ;; lhs expression, whichever is larger.
        (finalwidth (max (nfix lhs-size) x-selfsize))

        (warnings
         ;; We warn here about implicit extensions.  Truncation warnings get
         ;; handled when we size assignments, below.
         (b* (((unless (and (natp lhs-size)
                            (> lhs-size x-selfsize)))
               ;; Not an extension
               warnings))
           (vl-warn-about-implicit-extension lhs-size x-selfsize
                                             x mod ialist elem warnings))))

     ;; Phase 2, propagate desired final width and type of the expression
     ;; into its context-determined operands.
     (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings)))

 (defund vl-exprlist-size (x mod ialist elem warnings)
   "Self-determine sizes of a list of expressions.
    Returns (MV SUCCESSP WARNINGS X-PRIME)"
   (declare (xargs :guard (and (vl-exprlist-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod))
                               (vl-modelement-p elem)
                               (vl-warninglist-p warnings))
                   :measure (two-nats-measure (acl2-count x) 0)))
   (b* (((when (atom x))
         (mv t warnings nil))
        ((mv car-successp warnings car-prime)
         (vl-expr-size nil (car x) mod ialist elem warnings))
        ((mv cdr-successp warnings cdr-prime)
         (vl-exprlist-size (cdr x) mod ialist elem warnings)))
     (mv (and car-successp cdr-successp)
         warnings
         (cons car-prime cdr-prime))))

 (defund vl-exprlist-expandsizes (x finalwidth finaltype mod ialist elem warnings)
   "Propagate final width/type into a list of context-determined expressions.
    Returns (MV SUCCESSP WARNINGS X-PRIME)"
   (declare (xargs :guard (and (vl-exprlist-p x)
                               (natp finalwidth)
                               (vl-exprtype-p finaltype)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod))
                               (vl-modelement-p elem)
                               (vl-warninglist-p warnings))
                   :measure (two-nats-measure (acl2-count x) 0)))
   (b* (((when (atom x))
         (mv t warnings nil))
        ((mv car-successp warnings car-prime)
         (vl-expr-expandsizes (car x) finalwidth finaltype mod ialist elem warnings))
        ((mv cdr-successp warnings cdr-prime)
         (vl-exprlist-expandsizes (cdr x) finalwidth finaltype mod ialist elem warnings)))
     (mv (and car-successp cdr-successp)
         warnings
         (cons car-prime cdr-prime))))

 (defund vl-expr-expandsizes (x finalwidth finaltype mod ialist elem warnings)
   "Propagate the final width/type into a context-determined expression.
    Returns (MV SUCCESSP WARNINGS X-PRIME)"
   (declare (xargs :guard (and (vl-expr-p x)
                               (natp finalwidth)
                               (vl-exprtype-p finaltype)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod))
                               (vl-modelement-p elem)
                               (vl-warninglist-p warnings))
                   :measure (two-nats-measure (acl2-count x) 1)))

   (b* (((when (vl-fast-atom-p x))
         (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings))
        ((unless (mbt (consp x)))
         (mv (er hard 'vl-expr-expandsizes "Termination hack") warnings x))
        (op   (vl-nonatom->op x))
        (args (vl-nonatom->args x)))

     (case op

       ((;; Table 5-22, Lines 3 and 4.
         :vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
         :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
         :vl-binary-xnor :vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
        ;; Operands are all context-determined.
        (b* (((unless (posp finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ~x1 expression has zero width: ~a2."
                       :args (list elem op x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-expandsizes args finalwidth finaltype mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             (new-x (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth finalwidth
                                       :finaltype finaltype)))
          ;; new-x already has the right size, no need to zero-extend.
          (mv t warnings new-x)))


       ((;; Table 5-22, Line 5.
         :vl-binary-ceq :vl-binary-cne :vl-binary-eq :vl-binary-neq
         :vl-binary-gt :vl-binary-gte :vl-binary-lt :vl-binary-lte)
        ;; Trickiest case.  The two operands "shall affect each other as if
        ;; they were context-determined operands with a result type and size
        ;; (maximum of the two operand sizes) determined from them.  However,
        ;; the actual result type shall always be 1 bit unsigned."
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed comparison result???  Serious bug in ~
                             our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ;; Determine the maximum width of any operand in a/b and also
             ;; whether they are signed or unsigned.
             (a (first args))
             (b (second args))
             ((mv warnings a-selfsize) (vl-expr-selfsize a mod ialist elem warnings))
             ((mv warnings b-selfsize) (vl-expr-selfsize b mod ialist elem warnings))
             ((mv warnings a-type)     (vl-expr-typedecide a mod ialist elem warnings))
             ((mv warnings b-type)     (vl-expr-typedecide b mod ialist elem warnings))
             (a-goodp                  (and (posp a-selfsize) a-type))
             (b-goodp                  (and (posp b-selfsize) b-type))
             ((unless (and a-goodp b-goodp))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed ~s1 of comparison expression ~a2."
                       :args (list elem
                                   (cond (a-goodp "right-hand side")
                                         (b-goodp "left-hand side")
                                         (t       "left- and right-hand sides"))
                                   x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             ;; Expand the operands to the appropriate inner width/type.
             (innerwidth (max a-selfsize b-selfsize))
             (innertype  (vl-exprtype-max a-type b-type))
             ((mv successp warnings args-prime)
              (vl-exprlist-expandsizes args innerwidth innertype mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth 1
                                       :finaltype :vl-unsigned))
             ;; Inner is only one bit, so we may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))

       ((;; Table 5-22, Line 6.
         :vl-binary-logand :vl-binary-logor)
        ;; Both operands are self-determined.  We think the result is one-bit
        ;; unsigned; see "minutia"
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed logical op result???  Serious bug in ~
                             our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (a (first args))
             (b (second args))
             ((mv a-successp warnings a-prime)
              (vl-expr-size nil a mod ialist elem warnings))
             ((mv b-successp warnings b-prime)
              (vl-expr-size nil b mod ialist elem warnings))
             ((unless (and a-successp b-successp))
              (mv nil warnings x))
             (a-goodp (and (posp (vl-expr->finalwidth a-prime))
                           (vl-expr->finaltype a-prime)))
             (b-goodp (and (posp (vl-expr->finalwidth b-prime))
                           (vl-expr->finaltype b-prime)))
             ((unless (and a-goodp b-goodp))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed ~s1 of logical expression ~a2."
                       :args (list elem
                                   (cond (a-goodp "right-hand side")
                                         (b-goodp "left-hand side")
                                         (t       "left- and right-hand sides"))
                                   x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :args (list a-prime b-prime)
                                       :finalwidth 1
                                       :finaltype :vl-unsigned))
             ;; Inner is only one bit, so we may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))


       ((;; Table 5-22, Line 7.
         :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
         :vl-unary-xor :vl-unary-xnor :vl-unary-lognot)
        ;; The operand is self-determined.  We think the result is one-bit
        ;; unsigned; see "minutia"
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed logical/reduction op result???  ~
                             Serious bug in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (a (first args))
             ((mv successp warnings a-prime)
              (vl-expr-size nil a mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             ((unless (and (posp (vl-expr->finalwidth a-prime))
                           (vl-expr->finaltype a-prime)))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed argument in ~x1 expression ~a2."
                       :args (list elem op x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :args (list a-prime)
                                       :finalwidth 1
                                       :finaltype :vl-unsigned))
             ;; Inner is only one bit, so we may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))

       ((;; Table 5-22, Line 8.
         :vl-binary-shr :vl-binary-shl :vl-binary-power
         :vl-binary-ashr :vl-binary-ashl)
        ;; A is context-determined, B is self-determined.
        (b* (((unless (posp finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ~x1 expression has zero width: ~a2."
                       :args (list elem op x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (a (first args))
             (b (second args))
             ((mv a-successp warnings a-prime)
              (vl-expr-expandsizes a finalwidth finaltype mod ialist elem warnings))
             ((mv b-successp warnings b-prime)
              (vl-expr-size nil b mod ialist elem warnings))
             ((unless (and a-successp b-successp))
              (mv nil warnings x))
             ;; We don't require much of B, just that it has a type and that its
             ;; width is positive.
             ((unless (and (posp (vl-expr->finalwidth b-prime))
                           (vl-expr->finaltype b-prime)))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed right-hand side of ~x1 expression ~a2."
                       :args (list elem op x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ;; Special warning about signed shifts in Verilog-XL versus the Spec.
             (warnings (vl-warn-about-signed-shifts b-prime elem warnings))
             (new-x (change-vl-nonatom x
                                       :args (list a-prime b-prime)
                                       :finalwidth finalwidth
                                       :finaltype finaltype)))
          ;; New-x already has the right size, no need to zero-extend.
          (mv t warnings new-x)))

       ((;; Table 5-22, Line 9.
         :vl-qmark)
        ;; A is self-determined, B and C are context-determined.
        (b* (((unless (posp finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: conditional operation with zero width: ~a1."
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (a (first args))
             (b (second args))
             (c (third args))
             ((mv a-successp warnings a-prime)
              (vl-expr-size nil a mod ialist elem warnings))
             ((mv b-successp warnings b-prime)
              (vl-expr-expandsizes b finalwidth finaltype mod ialist elem warnings))
             ((mv c-successp warnings c-prime)
              (vl-expr-expandsizes c finalwidth finaltype mod ialist elem warnings))
             ((unless (and a-successp b-successp c-successp))
              (mv nil warnings x))
             ((unless (and (posp (vl-expr->finalwidth a-prime))
                           (vl-expr->finaltype a-prime)))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed test for conditional operator ~a1"
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (new-x (change-vl-nonatom x
                                       :args (list a-prime b-prime c-prime)
                                       :finalwidth finalwidth
                                       :finaltype finaltype)))
          ;; New-x already has the right size, no need to zero-extend
          (mv t warnings new-x)))

       ((;; Table 5-22, Line 10.
         :vl-concat)
        ;; All arguments self-determined, result is unsigned.
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed concatenation result???  Serious bug ~
                             in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             ;; Inner expression has width = sum of arg widths
             (widths  (vl-exprlist->finalwidths args-prime))
             ((when (member nil widths))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: ill-formed argument in concatenation ~a1.  ~
                             BOZO make this error message better by saying ~
                             which argument is invalid."
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             (inner-width (sum-nats widths))
             ((unless (posp inner-width))
              (b* ((w (make-vl-warning
                       :type :vl-bad-expression
                       :msg "~a0: concatenation with zero total width: ~a1."
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((unless (<= inner-width finalwidth))
              ;; BOZO can we move this into the guard?
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: concatenation width > finalwidth???  ~
                             Serious bug in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth inner-width
                                       :finaltype :vl-unsigned))
             ;; Inner-width can be less than finalwidth; may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))

       ((;; Table 5-22, Line 11.
         :vl-multiconcat)
        ;; All arguments are self-determined and the result is unsigned.  We
        ;; may also need to zero-extend the reuslt to the finalwidth for this
        ;; context.
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed multiconcat result??? Serious bug in ~
                             our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))

             (a (first args-prime))
             (b (second args-prime))

             ((unless (vl-expr-resolved-p a))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: multiconcat with unresolved multiplicity ~
                             should not be encountered here."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             ((unless (and (not (vl-fast-atom-p b))
                           (eq (vl-nonatom->op b) :vl-concat)))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: multple concatenation's second argument ~
                             isn't a concatenation?? ~a1"
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             ((unless (and (posp (vl-expr->finalwidth b))
                           (eq (vl-expr->finaltype b) :vl-unsigned)))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: multiple concat's second argument didn't ~
                             get a unsigned positive result?? serious bug ~
                             in our sizing/typing code.  Expression: ~a1"
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             (inner-width (* (vl-resolved->val a) (vl-expr->finalwidth b)))
             ((unless (<= inner-width finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: multiconcat width > finalwidth??? Serious ~
                             bug in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             ((when (and (= inner-width 0)
                         (< 0 finalwidth)))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: multiconcat width is zero but we want its ~
                             finalwidth to be ~x1??? serious bug in our ~
                             sizing code.  Expr: ~a2"
                       :args (list elem finalwidth x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth inner-width
                                       :finaltype :vl-unsigned))

             ;; Inner-width can be less than finalwidth; may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))

       ((:vl-bitselect)
        ;; Result is necessarily unsigned.  We go ahead and self-size the name
        ;; and indices, which isn't necessarily particularly sensible but seems
        ;; necessary at least for crazy things along the lines of foo[(i + 1)
        ;; >> 2], and helps keep the recursion in our vl-expr-welltyped-p
        ;; recognizer very straightforward.
        (b* (((unless (eq finaltype :vl-unsigned))
              ;; BOZO can this become part of our guard?
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed select result??? Serious bug in our ~
                             sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth 1
                                       :finaltype :vl-unsigned))
             ;; Inner is only one bit, so we may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))


       ((:vl-partselect-colon)
        ;; Result is necessarily unsigned.  We self-size the name and indices
        ;; as in the bitselect case.
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed select result??? Serious bug in our ~
                             sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))

             (left-expr  (second args-prime))
             (right-expr (third args-prime))
             ((unless (and (vl-expr-resolved-p left-expr)
                           (vl-expr-resolved-p right-expr)))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: part-select indices should be resolved."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))

             (inner-width (+ 1 (abs (- (vl-resolved->val left-expr)
                                       (vl-resolved->val right-expr)))))
             ((unless (<= inner-width finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: partselect width > finalwidth??? Serious ~
                             bug in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth inner-width
                                       :finaltype :vl-unsigned))
             ;; Inner-width can be less than finalwidth; may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))


       ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
        ;; Result is necessarily unsigned.  We self-size the name and indices
        ;; as in the bitselect case.
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed select result??? Serious bug in our ~
                             sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             (width-expr (third args-prime))
             ((unless (vl-expr-resolved-p width-expr))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: indexed part-select's width should be resolved."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner-width (vl-resolved->val width-expr))
             ((unless (<= inner-width finalwidth))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: indexed partselect width > finalwidth???  ~
                             Serious bug in our sizing code."
                       :args (list elem)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :args args-prime
                                       :finalwidth inner-width
                                       :finaltype :vl-unsigned))
              ;; Inner-width can be less than finalwidth; may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))

       ((:vl-hid-dot :vl-hid-arraydot)
        (b* (((unless (eq finaltype :vl-unsigned))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: signed HID? Shouldn't generate this: ~a1"
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             ((mv warnings selfsize) (vl-expr-selfsize x mod ialist elem warnings))
             ((mv warnings type)     (vl-expr-typedecide x mod ialist elem warnings))
             ((unless (and (posp selfsize)
                           (<= selfsize finalwidth)
                           (eq type :vl-unsigned)))
              (b* ((w (make-vl-warning
                       :type :vl-programming-error
                       :msg "~a0: bad HID size or type: ~a1"
                       :args (list elem x)
                       :fatalp t
                       :fn 'vl-expr-expandsizes)))
                (mv nil (cons w warnings) x)))
             (inner (change-vl-nonatom x
                                       :finalwidth selfsize
                                       :finaltype :vl-unsigned))
             ;; Inner-width can be less than finalwidth; may need to zero-extend.
             ((mv successp warnings new-x)
              (vl-expandsizes-zeroextend inner finalwidth elem warnings))
             ((unless successp)
              (mv nil warnings x)))
          (mv t warnings new-x)))


       ((:vl-funcall :vl-syscall :vl-mintypmax
                     :vl-array-index)
        (b* ((w (make-vl-warning
                 :type :vl-unsupported
                 :msg "~a0: add sizing support for ~x1."
                 :args (list elem op)
                 :fatalp t
                 :fn 'vl-expr-expandsizes)))
          (mv nil (cons w warnings) x)))

       (otherwise
        (progn$
         (er hard 'vl-expr-expandsizes "Provably impossible")
         (mv nil warnings x))))))))


(flag::make-flag flag-vl-expr-size vl-expr-size)


(defsection lemmas-for-vl-exprlist-size

    (defthm vl-exprlist-size-when-atom
      (implies (atom x)
               (equal (vl-exprlist-size x mod ialist elem warnings)
                      (mv t warnings nil)))
      :hints(("Goal" :in-theory (enable vl-exprlist-size))))

    (defthm vl-exprlist-size-of-cons
      (equal (vl-exprlist-size (cons a x) mod ialist elem warnings)
             (b* (((mv car-successp warnings car-prime)
                   (vl-expr-size nil a mod ialist elem warnings))
                  ((mv cdr-successp warnings cdr-prime)
                   (vl-exprlist-size x mod ialist elem warnings)))
               (mv (and car-successp cdr-successp)
                   warnings
                   (cons car-prime cdr-prime))))
      :hints(("Goal" :in-theory (enable vl-exprlist-size))))

    (local (defun my-induct (x mod ialist elem warnings)
             (b* (((when (atom x))
                   (mv t warnings nil))
                  ((mv car-successp warnings car-prime)
                   (vl-expr-size nil (car x) mod ialist elem warnings))
                  ((mv cdr-successp warnings cdr-prime)
                   (my-induct (cdr x) mod ialist elem warnings)))
               (mv (and car-successp cdr-successp)
                   warnings
                   (cons car-prime cdr-prime)))))

    (defthm len-of-vl-exprlist-size
      (equal (len (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))
             (len x))
      :hints(("Goal" :induct (my-induct x mod ialist elem warnings))))

    (defthm true-listp-of-vl-exprlist-size
      (true-listp (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))
      :rule-classes :type-prescription
      :hints(("Goal" :induct (my-induct x mod ialist elem warnings)))))



(defsection lemmas-for-vl-exprlist-expandsizes

    (defthm vl-exprlist-expandsizes-when-atom
      (implies (atom x)
               (equal (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)
                      (mv t warnings nil)))
      :hints(("Goal" :in-theory (enable vl-exprlist-expandsizes))))

    (defthm vl-exprlist-expandsizes-of-cons
      (equal (vl-exprlist-expandsizes (cons a x) finalwidth finaltype mod ialist elem warnings)
             (b* (((mv car-successp warnings car-prime)
                   (vl-expr-expandsizes a finalwidth finaltype mod ialist elem warnings))
                  ((mv cdr-successp warnings cdr-prime)
                   (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))
               (mv (and car-successp cdr-successp)
                   warnings
                   (cons car-prime cdr-prime))))
      :hints(("Goal" :in-theory (enable vl-exprlist-expandsizes))))

    (local (defun my-induct (x finalwidth finaltype mod ialist elem warnings)
             (b* (((when (atom x))
                   (mv t warnings nil))
                  ((mv car-successp warnings car-prime)
                   (vl-expr-expandsizes (car x) finalwidth finaltype mod ialist elem warnings))
                  ((mv cdr-successp warnings cdr-prime)
                   (my-induct (cdr x) finalwidth finaltype mod ialist elem warnings)))
               (mv (and car-successp cdr-successp)
                   warnings
                   (cons car-prime cdr-prime)))))

    (defthm len-of-vl-exprlist-expandsizes
      (let ((ret (vl-exprlist-expandsizes x finalwidth finaltype mod
                                          ialist elem warnings)))
        (equal (len (mv-nth 2 ret))
               (len x)))
      :hints(("Goal" :induct (my-induct x finalwidth finaltype mod
                                        ialist elem warnings))))

    (defthm true-listp-of-vl-exprlist-expandsizes
      (true-listp (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod
                                                     ialist elem warnings)))
      :rule-classes :type-prescription
      :hints(("Goal" :induct (my-induct x finalwidth finaltype mod
                                        ialist elem warnings))))

    (defthm vl-exprlist-expandsizes-2-under-iff
      (iff (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod
                                              ialist elem warnings))
           (consp x))
      :hints(("Goal" :induct (my-induct x finalwidth finaltype mod
                                        ialist elem warnings)))))



(local (acl2::def-ruleset! extra-disables
                           '(sets::double-containment
                            (:type-prescription member-equal)
                            acl2::member-of-cons
                            member-equal-when-member-equal-of-cdr-under-iff
                            acl2::subsetp-member
                            acl2::true-listp-member-equal
                            acl2::consp-member-equal
                            default-car
                            default-cdr
                            acl2::consp-under-iff-when-true-listp
                            ;args-exist-when-unary-op
                            ;args-exist-when-binary-op
                            ;args-exist-when-ternary-op
                            )))

(defsection vl-warninglist-p-of-vl-expr-size

  (local (autohide vl-expr-resolved-p vl-exprlist-resolved-p))

  (local (in-theory (disable
                     (:ruleset basic-arithmetic-rules)
                     (:ruleset tag-reasoning)
                     (:ruleset extra-disables)
                     (:rules-of-class :linear :here)
                     (:rules-of-class :type-prescription :here)
                     (:rules-of-class :compound-recognizer :here)
                     vl-warninglist-p-when-subsetp-equal
                     posp-when-member-equal-of-pos-listp
                     VL-EXPR-RESOLVED-P-OF-CAR-WHEN-VL-EXPRLIST-RESOLVED-P
                     VL-WARNING-P-WHEN-MEMBER-EQUAL-OF-VL-WARNINGLIST-P
                     )))

  (defthm-flag-vl-expr-size

    (defthm vl-warninglist-p-of-vl-expr-size
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-expr-size lhs-size x mod ialist elem warnings))))
      :flag vl-expr-size)

    (defthm vl-warninglist-p-of-vl-exprlist-size
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-exprlist-size x mod ialist elem warnings))))
      :flag vl-exprlist-size)

    (defthm vl-warninglist-p-of-vl-expr-expandsizes
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-expr-expandsizes x finalwidth finaltype mod
                                               ialist elem warnings))))
      :flag vl-expr-expandsizes)

    (defthm vl-warninglist-p-of-vl-exprlist-expandsizes
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-exprlist-expandsizes x finalwidth finaltype mod
                                                   ialist elem warnings))))
      :flag vl-exprlist-expandsizes)

    :hints(("Goal"
            :do-not '(generalize fertilize)
            :expand ((:free (lhs-size)
                            (vl-expr-size lhs-size x mod ialist elem warnings))
                     (:free (finalwidth finaltype)
                            (vl-expr-expandsizes x finalwidth finaltype mod
                                                 ialist elem warnings)))))))



(defsection no-change-loser-of-vl-expr-size

  (local (in-theory (disable
                     car-when-all-equalp
                     all-equalp
                     all-equalp-of-cdr-when-all-equalp
                     (:ruleset basic-arithmetic-rules)
                     (:ruleset tag-reasoning)
                     (:ruleset extra-disables)
                     (:rules-of-class :linear :here)
                     (:rules-of-class :type-prescription :here)
                     vl-warninglist-p-when-subsetp-equal
                     posp-when-member-equal-of-pos-listp
                     VL-EXPR-RESOLVED-P-OF-CAR-WHEN-VL-EXPRLIST-RESOLVED-P
                     VL-EXPRLIST-RESOLVED-P-OF-CDR-WHEN-VL-EXPRLIST-RESOLVED-P)))

  (defthm-flag-vl-expr-size

    (defthm no-change-loserp-of-vl-expr-size
      (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
        (implies (not (mv-nth 0 ret))
                 (equal (mv-nth 2 ret) x)))
      :flag vl-expr-size)

    (defthm no-change-loserp-of-vl-exprlist-size
      t
      :rule-classes nil
      :flag vl-exprlist-size)

    (defthm no-change-loserp-of-vl-expr-expandsizes
      (let ((ret (vl-expr-expandsizes x finalwidth finaltype mod
                                      ialist elem warnings)))
        (implies (not (mv-nth 0 ret))
                 (equal (mv-nth 2 ret) x)))
      :flag vl-expr-expandsizes)

    (defthm no-change-loserp-of-vl-exprlist-expandsizes
      t
      :rule-classes nil
      :flag vl-exprlist-expandsizes)

    :hints(("Goal"
            :do-not '(generalize fertilize)
            :expand ((:free (lhs-size)
                            (vl-expr-size lhs-size x mod ialist elem warnings))
                     (:free (finalwidth finaltype)
                            (vl-expr-expandsizes x finalwidth finaltype mod
                                                 ialist elem warnings)))))))


(defsection vl-expr-p-of-vl-expr-size

  (local (in-theory (disable (:ruleset basic-arithmetic-rules)
                             (:ruleset tag-reasoning)
                             (:rules-of-class :linear :here)
                             (:rules-of-class :type-prescription :here)
                             sets::double-containment
                             default-car
                             default-cdr
                             natp-when-member-equal-of-nat-listp
                             acl2::subsetp-member
                             member-equal-when-member-equal-of-cdr-under-iff
                             vl-expr-p-when-member-equal-of-vl-exprlist-p
                             vl-exprtype-p-when-vl-maybe-exprtype-p
                             vl-exprlist-p-when-subsetp-equal
                             vl-module-p-when-member-equal-of-vl-modulelist-p
                             vl-maybe-module-p-when-vl-module-p
                             acl2::consp-under-iff-when-true-listp
                             acl2::consp-by-len
                             acl2::consp-of-cdr-by-len
                             acl2::consp-of-cddr-by-len
                             car-when-all-equalp

                             ;; bozo these should be part of tag reasoning
                             vl-atom-p-by-tag-when-vl-expr-p
                             tag-when-vl-arguments-p
                             )))

  (defthm-flag-vl-expr-size

    (defthm vl-expr-p-of-vl-expr-size
      (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
        (implies (and (force (maybe-natp lhs-size))
                      (force (vl-expr-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-expr-p (mv-nth 2 ret))))
      :flag vl-expr-size)

    (defthm vl-exprlist-p-of-vl-exprlist-size
      (let ((ret (vl-exprlist-size x mod ialist elem warnings)))
        (implies (and (force (vl-exprlist-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-p (mv-nth 2 ret))))
      :flag vl-exprlist-size)

    (defthm vl-expr-p-of-vl-expr-expandsizes
      (let ((ret (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings)))
        (implies (and (force (vl-expr-p x))
                      (force (natp finalwidth))
                      (force (vl-exprtype-p finaltype))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-expr-p (mv-nth 2 ret))))
      :flag vl-expr-expandsizes)

    (defthm vl-exprlist-p-of-vl-exprlist-expandsizes
      (let ((ret (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))
        (implies (and (force (vl-exprlist-p x))
                      (force (natp finalwidth))
                      (force (vl-exprtype-p finaltype))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-p (mv-nth 2 ret))))
      :flag vl-exprlist-expandsizes)

    :hints(("Goal"
            :do-not '(generalize fertilize)
            :expand ((:free (lhs-size)
                            (vl-expr-size lhs-size x mod ialist elem warnings))
                     (:free (finalwidth finaltype)
                            (vl-expr-expandsizes x finalwidth finaltype mod
                                                 ialist elem warnings))))
           (and stable-under-simplificationp
                '(:in-theory (enable (:ruleset basic-arithmetic-rules)
                                     (:rules-of-class :type-prescription :here)
                                     default-car
                                     default-cdr
                                     maybe-natp))))))


(defsection vl-expr-size-guards

  (local (in-theory (disable
                     MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                     sets::double-containment
                     ACL2::TRUE-LISTP-MEMBER-EQUAL
                     (:ruleset tag-reasoning)
                     (:ruleset basic-arithmetic-rules)
                     acl2::subsetp-member
                     default-car
                     default-cdr
                     VL-MODELEMENT-P-WHEN-VL-VARDECL-P
                     VL-MODELEMENT-P-WHEN-VL-REGDECL-P
                     VL-MODELEMENT-P-WHEN-VL-PARAMDECL-P
                     VL-MODELEMENT-P-WHEN-VL-EVENTDECL-P
                     VL-MODELEMENT-P-WHEN-VL-PORTDECL-P
                     VL-MODELEMENT-P-WHEN-VL-PORT-P
                     VL-MODELEMENT-P-WHEN-VL-NETDECL-P
                     VL-MODELEMENT-P-WHEN-VL-MODINST-P
                     VL-MODELEMENT-P-WHEN-VL-INITIAL-P
                     VL-MODELEMENT-P-WHEN-VL-GATEINST-P
                     VL-MODELEMENT-P-WHEN-VL-ASSIGN-P
                     VL-MODELEMENT-P-WHEN-VL-ALWAYS-P
                     )))

  (local (defthm vl-exprlist-size-2-under-iff
           (iff (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings))
                (consp x))
           :hints(("goal"
                   :in-theory (disable len-of-vl-exprlist-size)
                   :use ((:instance len-of-vl-exprlist-size))))))

  (local (defthm vl-exprlist-size-2-cdr-under-iff
           (iff (cdr (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))
                (consp (cdr x)))
           :hints(("goal"
                   :in-theory (disable len-of-vl-exprlist-size)
                   :use ((:instance len-of-vl-exprlist-size))))))

  (local (defthm vl-exprlist-size-2-cddr-under-iff
           (iff (cddr (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))
                (consp (cddr x)))
           :hints(("goal"
                   :in-theory (disable len-of-vl-exprlist-size)
                   :use ((:instance len-of-vl-exprlist-size))))))

  (verify-guards vl-expr-size
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (vl-op-p maybe-natp
                                   (:ruleset basic-arithmetic-rules))
                                  (return-type-of-vl-nonatom->op))
                             :use ((:instance return-type-of-vl-nonatom->op)))))))




(defsection vl-expr-welltyped-p-of-vl-expr-size

  (local (in-theory (disable all-equalp)))

  (local (defthm c0
           (implies (all-equalp finaltype (vl-exprlist->finaltypes x))
                    (equal (vl-expr->finaltype (first x))
                           (if (consp x)
                               finaltype
                             nil)))))

  (local (defthm c1
           (implies (all-equalp finaltype (vl-exprlist->finaltypes x))
                    (equal (vl-expr->finaltype (second x))
                           (if (consp (cdr x))
                               finaltype
                             nil)))))

  (local (defthm c2
           (implies (all-equalp finalwidth (vl-exprlist->finalwidths x))
                    (equal (vl-expr->finalwidth (first x))
                           (if (consp x)
                               finalwidth
                             nil)))))

  (local (defthm c3
           (implies (all-equalp finalwidth (vl-exprlist->finalwidths x))
                    (equal (vl-expr->finalwidth (second x))
                           (if (consp (cdr x))
                               finalwidth
                             nil)))))

  (local (defthm vl-exprlist-expandsizes-2-cdr-under-iff
           (iff (cdr (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod
                                                        ialist elem warnings)))
                (consp (cdr x)))))


  ;; Speed hint
  (local (in-theory (disable
                     (:rules-of-class :type-prescription :here)
                     sets::double-containment
                     default-car
                     default-cdr
                     vl-module-p-when-wrong-tag
                     acl2::subsetp-member
                     natp-when-posp
                     integerp-when-natp
                     acl2::posp-rw
                     acl2::natp-posp
                     acl2::natp-rw
                     posp-when-member-equal-of-pos-listp
                     natp-when-member-equal-of-nat-listp
                     (:ruleset tag-reasoning)
                     car-when-all-equalp
                     member-equal-when-member-equal-of-cdr-under-iff
                     vl-atom-p-by-tag-when-vl-expr-p
                     tag-when-vl-arguments-p
                     (:ruleset basic-arithmetic-rules)
                     acl2::consp-by-len
                     acl2::consp-of-cdr-by-len
                     acl2::consp-of-cddr-by-len
                     vl-exprlist-p-when-subsetp-equal
                     vl-expr-p-when-member-equal-of-vl-exprlist-p
                     vl-module-p-when-member-equal-of-vl-modulelist-p
                     vl-maybe-module-p-when-vl-module-p
                     vl-expr-welltyped-p-when-member-equal-of-vl-exprlist-welltyped-p
                     vl-exprlist-resolved-p-when-subsetp-equal
                     vl-expr-resolved-p-when-member-equal-of-vl-exprlist-resolved-p
                     natp-when-member-equal-of-nat-listp
                     )))

  (local (in-theory (enable maybe-natp
                            tag-of-vl-nonatom
                            vl-atom-p-when-wrong-tag)))

  (defthm-flag-vl-expr-size

    (defthm vl-expr-welltyped-p-of-vl-expr-size
      (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (maybe-natp lhs-size))
                      (force (vl-expr-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-expr-welltyped-p (mv-nth 2 ret))))
      :flag vl-expr-size)

    (defthm vl-exprlist-welltyped-p-of-vl-exprlist-size
      (let ((ret (vl-exprlist-size x mod ialist elem warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-exprlist-p x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (vl-exprlist-welltyped-p (mv-nth 2 ret))))
      :flag vl-exprlist-size)

    (defthm vl-expr-welltyped-p-of-vl-expr-expandsizes
      (let ((ret (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-expr-p x))
                      (force (natp finalwidth))
                      (force (vl-exprtype-p finaltype))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (and
                  (vl-expr-welltyped-p (mv-nth 2 ret))
                  (equal (vl-expr->finalwidth (mv-nth 2 ret)) finalwidth)
                  (equal (vl-expr->finaltype (mv-nth 2 ret)) finaltype))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (ialist warnings)
                               (vl-expr-selfsize x mod ialist elem warnings))))))
      :flag vl-expr-expandsizes)

    (defthm vl-exprlist-welltyped-p-of-vl-exprlist-expandsizes
      (let ((ret (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))
        (implies (and (mv-nth 0 ret)
                      (force (vl-exprlist-p x))
                      (force (natp finalwidth))
                      (force (vl-exprtype-p finaltype))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (and
                  (vl-exprlist-welltyped-p (mv-nth 2 ret))
                  (all-equalp finalwidth (vl-exprlist->finalwidths (mv-nth 2 ret)))
                  (all-equalp finaltype (vl-exprlist->finaltypes (mv-nth 2 ret))))))
      :flag vl-exprlist-expandsizes)

    :hints(("Goal"
            :do-not '(generalize fertilize)
            :expand ((:free (lhs-size ialist)
                            (vl-expr-size lhs-size x mod ialist elem warnings))
                     (:free (finalwidth finaltype ialist)
                            (vl-expr-expandsizes x finalwidth finaltype mod
                                                 ialist elem warnings))
                     (vl-expr-welltyped-p x)
                     (:free (op atts args finalwidth finaltype)
                            (vl-expr-welltyped-p
                             (vl-nonatom op atts args finalwidth finaltype)))))
           (and stable-under-simplificationp
                '(:in-theory (enable (:ruleset basic-arithmetic-rules)
                                     (:rules-of-class :type-prescription :here)))))))


(defthm vl-expr->finalwidth-of-vl-expr-size-when-lhs-size
  ;; This is an important corollary.  It shows us that if we actually provide
  ;; an lhs-size argument, we're guaranteed to get back an expression that is
  ;; at least as large as lhs-size.
  (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
    (implies (and (mv-nth 0 ret)
                  (force (natp lhs-size))
                  (force (vl-expr-p x))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (<= lhs-size (vl-expr->finalwidth (mv-nth 2 ret)))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :expand ((:free (ialist)
                          (vl-expr-size lhs-size x mod ialist elem warnings))))))



; -----------------------------------------------------------------------------
;
;                    SIZING EXPRESSIONS THROUGHOUT A MODULE
;
; -----------------------------------------------------------------------------

(defmacro def-vl-exprsize (name &key type body takes-elem (long '""))
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (short      (cat "Compute sizes and types of expressions
throughout a @(see " type-s ")"))
         (long (cat "<p><b>Signature:</b> @(call " name-s ") returns @('(mv
successp warnings x-prime)').</p>" long))
         (formals    (append '(x mod ialist)
                             (if takes-elem '(elem) nil)
                             '(warnings))))

    `(defsection ,name
       :parents (expression-sizing)
       :short ,short
       :long ,long

       (defund ,name ,formals
         "Returns (MV SUCCESSP WARNINGS X-PRIME)"
         (declare (xargs :guard (and (,type x)
                                     (vl-module-p mod)
                                     (equal ialist (vl-moditem-alist mod))
                                     ,@(and takes-elem '((vl-modelement-p elem)))
                                     (vl-warninglist-p warnings))))
         ,body)

       (local (in-theory (enable ,name)))

       (defthm ,thm-warn
         (implies (force (vl-warninglist-p warnings))
                  (vl-warninglist-p (mv-nth 1 (,name . ,formals))))
         :hints(("Goal" :in-theory (disable (force)))))

       (defthm ,thm-type
         (implies (and (force (,type x))
                       (force (vl-module-p mod))
                       (force (equal ialist (vl-moditem-alist mod))))
                  (,type (mv-nth 2 (,name . ,formals))))))))


(defmacro def-vl-exprsize-list (name &key type element takes-elem)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name))
         (short      (cat "Compute sizes and types of expressions throughout
a @(see " type-s ")"))
         (long (cat "<p><b>Signature:</b> @(call " name-s ") returns @('(mv
successp warnings x-prime)').</p>"))
         (formals   (append '(x mod ialist)
                            (if takes-elem '(elem) nil)
                            '(warnings))))

    `(defsection ,name
       :parents (expression-sizing)
       :short ,short
       :long ,long

      (defund ,name ,formals
        (declare (xargs :guard (and (,type x)
                                    (vl-module-p mod)
                                    (equal ialist (vl-moditem-alist mod))
                                    ,@(and takes-elem '((vl-modelement-p elem)))
                                    (vl-warninglist-p warnings))))
        (if (atom x)
            (mv t warnings nil)
          (b* (((mv car-successp warnings car-prime)
                (,element . ,(subst '(car x) 'x formals)))
               ((mv cdr-successp warnings cdr-prime)
                (,name . ,(subst '(cdr x) 'x formals)))
               (successp (and car-successp cdr-successp))
               (x-prime  (cons car-prime cdr-prime)))
              (mv successp warnings x-prime))))

      (local (in-theory (enable ,name)))

      (defthm ,thm-warn
        (implies (vl-warninglist-p warnings)
                 (vl-warninglist-p (mv-nth 1 (,name . ,formals))))
        :hints(("Goal" :in-theory (disable (force)))))

      (defthm ,thm-type
        (implies (and (force (,type x))
                      (force (vl-module-p mod))
                      (force (equal ialist (vl-moditem-alist mod))))
                 (,type (mv-nth 2 (,name . ,formals)))))

      (defthm ,thm-true
        (true-listp (mv-nth 2 (,name . ,formals)))
        :rule-classes :type-prescription))))


(def-vl-exprsize vl-maybe-expr-size
  :takes-elem t
  :type vl-maybe-expr-p
  :body (if x
            (vl-expr-size nil x mod ialist elem warnings)
          (mv t warnings x)))


(def-vl-exprsize vl-range-exprsize
  :takes-elem t
  :type vl-range-p
  :body (b* (((vl-range x) x)
             ((mv msb-successp warnings msb-prime)
              (vl-expr-size nil x.msb mod ialist elem warnings))
             ((mv lsb-successp warnings lsb-prime)
              (vl-expr-size nil x.lsb mod ialist elem warnings))
             (successp (and msb-successp lsb-successp))
             (x-prime  (change-vl-range x
                                        :msb msb-prime
                                        :lsb lsb-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-range-exprsize
  :takes-elem t
  :type vl-maybe-range-p
  :body (if x
            (vl-range-exprsize x mod ialist elem warnings)
          (mv t warnings x)))

(def-vl-exprsize-list vl-rangelist-exprsize
  :takes-elem t
  :type vl-rangelist-p
  :element vl-range-exprsize)

(def-vl-exprsize vl-gatedelay-exprsize
  :takes-elem t
  :type vl-gatedelay-p
  :body (b* (((vl-gatedelay x) x)
             ((mv rise-okp warnings rise-prime)
              (vl-expr-size nil x.rise mod ialist elem warnings))
             ((mv fall-okp warnings fall-prime)
              (vl-expr-size nil x.fall mod ialist elem warnings))
             ((mv high-okp warnings high-prime)
              (vl-maybe-expr-size x.high mod ialist elem warnings))
             (successp (and rise-okp fall-okp high-okp))
             (x-prime  (change-vl-gatedelay x
                                            :rise rise-prime
                                            :fall fall-prime
                                            :high high-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-gatedelay-exprsize
  :takes-elem t
  :type vl-maybe-gatedelay-p
  :body (if x
            (vl-gatedelay-exprsize x mod ialist elem warnings)
          (mv t warnings x)))





(defsection vl-maybe-warn-about-implicit-truncation

; Truncation warnings are really, really good to have, and have found many
; bugs.  However, if we just issue a truncation warning about everything, we
; find that there are way too many nitpicky warnings and it's hard to go
; through them all.  So, we want to be clever and not warn in certain cases
; that we have seen where the truncation really doesn't matter.  Efficiency is
; of no concern because this is called so infrequently.
;
; Probably the biggest source of spurious truncation warnings is from the use
; of unsized numbers like 0 and 1.  It's a pretty good bet that any truncation
; from 32-bits to some other number of bits is no big deal and is just being
; caused by a unsized number.
;
; At any rate, we now have a notion of expression that are okay to truncate.
; We basically don't want to complain about things like
;
;    assign foo[3:0] = 0;              // 32 bits, but who cares, it fits
;
;    assign foo[3:0] = 5'd7;           // 5 bits, but who cares, it still fits
;
;    assign foo[3:0] = x0 ? 5'h0 :     // each are 5 bits, but who cares, they
;                      x1 ? 5'h1 :     // still fit.
;                      x2 ? 5'h2 :
;                      ...
;                      x14 ? 5'h14 :
;                      5'h15;

  (defund vl-okay-to-truncate-atom (width x)
    ;; Recognize:
    ;;
    ;; (1) atoms that were just ordinary constant integer numbers like 5, but
    ;;     which are not "negative" numbers (i.e., bit 31 should not be set), and
    ;;     whose value is small enough to fit into WIDTH many bits.
    ;;
    ;; (2) atoms that were sized but unsigned constant integers that can be
    ;;     chopped down to width-many bits without changing their value.
    (declare (xargs :guard (and (natp width)
                                (vl-atom-p x))))
    (b* ((guts (vl-atom->guts x))
         ((unless (vl-fast-constint-p guts))
          nil)
         ((vl-constint guts) guts))
      (or
       ;; Case 1:
       (and guts.wasunsized
            (= guts.origwidth 32)
            (not (logbitp 31 guts.value))
            (< guts.value (expt 2 width)))
       ;; Case 2:
       (and (eq guts.origtype :vl-unsigned)
            (< guts.value (expt 2 width))))))


  (local (assert!
          ;; Basic test to make sure it seems to be working right.
          (flet ((test (value)
                       (make-vl-atom :guts (make-vl-constint :value value
                                                             :origwidth 32
                                                             :origtype :vl-signed
                                                             :wasunsized t))))
                (and (vl-okay-to-truncate-atom 8 (test 0))
                     (vl-okay-to-truncate-atom 8 (test 255))
                     (not (vl-okay-to-truncate-atom 8 (test 256)))))))

  (defun vl-okay-to-truncate-expr (width x)
    ;; Recognize okay to truncate atoms and nests of (A ? B : C) where all of the
    ;; final branches are okay to truncate atoms.
    (declare (xargs :guard (and (natp width)
                                (vl-expr-p x))))
    (b* (((when (vl-fast-atom-p x))
          (vl-okay-to-truncate-atom width x))
         ((when (mbe :logic (atom x)
                     :exec nil))
          ;; Termination hack
          (er hard? 'vl-okay-to-truncate-expr "impossible"))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))
         ((unless (eq op :vl-qmark))
          nil))
      (and (vl-okay-to-truncate-expr width (second args))
           (vl-okay-to-truncate-expr width (third args)))))

  (defund vl-unsized-atom-p (x)
    (declare (xargs :guard (vl-atom-p x)))
    (b* ((guts (vl-atom->guts x)))
      (or (and (vl-fast-constint-p guts)
               (vl-constint->wasunsized guts))
          (and (vl-fast-weirdint-p guts)
               (vl-weirdint->wasunsized guts)))))

  (defund vl-some-unsized-atom-p (x)
    (declare (xargs :guard (vl-atomlist-p x)))
    (if (atom x)
        nil
      (or (vl-unsized-atom-p (car x))
          (vl-some-unsized-atom-p (cdr x)))))

  (defun vl-maybe-warn-about-implicit-truncation (lvalue expr x warnings)
    (declare (xargs :guard (and (vl-expr-p lvalue)
                                (vl-expr-p expr)
                                (vl-modelement-p x)
                                (vl-warninglist-p warnings))))
    (b* ((lw (vl-expr->finalwidth lvalue))
         (ew (vl-expr->finalwidth expr))

         ((when (and (natp lw)
                     (vl-okay-to-truncate-expr lw expr)))
          ;; Just ignore it, this is nothing to be worried about
          warnings)

         (probably-minor-p
          ;; We could probably improve this somewhat... if the RHS is 32 bits
          ;; and it at least has some atom that was originally unsized in it,
          ;; it's probably just a truncation because there's a plain number on
          ;; the rhs, and it probably isn't a real problem, so we'll call such
          ;; things minor.  This is something we couldn't check very well when
          ;; we were trying to handle truncation warnings as part of
          ;; assign-trunc, because by then the expressions had already been
          ;; split and the temp wires could hide unsized atoms.
          (and (equal ew 32)
               (vl-some-unsized-atom-p (vl-expr-atoms expr))))

         ;; Add a warning about implicit truncation.
         (warning (make-vl-warning
                   :type (if probably-minor-p
                             :vl-warn-truncation-minor
                           :vl-warn-truncation)
                   :msg "~a0: implicit truncation from ~x1-bit expression ~
                       to ~x2-bit lvalue.~%     ~
                         lhs: ~a3~%     ~
                         rhs: ~a4~%~%"
                   :args (list x ew lw lvalue expr)
                   :fatalp nil
                   :fn 'vl-maybe-add-truncation-warning)))

      (cons warning warnings))))



(def-vl-exprsize vl-assign-exprsize
  :takes-elem nil
  :type vl-assign-p
  :body (b* (((vl-assign x) x)
             (elem x)

             ;; Per Table 6-1 (Section 6; page 68), the left-hand side of the
             ;; assignment should be a net, bit-select, part-select, or
             ;; constant indexed part-select, recursively closed under
             ;; concatenation.  We explicitly check this with vl-expr-lvaluep
             ;; so that we can be sure the sizing algorithm won't do anything
             ;; weird like zero-extend some part of the lhs.
             ((unless (vl-expr-lvaluep x.lvalue))
              (b* ((w (make-vl-warning
                       :type :vl-bad-assignment
                       :msg "~a0: Illegal left-hand side: ~a1."
                       :args (list elem x.lvalue)
                       :fatalp t
                       :fn 'vl-assign-exprsize)))
                (mv nil (cons w warnings) x)))

             ((mv lhs-successp warnings lhs-prime)
              (vl-expr-size nil x.lvalue mod ialist elem warnings))
             ((unless lhs-successp)
              (mv nil warnings x))

             (lhs-size (vl-expr->finalwidth lhs-prime))
             ((unless (posp lhs-size))
              (b* ((w (make-vl-warning
                       :type :vl-bad-assignment
                       :msg "~a0: The size of the left-hand side ~a1 was not ~
                             a positive number?"
                       :args (list elem x.lvalue)
                       :fatalp t
                       :fn 'vl-assign-exprsize)))
                (mv nil (cons w warnings) x)))

             ((mv rhs-successp warnings rhs-prime)
              (vl-expr-size lhs-size x.expr mod ialist elem warnings))

             (warnings
              ;; By vl-expr->finalwidth-of-vl-expr-size-when-lhs-size, we know
              ;; that rhs-prime is at least as wide as lhs-size.  But it can be
              ;; wider, and in such cases we may wish to warn about truncation.
              (if (and (posp (vl-expr->finalwidth rhs-prime))
                       (< lhs-size (vl-expr->finalwidth rhs-prime)))
                  (vl-maybe-warn-about-implicit-truncation lhs-prime rhs-prime
                                                           x warnings)
                warnings))

             ((mv delay-successp warnings delay-prime)
              (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))

             ((unless (and rhs-successp delay-successp))
              (mv nil warnings x))

             (x-prime
              (change-vl-assign x
                                :lvalue lhs-prime
                                :expr rhs-prime
                                :delay delay-prime)))
            (mv t warnings x-prime)))

(def-vl-exprsize-list vl-assignlist-exprsize
  :takes-elem nil
  :type vl-assignlist-p
  :element vl-assign-exprsize)



(def-vl-exprsize vl-plainarg-exprsize
  :takes-elem t
  :type vl-plainarg-p

  :long "<h3>Additional Notes</h3>

<p>Minor note: We don't attempt to size blanks.  If there is no expression, it
remains as a blank.</p>

<p>Expressions in argument lists don't have a left-hand side.  They do need to
ultimately agree with the target port, but I am feeling pretty confident that
the port's width does <b>not</b> play a role in sizing the expression.  A good
reason for this is that, if you go and read xf-replicate-insts, and look at the
rules for splitting up instance arrays, it seems like there is more than one
possibility for the context width in this case, namely @('FW') or @('N * FW'),
where @('FW') is the width of the formal and @('N') is the size of the array,
so it doesn't seem like the port's width could in any sensible way used to size
the expression.</p>"

  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-plainarg x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-plainarglist-exprsize
  :takes-elem t
  :type vl-plainarglist-p
  :element vl-plainarg-exprsize)



(def-vl-exprsize vl-namedarg-exprsize
  :takes-elem t
  :type vl-namedarg-p
  :long "<p>See also the notes in @(see vl-plainarg-exprsize).</p>"
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-namedarg x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-namedarglist-exprsize
  :takes-elem t
  :type vl-namedarglist-p
  :element vl-namedarg-exprsize)

(def-vl-exprsize vl-arguments-exprsize
  :takes-elem t
  :type vl-arguments-p
  :body
  (b* ((namedp (vl-arguments->namedp x))
       (args   (vl-arguments->args x))
       ((mv successp warnings args-prime)
        (if namedp
            (vl-namedarglist-exprsize args mod ialist elem warnings)
          (vl-plainarglist-exprsize args mod ialist elem warnings)))
       (x-prime (vl-arguments namedp args-prime)))
      (mv successp warnings x-prime)))

(def-vl-exprsize vl-modinst-exprsize
  :takes-elem nil
  :type vl-modinst-p
  :body
  (b* (((vl-modinst x) x)
       (elem x)
       ((mv successp1 warnings portargs-prime)
        (vl-arguments-exprsize x.portargs mod ialist elem warnings))
       ((mv successp2 warnings paramargs-prime)
        (vl-arguments-exprsize x.paramargs mod ialist elem warnings))
       ((mv successp3 warnings range-prime)
        (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv successp4 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
       (successp
        (and successp1 successp2 successp3 successp4))
       (x-prime
        (change-vl-modinst x
                           :portargs portargs-prime
                           :paramargs paramargs-prime
                           :range range-prime
                           :delay delay-prime)))
      (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-modinstlist-exprsize
  :takes-elem nil
  :type vl-modinstlist-p
  :element vl-modinst-exprsize)



(def-vl-exprsize vl-gateinst-exprsize
  :takes-elem nil
  :type vl-gateinst-p
  :body
  (b* (((vl-gateinst x) x)
       (elem x)
       ((mv successp1 warnings args-prime)
        (vl-plainarglist-exprsize x.args mod ialist elem warnings))
       ((mv successp2 warnings range-prime)
        (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv successp3 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
       (successp
        (and successp1 successp2 successp3))
       (x-prime
        (change-vl-gateinst x
                            :args args-prime
                            :range range-prime
                            :delay delay-prime)))
      (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-gateinstlist-exprsize
  :takes-elem nil
  :type vl-gateinstlist-p
  :element vl-gateinst-exprsize)



(def-vl-exprsize vl-delaycontrol-exprsize
  :takes-elem t
  :type vl-delaycontrol-p
  :body (b* (((vl-delaycontrol x) x)
             ((mv successp warnings value-prime)
              (vl-expr-size nil x.value mod ialist elem warnings))
             (x-prime
              (change-vl-delaycontrol x :value value-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-evatom-exprsize
  :takes-elem t
  :type vl-evatom-p
  :body (b* (((vl-evatom x) x)
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-evatom x :expr expr-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-evatomlist-exprsize
  :takes-elem t
  :type vl-evatomlist-p
  :element vl-evatom-exprsize)

(def-vl-exprsize vl-eventcontrol-exprsize
  :takes-elem t
  :type vl-eventcontrol-p
  :body (b* (((vl-eventcontrol x) x)
             ((mv successp warnings atoms-prime)
              (vl-evatomlist-exprsize x.atoms mod ialist elem warnings))
             (x-prime
              (change-vl-eventcontrol x :atoms atoms-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-repeateventcontrol-exprsize
  :takes-elem t
  :type vl-repeateventcontrol-p
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv successp1 warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             ((mv successp2 warnings ctrl-prime)
              (vl-eventcontrol-exprsize x.ctrl mod ialist elem warnings))
             (successp
              (and successp1 successp2))
             (x-prime
              (change-vl-repeateventcontrol x
                                            :expr expr-prime
                                            :ctrl ctrl-prime)))
            (mv successp warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-exprsize vl-delayoreventcontrol-exprsize
   :takes-elem t
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol
            (vl-delaycontrol-exprsize x mod ialist elem warnings))
           (:vl-eventcontrol
            (vl-eventcontrol-exprsize x mod ialist elem warnings))
           (:vl-repeat-eventcontrol
            (vl-repeateventcontrol-exprsize x mod ialist elem warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-p "Provably impossible.")
                warnings x)))))

(def-vl-exprsize vl-maybe-delayoreventcontrol-exprsize
  :takes-elem t
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-exprsize x mod ialist elem warnings)
          (mv t warnings nil)))

(defthm vl-maybe-delayoreventcontrol-exprsize-under-iff
  (implies (and (force (vl-maybe-delayoreventcontrol-p x))
                (force (vl-module-p mod))
                (force (equal ialist (vl-moditem-alist mod))))
           (iff (mv-nth 2 (vl-maybe-delayoreventcontrol-exprsize x mod ialist elem warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-exprsize
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-exprsize))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-exprsize)))))


(def-vl-exprsize vl-assignstmt-exprsize
  :takes-elem t
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x)

             ;; This is very similar to vl-assign-exprsize.
             ((unless (vl-expr-lvaluep x.lvalue))
              (b* ((w (make-vl-warning
                       :type :vl-bad-assignment
                       :msg "~a0: Illegal left-hand side: ~a1."
                       :args (list elem x.lvalue)
                       :fatalp t
                       :fn 'vl-assignstmt-exprsize)))
                (mv nil (cons w warnings) x)))

             ((mv lhs-successp warnings lhs-prime)
              (vl-expr-size nil x.lvalue mod ialist elem warnings))
             ((unless lhs-successp)
              (mv nil warnings x))

             (lhs-size (vl-expr->finalwidth lhs-prime))
             ((unless (posp lhs-size))
              (b* ((w (make-vl-warning
                       :type :vl-bad-assignment
                       :msg "~a0: The size of the left-hand side ~a1 was not ~
                             a positive number?"
                       :args (list elem x.lvalue)
                       :fatalp t
                       :fn 'vl-assignstmt-exprsize)))
                (mv nil (cons w warnings) x)))

             ((mv rhs-successp warnings rhs-prime)
              (vl-expr-size lhs-size x.expr mod ialist elem warnings))

             (warnings
              ;; By vl-expr->finalwidth-of-vl-expr-size-when-lhs-size, we know
              ;; that rhs-prime is at least as wide as lhs-size.  But it can be
              ;; wider, and in such cases we may wish to warn about truncation.
              (if (and (posp (vl-expr->finalwidth rhs-prime))
                       (< lhs-size (vl-expr->finalwidth rhs-prime)))
                  (vl-maybe-warn-about-implicit-truncation lhs-prime rhs-prime
                                                           elem warnings)
                warnings))

             ((mv delay-successp warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-exprsize x.ctrl mod ialist elem warnings))
             (successp
              (and rhs-successp delay-successp))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lhs-prime
                                    :expr rhs-prime
                                    :ctrl ctrl-prime)))
          (mv successp warnings x-prime)))


(def-vl-exprsize vl-enablestmt-exprsize
  :takes-elem t
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x)
             ((mv successp1 warnings id-prime)
              (vl-expr-size nil x.id mod ialist elem warnings))
             ((mv successp2 warnings args-prime)
              (vl-exprlist-size x.args mod ialist elem warnings))
             (successp
              (and successp1 successp2))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-deassignstmt-exprsize
  :takes-elem t
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x)
             ((mv successp warnings lvalue-prime)
              (vl-expr-size nil x.lvalue mod ialist elem warnings))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-disablestmt-exprsize
  :takes-elem t
  :type vl-disablestmt-p
  :body (b* (((vl-disablestmt x) x)
             ((mv successp warnings id-prime)
              (vl-expr-size nil x.id mod ialist elem warnings))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-eventtriggerstmt-exprsize
  :takes-elem t
  :type vl-eventtriggerstmt-p
  :body (b* (((vl-eventtriggerstmt x) x)
             ((mv successp warnings id-prime)
              (vl-expr-size nil x.id mod ialist elem warnings))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-atomicstmt-exprsize
  :takes-elem t
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (mv t warnings x))
          (:vl-assignstmt       (vl-assignstmt-exprsize x mod ialist elem warnings))
          (:vl-deassignstmt     (vl-deassignstmt-exprsize x mod ialist elem warnings))
          (:vl-enablestmt       (vl-enablestmt-exprsize x mod ialist elem warnings))
          (:vl-disablestmt      (vl-disablestmt-exprsize x mod ialist elem warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-exprsize x mod ialist elem warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-exprsize
                   "Impossible error to ensure all cases are covered.")
               warnings
               x))))

(defsection vl-stmt-exprsize

  (mutual-recursion

   (defund vl-stmt-exprsize (x mod ialist elem warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (vl-atomicstmt-exprsize x mod ialist elem warnings))
          ((vl-compoundstmt x) x)
          ((mv successp1 warnings exprs-prime)
           (vl-exprlist-size x.exprs mod ialist elem warnings))
          ((mv successp2 warnings stmts-prime)
           (vl-stmtlist-exprsize x.stmts mod ialist elem warnings))
          ((mv successp3 warnings ctrl-prime)
           (vl-maybe-delayoreventcontrol-exprsize x.ctrl mod ialist elem warnings))
          (warnings
           (if (not (vl-compoundstmt->decls x))
               warnings
             (cons (make-vl-warning
                    :type :vl-unsupported-block
                    :msg "~a0: block ~s0 has declarations, which are not supported."
                    :args (list (vl-compoundstmt->name x))
                    :fatalp t
                    :fn 'vl-stmt-exprsize)
                   warnings)))
          (successp (and successp1 successp2 successp3))
          (x-prime
           (change-vl-compoundstmt x
                                   :exprs exprs-prime
                                   :stmts stmts-prime
                                   :ctrl ctrl-prime)))
       (mv successp warnings x-prime)))

   (defund vl-stmtlist-exprsize (x mod ialist elem warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod))
                                 (vl-modelement-p elem)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv t warnings nil))
          ((mv car-successp warnings car-prime)
           (vl-stmt-exprsize (car x) mod ialist elem warnings))
          ((mv cdr-successp warnings cdr-prime)
           (vl-stmtlist-exprsize (cdr x) mod ialist elem warnings))
          (successp
           (and car-successp cdr-successp))
          (x-prime
           (cons car-prime cdr-prime)))
       (mv successp warnings x-prime))))

  (FLAG::make-flag vl-flag-stmt-exprsize
                   vl-stmt-exprsize
                   :flag-mapping ((vl-stmt-exprsize . stmt)
                                  (vl-stmtlist-exprsize . list)))

  (defthm-vl-flag-stmt-exprsize
    (defthm vl-warninglist-p-of-vl-stmt-exprsize
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-stmt-exprsize x mod ialist elem warnings))))
      :flag stmt)
    (defthm vl-warninglist-p-of-vl-stmtlist-exprsize
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 1 (vl-stmtlist-exprsize x mod ialist elem warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-stmt-exprsize x mod ialist elem warnings)
                     (vl-stmtlist-exprsize x mod ialist elem warnings)))))

  (defthm vl-stmtlist-exprsize-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-exprsize x mod ialist elem warnings)
                    (mv t warnings nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-exprsize))))

  (defthm vl-stmtlist-exprsize-of-cons
    (equal (vl-stmtlist-exprsize (cons a x) mod ialist elem warnings)
           (b* (((mv car-successp warnings car-prime)
                 (vl-stmt-exprsize a mod ialist elem warnings))
                ((mv cdr-successp warnings cdr-prime)
                 (vl-stmtlist-exprsize x mod ialist elem warnings))
                (successp
                 (and car-successp cdr-successp))
                (x-prime
                 (cons car-prime cdr-prime)))
             (mv successp warnings x-prime)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-exprsize))))

  (local (defun my-induction (x mod ialist elem warnings)
           (b* (((when (atom x))
                 (mv t warnings nil))
                ((mv car-successp warnings car-prime)
                 (vl-stmt-exprsize (car x) mod ialist elem warnings))
                ((mv cdr-successp warnings cdr-prime)
                 (my-induction (cdr x) mod ialist elem warnings))
                (successp
                 (and car-successp cdr-successp))
                (x-prime
                 (cons car-prime cdr-prime)))
             (mv successp warnings x-prime))))

  (defthm len-of-vl-stmtlist-exprsize
    (equal (len (mv-nth 2 (vl-stmtlist-exprsize x mod ialist elem warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x mod ialist elem warnings))))

  (defthm-vl-flag-stmt-exprsize
    (defthm vl-stmt-p-of-vl-stmt-exprsize
      (implies (and (force (vl-stmt-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-stmt-p (mv-nth 2 (vl-stmt-exprsize x mod ialist elem warnings))))
      :flag stmt)
    (defthm vl-stmtlist-p-of-vl-stmtlist-exprsize
      (implies (and (force (vl-stmtlist-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-stmtlist-p (mv-nth 2 (vl-stmtlist-exprsize x mod ialist elem warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-stmt-exprsize x mod ialist elem warnings)
                     (vl-stmtlist-exprsize x mod ialist elem warnings)))))

  (verify-guards vl-stmt-exprsize))



(def-vl-exprsize vl-always-exprsize
  :takes-elem nil
  :type vl-always-p
  :body (b* (((vl-always x) x)
             (elem x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt mod ialist elem warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-alwayslist-exprsize
  :takes-elem nil
  :type vl-alwayslist-p
  :element vl-always-exprsize)


(def-vl-exprsize vl-initial-exprsize
  :takes-elem nil
  :type vl-initial-p
  :body (b* (((vl-initial x) x)
             (elem x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt mod ialist elem warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-initiallist-exprsize
  :takes-elem nil
  :type vl-initiallist-p
  :element vl-initial-exprsize)


(def-vl-exprsize vl-port-exprsize
  :takes-elem nil
  :type vl-port-p
  :body (b* (((vl-port x) x)
             (elem x)
             ((mv successp warnings expr-prime)
              (vl-maybe-expr-size x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-port x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-portlist-exprsize
  :takes-elem nil
  :type vl-portlist-p
  :element vl-port-exprsize)



; It doesn't necessarily make a lot of sense to size the expressions in
; declarations, but on the other hand it doesn't seem like it's a bad thing to
; do.

(def-vl-exprsize vl-portdecl-exprsize
  :takes-elem nil
  :type vl-portdecl-p
  :body (b* (((vl-portdecl x) x)
             (elem x)
             ((mv successp warnings range-prime)
              (vl-maybe-range-exprsize x.range mod ialist elem warnings))
             (x-prime
              (change-vl-portdecl x :range range-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-portdecllist-exprsize
  :takes-elem nil
  :type vl-portdecllist-p
  :element vl-portdecl-exprsize)


(def-vl-exprsize vl-netdecl-exprsize
  :takes-elem nil
  :type vl-netdecl-p
  :body (b* (((vl-netdecl x) x)
             (elem x)
             ((mv successp1 warnings range-prime)
              (vl-maybe-range-exprsize x.range mod ialist elem warnings))
             ((mv successp2 warnings arrdims-prime)
              (vl-rangelist-exprsize x.arrdims mod ialist elem warnings))
             ((mv successp3 warnings delay-prime)
              (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
             (successp (and successp1 successp2 successp3))
             (x-prime
              (change-vl-netdecl x
                                 :range range-prime
                                 :arrdims arrdims-prime
                                 :delay delay-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-netdecllist-exprsize
  :takes-elem nil
  :type vl-netdecllist-p
  :element vl-netdecl-exprsize)


(def-vl-exprsize vl-regdecl-exprsize
  :takes-elem nil
  :type vl-regdecl-p
  :body (b* (((vl-regdecl x) x)
             (elem x)
             ((mv successp1 warnings range-prime)
              (vl-maybe-range-exprsize x.range mod ialist elem warnings))
             ((mv successp2 warnings arrdims-prime)
              (vl-rangelist-exprsize x.arrdims mod ialist elem warnings))

             ;; BOZO we should really separate out initvals from regdecls.
             ;; For now lets just not size the initval, since it's hard to
             ;; do it right.  We have to compute the size of the range and
             ;; stuff it in there.

             (successp (and successp1 successp2))
             (x-prime
              (change-vl-regdecl x
                                 :range range-prime
                                 :arrdims arrdims-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-regdecllist-exprsize
  :takes-elem nil
  :type vl-regdecllist-p
  :element vl-regdecl-exprsize)



(def-vl-exprsize vl-vardecl-exprsize
  :takes-elem nil
  :type vl-vardecl-p
  :body (b* (((vl-vardecl x) x)
             (elem x)
             ((mv successp warnings arrdims-prime)
              (vl-rangelist-exprsize x.arrdims mod ialist elem warnings))

             ;; BOZO we should really separate out initvals from vardecls.
             ;; For now lets just not size the initval, since it's hard to
             ;; do it right.  We have to compute the size of the range and
             ;; stuff it in there.

             (x-prime
              (change-vl-vardecl x :arrdims arrdims-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-vardecllist-exprsize
  :takes-elem nil
  :type vl-vardecllist-p
  :element vl-vardecl-exprsize)



(def-vl-exprsize vl-eventdecl-exprsize
  :takes-elem nil
  :type vl-eventdecl-p
  :body (b* (((vl-eventdecl x) x)
             (elem x)
             ((mv successp warnings arrdims-prime)
              (vl-rangelist-exprsize x.arrdims mod ialist elem warnings))
             (x-prime
              (change-vl-eventdecl x :arrdims arrdims-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-eventdecllist-exprsize
  :takes-elem nil
  :type vl-eventdecllist-p
  :element vl-eventdecl-exprsize)



(defsection vl-module-exprsize
  :parents (expression-sizing)

  (defund vl-module-exprsize (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)

         ((vl-module x) x)
         (warnings  x.warnings)

         ((when x.paramdecls)
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "Trying to size module ~m0, which has parameters."
                   :args (list x.name)
                   :fatalp t
                   :fn 'vl-module-exprsize)))
            (change-vl-module x :warnings (cons w warnings))))

         (ialist (vl-moditem-alist x))

         ((mv & warnings assigns)     (vl-assignlist-exprsize x.assigns x ialist warnings))
         ((mv & warnings modinsts)    (vl-modinstlist-exprsize x.modinsts x ialist warnings))
         ((mv & warnings gateinsts)   (vl-gateinstlist-exprsize x.gateinsts x ialist warnings))
         ((mv & warnings alwayses)    (vl-alwayslist-exprsize x.alwayses x ialist warnings))
         ((mv & warnings initials)    (vl-initiallist-exprsize x.initials x ialist warnings))
         ((mv & warnings ports)       (vl-portlist-exprsize x.ports x ialist warnings))
         ((mv & warnings portdecls)   (vl-portdecllist-exprsize x.portdecls x ialist warnings))
         ((mv & warnings netdecls)    (vl-netdecllist-exprsize x.netdecls x ialist warnings))
         ((mv & warnings regdecls)    (vl-regdecllist-exprsize x.regdecls x ialist warnings))
         ((mv & warnings vardecls)   (vl-vardecllist-exprsize x.vardecls x ialist warnings))
         ((mv & warnings eventdecls) (vl-eventdecllist-exprsize x.eventdecls x ialist warnings))

         (- (fast-alist-free ialist))
         )
      (change-vl-module x
                        :assigns assigns
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :alwayses alwayses
                        :initials initials
                        :ports ports
                        :portdecls portdecls
                        :netdecls netdecls
                        :regdecls regdecls
                        :vardecls vardecls
                        :eventdecls eventdecls
                        :warnings warnings)))

  (local (in-theory (enable vl-module-exprsize)))

  (defthm vl-module-p-of-vl-module-exprsize
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-exprsize x))))

  (defthm vl-module->name-of-vl-module-exprsize
    (equal (vl-module->name (vl-module-exprsize x))
           (vl-module->name x))))


(defprojection vl-modulelist-exprsize (x)
  (vl-module-exprsize x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (expression-sizing)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-exprsize
     (equal (vl-modulelist->names (vl-modulelist-exprsize x))
            (vl-modulelist->names x)))))

