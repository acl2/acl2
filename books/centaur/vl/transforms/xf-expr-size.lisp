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
(include-book "../mlib/range-tools")
(include-book "../util/sum-nats")
(include-book "../mlib/context")
(include-book "../mlib/welltyped")
(include-book "../mlib/lvalues")
(include-book "centaur/misc/arith-equivs" :dir :system)
(local (in-theory (enable acl2::arith-equiv-forwarding lnfix)))
(local (include-book "clause-processors/autohide" :dir :system))
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                           acl2::consp-under-iff-when-true-listp)))

(local (in-theory (disable acl2::hons-assoc-equal-of-cons
                           acl2::member-of-cons
                           integerp-when-natp
                           not nfix acl2::zp-open)))

(local (defun make-cases (ops)
         (if (atom ops)
             nil
           (cons `(equal (vl-nonatom->op x) ,(car ops))
                 (make-cases (cdr ops))))))

(local (make-event
        `(defruled vl-nonatom->op-forward
           (or . ,(make-cases (strip-cars *vl-ops-table*)))
           :rule-classes ((:forward-chaining
                           :trigger-terms ((vl-nonatom->op x))))
           :enable (vl-op-p acl2::hons-assoc-equal-of-cons)
           :disable vl-op-p-of-vl-nonatom->op
           :use ((:instance vl-op-p-of-vl-nonatom->op)))))

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

(local (xdoc::set-default-parents expression-sizing))

(defxdoc expression-sizing-intro
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
area where NCVerilog was designed to match the Verilog-2005 standard instead of
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

(define vl-atom-selfsize
  :parents (vl-expr-selfsize)
  :short "Compute the self-determined size of an atom."
  ((x        vl-expr-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod)))
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :guard (vl-atom-p x)
  :verbosep t
  :returns (mv (warnings vl-warninglist-p)
               (size     maybe-natp :rule-classes :type-prescription))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

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

  (b* ((x    (vl-expr-fix x))
       (elem (vl-modelement-fix elem))
       (guts (vl-atom->guts x))

       ((when (vl-fast-constint-p guts))
        (mv (ok) (vl-constint->origwidth guts)))

       ((when (vl-fast-weirdint-p guts))
        (mv (ok) (vl-weirdint->origwidth guts)))

       ((when (vl-fast-string-p guts))
        (mv (ok) (* 8 (length (vl-string->value guts)))))

       ((unless (vl-fast-id-p guts))
        ;; Reals, function names, hierarchical identifier pieces, etc., for which
        ;; a size is not applicable.
        (mv (ok) nil))

       (name (vl-id->name guts))
       (item (vl-fast-find-moduleitem name mod ialist))

       ((unless item)
        ;; Shouldn't happen if the module is well-formed and all used names
        ;; are declared.
        (mv (fatal :type :vl-bad-identifier
                   :msg "~a0: cannot size ~w1 because it is not declared."
                   :args (list elem name))
            nil))

       (tag (tag item))
       ((when (eq tag :vl-netdecl))
        (b* (((vl-netdecl item) item)
             ((when (consp item.arrdims))
              ;; Shouldn't happen unless the module directly uses the name of
              ;; an array in an expression; if we've properly converted
              ;; bitselects to array-references, our expression-sizing code
              ;; should not try to size its name.
              (mv (fatal :type :vl-bad-identifier
                         :msg "~a0: cannot size w1 because it is an array."
                         :args (list elem name))
                  nil))
             ((unless (vl-maybe-range-resolved-p item.range))
              ;; Shouldn't happen unless we had a problem resolving ranges
              ;; earlier.
              (mv (fatal :type :vl-bad-range
                         :msg "~a0: cannot size ~w1 because its range is not ~
                               resolved: ~a2."
                         :args (list elem name item.range))
                  nil))
             (size (vl-maybe-range-size item.range)))
          (mv (ok) size)))

       ((when (eq tag :vl-vardecl))
        (b* (((vl-vardecl item) item)
             ((when (consp item.dims))
              ;; Analogous to the netdecl array case.
              (mv (fatal :type :vl-bad-identifier
                         :msg "~a0: cannot size ~w1 because it is an array."
                         :args (list elem name))
                  nil))
             ((unless (eq (vl-datatype-kind item.vartype) :vl-coretype))
              ;; Don't try to size tricky things yet.
              (mv (ok) nil))
             ((vl-coretype item.vartype) item.vartype)

             ;; These sizes come from Section 6.11 of the SystemVerilog-2012 Standard
             ((when (eq item.vartype.name :vl-byte))     (mv (ok) 8))
             ((when (eq item.vartype.name :vl-shortint)) (mv (ok) 16))
             ((when (eq item.vartype.name :vl-int))      (mv (ok) 32))
             ((when (eq item.vartype.name :vl-integer))  (mv (ok) 32))
             ((when (eq item.vartype.name :vl-longint))  (mv (ok) 64))
             ((when (eq item.vartype.name :vl-time))     (mv (ok) 64))

             ((unless (or (eq item.vartype.name :vl-bit)
                          (eq item.vartype.name :vl-logic)
                          (eq item.vartype.name :vl-reg)))
              ;; Something like a real, shortreal, void, realtime, chandle, etc.,
              ;; I'm just not going to try to size these.
              (mv (ok) nil))

             ;; Else, some integer vector type.
             ((when (atom item.vartype.dims)) (mv (ok) 1)) ;; No dimensions --> 1 bit.
             ((when (consp (cdr item.vartype.dims)))
              (mv (fatal :type :vl-bad-dimensions
                         :msg "~a0: cannot size ~w1.  It has multiple dimensions,
                               which we don't yet support."
                         :args (list elem name))
                  nil))

             ;; Else there's exactly one packed dimension here.
             (dim (car item.vartype.dims))
             ((when (eq dim :vl-unsized-dimension))
              (mv (fatal :type :vl-bad-dimensions
                         :msg "~a0: cannot size ~w1.  It has an unsized dimension."
                         :args (list elem name))
                  nil))

             ((unless (vl-range-resolved-p dim))
              ;; Shouldn't happen unless we had a problem resolving ranges
              ;; earlier.
              (mv (fatal :type :vl-bad-range
                         :msg "~a0: cannot size ~w1 because its range is not ~
                               resolved: ~a2."
                         :args (list elem name dim))
                  nil))
             (size (vl-maybe-range-size dim)))
          (mv (ok) size))))

    ;; It would be surprising if we get here -- this is an identifier that
    ;; refers to something in the module, maybe an event, parameter, or
    ;; instance?  It seems like we shouldn't hit this case unless the module
    ;; contains something really strange.
    (mv (fatal :type :vl-bad-identifier
               :msg "~a0: cannot size ~w1 because it is a ~x2; we expected to ~
                     only need to size nets, registers, and variables."
               :args (list elem name (tag item)))
        nil))
  ///
  (defrule warning-irrelevance-of-vl-atom-selfsize
    (let ((ret1 (vl-atom-selfsize x mod ialist elem warnings))
          (ret2 (vl-atom-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))


(define vl-syscall-selfsize
  :parents (vl-expr-selfsize)
  :short "Compute the self-determined size of an system call."
  ((args      vl-exprlist-p)
   (arg-sizes nat-listp)
   (context   vl-expr-p)
   (elem      vl-modelement-p)
   (warnings  vl-warninglist-p))
  :guard (same-lengthp args arg-sizes)
  :returns
  (mv (warnings vl-warninglist-p)
      (size     maybe-natp :rule-classes :type-prescription))
  (declare (ignorable arg-sizes context elem))
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

  (b* ((expr (make-vl-nonatom :op :vl-syscall :args args))
       ((when (vl-$random-expr-p expr))
        (mv (ok) 32)))
    (mv (ok) nil))

  ///
  (defrule warning-irrelevance-of-vl-syscall-selfsize
    (let ((ret1 (vl-syscall-selfsize args arg-sizes context elem warnings))
          (ret2 (vl-syscall-selfsize args arg-sizes context elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))




(defines vl-interesting-size-atoms
  :parents (vl-tweak-fussy-warning-type)
  :short "Heuristic for tweaking fussy size warnings."
  :long "<p>Our basic goal is to gather all the atoms throughout an expression
that are \"relevant\" to the current self-size computation.  This is a fuzzy
concept and you should never use it for anything semantically meaningful, it's
only meant as a heuristic for generating more useful warnings.</p>"

  (define vl-expr-interesting-size-atoms ((x vl-expr-p))
    :measure (vl-expr-count x)
    :verify-guards nil
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-atomlist-p exprs)))
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (list x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x)))
      (case op
        ((:vl-bitselect :vl-unary-bitand :vl-unary-nand :vl-unary-bitor
                        :vl-unary-nor :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
                        :vl-binary-logand :vl-binary-logor
                        :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
                        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
                        :vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
                        :vl-syscall :vl-funcall :vl-mintypmax :vl-hid-dot
                        :vl-array-index :vl-index :vl-scope

                        ;; Eventually many of these may be worth considering...
                        :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
                        :vl-stream-left :vl-stream-right
                        :vl-stream-left-sized :vl-stream-right-sized

                        :vl-tagged

                        :vl-binary-wildeq :vl-binary-wildneq
                        :vl-implies :vl-equiv
                        )
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
         (impossible)))))

  (define vl-exprlist-interesting-size-atoms ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-atomlist-p exprs)))
    (if (consp x)
        (append (vl-expr-interesting-size-atoms (car x))
                (vl-exprlist-interesting-size-atoms (cdr x)))
      nil))
  ///
  (defrule true-listp-of-vl-expr-interesting-size-atoms
    (true-listp (vl-expr-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (defrule true-listp-of-vl-exprlist-interesting-size-atoms
    (true-listp (vl-exprlist-interesting-size-atoms x))
    :rule-classes :type-prescription)

  (verify-guards vl-expr-interesting-size-atoms
    :hints(("Goal" :in-theory (enable vl-nonatom->op-forward
                                      acl2::member-of-cons))))

  (deffixequiv-mutual vl-interesting-size-atoms))


(define vl-collect-unsized-ints ((x vl-exprlist-p))
  :parents (vl-tweak-fussy-warning-type)
  :returns (sub-x vl-exprlist-p)
  (cond ((atom x)
         nil)
        ((and (vl-fast-atom-p (car x))
              (vl-fast-constint-p (vl-atom->guts (car x)))
              (vl-constint->wasunsized (vl-atom->guts (car x))))
         (cons (vl-expr-fix (car x))
               (vl-collect-unsized-ints (cdr x))))
        (t
         (vl-collect-unsized-ints (cdr x))))
  ///
  (defrule vl-exprlist-resolved-p-of-vl-collect-unsized-ints
    (vl-exprlist-resolved-p (vl-collect-unsized-ints x))
    :enable vl-expr-resolved-p))


(define nats-below-p
  :parents (vl-tweak-fussy-warning-type)
  :short "Is every number in a list smaller than some maximum?"
  ((max natp)
   (x   nat-listp))
  :hooks nil
  (if (atom x)
      t
    (and (< (car x) max)
         (nats-below-p max (cdr x)))))

(define vl-tweak-fussy-warning-type
  :short "Heuristically categorize fussy warnings according to severity."
  ((type  symbolp   "Base warning type, which we may adjust.")
   (a     vl-expr-p "LHS expression, i.e., A in: A + B, or C ? A : B")
   (b     vl-expr-p "RHS expression, i.e., B in: A + B, or C ? A : B")
   (asize natp      "Self-determined size of A.")
   (bsize natp      "Self-determined size of B.")
   (op    vl-op-p   "The particular operation."))
  :returns
  (adjusted-type symbolp :rule-classes :type-prescription
                 "@('NIL') for <i>do not warn</i>, or some other warning type
                  that is derived from @('type').")

  :long "<p>This function is called when we've just noticed that A and B have
different self-sizes but are used in an expression like @('A == B'), @('A &
B'), @('C ? A : B'), or similar, and hence one or the other is going to be
implicitly extended.  We're going to issue a fussy size warning, and we want to
decide what type to give it.  I.e., is this a minor warning, or a normal
warning?</p>

<p>My original approach was just to say: the warning should be minor if ASIZE
or BSIZE is 32.  But this happens in many very common cases where unsized
numbers are used, such as:</p>

@({
    foo[3:0] == 7;          //  4 bits == 32 bits
    foo[0] ? bar[3:0] : 0;  //  foo[0] ? 4 bits : 32 bits
})

<p>Over time I have added many additional tweaks, see the comments for
details.</p>"
  (b* ((type  (acl2::symbol-fix type))
       (op    (vl-op-fix op))
       (asize (lnfix asize))
       (bsize (lnfix bsize))
       (a     (vl-expr-fix a))
       (b     (vl-expr-fix b))

       ((when (and (or (and (vl-expr-resolved-p a)
                            (< (vl-resolved->val a) (ash 1 bsize)))
                       (and (vl-expr-resolved-p b)
                            (< (vl-resolved->val b) (ash 1 asize))))
                   (member op '(:vl-qmark
                                :vl-binary-eq :vl-binary-neq
                                :vl-binary-ceq :vl-binary-cne
                                :vl-binary-lt :vl-binary-lte
                                :vl-binary-gt :vl-binary-gte
                                :vl-binary-wildeq :vl-binary-wildneq
                                :vl-binary-xnor))))
        ;; Always suppress warnings in the case where one argument or the other
        ;; is a constant.  Even though its size isn't quite right, it is not
        ;; *really* wrong.  For instance, if foo was once a three-bit wire but
        ;; now is a five-bit wire, we might run into an expression like "foo ==
        ;; 3'b7," which isn't really any kind of problem.
        nil)

       (a32p (eql asize 32))
       (b32p (eql bsize 32))
       ((unless (or a32p b32p))
        ;; Neither op is 32 bits, so this doesn't seem like it's related to
        ;; unsized numbers, go ahead and warn.
        type)

       ;; Figure out which one is 32-bit and which one is not.  We assume
       ;; they aren't both 32 bits, since otherwise we shouldn't be called.
       ((mv expr-32 size-other) (if a32p (mv a bsize) (mv b asize)))

       ;; Collect up interesting unsized ints in the 32-bit expression.  If it
       ;; has unsized ints, they're probably the reason it's 32 bits.  After
       ;; collecting them, see if they fit into the size of the other expr.
       (atoms         (vl-expr-interesting-size-atoms expr-32))
       (unsized       (vl-collect-unsized-ints atoms))
       (unsized-fit-p (nats-below-p (ash 1 size-other)
                                    (vl-exprlist-resolved->vals unsized)))
       ((unless unsized-fit-p)
        ;; Well, hrmn, there's some integer here that doesn't fit into the size
        ;; of the other argument.  This is especially interesting because
        ;; there's likely to be some kind of truncation here.  Give it a new
        ;; type.
        (intern-in-package-of-symbol (cat (symbol-name type) "-CONST-TOOBIG") type))

       ((when (consp unsized))
        ;; What does this mean?  Well, there are at least some unsized numbers
        ;; in positions that are affecting our selfsize, and every such unsized
        ;; number does fit into the new size we're going into, so it seems
        ;; pretty safe to make this a minor warning.
        (intern-in-package-of-symbol (cat (symbol-name type) "-MINOR") type)))

    ;; Otherwise, we didn't find any unsized atoms, so just go ahead and do the
    ;; warning.
    type))


(define vl-op-selfsize
  :parents (vl-expr-selfsize)
  :short "Main function for computing self-determined expression sizes."
  ((op        vl-op-p)
   (args      vl-exprlist-p)
   (arg-sizes nat-listp)
   (context   vl-expr-p)
   (elem      vl-modelement-p)
   (warnings  vl-warninglist-p))
  :guard
  (and (or (not (vl-op-arity op))
           (equal (len args) (vl-op-arity op)))
       (same-lengthp args arg-sizes))
  :returns
  (mv (warnings vl-warninglist-p)
      (size     maybe-natp :rule-classes :type-prescription))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We attempt to determine the size of the expression formed by applying some
operator, @('op'), to some arguments, @('args').  We assume that each argument
has already had its self-size computed successfully and that the results of
these computations are given as the @('arg-sizes').</p>

<p>The @('context') is irrelevant and is only used to form better error
messages; it is supposed to be the expression we are trying to size.  The
@('elem') is similarly irrelevant, and gives the broader context for this
expression.</p>

<p>This function basically implements Verilog-2005 Table 5-22, or
SystemVerilog-2012 Table 11-21. See @(see expression-sizing).</p>"

  :prepwork ((local (in-theory (enable maybe-natp))))
  :guard-hints (("Goal" :in-theory (e/d (vl-op-p vl-op-arity
                                                 acl2::hons-assoc-equal-of-cons)
                                        (nfix max (tau-system)))))

  (b* ((op      (vl-op-fix op))
       (context (vl-expr-fix context))
       (elem    (vl-modelement-fix elem)))
    (case (vl-op-fix op)
      (( ;; All of these operations have one-bit results, and we have no
        ;; expectations that their argument sizes should agree or anything like
        ;; that.
        :vl-bitselect
        :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
        :vl-unary-xor :vl-unary-xnor :vl-unary-lognot
        :vl-binary-logand :vl-binary-logor

        ;; SystemVerilog-2012 additions.  These also produce 1-bit results and
        ;; we don't care if their arguments have equal sizes.
        :vl-implies :vl-equiv)
       (mv (ok) 1))

      (( ;; These were originally part of the above case; they all return
        ;; one-bit results.  However, we separate them out because,
        ;; intuitively, their arguments "should" be the same size.  So as a
        ;; Linting feature, we add warnings if any implicit size extension will
        ;; occur.
        :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
        :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

        ;; SystemVerilog-2012 additions.  Although Table 11-21 doesn't specify
        ;; what the sizes are here, Section 11.4.6 says these produce a 1-bit
        ;; self-sized result and explains how the arguments are to be widened
        ;; similarly to ordinary equality comparisons.
        :vl-binary-wildeq :vl-binary-wildneq)
       (b* ((type (and (/= (first arg-sizes) (second arg-sizes))
                       (vl-tweak-fussy-warning-type :vl-fussy-size-warning-1
                                                    (first args)
                                                    (second args)
                                                    (first arg-sizes)
                                                    (second arg-sizes)
                                                    op)))
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: arguments to a comparison operator have ~
                         different \"self-sizes\" (~x1 versus ~x2).  The ~
                         smaller argument will be implicitly widened to match ~
                         the larger argument.  The sub-expression in question ~
                         is: ~a3."
                     :args (list elem (first arg-sizes) (second arg-sizes)
                                 context)))))
         (mv (ok) 1)))

      ((:vl-binary-power
        :vl-unary-plus :vl-unary-minus :vl-unary-bitnot
        :vl-binary-shl :vl-binary-shr :vl-binary-ashl :vl-binary-ashr)
       ;; All of these operations keep the size of their first operands.
       (mv (ok) (lnfix (first arg-sizes))))

      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem)
       ;; All of these operations take the max size of either operand.
       ;; Practically speaking we will probably never see times, div, or rem
       ;; operators.  However, plus and minus are common.  We probably do not
       ;; want to issue any size warnings in the case of plus or minus, since
       ;; one argument or the other often needs to be expanded.
       (mv (ok) (max (lnfix (first arg-sizes))
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
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: arguments to a bitwise operator have different ~
                         self-sizes (~x1 versus ~x2).  The smaller argument ~
                         will be implicitly widened to match the larger ~
                         argument.  The sub-expression in question is: ~a3."
                     :args (list elem (first arg-sizes) (second arg-sizes)
                                 context)))))
         (mv (ok) max)))

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
            (warnings
             (if (not type)
                 (ok)
               (warn :type type
                     :msg "~a0: branches of a ?: operator have different ~
                         self-sizes (~x1 versus ~x2).  The smaller branch ~
                         will be implicitly widened to match the larger ~
                         argument.  The sub-expression in question is: ~a3."
                     :args (list elem (second arg-sizes) (third arg-sizes)
                                 context)))))
         (mv (ok) max)))

      ((:vl-concat)
       ;; Concatenations have the sum of their arguments' widths
       (mv (ok) (sum-nats arg-sizes)))

      ((:vl-syscall)
       ;; We do all syscall sizing in a separate function.
       (vl-syscall-selfsize args arg-sizes context elem warnings))

      ((:vl-multiconcat)
       ;; For multiple concatenations, the size is its multiplicity times the
       ;; size of the concatenation-part.  The multiplicity can be zero.
       (b* ((multiplicity (first args))
            (concat-width (lnfix (second arg-sizes)))
            ((unless (vl-expr-resolved-p multiplicity))
             (mv (fatal :type :vl-unresolved-multiplicity
                        :msg "~a0: cannot size ~a1 because its multiplicity ~
                              has not been resolved."
                        :args (list elem context))
                 nil))
            (size (* (vl-resolved->val multiplicity) concat-width)))
         (mv (ok) size)))

      ((:vl-partselect-colon)
       ;; A part-select's width is one greater than the difference in its
       ;; indices.  For instance, a[3:0] is 4 bits, while a[3:3] is one bit.
       (b* ((left  (second args))
            (right (third args))
            ((unless (and (vl-expr-resolved-p left)
                          (vl-expr-resolved-p right)))
             (mv (fatal :type :vl-unresolved-select
                        :msg "~a0: cannot size ~a1 since it does not have ~
                              resolved indices."
                        :args (list elem context))
                 nil))
            (left-val  (vl-resolved->val left))
            (right-val (vl-resolved->val right))
            (size      (+ 1 (abs (- left-val right-val)))))
         (mv (ok) size)))

      ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
       ;; foo[base_expr +: width_expr] has the width specified by width_expr,
       ;; which must be a positive constant. (See Section 5.2.1)
       (b* ((width-expr (second args))
            ((unless (and (vl-expr-resolved-p width-expr)
                          (> (vl-resolved->val width-expr) 0)))
             (mv (fatal :type :vl-unresolved-select
                        :msg "~a0: cannot size ~a1 since its width expression ~
                              is not a resolved, positive constant."
                        :args (list elem context))
                 nil))
            (size (vl-resolved->val width-expr)))
         (mv (ok) size)))

      ((:vl-funcall)
       ;; BOZO we don't currently try to support function calls.  Eventually it
       ;; should be easy to support sizing these, since it looks like functions
       ;; are returned with a syntax like "function [7:0] getbyte;" -- we'll
       ;; just need to look up the function and return the size of its range.
       (mv (ok) nil))

      ((:vl-mintypmax)
       ;; I do not think it makes any sense to think about the size of a
       ;; mintypmax expression.  We just return nil and cause no warnings since
       ;; the width is basically "inapplicable."
       (mv (ok) nil))

      ((:vl-hid-dot :vl-array-index :vl-index :vl-scope

        ;; BOZO these might not belong here, but it seems like the
        ;; safest place to put them until they're implemented
        :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
        :vl-stream-left :vl-stream-right
        :vl-stream-left-sized :vl-stream-right-sized
        :vl-tagged
        )
       ;; We don't handle these here.  They should be handled in
       ;; vl-expr-selfsize specially, because unlike all of the other
       ;; operators, we can't assume that their subexpressions' sizes can be
       ;; computed.  Instead, we need to only try to determine the size of
       ;; "top-level" HIDs, and also specially handle array indexes.
       (mv (fatal :type :vl-programming-error
                  :msg "~a0: vl-op-selfsize should not encounter ~a1"
                  :args (list elem context))
           nil))

      (otherwise
       (progn$ (impossible)
               (mv (ok) nil)))))
  ///
  (defrule warning-irrelevance-of-vl-op-selfsize
    (let ((ret1 (vl-op-selfsize op args arg-sizes context elem warnings))
          (ret2 (vl-op-selfsize op args arg-sizes context elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))


(define vl-hidexpr-selfsize ((x        vl-expr-p)
                             (warnings vl-warninglist-p))
  :guard (vl-hidexpr-p x)
  :returns (mv (new-warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  (b* ((x (vl-expr-fix x))
       ((when (vl-fast-atom-p x))
        (mv (fatal :type :vl-hid-size-failed
                   :msg "~a0: found atomic hierarchical identifier???"
                   :args (list x))
            nil))
       (width (vl-hid-width x))
       ((unless width)
        (mv (fatal :type :vl-hid-size-failed
                   :msg "~a0: range of HID is not known."
                   :args (list x))
            nil)))
    (mv (ok) width))
  ///
  (defrule vl-hidexpr-selfsize-normalize-warnings
    (implies (syntaxp (not (equal warnings ''nil)))
             (equal (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                    (mv-nth 1 (vl-hidexpr-selfsize x nil)))))

  (defrule vl-hidexpr-welltyped-p-of-selfsize
    (implies (and (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                  (equal type :vl-unsigned)
                  (force (not (vl-atom-p x)))
                  (force (vl-hidexpr-p x))
                  )
             (vl-hidexpr-welltyped-p
              (make-vl-nonatom :op op
                               :args (vl-nonatom->args x)
                               :atts (vl-nonatom->atts x)
                               :finalwidth (mv-nth 1 (vl-hidexpr-selfsize x warnings))
                               :finaltype type)))
    :enable vl-hidexpr-welltyped-p))


(defines vl-expr-selfsize
  :short "Computation of self-determined expression sizes."

  :long "<p><b>Warning</b>: these functions should typically only be called by
the @(see expression-sizing) transform.</p>

<p>Some failures are expected, e.g., we do not know how to size some system
calls.  In these cases we do not cause any warnings.  But in other cases, a
failure might mean that the expression is malformed in some way, e.g., maybe it
references an undefined wire or contains a raw, \"unindexed\" reference to an
array.  In these cases we generate fatal warnings.</p>

<p>BOZO we might eventually add as inputs the full list of modules and a
modalist so that we can look up HIDs.  An alternative would be to use the
annotations left by @(see vl-modulelist-follow-hids) like (e.g.,
@('VL_HID_RESOLVED_RANGE_P')) to see how wide HIDs are.</p>"

  (define vl-expr-selfsize
    ((x        vl-expr-p        "Expression whose size we are to compute.")
     (mod      vl-module-p      "Module where the expression occurs, so we
                                 can look up wire sizes, etc.")
     (ialist   (equal ialist (vl-moditem-alist mod)) "For fast lookups.")
     (elem     vl-modelement-p  "Context for warnings.")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
    :returns
    (mv (warnings vl-warninglist-p)
        (size     maybe-natp :rule-classes :type-prescription))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))

         ((when (vl-fast-atom-p x))
          (vl-atom-selfsize x mod ialist elem warnings))

         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ((when (vl-hidexpr-p x))
          (vl-hidexpr-selfsize x warnings))

         ((when (member op '(:vl-array-index)))
          ;; BOZO we should try to size array-indexing here.  For now I'm
          ;; skipping this so I can press on.
          (mv (ok) nil))

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

  (define vl-exprlist-selfsize
    ((x        vl-exprlist-p    "Expressions whose sizes we are to compute.")
     (mod      vl-module-p      "Module where the expression occurs, so we
                                 can look up wire sizes, etc.")
     (ialist   (equal ialist (vl-moditem-alist mod)) "For fast lookups.")
     (elem     vl-modelement-p  "Context for warnings.")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
    :returns
    (mv (warnings vl-warninglist-p)
        (size-list (and (vl-maybe-nat-listp size-list)
                        (equal (len size-list) (len x)))))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-size)
          (vl-expr-selfsize (car x) mod ialist elem warnings))
         ((mv warnings cdr-sizes)
          (vl-exprlist-selfsize (cdr x) mod ialist elem warnings))
         (sizes (cons car-size cdr-sizes)))
      (mv warnings sizes)))
  ///

  (local
   (defthm-vl-expr-selfsize-flag
     (defthm true-listp-of-vl-exprlist-selfsize
       (true-listp (mv-nth 1 (vl-exprlist-selfsize x mod ialist elem warnings)))
       :rule-classes :type-prescription
       :flag :list)
     :skip-others t))

  (verify-guards vl-expr-selfsize)

  (local
   (defthm-vl-expr-selfsize-flag
     ;; This is pretty subtle.  The induction scheme that the flag function
     ;; would generate if we tried to directly use warnings and NIL isn't right
     ;; in the list case.  We have to generalize this to an arbitrary warnings1
     ;; and warnings2.  Then, ACL2's induction heuristic is smart enough to get
     ;; the right scheme, but only when we tell it to consider the flag function
     ;; for both warnings1 and warnings2.  Ugh.  This took a long time to figure
     ;; out.
     (defthm l0
       (let ((ret1 (vl-expr-selfsize x mod ialist elem warnings1))
             (ret2 (vl-expr-selfsize x mod ialist elem warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :expr)

     (defthm l1
       (let ((ret1 (vl-exprlist-selfsize x mod ialist elem warnings1))
             (ret2 (vl-exprlist-selfsize x mod ialist elem warnings2)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :list)

     :hints(("Goal"
             :do-not '(generalize fertilize)
             :induct (and (vl-expr-selfsize-flag flag x mod ialist elem warnings1)
                          (vl-expr-selfsize-flag flag x mod ialist elem warnings2))
             :expand ((vl-expr-selfsize x mod ialist elem warnings1)
                      (vl-expr-selfsize x mod ialist elem warnings2))))))

  (defrule warning-irrelevance-of-vl-expr-selfsize
    (let ((ret1 (vl-expr-selfsize x mod ialist elem warnings))
          (ret2 (vl-expr-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance l0 (warnings1 warnings) (warnings2 nil))))

  (defrule warning-irrelevance-of-vl-exprlist-selfsize
    (let ((ret1 (vl-exprlist-selfsize x mod ialist elem warnings))
          (ret2 (vl-exprlist-selfsize x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance l1 (warnings1 warnings) (warnings2 nil))))

  (deffixequiv-mutual vl-expr-selfsize))


; -----------------------------------------------------------------------------
;
;                    DETERMINATION OF FINAL SIGNEDNESS
;
; -----------------------------------------------------------------------------

(define vl-atom-typedecide
  :parents (vl-expr-typedecide)
  :short "Effectively computes the \"self-determined\" type of an atom."
  ((x        vl-expr-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod)))
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :guard (vl-atom-p x)
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (equal (vl-exprtype-p type) (if type t nil)))))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We compute what the type of the atom @('x') would be if it were in a
self-determined location.  Another way to look at this function is as an
extension of \"origtype\" from constint/weirdint atoms to include identifiers
and strings.</p>

<p>The @('type') we return is a @(see vl-maybe-exprtype-p).  Similarly to @(see
vl-atom-selfsize), we might fail and return @('nil') for the type, perhaps
producing some warnings.</p>"

  (b* ((elem (vl-modelement-fix elem))
       (guts (vl-atom->guts x))

       ((when (vl-fast-constint-p guts))
        (mv (ok) (vl-constint->origtype guts)))

       ((when (vl-fast-weirdint-p guts))
        (mv (ok) (vl-weirdint->origtype guts)))

       ((when (vl-fast-string-p guts))
        (mv (ok) :vl-unsigned))

       ((unless (vl-fast-id-p guts))
        ;; Other kinds of atoms don't get a type.
        (mv (ok) nil))

       (name (vl-id->name guts))
       (item (vl-fast-find-moduleitem name mod ialist))

       ((unless item)
        ;; Shouldn't happen if the module is well-formed and all used names are
        ;; declared.
        (mv (fatal :type :vl-bad-identifier
                   :msg "~a0: cannot determine the type of ~w1 because it ~
                         is not declared."
                   :args (list elem name))
            nil))

       (tag (tag item))
       ((when (eq tag :vl-netdecl))
        (b* (((vl-netdecl item) item)
             ((when (consp item.arrdims))
              ;; Shouldn't happen unless the module directly uses the name of
              ;; an array in an expression.
              (mv (fatal :type :vl-bad-identifier
                         :msg "~a0: cannot determine the type of ~w1 because ~
                               it is an unindexed reference to an array."
                         :args (list elem name))
                  nil))
             (type (if item.signedp :vl-signed :vl-unsigned)))
          (mv (ok) type)))

       ((when (eq tag :vl-vardecl))
        (b* (((vl-vardecl item) item)
             ((when (consp item.dims))
              ;; Shouldn't happen unless the module directly uses the name of
              ;; an array in an expression.
              (mv (fatal :type :vl-bad-identifier
                         :msg "~a0: cannot determine the type of ~w1 because ~
                               it is an unindexed reference to an array."
                         :args (list elem name))
                  nil))
             ((unless (eq (vl-datatype-kind item.vartype) :vl-coretype))
              ;; Don't try to size tricky things yet.
              (mv (ok) nil))
             ((vl-coretype item.vartype) item.vartype)
             ((when (member item.vartype.name
                            '(:vl-byte :vl-shortint :vl-int :vl-integer :vl-longint :vl-time
                              :vl-bit :vl-logic :vl-reg)))
              ;; See also vl-parse-core-data-type.  When using any of the above
              ;; types, a logic designer can provide an optional `signed` or
              ;; `unsigned` keyword that, presumably, overrides the default
              ;; signedness.  The parser handles this and must set up the
              ;; coretype.signedp field appropriately.  So, here, we just need
              ;; to look at that field.
              (mv (ok) (if item.vartype.signedp
                           :vl-signed
                         :vl-unsigned))))
          ;; Else, some other kind of core type, like void, string, chandle,
          ;; event, or similar.  We're not going to assign any type to these.
          (mv (ok) nil))))

    ;; It would be surprising if we get here -- this is an identifier that
    ;; refers to something in the module, maybe an event, parameter, or
    ;; instance?  It seems like we shouldn't hit this case unless the module
    ;; contains something really strange.
    (mv (fatal :type :vl-bad-identifier
               :msg "~a0: cannot determine the type of ~w1 because it is a ~
                     ~x2; we only expected to type net, register, and ~
                     variable declarations."
               :args (list elem name (tag item)))
        nil))
  ///
  (defrule warning-irrelevance-of-vl-atom-typedecide
    (let ((ret1 (vl-atom-typedecide x mod ialist elem warnings))
          (ret2 (vl-atom-typedecide x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))


(deflist vl-maybe-exprtype-list-p (x)
  (vl-maybe-exprtype-p x))

(defines vl-expr-typedecide-aux
  :parents (vl-expr-typedecide)
  :short "Core of computing expression signedness."

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

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

  (define vl-expr-typedecide-aux ((x        vl-expr-p)
                                  (mod      vl-module-p)
                                  (ialist   (equal ialist (vl-moditem-alist mod)))
                                  (elem     vl-modelement-p)
                                  (warnings vl-warninglist-p)
                                  (mode     (or (eq mode :probably-wrong)
                                                (eq mode :probably-right))))
    :verify-guards nil
    :returns (mv (warnings vl-warninglist-p)
                 (type     (and (vl-maybe-exprtype-p type)
                                (equal (vl-exprtype-p type)
                                       (if type t nil)))))
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x        (vl-expr-fix x))
         (warnings (vl-warninglist-fix warnings))
         (elem     (vl-modelement-fix elem))

         ((when (vl-fast-atom-p x))
          (vl-atom-typedecide x mod ialist elem warnings))

         ((when (vl-hidexpr-p x))
          (if (assoc-equal "VL_HID_RESOLVED_RANGE_P" (vl-nonatom->atts x))
              ;; this implies it's unsigned
              (mv warnings :vl-unsigned)
            (mv (fatal :type :vl-bad-hid
                       :msg "~a0: Couldn't resolve the type of HID ~a1."
                       :args (list elem x))
                nil)))

         (op        (vl-nonatom->op x))
         (args      (vl-nonatom->args x))
         ((mv warnings arg-types)
          (vl-exprlist-typedecide-aux args mod ialist elem warnings mode)))

      (case op

        (( ;; From Verilog-2005 5.5.1, bit-selects, part-selects,
          ;; concatenations, and comparisons always produce unsigned results,
          ;; no matter the signedness of their operands.
          :vl-bitselect
          :vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
          :vl-concat :vl-multiconcat
          :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
          :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

          ;; SystemVerilog-2012 extensions: I believe (although it's hard to
          ;; find good evidence in the spec to support this) that these are
          ;; also producing 1-bit unsigned answers.
          :vl-binary-wildneq :vl-binary-wildeq
          )

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

        ((:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)
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

        ((:vl-index :vl-hid-dot :vl-scope

          ;; BOZO these might not belong here, but it seems like the
          ;; safest place to put them until they're implemented
          :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
          :vl-stream-left :vl-stream-right
          :vl-stream-left-sized :vl-stream-right-sized
          :vl-tagged
          )
         ;; Should have handled these above.
         (mv warnings nil))

        ((:vl-mintypmax)
         ;; I think it makes no sense to try to assign a type to these.
         (mv warnings nil))

        (otherwise
         (mv warnings (impossible))))))

  (define vl-exprlist-typedecide-aux ((x        vl-exprlist-p)
                                      (mod      vl-module-p)
                                      (ialist   (equal ialist (vl-moditem-alist mod)))
                                      (elem     vl-modelement-p)
                                      (warnings vl-warninglist-p)
                                      (mode     (or (eq mode :probably-wrong)
                                                    (eq mode :probably-right))))
    :returns (mv (warnings vl-warninglist-p)
                 (types    vl-maybe-exprtype-list-p))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-type)
          (vl-expr-typedecide-aux (car x) mod ialist elem warnings mode))
         ((mv warnings cdr-type)
          (vl-exprlist-typedecide-aux (cdr x) mod ialist elem warnings mode)))
      (mv warnings (cons car-type cdr-type))))

  ///
  (local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                            vl-warninglist-p-when-subsetp-equal
                            set::double-containment
                            arg1-exists-by-arity
                            default-car
                            default-cdr)))

  (defrule vl-exprlist-typedecide-aux-when-atom
    (implies (atom x)
             (equal (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)
                    (mv (ok) nil))))

  (defrule vl-exprlist-typedecide-aux-of-cons
    (equal (vl-exprlist-typedecide-aux (cons a x) mod ialist elem warnings mode)
           (b* (((mv warnings car-type)
                 (vl-expr-typedecide-aux a mod ialist elem warnings mode))
                ((mv warnings cdr-type)
                 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
             (mv warnings (cons car-type cdr-type)))))

  (defthm-vl-expr-typedecide-aux-flag
    (defthm len-of-vl-exprlist-typedecide-aux
      (equal (len (mv-nth 1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
             (len x))
      :flag :list)
    :skip-others t)

  (defthm-vl-expr-typedecide-aux-flag
    (defthm true-listp-of-vl-exprlist-typedecide-aux
      (true-listp (mv-nth 1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode)))
      :rule-classes :type-prescription
      :flag :list)
    :skip-others t)

  (verify-guards vl-expr-typedecide-aux
    :hints(("Goal" :in-theory (enable vl-nonatom->op-forward
                                      acl2::member-of-cons))))

  (local
   (defthm-vl-expr-typedecide-aux-flag
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
       :flag :expr)
     (defthm w1
       (let ((ret1 (vl-exprlist-typedecide-aux x mod ialist elem warnings1 mode))
             (ret2 (vl-exprlist-typedecide-aux x mod ialist elem warnings2 mode)))
         (equal (mv-nth 1 ret1)
                (mv-nth 1 ret2)))
       :rule-classes nil
       :flag :list)
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :induct (and (vl-expr-typedecide-aux-flag flag x mod ialist elem warnings1 mode)
                          (vl-expr-typedecide-aux-flag flag x mod ialist elem warnings2 mode))
             :expand ((:free (mode) (vl-expr-typedecide-aux x mod ialist elem warnings1 mode))
                      (:free (mode) (vl-expr-typedecide-aux x mod ialist elem warnings2 mode)))))))

  (defrule warning-irrelevance-of-vl-expr-typedecide-aux
    (let ((ret1 (vl-expr-typedecide-aux x mod ialist elem warnings mode))
          (ret2 (vl-expr-typedecide-aux x mod ialist elem nil mode)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance w0 (warnings1 warnings) (warnings2 nil))))

  (defrule warning-irrelevance-of-vl-exprlist-typedecide-aux
    (let ((ret1 (vl-exprlist-typedecide-aux x mod ialist elem warnings mode))
          (ret2 (vl-exprlist-typedecide-aux x mod ialist elem nil mode)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))
    :use ((:instance w1 (warnings1 warnings) (warnings2 nil))))

  (defrule symbolp-of-vl-expr-typedecide-aux
    (symbolp (mv-nth 1 (vl-expr-typedecide-aux x mod ialist elem warnings mode)))
    :rule-classes :type-prescription)

  (deffixequiv-mutual vl-expr-typedecide-aux))



(define vl-expr-typedecide
  :parents (vl-expr-size)
  :short "Computation of expression signedness (main routine)."

  ((x        vl-expr-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod)))
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (type     (and (vl-maybe-exprtype-p type)
                              (equal (vl-exprtype-p type) (if type t nil)))))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

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

  (b* ((x    (vl-expr-fix x))
       (elem (vl-modelement-fix elem))
       ((mv warnings right-type) (vl-expr-typedecide-aux x mod ialist elem warnings :probably-right))
       ((mv warnings wrong-type) (vl-expr-typedecide-aux x mod ialist elem warnings :probably-wrong))
       (warnings
        (if (eq right-type wrong-type)
            warnings
          (warn :type :vl-warn-vague-spec
                :msg "~a0: expression ~a1 has a type which is not necessarily ~
                      clear according to the discussion in the Verilog-2005 ~
                      standard.  We believe its type should be ~s2, but think ~
                      it would be easy for other Verilog systems to ~
                      mistakenly interpret the expression as ~s3.  To reduce ~
                      any potential confusion, you may wish to rewrite this ~
                      expression to make its signedness unambiguous.  Some ~
                      typical causes of signedness are plain decimal numbers ~
                      like 10, and the use of integer variables instead of ~
                      regs."
                :args (list elem x right-type wrong-type)))))
    (mv warnings right-type))

  ///
  (defrule warning-irrelevance-of-vl-expr-typedecide
    (let ((ret1 (vl-expr-typedecide x mod ialist elem warnings))
          (ret2 (vl-expr-typedecide x mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))



; -----------------------------------------------------------------------------
;
;                PROPAGATION OF FINAL WIDTH/SIGN INTO OPERANDS
;
; -----------------------------------------------------------------------------

(define vl-expandsizes-zeroextend
  :parents (vl-expr-expandsizes)
  :short "Safely zero-extend an already-sized, unsigned expression to finalwidth."

  ((x          vl-expr-p        "An expression that we may need to zero-extend.")
   (finalwidth natp             "Width we want to expand @('x') to.  Must be at least
                                 as large as the final width of @('x').")
   (elem       vl-modelement-p  "Context for warnings.")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard (and (vl-expr->finalwidth x)
              (eq (vl-expr->finaltype x) :vl-unsigned))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>If an extension is needed, we introduce an explicit concatenation, e.g., if
we are expanding @('foo') from 3 to 7 bits, we produce a new expression like
@('{ 4'b0, foo }').  When no extension is needed, we just return @('x')
unchanged.</p>"

  (b* ((x            (vl-expr-fix x))
       (elem         (vl-modelement-fix elem))
       (finalwidth   (lnfix finalwidth))
       (x.finalwidth (lnfix (vl-expr->finalwidth x)))

       ((when (> x.finalwidth finalwidth))
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: trying to zero-extend ~a1, which has width ~x2, ~
                         to ~x3 bits??? Serious bug in our sizing code."
                   :args (list elem x x.finalwidth finalwidth))
            x))

       ((when (eql x.finalwidth finalwidth))
        ;; No need to expand.
        (mv t (ok) x))

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
    (mv t (ok) concat))
  ///
  (defrule warning-irrelevance-of-vl-expandsizes-zeroextend
    (let ((ret1 (vl-expandsizes-zeroextend x finalwidth elem warnings))
          (ret2 (vl-expandsizes-zeroextend x finalwidth elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule vl-expr->finalwidth-of-vl-expandsizes-zeroextend
    (implies (and (mv-nth 0 (vl-expandsizes-zeroextend x finalwidth elem warnings))
                  (force (vl-expr->finalwidth x))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (equal (vl-expr->finalwidth
                     (mv-nth 2 (vl-expandsizes-zeroextend x finalwidth elem warnings)))
                    (nfix finalwidth))))

  (defrule no-change-loser-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr->finaltype-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      :vl-unsigned))))

  (defrule vl-expr-welltyped-p-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-expr-welltyped-p vl-atom-welltyped-p acl2::member-of-cons)))



(define vl-sign-extend-constint
  :parents (vl-expr-expandsizes)
  :short "@(call vl-sign-extend-constint) returns a new value, which is the
sign extension of the @('origwidth')-bit @('value') to @('finalwidth') bits."
  ((value natp)
   (origwidth posp)
   (finalwidth posp))
  :guard (and (< value (expt 2 origwidth))
              (< origwidth finalwidth))
  :hooks nil
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
  (b* ( ;; Logbitp indexes from 0, so to get the most significant bit of an
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
    result)
  ///
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

  (defrule natp-of-vl-sign-extend-constint
    (implies (and (force (natp value))
                  (force (posp origwidth))
                  (force (< value (expt 2 origwidth)))
                  (force (posp finalwidth))
                  (force (< origwidth finalwidth)))
             (natp (vl-sign-extend-constint value origwidth finalwidth)))
    :rule-classes :type-prescription
    :enable logxor)

  (defrule upper-bound-of-vl-sign-extend-constint
    (implies (and (force (natp value))
                  (force (posp origwidth))
                  (force (< value (expt 2 origwidth)))
                  (force (posp finalwidth))
                  (force (< origwidth finalwidth)))
             (< (vl-sign-extend-constint value origwidth finalwidth)
                (expt 2 finalwidth)))
    :rule-classes ((:rewrite) (:linear))))


(define vl-constint-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a constant
integer atom."

  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (elem       vl-modelement-p)
   (warnings   vl-warninglist-p))
  :guard (and (vl-atom-p x)
              (vl-fast-constint-p (vl-atom->guts x)))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

  :verbosep t
  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

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

  ;; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (elem       (vl-modelement-fix elem))
       (finalwidth (lnfix finalwidth))
       (finaltype  (vl-exprtype-fix finaltype))

       (guts (vl-atom->guts x))
       ((vl-constint guts) guts)

       ((when (> guts.origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. ~
                           This indicates a serious bug in our sizing code."
                   :args (list elem x))
            x))

       ((unless (or (eq guts.origtype finaltype)
                    (and (eq guts.origtype :vl-signed)
                         (eq finaltype :vl-unsigned))))
        ;; Sanity check.  This must never happen because the finaltype of the
        ;; expression must be unsigned if any operand was unsigned.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                           expanding ~a3.  This indicates a serious bug in ~
                           our typing code."
                   :args (list elem guts.origtype finaltype x))
            x))

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
          (mv t (ok) new-x)))

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
          (mv t (ok) new-x)))

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
        (mv t (ok) new-x))

       ;; Unsized, signed value being extended -- we add a special warning,
       (minorp (= new-value guts.value))
       (warnings
        (warn :type (if minorp
                        :vl-warn-integer-size-minor
                      :vl-warn-integer-size)
              :msg (if minorp
                       "~a0: the unsized integer ~a1 occurs in a context ~
                          that is larger than 32-bits.  In rare cases ~
                          (particularly involving right-shifts), the ~
                          resulting expression may produce different results ~
                          on Verilog implementations with different integer ~
                          sizes; consider adding an explicit size to this ~
                          number."
                     "~a0: the unsized integer ~a1 occurs in a signed ~
                        context that is larger than 32-bits; it is likely ~
                        that this could cause the expression results to ~
                        differ between Verilog implementations that have ~
                        different integer sizes.  Adding an explicit size to ~
                        this number is recommended.")
              :args (list elem x))))
    (mv t warnings new-x))
  ///
  (defrule warning-irrelevance-of-vl-constint-atom-expandsizes
    (let ((ret1 (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-constint-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-weirdint-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."

  :verbosep t
  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (elem       vl-modelement-p)
   (warnings   vl-warninglist-p))
  :guard (and (vl-atom-p x)
              (vl-fast-weirdint-p (vl-atom->guts x)))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (guts       (vl-atom->guts x))
       (finalwidth (lnfix finalwidth))
       (finaltype  (vl-exprtype-fix finaltype))
       (elem       (vl-modelement-fix elem))

       ((vl-weirdint guts) guts)

       ((when (> guts.origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x))
            x))

       ((unless (or (eq guts.origtype finaltype)
                    (and (eq guts.origtype :vl-signed)
                         (eq finaltype :vl-unsigned))))
        ;; Sanity check.  This must never happen because the finaltype of the
        ;; expression must be unsigned if any operand was unsigned.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                         expanding ~a3.  This indicates a serious bug in our ~
                         typing code."
                   :args (list elem guts.origtype finaltype x))
            x))

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
          (mv t (ok) new-x)))

       ;; If we get this far, expansion is necessary.  If the finaltype is
       ;; signed, then by our above check we know that the origtype is also
       ;; signed, and we want to do a sign-extension.
       ((when (eq finaltype :vl-unsigned))
        ;; Just do a zero-extension.
        (b* ((new-bits (append (replicate (- finalwidth guts.origwidth) :vl-0val)
                               (redundant-list-fix guts.bits)))
             (new-guts (change-vl-weirdint guts
                                           :bits new-bits
                                           :origwidth finalwidth
                                           :origtype finaltype))
             (new-x    (change-vl-atom x
                                       :guts new-guts
                                       :finalwidth finalwidth
                                       :finaltype finaltype)))
          (mv t (ok) new-x)))

       ;; Else, we want a sign-extension.
       (sign-bit  (car guts.bits))
       (new-bits  (append (replicate (- finalwidth guts.origwidth) sign-bit)
                          (redundant-list-fix guts.bits)))
       (new-guts  (change-vl-weirdint guts
                                      :bits new-bits
                                      :origwidth finalwidth))
       (new-x     (change-vl-atom x
                                  :guts new-guts
                                  :finalwidth finalwidth
                                  :finaltype finaltype))

       ((unless guts.wasunsized)
        (mv t (ok) new-x))

       ;; Unsized, signed value being extended -- we add a special warning,

       (minorp (eq sign-bit :vl-0val))
       (warnings
        (warn :type (if minorp
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
                      that is larger than 32-bits; it is likely that this ~
                      could cause the expression results to differ between ~
                      Verilog implementations that have different integer ~
                      sizes.  Adding an explicit size to this number is ~
                      recommended.")
              :args (list elem x))))

    (mv t warnings new-x))
  ///
  (defrule warning-irrelevance-of-vl-weirdint-atom-expandsizes
    (let ((ret1 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-weirdint-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (lnfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-idatom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into an
identifier atom."

  ((x           vl-expr-p)
   (finalwidth  natp)
   (finaltype   vl-exprtype-p)
   (mod         vl-module-p)
   (ialist      (equal ialist (vl-moditem-alist mod)))
   (elem        vl-modelement-p)
   (warnings    vl-warninglist-p))
  :guard (and (vl-atom-p x)
              (vl-fast-id-p (vl-atom->guts x)))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

  ;; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (elem       (vl-modelement-fix elem))
       (finalwidth (lnfix finalwidth))
       (finaltype  (vl-exprtype-fix finaltype))

       (guts (vl-atom->guts x))
       (name (vl-id->name guts))

       ((mv warnings origwidth) (vl-atom-selfsize x mod ialist elem warnings))
       ((mv warnings origtype)  (vl-atom-typedecide x mod ialist elem warnings))

       ((unless (and origwidth origtype))
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: expected to only try to expand sizes for atoms ~
                         whose sizes types can be successfully determined, ~
                         but we failed to determine the size or type of ~w1."
                   :args (list elem name))
            x))

       ((when (> origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x))
            x))

       ((unless (or (eq origtype finaltype)
                    (and (eq origtype :vl-signed)
                         (eq finaltype :vl-unsigned))))
        ;; Sanity check.  This must never happen because the finaltype of the
        ;; expression must be unsigned if any operand was unsigned.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origtype is ~s1 but finaltype is ~s2 when ~
                         expanding ~a3.  This indicates a serious bug in our ~
                         typing code."
                   :args (list elem origtype finaltype x))
            x))

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
    (mv t (ok) new-x))
  ///
  (defrule warning-irrelevance-of-vl-idatom-expandsizes
    (let ((ret1 (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings))
          (ret2 (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist
                                      elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p
             vl-expr-welltyped-p
             ;; ugly, but we need to see that the atom size is non-zero.
             vl-atom-selfsize))

  (defrule vl-expr->finalwidth-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-idatom-expandsizes
    (let ((ret (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-id-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-string-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."

  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (elem       vl-modelement-p)
   (warnings   vl-warninglist-p))
  :guard (and (vl-atom-p x)
              (vl-fast-string-p (vl-atom->guts x)))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

  ;; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (finalwidth (lnfix finalwidth))
       (finaltype  (vl-exprtype-fix finaltype))
       (elem       (vl-modelement-fix elem))

       (guts (vl-atom->guts x))
       ((vl-string guts) guts)

       (origwidth (* 8 (length guts.value)))

       ((when (> origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list elem x))
            x))

       ((unless (eq finaltype :vl-unsigned))
        ;; Sanity check.  This must never happen because the finaltype of the
        ;; expression must be unsigned if any operand was unsigned.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: finaltype is ~s1 when expanding ~a2.  This ~
                         indicates a serious bug in our sizing/typing code."
                   :args (list elem finaltype x))
            x))

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

    (mv t warnings new-x))

  ///
  (defrule warning-irrelevance-of-vl-string-atom-expandsizes
    (let ((ret1 (vl-string-atom-expandsizes x finalwidth finaltype elem warnings))
          (ret2 (vl-string-atom-expandsizes x finalwidth finaltype elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into an atom."
  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (mod        vl-module-p)
   (ialist     (equal ialist (vl-moditem-alist mod)))
   (elem       vl-modelement-p)
   (warnings   vl-warninglist-p))
  :guard (vl-atom-p x)
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))
  (b* ((x    (vl-expr-fix x))
       (elem (vl-modelement-fix elem))
       (guts (vl-atom->guts x))
       ((when (vl-fast-constint-p guts)) (vl-constint-atom-expandsizes x finalwidth finaltype elem warnings))
       ((when (vl-fast-weirdint-p guts)) (vl-weirdint-atom-expandsizes x finalwidth finaltype elem warnings))
       ((when (vl-fast-id-p guts))       (vl-idatom-expandsizes x finalwidth finaltype mod ialist elem warnings))
       ((when (vl-fast-string-p guts))   (vl-string-atom-expandsizes x finalwidth finaltype elem warnings)))
    ;; Otherwise, we shouldn't have tried to size this.
    (mv nil
        (fatal :type :vl-programming-error
               :msg "~a0: expected to only try to expand sizes for atoms ~
                     whose self-sizes and types can be successfully ~
                     determined, but we are trying to expand an atom of type ~
                     ~x1: ~a2."
               :args (list elem (tag guts) x))
        x))
  ///
  (local (in-theory (disable natp nfix)))

  (defrule warning-irrelevance-of-vl-atom-expandsizes
    (let ((ret1 (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings))
          (ret2 (vl-atom-expandsizes x finalwidth finaltype mod ialist elem nil)))
      (implies (syntaxp (not (equal warnings ''nil)))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-warn-about-signed-shifts
  :parents (vl-expr-typedecide)
  :short "Special warnings about shifting by signed amounts."
  :long "<p>See @(see expression-sizing-minutia); we warn about shifts by
a signed value since Verilog-XL doesn't handle them correctly.</p>"
  ((rhs      vl-expr-p)
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :guard (vl-expr->finaltype rhs)
  :returns (new-warnings vl-warninglist-p)
  (b* ((rhs  (vl-expr-fix rhs))
       (elem (vl-modelement-fix elem))

       (want-to-warn-p
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
        (ok)))
    (warn :type :vl-warn-signed-shift
          :msg "~a0: found a shift-expression with a signed shift amount, ~
                ~a1.  This is dangerous because whereas NCVerilog properly ~
                follows the Verilog-2005 standard (5.1.12) and treats the ~
                right-hand side as unsigned, Verilog-XL incorrectly treats ~
                negative right-shifts as left-shifts.  We follow the ~
                Verilog-2005 standard and mimick NCVerilog, but to ensure ~
                compatibility, you should probably rewrite this expression to ~
                ensure that the right-hand side is unsigned.  For example, ~
                you might wrap the right-hand side in a concatnation, e.g., ~
                \"a >> {b}\" instead of \"a >> b\"."
          :args (list elem rhs))))


(define vl-warn-about-implicit-extension
  :short "Lint-like warnings about right hand sides being extended."

  :long "<p>Extension warnings are very, very good to have, and have found a
lot of bugs.  However, we need to be pretty clever to avoid getting too many
trivial, nitpicky complaints about assignments that aren't really bugs.</p>

<p>We found that extension warnings were frequently triggered by things like
@('assign {carry,sum} = a + b') where the designer seems to explicitly intend
to get the carry bit.  We therefore only cause a minor warning if the
right-hand side is composed only of additions.  Later it turned out we need to
permit selects, too.  And later we decided to also add subtraction as a
permitted operation.</p>

<p>Another kind of extension warning that is stupidly minor is when we just
have assignments like @('assign foo[127:0] = 0;').  We now do not even create a
minor warning for assignments where the rhs is a constant.</p>"

  ((lhs-size natp       "We assume this is greater than the size of X, so we are
                         going to issue an extension warning.")
   (x-selfsize natp)
   (x          vl-expr-p)
   (mod        vl-module-p)
   (ialist     (equal ialist (vl-moditem-alist mod)))
   (elem       vl-modelement-p)
   (warnings   vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  :verbosep t
  (declare (ignorable
            ;; We add these in case we want to look at sizes of subexpressions
            ;; in the future.
            lhs-size mod ialist))

  ;; We need to determine what kind of warning to issue.  Note that this can be
  ;; pretty inefficient since we only call it infrequently.

  (b* ((lhs-size   (lnfix lhs-size))
       (x-selfsize (lnfix x-selfsize))
       (x          (vl-expr-fix x))
       (elem       (vl-modelement-fix elem))

       (ops     (vl-expr-ops x))

       ((when (and (vl-fast-atom-p x)
                   (vl-constint-p (vl-atom->guts x))
                   (vl-constint->wasunsized (vl-atom->guts x))))
        ;; Completely trivial, don't give any warning.
        (ok))

       (minorp (and (or (member-equal :vl-binary-plus ops)
                        (member-equal :vl-binary-minus ops))
                    (subsetp-equal ops '(:vl-binary-plus
                                         :vl-binary-minus
                                         :vl-partselect-colon
                                         :vl-bitselect)))))
    (warn :type (if minorp
                    :vl-warn-extension-minor
                  :vl-warn-extension)
          :msg "~a0: implicit extension from ~x1-bit expression to ~x2-bit ~
                 lvalue.~%     rhs: ~a3"
          :args (list elem x-selfsize lhs-size x))))



(local (in-theory (enable maybe-natp-fix)))

(local (def-ruleset my-disables
         '( ;(:rules-of-class :type-prescription :here)
           set::double-containment
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
           vl-expr-resolved-p-of-car-when-vl-exprlist-resolved-p
           vl-exprlist-resolved-p-of-cdr-when-vl-exprlist-resolved-p
           natp-when-member-equal-of-nat-listp
           vl-modelement-fix-when-vl-modelement-p
           vl-warninglist-fix-when-vl-warninglist-p
           vl-nonatom->op-when-hidindex-resolved-p
           vl-nonatom->op-when-vl-hidindex-p
           vl-atom-p-of-car-when-vl-atomlist-p
           acl2::true-listp-member-equal
           SUM-NATS-WHEN-ATOM
           ALL-EQUALP-WHEN-ATOM
           ARG1-EXISTS-BY-ARITY
           all-equalp

           WARNING-IRRELEVANCE-OF-VL-EXPANDSIZES-ZEROEXTEND
           WARNING-IRRELEVANCE-OF-VL-EXPR-TYPEDECIDE
           WARNING-IRRELEVANCE-OF-VL-EXPR-SELFSIZE
           NO-CHANGE-LOSER-OF-VL-EXPANDSIZES-ZEROEXTEND
           NO-CHANGE-LOSERP-OF-VL-ATOM-EXPANDSIZES

           ACL2::CONSP-MEMBER-EQUAL
           VL-EXPR-FIX-WHEN-VL-EXPR-P
           VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
           VL-EXPRLIST->FINALWIDTHS-WHEN-NOT-CONSP

           (:TYPE-PRESCRIPTION MEMBER-EQUAL)
           VL-EXPANDSIZES-ZEROEXTEND-OF-VL-MODELEMENT-FIX-ELEM

           VL-HIDINDEX-RESOLVED-P-WHEN-VL-HIDEXPR-RESOLVED-P
           VL-HIDINDEX-P-WHEN-VL-HIDEXPR-P
           (:TYPE-PRESCRIPTION VL-NONATOM->OP$INLINE)
           ACL2::NATP-WHEN-MAYBE-NATP
           MEMBER-EQUAL-WHEN-ALL-EQUALP
           )))


(defines vl-expr-size
  :parents (expression-sizing)
  :verify-guards nil

; BOZO we might be able to strengthen the guards here so that we don't need to
; explicitly check for signed finalwidths in unsigned operators like compares.
; But I'm not sure exactly how this would work, yet.

  (define vl-expr-size
    :short "Determine sizes for a top-level or self-determined expression."
    ((lhs-size maybe-natp
               "To size an expression @('x') which occurs in an assignment such
               as @('assign lhs = x'), the @('lhs-size') should be the width of
               @('lhs').  To size other expressions that do not occur in
               assignments, such as a self-determined subexpression, the
               @('lhs-size') should be nil.")
     (x        vl-expr-p                             "The expression that we want to size.")
     (mod      vl-module-p                           "The module where the expression occurs.")
     (ialist   (equal ialist (vl-moditem-alist mod)) "For fast wire lookups.")
     (elem     vl-modelement-p                       "Context for sizing error messages.")
     (warnings vl-warninglist-p                      "Ordinary @(see warnings) accumulator."))
    :returns
    (mv (successp booleanp :rule-classes :type-prescription
                  "Indicates whether all sizing was successful."
                  :hints ((and stable-under-simplificationp
                               '(:expand ((:free (ialist lhs-size elem warnings)
                                           (vl-expr-size lhs-size x mod ialist elem warnings))))))
                  )
        (warnings vl-warninglist-p
                  "Possibly extended with fatal or non-fatal warnings."
                  :hints ((and stable-under-simplificationp
                               '(:expand ((:free (ialist lhs-size elem warnings)
                                           (vl-expr-size lhs-size x mod ialist elem warnings)))))))
        (new-x    vl-expr-p
                  "Updated version of @('x') where all the sizes/types have
                  been computed and installed."
                  :hints ((and stable-under-simplificationp
                               '(:expand ((:free (ialist lhs-size elem warnings)
                                           (vl-expr-size lhs-size x mod ialist elem warnings))))))))
    :long "<p>This function implements the two-phase algorithm described in
           @(see expression-sizing).  That is, it first determines the maximum
           size of any operand in @('x') and the desired type of @('x'), using
           @(see vl-expr-selfsize) and @(see vl-expr-typedecide) (which are not
           part of the mutual recursion).  It then propagates this size and
           type into the operands, using @('vl-expr-expandsizes').</p>"
    :measure (two-nats-measure (vl-expr-count x) 2)

    (b* ((lhs-size (maybe-natp-fix lhs-size))
         (x        (vl-expr-fix x))
         (mod      (vl-module-fix mod))
         (elem     (vl-modelement-fix elem))

         ;; Phase 1, determine maximum size of any operand within X, and the
         ;; final expression type of X.
         ((mv warnings x-selfsize) (vl-expr-selfsize   x mod ialist elem warnings))
         ((mv warnings finaltype)  (vl-expr-typedecide x mod ialist elem warnings))
         ((unless (and x-selfsize finaltype))
          (mv nil warnings x))

         ;; The finalwidth we will is either (1) the maximum size of any operand
         ;; in X, which we computed above as x-selfsize, or (2) the size of the
         ;; lhs expression, whichever is larger.
         (finalwidth
          (if lhs-size
              (max lhs-size x-selfsize)
            x-selfsize))

         (warnings
          ;; We warn here about implicit extensions.  Truncation warnings get
          ;; handled when we size assignments, below.
          (b* (((unless (and (natp lhs-size)
                             (> lhs-size x-selfsize)))
                ;; Not an extension
                warnings))
            (vl-warn-about-implicit-extension lhs-size x-selfsize x mod ialist elem warnings))))

      ;; Phase 2, propagate desired final width and type of the expression
      ;; into its context-determined operands.
      (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings)))

  (define vl-exprlist-size
    :short "Self-determine the sizes of a list of expressions."
    ((x        vl-exprlist-p "Should be a list of self-determined expressions.")
     (mod      vl-module-p)
     (ialist   (equal ialist (vl-moditem-alist mod)))
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    (and (vl-exprlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (two-nats-measure (vl-exprlist-count x) 0)
    :long "<p>We just use @(see vl-expr-size) (with @('lhs-size = nil')) to size
           each of the expressions in @('x').</p>"
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings car-prime) (vl-expr-size nil (car x) mod ialist elem warnings))
         ((mv cdr-successp warnings cdr-prime) (vl-exprlist-size (cdr x) mod ialist elem warnings)))
      (mv (and car-successp cdr-successp)
          warnings
          (cons car-prime cdr-prime))))

  (define vl-exprlist-expandsizes
    :short "Propagate final width/type into a list of context-determined
            expressions."
    ((x          vl-exprlist-p "Should be a list of context-determined expressions.")
     (finalwidth natp)
     (finaltype  vl-exprtype-p)
     (mod        vl-module-p)
     (ialist     (equal ialist (vl-moditem-alist mod)))
     (elem       vl-modelement-p)
     (warnings   vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    (and (vl-exprlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (two-nats-measure (vl-exprlist-count x) 0)
    :long "<p>We just use @(see vl-expr-expandsizes) to expand the operands
          within each member of @('x') to the desired @('finalwidth') and
          @('finaltype').</p>"
    (b* ((finalwidth (lnfix finalwidth))
         ((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings car-prime)
          (vl-expr-expandsizes (car x) finalwidth finaltype mod ialist elem warnings))
         ((mv cdr-successp warnings cdr-prime)
          (vl-exprlist-expandsizes (cdr x) finalwidth finaltype mod ialist elem warnings)))
      (mv (and car-successp cdr-successp)
          warnings
          (cons car-prime cdr-prime))))

 (define vl-expr-expandsizes
   :short "Propagate the final width/type into a context-determined expression."
   ((x          vl-expr-p
                "Should be a list of context-determined expressions.")
    (finalwidth natp
                "Finalwidth to extend every expression in @('x') to, should be
                 determined by the first pass of the sizing algorithm.")
    (finaltype  vl-exprtype-p
                "Finaltype to coerce every expression in @('x') to, should be
                 determined by the first pass of the sizing algorithm.")
    (mod        vl-module-p)
    (ialist     (equal ialist (vl-moditem-alist mod)))
    (elem       vl-modelement-p)
    (warnings   vl-warninglist-p))
   :returns
   (mv (successp booleanp :rule-classes :type-prescription)
       (warnings vl-warninglist-p)
       (new-x    vl-expr-p))
   :measure (two-nats-measure (vl-expr-count x) 1)
   (b* ((x          (vl-expr-fix x))
        (finalwidth (lnfix finalwidth))
        (finaltype  (vl-exprtype-fix finaltype))
        (mod        (vl-module-fix mod))
        (elem       (vl-modelement-fix elem))
        (warnings   (vl-warninglist-fix warnings))

        ((when (vl-fast-atom-p x))
         (vl-atom-expandsizes x finalwidth finaltype mod ialist elem warnings))

        ((when (vl-hidexpr-p x))
         (b* (((unless (eq finaltype :vl-unsigned))
               (mv nil
                   (fatal :type :vl-programming-error
                          :msg "~a0: signed HID? Shouldn't generate this: ~a1"
                          :args (list elem x))
                   x))
              ((mv warnings selfsize) (vl-expr-selfsize x mod ialist elem warnings))
              ((mv warnings type)     (vl-expr-typedecide x mod ialist elem warnings))
              ((unless (and (posp selfsize)
                            (<= selfsize finalwidth)
                            (eq type :vl-unsigned)))
               (mv nil
                   (fatal :type :vl-programming-error
                          :msg "~a0: bad HID size or type: ~a1"
                          :args (list elem x))
                   x))
              (inner (change-vl-nonatom x
                                        :finalwidth selfsize
                                        :finaltype :vl-unsigned))
              ;; Inner-width can be less than finalwidth; may need to zero-extend.
              ((mv successp warnings new-x)
               (vl-expandsizes-zeroextend inner finalwidth elem warnings))
              ((unless successp)
               (mv nil warnings x)))
           (mv t warnings new-x)))

        (op   (vl-nonatom->op x))
        (args (vl-nonatom->args x)))

     (case op

       ((;; Table 5-22, Lines 3 and 4.
         :vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
         :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
         :vl-binary-xnor :vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
        ;; Operands are all context-determined.
        (b* (((unless (posp finalwidth))
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ~x1 expression has zero width: ~a2."
                         :args (list elem op x))
                  x))
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
         :vl-binary-gt :vl-binary-gte :vl-binary-lt :vl-binary-lte

         ;; SystemVerilog extensions: we think these operate identically with
         ;; the expressions being extended.
         :vl-binary-wildeq :vl-binary-wildneq
         )
        ;; Trickiest case.  The two operands "shall affect each other as if
        ;; they were context-determined operands with a result type and size
        ;; (maximum of the two operand sizes) determined from them.  However,
        ;; the actual result type shall always be 1 bit unsigned."
        (b* (((unless (eq finaltype :vl-unsigned))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed comparison result???  Serious bug in ~
                               our sizing code."
                         :args (list elem))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed ~s1 of comparison expression ~a2."
                         :args (list elem
                                     (cond (a-goodp "right-hand side")
                                           (b-goodp "left-hand side")
                                           (t       "left- and right-hand sides"))
                                     x))
                  x))

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
         :vl-binary-logand
         :vl-binary-logor

         ;; SystemVerilog extensions: we think these work out the same way:
         :vl-implies
         :vl-equiv)
        ;; Both operands are self-determined.  We think the result is one-bit
        ;; unsigned; see "minutia"
        (b* (((unless (eq finaltype :vl-unsigned))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed logical op result???  Serious bug in ~
                               our sizing code."
                         :args (list elem))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed ~s1 of logical expression ~a2."
                         :args (list elem
                                     (cond (a-goodp "right-hand side")
                                           (b-goodp "left-hand side")
                                           (t       "left- and right-hand sides"))
                                     x))
                  x))
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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed logical/reduction op result???  ~
                               Serious bug in our sizing code."
                         :args (list elem))
                  x))
             (a (first args))
             ((mv successp warnings a-prime)
              (vl-expr-size nil a mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             ((unless (and (posp (vl-expr->finalwidth a-prime))
                           (vl-expr->finaltype a-prime)))
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed argument in ~x1 expression ~a2."
                         :args (list elem op x))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ~x1 expression has zero width: ~a2."
                         :args (list elem op x))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed right-hand side of ~x1 expression ~a2."
                         :args (list elem op x))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: conditional operation with zero width: ~a1."
                         :args (list elem x))
                  x))
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
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed test for conditional operator ~a1"
                         :args (list elem x))
                  x))
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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed concatenation result???  Serious bug ~
                               in our sizing code."
                         :args (list elem))
                  x))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             ;; Inner expression has width = sum of arg widths
             (widths  (vl-exprlist->finalwidths args-prime))
             ((when (member nil widths))
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: ill-formed argument in concatenation ~a1.  ~
                               BOZO make this error message better by saying ~
                               which argument is invalid."
                         :args (list elem x))
                  x))

             (inner-width (sum-nats widths))
             ((unless (posp inner-width))
              (mv nil
                  (fatal :type :vl-bad-expression
                         :msg "~a0: concatenation with zero total width: ~a1."
                         :args (list elem x))
                  x))
             ((unless (<= inner-width finalwidth))
              ;; BOZO can we move this into the guard?
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: concatenation width > finalwidth???  ~
                               Serious bug in our sizing code."
                         :args (list elem))
                  x))
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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed multiconcat result??? Serious bug in ~
                               our sizing code."
                         :args (list elem))
                  x))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))

             (a (first args-prime))
             (b (second args-prime))

             ((unless (vl-expr-resolved-p a))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: multiconcat with unresolved multiplicity ~
                               should not be encountered here."
                         :args (list elem))
                  x))

             ((unless (and (not (vl-fast-atom-p b))
                           (eq (vl-nonatom->op b) :vl-concat)))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: multple concatenation's second argument ~
                               isn't a concatenation?? ~a1"
                         :args (list elem x))
                  x))

             ((unless (and (posp (vl-expr->finalwidth b))
                           (eq (vl-expr->finaltype b) :vl-unsigned)))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: multiple concat's second argument didn't ~
                               get a unsigned positive result?? serious bug ~
                               in our sizing/typing code.  Expression: ~a1"
                         :args (list elem x))
                  x))

             (inner-width (* (vl-resolved->val a) (vl-expr->finalwidth b)))
             ((unless (<= inner-width finalwidth))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: multiconcat width > finalwidth??? Serious ~
                               bug in our sizing code."
                         :args (list elem))
                  x))

             ((when (and (= inner-width 0)
                         (< 0 finalwidth)))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: multiconcat width is zero but we want its ~
                               finalwidth to be ~x1??? serious bug in our ~
                               sizing code.  Expr: ~a2"
                         :args (list elem finalwidth x))
                  x))

             (warnings
              ;; Special extra (non-fatal) warning for 0-replications, because
              ;; some tools do crazy things with them.
              (if (posp (vl-resolved->val a))
                  warnings
                (warn :type :vl-zero-replication
                      :msg "~a0: found 0-sized replication operation.  This is ~
                            well defined by the Verilog standards and is handled ~
                            correctly by NCVerilog.  However, we have seen bugs ~
                            in VCS and Verilog-XL.  To avoid mismatches between ~
                            Verilog tools, you should probably avoid this ~
                            construct!"
                      :args (list elem x))))

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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed select result??? Serious bug in our ~
                               sizing code."
                         :args (list elem))
                  x))
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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed select result??? Serious bug in our ~
                               sizing code."
                         :args (list elem))
                  x))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))

             (left-expr  (second args-prime))
             (right-expr (third args-prime))
             ((unless (and (vl-expr-resolved-p left-expr)
                           (vl-expr-resolved-p right-expr)))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: part-select indices should be resolved."
                         :args (list elem))
                  x))

             (inner-width (+ 1 (abs (- (vl-resolved->val left-expr)
                                       (vl-resolved->val right-expr)))))
             ((unless (<= inner-width finalwidth))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: partselect width > finalwidth??? Serious ~
                               bug in our sizing code."
                         :args (list elem))
                  x))
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
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: signed select result??? Serious bug in our ~
                               sizing code."
                         :args (list elem))
                  x))
             ((mv successp warnings args-prime)
              (vl-exprlist-size args mod ialist elem warnings))
             ((unless successp)
              (mv nil warnings x))
             (width-expr (third args-prime))
             ((unless (vl-expr-resolved-p width-expr))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: indexed part-select's width should be resolved."
                         :args (list elem))
                  x))
             (inner-width (vl-resolved->val width-expr))
             ((unless (<= inner-width finalwidth))
              (mv nil
                  (fatal :type :vl-programming-error
                         :msg "~a0: indexed partselect width > finalwidth???  ~
                               Serious bug in our sizing code."
                         :args (list elem))
                  x))
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

       ((:vl-funcall :vl-syscall :vl-mintypmax :vl-array-index :vl-index
                     :vl-scope :vl-hid-dot

                    ;; BOZO these might not belong here, but it seems like the
                    ;; safest place to put them until they're implemented
                    :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
                    :vl-stream-left :vl-stream-right
                    :vl-stream-left-sized :vl-stream-right-sized
                    :vl-tagged
                    )
        (mv nil
            (fatal :type :vl-unsupported
                   :msg "~a0: add sizing support for ~x1."
                   :args (list elem op))
            x))

       (otherwise
        (progn$ (impossible)
                (mv nil warnings x))))))
 :prepwork
 ((local (in-theory (disable my-disables))))
 :flag-local nil)


(local (in-theory (e/d (vl-expr-size
                        vl-exprlist-size
                        vl-expr-expandsizes
                        vl-exprlist-expandsizes)
                       (my-disables)
                       (lnfix))))


(deffixequiv vl-expr-size
  :hints(("Goal"
          :expand ((:free (lhs-size mod ialist elem warnings)
                    (vl-expr-size lhs-size x mod ialist elem warnings))
                   (:free (lhs-size mod ialist elem warnings)
                    (vl-expr-size lhs-size (vl-expr-fix x) mod ialist elem warnings))))))

(deffixequiv vl-expr-expandsizes
  :hints(("Goal"
          :expand
          ((:free (finalwidth finaltype mod ialist elem warnings)
            (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings))
           (:free (finalwidth finaltype mod ialist elem warnings)
            (vl-expr-expandsizes (vl-expr-fix x) finalwidth finaltype mod ialist elem warnings))))))

(encapsulate
  ()
  (local (defun my-ind (x mod ialist elem warnings)
           ;; Same as vl-exprlist-size
           (b* (((when (atom x))
                 (mv t (ok) nil))
                ((mv car-successp warnings car-prime) (vl-expr-size nil (car x) mod ialist elem warnings))
                ((mv cdr-successp warnings cdr-prime) (my-ind (cdr x) mod ialist elem warnings)))
             (mv (and car-successp cdr-successp)
                 warnings
                 (cons car-prime cdr-prime)))))

  (defthm true-listp-of-vl-exprlist-size
    (true-listp (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-ind x mod ialist elem warnings))))

  (deffixequiv vl-exprlist-size
    :hints(("Goal"
            :induct (my-ind x mod ialist elem warnings)
            :do-not '(generalize fertilize)
            :expand
            ((:free (mod ialist elem warnings)
              (vl-exprlist-size x mod ialist elem warnings))
             (:free (mod ialist elem warnings)
              (vl-exprlist-size (vl-exprlist-fix x) mod ialist elem warnings)))))))

(encapsulate
  ()
  (local (defun my-ind (x finalwidth finaltype mod ialist elem warnings)
           ;; same as vl-exprlist-expandsizes
           (b* ((finalwidth (lnfix finalwidth))
                ((when (atom x))
                 (mv t (ok) nil))
                ((mv car-successp warnings car-prime)
                 (vl-expr-expandsizes (car x) finalwidth finaltype mod ialist elem warnings))
                ((mv cdr-successp warnings cdr-prime)
                 (my-ind (cdr x) finalwidth finaltype mod ialist elem warnings)))
             (mv (and car-successp cdr-successp)
                 warnings
                 (cons car-prime cdr-prime)))))

  (defthm true-listp-of-vl-exprlist-expandsizes
    (true-listp (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-ind x finalwidth finaltype mod ialist elem warnings))))

  (deffixequiv vl-exprlist-expandsizes
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :induct (my-ind x finalwidth finaltype mod ialist elem warnings)
            :expand
            ((:free (finalwidth finaltype mod ialist elem warnings)
              (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings))
             (:free (finalwidth finaltype mod ialist elem warnings)
              (vl-exprlist-expandsizes (vl-exprlist-fix x) finalwidth finaltype mod ialist elem warnings))
             (vl-exprlist-fix x))))))

(local (defthm crock
          ;; this. fucking. blows.
          (implies (and (true-listp new-x)
                        (equal (len new-x) (len x)))
                   (and (iff new-x (consp x))
                        (iff (cdr new-x) (consp (cdr x)))
                        (iff (cddr new-x) (consp (cddr x)))
                        (equal (consp new-x) (consp x))
                        (equal (consp (cdr new-x)) (consp (cdr x)))
                        (equal (consp (cddr new-x)) (consp (cddr x)))))
          :rule-classes nil
          :hints(("Goal" :expand ((len new-x)
                                  (len (cdr new-x))
                                  (len (cddr new-x))
                                  (len x)
                                  (len (cdr x))
                                  (len (cddr x)))))))

(local (defrule vl-exprlist-size-under-iff
          (let ((new-x (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings))))
            (and (iff new-x (consp x))
                 (iff (cdr new-x) (consp (cdr x)))
                 (iff (cddr new-x) (consp (cddr x)))
                 (equal (consp new-x) (consp x))
                 (equal (consp (cdr new-x)) (consp (cdr x)))
                 (equal (consp (cddr new-x)) (consp (cddr x)))))
          :use ((:instance crock
                 (new-x (mv-nth 2 (vl-exprlist-size x mod ialist elem warnings)))))))

(local (defrule vl-exprlist-expandsizes-under-iff
          (let ((new-x (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings))))
            (and (iff new-x (consp x))
                 (iff (cdr new-x) (consp (cdr x)))
                 (iff (cddr new-x) (consp (cddr x)))
                 (equal (consp new-x) (consp x))
                 (equal (consp (cdr new-x)) (consp (cdr x)))
                 (equal (consp (cddr new-x)) (consp (cddr x)))))
          :use ((:instance crock
                 (new-x (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))))))

(verify-guards vl-expr-size
   :hints(("Goal"
           :in-theory (e/d (maybe-natp
                            acl2::member-of-cons
                            ARG1-EXISTS-BY-ARITY
                            VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
                            vl-nonatom->op-forward
                            )))))

(encapsulate
   ()
   (local (in-theory (enable no-change-loser-of-vl-expandsizes-zeroextend
                             no-change-loserp-of-vl-atom-expandsizes)))

   (defthm-vl-expr-size-flag

     (defthm no-change-loserp-of-vl-expr-size
       (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
         (implies (not (mv-nth 0 ret))
                  (equal (mv-nth 2 ret)
                         (vl-expr-fix x))))
       :flag vl-expr-size)

     (defthm no-change-loserp-of-vl-expr-expandsizes
       (let ((ret (vl-expr-expandsizes x finalwidth finaltype mod
                                       ialist elem warnings)))
         (implies (not (mv-nth 0 ret))
                  (equal (mv-nth 2 ret)
                         (vl-expr-fix x))))
       :flag vl-expr-expandsizes)
     :skip-others t
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :expand ((:free (lhs-size mod ialist elem warnings)
                       (vl-expr-size lhs-size x mod ialist elem warnings))
                      (:free (finalwidth finaltype mod ialist elem warnings)
                       (vl-expr-expandsizes x finalwidth finaltype mod
                                            ialist elem warnings)))))))

(defsection vl-expr-welltyped-p-of-vl-expr-size

   (local (in-theory (e/d (all-equalp-when-atom
                           all-equalp-of-cons)
                          (all-equalp
                           MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                           ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                           default-car
                           default-cdr
                           acl2::true-listp-member-equal
                           VL-NONATOM->OP-WHEN-HIDINDEX-RESOLVED-P
                           set::double-containment
                           acl2::subsetp-member
                           acl2::zp-open
                           ))))

   (local (defthm posp-of-nfix
            (equal (posp (nfix x))
                   (posp x))
            :hints(("Goal" :in-theory (enable nfix)))))

   (local (defthm c0
            (implies (and (all-equalp finaltype (vl-exprlist->finaltypes x))
                          (force (consp x)))
                     (equal (vl-expr->finaltype (first x))
                            finaltype))))

   (local (defthm c1
            (implies (and (all-equalp finaltype (vl-exprlist->finaltypes x))
                          (force (consp (cdr x))))
                     (equal (vl-expr->finaltype (second x))
                            finaltype))))

   (local (defthm c2
            (implies (and (all-equalp finalwidth (vl-exprlist->finalwidths x))
                          (force (consp x)))
                     (equal (vl-expr->finalwidth (first x))
                            finalwidth))))

   (local (defthm c3
            (implies (and (all-equalp finalwidth (vl-exprlist->finalwidths x))
                          (force (consp (cdr x))))
                     (equal (vl-expr->finalwidth (second x))
                            finalwidth))))

   (defthm-vl-expr-size-flag

     (defthm vl-expr-welltyped-p-of-vl-expr-size
       (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
         (implies (mv-nth 0 ret)
                  (vl-expr-welltyped-p (mv-nth 2 ret))))
       :flag vl-expr-size)

     (defthm vl-exprlist-welltyped-p-of-vl-exprlist-size
       (let ((ret (vl-exprlist-size x mod ialist elem warnings)))
         (implies (mv-nth 0 ret)
                  (vl-exprlist-welltyped-p (mv-nth 2 ret))))
       :flag vl-exprlist-size)

     (defthm vl-expr-welltyped-p-of-vl-expr-expandsizes
       (let ((ret (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings)))
         (implies (mv-nth 0 ret)
                  (and (vl-expr-welltyped-p (mv-nth 2 ret))
                       (equal (vl-expr->finalwidth (mv-nth 2 ret))
                              (nfix finalwidth))
                       (equal (vl-expr->finaltype (mv-nth 2 ret))
                              (vl-exprtype-fix finaltype)))))
       :hints ((and stable-under-simplificationp
                    '(:expand ((:free (ialist warnings)
                                (vl-expr-selfsize x mod ialist elem warnings))))))
       :flag vl-expr-expandsizes)

     (defthm vl-exprlist-welltyped-p-of-vl-exprlist-expandsizes
       (let ((ret (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings)))
         (implies (mv-nth 0 ret)
                  (and (vl-exprlist-welltyped-p (mv-nth 2 ret))
                       (all-equalp (nfix finalwidth)
                                   (vl-exprlist->finalwidths (mv-nth 2 ret)))
                       (all-equalp (vl-exprtype-fix finaltype)
                                   (vl-exprlist->finaltypes (mv-nth 2 ret))))))
       :flag vl-exprlist-expandsizes)

     :hints(("Goal"
             :in-theory (enable vl-nonatom->op-forward
                                acl2::member-of-cons
                                ARG1-EXISTS-BY-ARITY
                                acl2::member-when-atom)
             :do-not '(generalize fertilize)
             :expand ((:free (lhs-size ialist)
                       (vl-expr-size lhs-size x mod ialist elem warnings))
                      (:free (finalwidth finaltype ialist)
                       (vl-expr-expandsizes x finalwidth finaltype mod ialist elem warnings))
                      (:free (finalwidth finaltype mod ialist elem warnings)
                       (vl-exprlist-expandsizes x finalwidth finaltype mod ialist elem warnings))
                      (:free (mod ialist elem warnings)
                       (vl-exprlist-size x mod ialist elem warnings))
                      (:free (op atts args finalwidth finaltype)
                       (vl-expr-welltyped-p
                        (vl-nonatom op atts args finalwidth finaltype))))))))

(defthm vl-expr->finalwidth-of-vl-expr-size-when-lhs-size
  ;; ;; This is an important corollary.  It shows us that if we actually provide
  ;; ;; an lhs-size argument, we're guaranteed to get back an expression that is
  ;; ;; at least as large as lhs-size.
  (let ((ret (vl-expr-size lhs-size x mod ialist elem warnings)))
    (implies (and (mv-nth 0 ret)
                  (natp lhs-size))
             (<= lhs-size (vl-expr->finalwidth (mv-nth 2 ret)))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :expand ((:free (ialist)
                    (vl-expr-size lhs-size x mod ialist elem warnings))))))
