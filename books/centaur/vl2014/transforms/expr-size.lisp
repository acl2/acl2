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
(include-book "../mlib/selfsize")
(include-book "../mlib/typedecide")
(include-book "../mlib/welltyped")
(include-book "../mlib/lvalues")
(include-book "std/basic/arith-equivs" :dir :system)
(local (in-theory (enable acl2::arith-equiv-forwarding lnfix)))
;; (local (include-book "clause-processors/autohide" :dir :system))
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                           acl2::consp-under-iff-when-true-listp)))

(local (in-theory (disable acl2::hons-assoc-equal-of-cons
                           acl2::member-of-cons
                           integerp-when-natp
                           not nfix acl2::zp-open)))
(local (in-theory (disable (tau-system))))



(local (defthm vl-expr-fix-nonnil
         (vl-expr-fix x)
         :hints(("Goal" :in-theory (enable (tau-system))))
         :rule-classes :type-prescription))

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



(defsection unsigned-when-size-zero
  ;; It would be weird for a size zero expression to be signed, because how do
  ;; you sign extend something that has no sign bit?

  (defthm vl-atom-unsigned-when-size-zero
    (b* (((mv & size) (vl-atom-selfsize x ss ctx1 warnings1))
         ((mv & type) (vl-atom-typedecide x ss ctx2 warnings2)))
      (implies (equal size 0)
               (equal type :vl-unsigned)))
    :hints(("Goal" :in-theory (enable vl-atom-selfsize
                                      vl-atom-typedecide))))

  (define vl-unsigned-when-size-zero-lst ((sizes vl-maybe-nat-listp)
                                          (types vl-maybe-exprtype-list-p))
    :guard (eql (len sizes) (len types))
    (if (atom sizes)
        t
      (and (or (not (equal (car sizes) 0))
               (not (car types))
               (equal (car types) :vl-unsigned))
           (vl-unsigned-when-size-zero-lst (cdr sizes) (cdr types)))))

  (local (defthm consp-by-len
           (implies (and (syntaxp (not (and (consp x) (eq (car x) 'cdr))))
                         (<= 1 (len x)))
                    (consp x))
           :rule-classes ((:rewrite :backchain-limit-lst 2))))

  (local (defthm consp-cdr-by-len
           (implies (and (syntaxp (not (and (consp x) (eq (car x) 'cdr))))
                         (<= 2 (len x)))
                    (consp (cdr x)))
           :rule-classes ((:rewrite :backchain-limit-lst 2))))

  (local (defthm consp-cddr-by-len
           (implies (and (syntaxp (not (and (consp x) (eq (car x) 'cdr))))
                         (<= 3 (len x)))
                    (consp (cddr x)))
           :rule-classes ((:rewrite :backchain-limit-lst 2))))

  (local (in-theory (disable acl2::nat-listp-when-not-consp
                             len-of-vl-nonatom->args-when-vl-hidexpr-p)))

  (defthm index-unsigned-when-size-zero
    (b* (((mv & size) (vl-index-selfsize x ss ctx warnings))
         ((mv & type) (vl-index-typedecide x ss ctx warnings)))
      (implies (equal size 0)
               (equal type :vl-unsigned)))
    :hints(("Goal" :in-theory (enable vl-index-selfsize
                                      vl-index-typedecide))))

  ;; (local (defthm len-of-cdr-less
  ;;          (implies (and (syntaxp (quotep n))
  ;;                        (natp n)
  ;;                        (consp x))
  ;;                   (equal (< (len (cdr x)) n)
  ;;                          (< (len x) (+ 1 n))))
  ;;          :hints(("Goal" :in-theory (enable len)))))

  ;; (local (defthm vl-unsigned-when-size-zero-lst-expand-when-consp
  ;;          (implies (consp sizes)
  ;;                   (equal (vl-unsigned-when-size-zero-lst sizes types)
  ;;                          (and (or (not (equal (car sizes) 0))
  ;;                                   (not (car types))
  ;;                                   (equal (car types) :vl-unsigned))
  ;;                               (vl-unsigned-when-size-zero-lst (cdr sizes) (cdr types)))))
  ;;          :hints(("Goal" :in-theory (enable vl-unsigned-when-size-zero-lst)))))

  (local (in-theory (disable max acl2::len-when-atom
                             default-car default-cdr
                             vl-context-fix-when-vl-context-p
                             vl-context-p-when-vl-ctxelement-p
                             double-containment
                             vl-expr-selfsize
                             vl-expr-typedecide-aux)))

  ;; (local (Defthm vl-exprtype-max-when-one-unsigned
  ;;          (implies (or (equal a :vl-unsigned)
  ;;                       (equal b :vl-unsigned))
  ;;                   (equal (equal (vl-exprtype-max a b) :vl-unsigned) t))
  ;;          :hints(("Goal" :in-theory (enable vl-exprtype-max)))))

  (local (defthm maybe-posp-of-vl-coredatatype-info->size
           (maybe-posp (VL-COREDATATYPE-INFO->SIZE (VL-SYSCALL->RETURNINFO X)))
           :hints(("Goal" :in-theory (enable vl-syscall->returninfo)))
           :rule-classes :type-prescription))

  (defthm-vl-expr-typedecide-aux-flag
    (defthm vl-expr-unsigned-when-size-zero-aux
      (b* (((mv & size) (vl-expr-selfsize x ss ctx1 warnings1))
           ((mv & type) (vl-expr-typedecide-aux x ss ctx2 warnings2 mode)))
        (implies (and (equal size 0)
                      type)
                 (equal type :vl-unsigned)))
      :hints (;;(and stable-under-simplificationp
              '(:expand ((:free (ctx warnings)
                          (vl-expr-selfsize x ss ctx warnings))
                         (:free (ctx warnings mode)
                          (vl-expr-typedecide-aux x ss ctx warnings mode))
                         (:free (a b c)
                          (vl-unsigned-when-size-zero-lst (cons a b) c)))
                :in-theory (enable acl2::member-of-cons))
              (and stable-under-simplificationp
                   '(:in-theory (enable vl-op-selfsize
                                        vl-syscall-selfsize
                                        vl-funcall-selfsize
                                        vl-exprtype-max

                                        ;; BOZO faint sound of screaming, muffled by the waves above
                                        vl-indexexpr-p
                                        vl-scopeexpr-p
                                        acl2::member-of-cons
                                        ;; vl-unsigned-when-size-zero-lst
                                        )))
              ;; (and (member-equal id
              ;;                    (list (acl2::parse-clause-id "Subgoal *1/13.5")
              ;;                          (acl2::parse-clause-id "Subgoal *1/13''")))
              ;;      (cw "clause: ~x0~%" (acl2::prettyify-clause clause nil world)))
              )

      :flag :expr)
    (defthm vl-exprlist-unsigned-when-size-zero-aux
      (b* (((mv & sizes) (vl-exprlist-selfsize x ss ctx1 warnings1))
           ((mv & types) (vl-exprlist-typedecide-aux x ss ctx2 warnings2 mode)))
        (vl-unsigned-when-size-zero-lst sizes types))
      :hints ('(:expand ((:free (ctx warnings)
                          (vl-exprlist-selfsize x ss ctx warnings))
                         ;; (:free (ctx warnings mode)
                         ;;  (vl-exprlist-typedecide-aux x ss ctx warnings mode))
                         (:free (a b c d)
                          (vl-unsigned-when-size-zero-lst
                           (cons a b) (cons c d))))))
      :flag :list)))



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
   (ctx       vl-context-p  "Context for warnings.")
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
       (ctx          (vl-context-fix ctx))
       (finalwidth   (lnfix finalwidth))
       (x.finalwidth (lnfix (vl-expr->finalwidth x)))

       ((when (> x.finalwidth finalwidth))
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: trying to zero-extend ~a1, which has width ~x2, ~
                         to ~x3 bits??? Serious bug in our sizing code."
                   :args (list ctx x x.finalwidth finalwidth))
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
    (let ((ret1 (vl-expandsizes-zeroextend x finalwidth ctx warnings))
          (ret2 (vl-expandsizes-zeroextend x finalwidth nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule vl-expr->finalwidth-of-vl-expandsizes-zeroextend
    (implies (and (mv-nth 0 (vl-expandsizes-zeroextend x finalwidth ctx warnings))
                  (force (vl-expr->finalwidth x))
                  (force (equal (vl-expr->finaltype x) :vl-unsigned)))
             (equal (vl-expr->finalwidth
                     (mv-nth 2 (vl-expandsizes-zeroextend x finalwidth ctx warnings)))
                    (nfix finalwidth))))

  (defrule no-change-loser-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr->finaltype-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned)))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      :vl-unsigned))))

  (defrule vl-expr-welltyped-p-of-vl-expandsizes-zeroextend
    (let ((ret (vl-expandsizes-zeroextend x finalwidth ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-expr-welltyped-p x))
                    (force (vl-expr->finalwidth x))
                    (force (equal (vl-expr->finaltype x) :vl-unsigned)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-expr-welltyped-p
             vl-atom-welltyped-p
             acl2::member-of-cons)))



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
                  (syntaxp
                   ;; Safety valve to avoid blowing up Lisp by creating huge expt calls.
                   (or (not (quotep origwidth))
                       (< (acl2::unquote origwidth) 10000)))
                  (force (< value (expt 2 origwidth)))
                  (force (posp finalwidth))
                  (force (< origwidth finalwidth)))
             (natp (vl-sign-extend-constint value origwidth finalwidth)))
    :rule-classes :type-prescription
    :enable logxor)

  (defrule upper-bound-of-vl-sign-extend-constint
    (implies (and (force (natp value))
                  (force (posp origwidth))
                  (syntaxp
                   ;; Safety valve to avoid blowing up Lisp by creating huge expt calls.
                   (or (not (quotep origwidth))
                       (< (acl2::unquote origwidth) 10000)))
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
   (ctx       vl-context-p)
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
  :prepwork ((local (in-theory (disable (tau-system)))))

  ;; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (ctx       (vl-context-fix ctx))
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
                   :args (list ctx x))
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
                   :args (list ctx guts.origtype finaltype x))
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
              :args (list ctx x))))
    (mv t warnings new-x))
  ///
  (defrule warning-irrelevance-of-vl-constint-atom-expandsizes
    (let ((ret1 (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings))
          (ret2 (vl-constint-atom-expandsizes x finalwidth finaltype nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-constint-atom-expandsizes
    (let ((ret (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-constint-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-weirdint-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."
  :prepwork ((local (in-theory (disable (tau-system)))))
  :verbosep t
  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (ctx       vl-context-p)
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
       (ctx       (vl-context-fix ctx))

       ((vl-weirdint guts) guts)

       ((when (> guts.origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list ctx x))
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
                   :args (list ctx guts.origtype finaltype x))
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
                               (list-fix guts.bits)))
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
                          (list-fix guts.bits)))
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
              :args (list ctx x))))

    (mv t warnings new-x))
  ///
  (defrule warning-irrelevance-of-vl-weirdint-atom-expandsizes
    (let ((ret1 (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings))
          (ret2 (vl-weirdint-atom-expandsizes x finalwidth finaltype nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (lnfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-weirdint-atom-expandsizes
    (let ((ret (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-weirdint-p (vl-atom->guts x))))
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(local (defthm selfsize-of-select-plusminus-implies-resolved
         (implies (and (mv-nth 1 (vl-expr-selfsize x ss ctx warnings))
                       (not (vl-atom-p x))
                       (member (vl-nonatom->op x)
                               '(:vl-select-pluscolon
                                 :vl-select-minuscolon)))
                  (vl-expr-resolved-p (third (vl-nonatom->args x))))
         :hints(("Goal" :in-theory (enable vl-expr-selfsize
                                           vl-partselect-selfsize
                                           vl-partselect-expr-type
                                           vl-partselect-type-top-dimension-replacement
                                           acl2::member-of-cons)))))

(local (defthm selfsize-of-select-colon-implies-resolved
         (implies (and (mv-nth 1 (vl-expr-selfsize x ss ctx warnings))
                       (not (vl-atom-p x))
                       (eq (vl-nonatom->op x) :vl-select-colon))
                  (and (vl-expr-resolved-p (second (vl-nonatom->args x)))
                       (vl-expr-resolved-p (third (vl-nonatom->args x)))))
         :hints(("Goal" :in-theory (enable vl-expr-selfsize
                                           vl-partselect-selfsize
                                           vl-partselect-expr-type
                                           vl-partselect-type-top-dimension-replacement
                                           acl2::member-of-cons)))))

(define vl-hidexpr-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into an
identifier or HID."
  :prepwork ((local (in-theory (disable (tau-system)))))
  ((x           vl-expr-p)
   (finalwidth  natp)
   (finaltype   vl-exprtype-p)
   (ss vl-scopestack-p)
   (ctx        vl-context-p)
   (warnings    vl-warninglist-p))

  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))

  ;; BOZO can we push the sanity checks into the guard?

  (b* ((x          (vl-expr-fix x))
       (ctx       (vl-context-fix ctx))
       (finalwidth (lnfix finalwidth))
       (finaltype  (vl-exprtype-fix finaltype))

       ((mv warnings origwidth) (vl-expr-selfsize x ss ctx warnings))
       ((mv warnings origtype)  (vl-expr-typedecide x ss ctx warnings))

       ((unless (and origwidth origtype))
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: expected to only try to expand sizes for atoms ~
                         whose sizes types can be successfully determined, ~
                         but we failed to determine the size or type of ~a1."
                   :args (list ctx x))
            x))

       ((when (> origwidth finalwidth))
        ;; Sanity check.  This must never happen because the finalwidth of
        ;; the expression is the maximum of any operand's size.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: origwidth > finalwidth when expanding ~a1. This ~
                         indicates a serious bug in our sizing code."
                   :args (list ctx x))
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
                   :args (list ctx origtype finaltype x))
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

       (new-x (if (vl-fast-atom-p x)
                  (change-vl-atom x
                                  :finalwidth finalwidth
                                  :finaltype finaltype)
                (change-vl-nonatom x
                                   :finalwidth finalwidth
                                   :finaltype finaltype))))
    (mv t (ok) new-x))
  ///

  (defrule no-change-loserp-of-vl-hidexpr-expandsizes
    (let ((ret (vl-hidexpr-expandsizes x finalwidth finaltype ss
                                      ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (local (defthm vl-expr-selfsize-of-idexpr
           (b* (((mv & size) (vl-expr-selfsize x ss ctx warnings)))
             (implies (vl-idexpr-p x)
                      (not (equal size 0))))
           :hints(("Goal" :in-theory (enable vl-expr-selfsize
                                             vl-idexpr-p
                                             vl-atom-selfsize
                                             tag-reasoning)))))

  (local (defthm hidexpr-ops
           (implies (and (vl-hidexpr-p x)
                         (not (equal (vl-expr-kind x) :atom)))
                    (member (vl-nonatom->op x) '(:vl-index :vl-hid-dot)))
           :hints(("Goal" :in-theory (enable vl-hidexpr-p vl-hidindex-p
                                             acl2::member-of-cons)))))

  (local (defthm hidexpr-ops-extra
           (implies (and (vl-hidexpr-p x)
                         (not (equal (vl-expr-kind x) :atom)))
                    (member (vl-nonatom->op x) '(:vl-hid-dot :vl-index :vl-bitselect)))
           :hints(("Goal" :in-theory (enable vl-hidexpr-p vl-hidindex-p
                                             acl2::member-of-cons)))))

  (local (defthm vl-expr-selfsize-of-hidexpr
           (b* (((mv & size) (vl-expr-selfsize x ss ctx warnings)))
             (implies (and (vl-hidexpr-p x)
                           (not (vl-atom-p x)))
                      (not (equal size 0))))
           :hints(("Goal" :in-theory (enable vl-expr-selfsize)
                   :expand ((vl-expr-selfsize x ss ctx nil))))))

  (local (defthm vl-expr-selfsize-of-index
           (b* (((mv & size) (vl-expr-selfsize x ss ctx warnings)))
             (implies (and (not (vl-atom-p x))
                           (member (vl-nonatom->op x) '(:vl-index
                                                        :vl-select-colon
                                                        :vl-select-pluscolon
                                                        :vl-select-minuscolon)))
                      (not (equal size 0))))
           :hints(("Goal" :in-theory (enable acl2::member-of-cons
                                             vl-partselect-selfsize
                                             vl-index-selfsize)
                   :expand ((:Free (ctx) (vl-expr-selfsize x ss ctx nil)))))))

  (local (defthm vl-indexexpr-p-when-hidexpr-p
           (implies (vl-hidexpr-p x)
                    (vl-indexexpr-p x))
           :hints(("Goal" :in-theory (e/d (vl-hidexpr-p
                                           vl-scopeexpr-p
                                           vl-indexexpr-p
                                           vl-hidindex-p)
                                          ((force)))))))



  (defrule vl-expr-welltyped-p-of-vl-hidexpr-expandsizes
    (let ((ret (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (vl-idexpr-p x))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p
             vl-selexpr-welltyped-p
             vl-idexpr-p
             vl-hidexpr-p
             vl-hidindex-p
             vl-indexexpr-p
             vl-expr-welltyped-p))

  (defrule warning-irrelevance-of-vl-hidexpr-expandsizes
    (let ((ret1 (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings))
          (ret2 (vl-hidexpr-expandsizes x finalwidth finaltype ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))




  ;; (defrule vl-expr-welltyped-p-of-vl-hidexpr-expandsizes-unresolved-index
  ;;   (let ((ret (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings)))
  ;;     (implies (and (mv-nth 0 ret)
  ;;                   (not (vl-atom-p x))
  ;;                   (member (vl-nonatom->op x) '(:vl-index
  ;;                                                :vl-select-colon
  ;;                                                :vl-select-pluscolon
  ;;                                                :vl-select-minuscolon)))
  ;;              (vl-expr-welltyped-p (mv-nth 2 ret))))
  ;;   :enable (vl-selexpr-welltyped-p
  ;;            vl-expr-welltyped-p
  ;;            acl2::member-of-cons))

  (defrule vl-expr->finalwidth-of-vl-hidexpr-expandsizes
    (let ((ret (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (mv-nth 0 ret)
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-hidexpr-expandsizes
    (let ((ret (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (mv-nth 0 ret)
               (equal (vl-expr->finaltype (mv-nth 2 ret))
                      (vl-exprtype-fix finaltype))))))


(define vl-string-atom-expandsizes
  :parents (vl-expr-expandsizes)
  :short "Propagate the final width and type of an expression into a weird
integer atom."

  ((x          vl-expr-p)
   (finalwidth natp)
   (finaltype  vl-exprtype-p)
   (ctx       vl-context-p)
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
       (ctx       (vl-context-fix ctx))

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
                   :args (list ctx x))
            x))

       ((unless (eq finaltype :vl-unsigned))
        ;; Sanity check.  This must never happen because the finaltype of the
        ;; expression must be unsigned if any operand was unsigned.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: finaltype is ~s1 when expanding ~a2.  This ~
                         indicates a serious bug in our sizing/typing code."
                   :args (list ctx finaltype x))
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
        (vl-expandsizes-zeroextend inner finalwidth ctx warnings))

       ((unless successp)
        (mv nil warnings x)))

    (mv t warnings new-x))

  ///
  (defrule warning-irrelevance-of-vl-string-atom-expandsizes
    (let ((ret1 (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings))
          (ret2 (vl-string-atom-expandsizes x finalwidth finaltype nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x))))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x))
                    (force (vl-string-p (vl-atom->guts x))))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-vl-string-atom-expandsizes
    (let ((ret (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings)))
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
   (ss vl-scopestack-p)
   (ctx       vl-context-p)
   (warnings   vl-warninglist-p))
  :guard (vl-atom-p x)
  :prepwork ((local (in-theory (enable vl-idexpr-p))))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-expr-p))
  (b* ((x    (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       (guts (vl-atom->guts x))
       ((when (vl-fast-constint-p guts)) (vl-constint-atom-expandsizes x finalwidth finaltype ctx warnings))
       ((when (vl-fast-weirdint-p guts)) (vl-weirdint-atom-expandsizes x finalwidth finaltype ctx warnings))
       ((when (vl-fast-id-p guts))       (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings))
       ((when (vl-fast-string-p guts))   (vl-string-atom-expandsizes x finalwidth finaltype ctx warnings))

       ((when (eq (tag guts) :vl-extint))
        (cond ((zp finalwidth)
               (mv nil (warn :type :vl-expr-size-fail
                             :msg "~a0: size 0 extint"
                             :args (list ctx))
                   x))
              (t (mv t (ok) (change-vl-atom x
                                            :finalwidth finalwidth
                                            :finaltype (vl-exprtype-fix finaltype)))))))

    ;; Otherwise, we shouldn't have tried to size this.
    (mv nil
        (fatal :type :vl-programming-error
               :msg "~a0: expected to only try to expand sizes for atoms ~
                     whose self-sizes and types can be successfully ~
                     determined, but we are trying to expand an atom of type ~
                     ~x1: ~a2."
               :args (list ctx (tag guts) x))
        x))
  ///
  (local (in-theory (disable natp nfix)))

  (defrule warning-irrelevance-of-vl-atom-expandsizes
    (let ((ret1 (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings))
          (ret2 (vl-atom-expandsizes x finalwidth finaltype ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (and (equal (mv-nth 0 ret1) (mv-nth 0 ret2))
                    (equal (mv-nth 2 ret1) (mv-nth 2 ret2))))))

  (defrule no-change-loserp-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (not (mv-nth 0 ret))
               (equal (mv-nth 2 ret)
                      (vl-expr-fix x)))))

  (defrule vl-expr-welltyped-p-of-vl-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x)))
               (vl-expr-welltyped-p (mv-nth 2 ret))))
    :enable (vl-atom-welltyped-p vl-expr-welltyped-p))

  (defrule vl-expr->finalwidth-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings)))
      (implies (and (mv-nth 0 ret)
                    (force (vl-atom-p x)))
               (equal (vl-expr->finalwidth (mv-nth 2 ret))
                      (nfix finalwidth)))))

  (defrule vl-expr->finaltype-of-atom-expandsizes
    (let ((ret (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings)))
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
   (ctx     vl-context-p)
   (warnings vl-warninglist-p))
  :guard (vl-expr->finaltype rhs)
  :returns (new-warnings vl-warninglist-p)
  (b* ((rhs  (vl-expr-fix rhs))
       (ctx (vl-context-fix ctx))

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
          :args (list ctx rhs))))



(defsection vl-classify-extension-warning-hook
  :short "Configurable hook for classifying extension warnings."

  :long "<p>Extension warnings are very good to have and have helped us to find
many bugs.  However, we need to be pretty clever to avoid getting too many
trivial, nitpicky complaints about assignments that aren't really bugs.</p>

<p>This hook can be used with @(see defattach) to customize exactly how
extension warnings are filtered out and easily experiment with new heuristics.
See @(see vl-classify-extension-warning-default) for the arguments.  The task
of your function is to classify the type of warning to issue.  Typically the
type should be one of the following:</p>

<ul>
<li>@('nil') - do not issue any warnings about this extension,</li>
<li>@(':vl-warn-extension') - issue a default warning, or</li>
<li>@(':vl-warn-extension-minor') - issue a minor warning.</li>
</ul>

<p>However in principle you can return any warning type you like.</p>

<p>Note that your function will only be called when there is an extension
taking place, so it is generally fine to use a function that is relatively
expensive or inefficient here.</p>

@(def vl-classify-extension-warning-hook)"
  :autodoc nil

  (encapsulate
    (((vl-classify-extension-warning-hook * * * * *) => *
      :formals (lhs-size x-selfsize x ss ctx)
      :guard (and (natp lhs-size)
                  (natp x-selfsize)
                  (> lhs-size x-selfsize)
                  (vl-expr-p x)
                  (vl-scopestack-p ss)
                  (vl-context-p ctx))))

    (local (defun vl-classify-extension-warning-hook (lhs-size x-selfsize x ss ctx)
             (declare (ignorable lhs-size x-selfsize x ss ctx))
             nil))

    (defthm symbolp-of-vl-classify-extension-warning-hook
      (symbolp (vl-classify-extension-warning-hook lhs-size x-selfsize x ss ctx))
      :rule-classes :type-prescription)))

(define vl-classify-extension-warning-default
  :parents (vl-classify-extension-warning-hook)
  :short "Default heuristic for filtering extension warnings."

  :long "<p>We found that extension warnings were frequently triggered by
things like @('assign {carry,sum} = a + b') where the designer seems to
explicitly intend to get the carry bit.  We therefore only cause a minor
warning if the right-hand side is composed only of additions.  Later it turned
out we need to permit selects, too.  And later we decided to also add
subtraction as a permitted operation.</p>

<p>Another kind of extension warning that is stupidly minor is when we just
have assignments like @('assign foo[127:0] = 0;').  We now do not even create a
minor warning for assignments where the rhs is a constant.</p>"

  ((lhs-size   natp)
   (x-selfsize natp)
   (x          vl-expr-p)
   (ss         vl-scopestack-p)
   (ctx        vl-context-p))
  :guard (> lhs-size x-selfsize)
  (declare (ignorable lhs-size x-selfsize ss ctx))

  (b* ((x (vl-expr-fix x))

       ((when (and (vl-fast-atom-p x)
                   (or (vl-extint-p (vl-atom->guts x))
                       (and (vl-constint-p (vl-atom->guts x))
                            (vl-constint->wasunsized (vl-atom->guts x))))))
        ;; Completely trivial, don't give any warning.
        nil)

       (ops    (vl-expr-ops x))
       (minorp (and (or (member-equal :vl-binary-plus ops)
                        (member-equal :vl-binary-minus ops))
                    (subsetp-equal ops '(:vl-binary-plus
                                         :vl-binary-minus
                                         :vl-partselect-colon
                                         :vl-bitselect)))))
    (if minorp
        :vl-warn-extension-minor
      :vl-warn-extension))
  ///
  (defattach vl-classify-extension-warning-hook
    vl-classify-extension-warning-default))

(define vl-warn-about-implicit-extension
  :short "Lint-like warnings about right hand sides being extended."
  ((lhs-size   natp)
   (x-selfsize natp)
   (x          vl-expr-p)
   (ss         vl-scopestack-p)
   (ctx        vl-context-p)
   (warnings   vl-warninglist-p))
  :guard (> lhs-size x-selfsize)
  :returns (new-warnings vl-warninglist-p)
  (b* ((lhs-size   (lnfix lhs-size))
       (x-selfsize (lnfix x-selfsize))
       (x          (vl-expr-fix x))
       (ss         (vl-scopestack-fix ss))
       (ctx        (vl-context-fix ctx))
       (type       (vl-classify-extension-warning-hook lhs-size x-selfsize x ss ctx))
       ((unless type)
        (ok)))
    (warn :type type
          :msg "~a0: implicit extension from ~x1-bit expression to ~x2-bit ~
                 lvalue.~%     rhs: ~a3"
          :args (list ctx x-selfsize lhs-size x))))

(local (in-theory (enable maybe-natp-fix)))

(local (def-ruleset! my-disables
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
           acl2::car-when-all-equalp
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
           vl-context-fix-when-vl-context-p
           vl-warninglist-fix-when-vl-warninglist-p
           ;; vl-nonatom->op-when-hidindex-resolved-p
           vl-nonatom->op-when-vl-hidindex-p
           vl-atom-p-of-car-when-vl-atomlist-p
           acl2::true-listp-member-equal
           SUM-NATS-WHEN-ATOM
           acl2::ALL-EQUALP-WHEN-ATOM
           ARG1-EXISTS-BY-ARITY
           all-equalp

           WARNING-IRRELEVANCE-OF-VL-EXPANDSIZES-ZEROEXTEND
           WARNING-IRRELEVANCE-OF-VL-EXPR-TYPEDECIDE
           WARNING-IRRELEVANCE-OF-VL-EXPR-SELFSIZE
           NO-CHANGE-LOSER-OF-VL-EXPANDSIZES-ZEROEXTEND
           NO-CHANGE-LOSERP-OF-VL-ATOM-EXPANDSIZES

           ACL2::CONSP-MEMBER-EQUAL
           ;; VL-EXPR-FIX-WHEN-VL-EXPR-P
           VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
           VL-EXPRLIST->FINALWIDTHS-WHEN-NOT-CONSP

           (:TYPE-PRESCRIPTION MEMBER-EQUAL)
           VL-EXPANDSIZES-ZEROEXTEND-OF-VL-CONTEXT-FIX-CTX

           (:TYPE-PRESCRIPTION VL-NONATOM->OP$INLINE)
           ACL2::NATP-WHEN-MAYBE-NATP
           acl2::MEMBER-EQUAL-WHEN-ALL-EQUALP
           vl-warninglist-p-when-not-consp
           )))

(with-output :off (prove)
  (defines vl-expr-size
    :parents (expression-sizing)
    :verify-guards nil

; BOZO we might be able to strengthen the guards here so that we don't need to
; explicitly check for signed finalwidths in unsigned operators like compares.
; But I'm not sure exactly how this would work, yet.
    ;; :returns-hints nil
    (define vl-expr-size
      :short "Determine sizes for a top-level or self-determined expression."
      ((lhs-size maybe-natp
                 "To size an expression @('x') which occurs in an assignment such
               as @('assign lhs = x'), the @('lhs-size') should be the width of
               @('lhs').  To size other expressions that do not occur in
               assignments, such as a self-determined subexpression, the
               @('lhs-size') should be nil.")
       (x        vl-expr-p                             "The expression that we want to size.")
       (ss       vl-scopestack-p)
       (ctx      vl-context-p                       "Context for sizing error messages.")
       (warnings vl-warninglist-p                      "Ordinary @(see warnings) accumulator."))
      :returns
      (mv (successp booleanp :rule-classes :type-prescription
                    "Indicates whether all sizing was successful."
                    ;; :hints ('(:in-theory (disable vl-expr-size vl-exprlist-size
                    ;;                               vl-expr-expandsizes vl-exprlist-expandsizes)
                    ;;           :expand ((vl-expr-size lhs-size x ss ctx warnings)
                    ;;                    (vl-expr-size nil x ss ctx warnings))))
                    )
          (warnings vl-warninglist-p
                    "Possibly extended with fatal or non-fatal warnings.")
          (new-x    vl-expr-p
                    "Updated version of @('x') where all the sizes/types have
                  been computed and installed."))
      :long "<p>This function implements the two-phase algorithm described in
           @(see expression-sizing).  That is, it first determines the maximum
           size of any operand in @('x') and the desired type of @('x'), using
           @(see vl-expr-selfsize) and @(see vl-expr-typedecide) (which are not
           part of the mutual recursion).  It then propagates this size and
           type into the operands, using @('vl-expr-expandsizes').</p>"
      :measure (two-nats-measure (vl-expr-count x) 2)

      (b* ((lhs-size (maybe-natp-fix lhs-size))
           (x        (vl-expr-fix x))
           (ss       (vl-scopestack-fix ss))
           (ctx     (vl-context-fix ctx))

           ;; Phase 1, determine maximum size of any operand within X, and the
           ;; final expression type of X.
           ((mv warnings x-selfsize) (vl-expr-selfsize   x ss ctx warnings))
           ((mv warnings finaltype)  (vl-expr-typedecide x ss ctx warnings))
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
              (vl-warn-about-implicit-extension lhs-size x-selfsize x ss ctx warnings))))

        ;; Phase 2, propagate desired final width and type of the expression
        ;; into its context-determined operands.
        (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))

    (define vl-exprlist-size
      :short "Self-determine the sizes of a list of expressions."
      ((x        vl-exprlist-p "Should be a list of self-determined expressions.")
       (ss vl-scopestack-p)
       (ctx     vl-context-p)
       (warnings vl-warninglist-p))
      :returns (mv (successp booleanp :rule-classes :type-prescription
                             ;; :hints ('(:in-theory (disable vl-expr-size vl-exprlist-size
                             ;;                               vl-expr-expandsizes vl-exprlist-expandsizes)
                             ;;           :expand ((vl-exprlist-size x ss ctx warnings))))
                             )
                   (warnings vl-warninglist-p)
                   (new-x    (and (vl-exprlist-p new-x)
                                  (equal (len new-x) (len x)))))
      :measure (two-nats-measure (vl-exprlist-count x) 0)
      :long "<p>We just use @(see vl-expr-size) (with @('lhs-size = nil')) to size
           each of the expressions in @('x').</p>"
      (b* (((when (atom x))
            (mv t (ok) nil))
           ((mv car-successp warnings car-prime) (vl-expr-size nil (car x) ss ctx warnings))
           ((mv cdr-successp warnings cdr-prime) (vl-exprlist-size (cdr x) ss ctx warnings)))
        (mv (and car-successp cdr-successp)
            warnings
            (cons car-prime cdr-prime))))

    (define vl-exprlist-expandsizes
      :short "Propagate final width/type into a list of context-determined
            expressions."
      ((x          vl-exprlist-p "Should be a list of context-determined expressions.")
       (finalwidth natp)
       (finaltype  vl-exprtype-p)
       (ss vl-scopestack-p)
       (ctx       vl-context-p)
       (warnings   vl-warninglist-p))
      :returns (mv (successp booleanp :rule-classes :type-prescription
                             ;; :hints ('(:in-theory (disable vl-expr-size vl-exprlist-size
                             ;;                               vl-expr-expandsizes vl-exprlist-expandsizes)
                             ;;           :expand ((vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))))
                             )
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
            (vl-expr-expandsizes (car x) finalwidth finaltype ss ctx warnings))
           ((mv cdr-successp warnings cdr-prime)
            (vl-exprlist-expandsizes (cdr x) finalwidth finaltype ss ctx warnings)))
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
       (ss vl-scopestack-p)
       (ctx       vl-context-p)
       (warnings   vl-warninglist-p))
      :returns
      (mv (successp booleanp :rule-classes :type-prescription
                    ;; :hints ('(:in-theory (disable vl-expr-size vl-exprlist-size
                    ;;                               vl-expr-expandsizes vl-exprlist-expandsizes)
                    ;;           :expand ((:free (finalwidth)
                    ;;                     (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))))
                    )
          (warnings vl-warninglist-p)
          (new-x    vl-expr-p))
      :measure (two-nats-measure (vl-expr-count x) 1)
      (b* ((x          (vl-expr-fix x))
           (ss         (vl-scopestack-fix ss))
           (finalwidth (lnfix finalwidth))
           (finaltype  (vl-exprtype-fix finaltype))
           (ctx       (vl-context-fix ctx))
           (warnings   (vl-warninglist-fix warnings))

           ((when (vl-fast-atom-p x))
            (vl-atom-expandsizes x finalwidth finaltype ss ctx warnings))

           ;; ((when (vl-hidexpr-p x))
           ;;  (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings))

           (op   (vl-nonatom->op x))

           ;; ((when (member op '(:vl-index
           ;;                     :vl-select-colon
           ;;                     :vl-select-pluscolon
           ;;                     :vl-select-minuscolon)))
           ;;  (vl-hidexpr-expandsizes x finalwidth finaltype ss ctx warnings))

           (args (vl-nonatom->args x)))

        (case op

          (:vl-hid-dot
           (b* (((unless (vl-hidexpr-p x))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 is not a well-formed HID."
                            :args (list ctx x))
                     x))
                ((unless (posp finalwidth))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 has 0 width?"
                            :args (list ctx x))
                     x))
                (new-x (change-vl-nonatom x
                                          :finalwidth finalwidth
                                          :finaltype finaltype)))
             (mv t warnings new-x)))

          ((:vl-index)
           (b* (((unless (vl-indexexpr-p (first args)))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 is not a well-formed index expression."
                            :args (list ctx x))
                     x))
                ((unless (posp finalwidth))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 has 0 width?"
                            :args (list ctx x))
                     x))
                ((mv successp warnings indices)
                 (vl-exprlist-size (cdr args) ss ctx warnings))
                ((unless successp) (mv nil warnings x))
                (new-x (change-vl-nonatom x
                                          :args (cons (first args) indices)
                                          :finalwidth finalwidth
                                          :finaltype finaltype)))
             (mv t warnings new-x)))

          ((:vl-select-colon
            :vl-select-pluscolon
            :vl-select-minuscolon)
           (b* (((unless (posp finalwidth))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 has 0 width?"
                            :args (list ctx x))
                     x))
                ((mv successp warnings indices)
                 (vl-exprlist-size (cdr args) ss ctx warnings))
                ((unless successp) (mv nil warnings x))
                (resolved-ok (case op
                               (:vl-select-colon
                                (and (vl-expr-resolved-p (first indices))
                                     (vl-expr-resolved-p (second indices))))
                               (otherwise (vl-expr-resolved-p (second indices)))))
                ((unless resolved-ok)
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 has some non-constant indices that ~
                                  are required to be constant"
                            :args (list ctx x))
                     x))
                (new-x (change-vl-nonatom x
                                          :args (cons (first args) indices)
                                          :finalwidth finalwidth
                                          :finaltype finaltype)))
             (mv t warnings new-x)))

          ((;; Table 5-22, Lines 3 and 4.
            :vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
            :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
            :vl-binary-xnor :vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
           ;; Operands are all context-determined.
           (b* (((unless (posp finalwidth))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ~x1 expression has zero width: ~a2."
                            :args (list ctx op x))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-expandsizes args finalwidth finaltype ss ctx warnings))
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
                            :args (list ctx))
                     x))
                ;; Determine the maximum width of any operand in a/b and also
                ;; whether they are signed or unsigned.
                (a (first args))
                (b (second args))
                ((mv warnings a-selfsize) (vl-expr-selfsize a ss ctx warnings))
                ((mv warnings b-selfsize) (vl-expr-selfsize b ss ctx warnings))
                ((mv warnings a-type)     (vl-expr-typedecide a ss ctx warnings))
                ((mv warnings b-type)     (vl-expr-typedecide b ss ctx warnings))
                (a-goodp                  (and (posp a-selfsize) a-type))
                (b-goodp                  (and (posp b-selfsize) b-type))
                ((unless (and a-goodp b-goodp))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ill-formed ~s1 of comparison expression ~a2."
                            :args (list ctx
                                        (cond (a-goodp "right-hand side")
                                              (b-goodp "left-hand side")
                                              (t       "left- and right-hand sides"))
                                        x))
                     x))

                ;; Expand the operands to the appropriate inner width/type.
                (innerwidth (max a-selfsize b-selfsize))
                (innertype  (vl-exprtype-max a-type b-type))
                ((mv successp warnings args-prime)
                 (vl-exprlist-expandsizes args innerwidth innertype ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))
                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth 1
                                          :finaltype :vl-unsigned))
                ;; Inner is only one bit, so we may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                (a (first args))
                (b (second args))
                ((mv a-successp warnings a-prime)
                 (vl-expr-size nil a ss ctx warnings))
                ((mv b-successp warnings b-prime)
                 (vl-expr-size nil b ss ctx warnings))
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
                            :args (list ctx
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
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                (a (first args))
                ((mv successp warnings a-prime)
                 (vl-expr-size nil a ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))
                ((unless (and (posp (vl-expr->finalwidth a-prime))
                              (vl-expr->finaltype a-prime)))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ill-formed argument in ~x1 expression ~a2."
                            :args (list ctx op x))
                     x))
                (inner (change-vl-nonatom x
                                          :args (list a-prime)
                                          :finalwidth 1
                                          :finaltype :vl-unsigned))
                ;; Inner is only one bit, so we may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx op x))
                     x))
                (a (first args))
                (b (second args))
                ((mv a-successp warnings a-prime)
                 (vl-expr-expandsizes a finalwidth finaltype ss ctx warnings))
                ((mv b-successp warnings b-prime)
                 (vl-expr-size nil b ss ctx warnings))
                ((unless (and a-successp b-successp))
                 (mv nil warnings x))
                ;; We don't require much of B, just that it has a type and that its
                ;; width is positive.
                ((unless (and (posp (vl-expr->finalwidth b-prime))
                              (vl-expr->finaltype b-prime)))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ill-formed right-hand side of ~x1 expression ~a2."
                            :args (list ctx op x))
                     x))
                ;; Special warning about signed shifts in Verilog-XL versus the Spec.
                (warnings (vl-warn-about-signed-shifts b-prime ctx warnings))
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
                            :args (list ctx x))
                     x))
                (a (first args))
                (b (second args))
                (c (third args))
                ((mv a-successp warnings a-prime)
                 (vl-expr-size nil a ss ctx warnings))
                ((mv b-successp warnings b-prime)
                 (vl-expr-expandsizes b finalwidth finaltype ss ctx warnings))
                ((mv c-successp warnings c-prime)
                 (vl-expr-expandsizes c finalwidth finaltype ss ctx warnings))
                ((unless (and a-successp b-successp c-successp))
                 (mv nil warnings x))
                ((unless (and (posp (vl-expr->finalwidth a-prime))
                              (vl-expr->finaltype a-prime)))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: ill-formed test for conditional operator ~a1"
                            :args (list ctx x))
                     x))
                (new-x (change-vl-nonatom x
                                          :args (list a-prime b-prime c-prime)
                                          :finalwidth finalwidth
                                          :finaltype finaltype)))
             ;; New-x already has the right size, no need to zero-extend
             (mv t warnings new-x)))

          ((;; Table 5-22, Line 10.
            :vl-concat
            :vl-stream-left :vl-stream-right
            :vl-stream-left-sized :vl-stream-right-sized)
           ;; All arguments self-determined, result is unsigned.
           (b* (((unless (eq finaltype :vl-unsigned))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: signed concatenation result???  Serious bug ~
                               in our sizing code."
                            :args (list ctx))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-size args ss ctx warnings))
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
                            :args (list ctx x))
                     x))

                (inner-width (if (member op '(:vl-stream-left-sized :vl-stream-right-sized))
                                 (sum-nats (mbe :logic (cdr widths)
                                                :exec (and (consp widths) (cdr widths))))
                               (sum-nats widths)))
                ((unless (posp inner-width))
                 (mv nil
                     (fatal :type :vl-bad-expression
                            :msg "~a0: concatenation with zero total width: ~a1."
                            :args (list ctx x))
                     x))
                ((unless (<= inner-width finalwidth))
                 ;; BOZO can we move this into the guard?
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: concatenation width > finalwidth???  ~
                               Serious bug in our sizing code."
                            :args (list ctx))
                     x))
                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth inner-width
                                          :finaltype :vl-unsigned))
                ;; Inner-width can be less than finalwidth; may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-size args ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))

                (a (first args-prime))
                (b (second args-prime))

                ((unless (vl-expr-resolved-p a))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: multiconcat with unresolved multiplicity ~
                               should not be encountered here."
                            :args (list ctx))
                     x))

                ((unless (and (not (vl-fast-atom-p b))
                              (eq (vl-nonatom->op b) :vl-concat)))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: multple concatenation's second argument ~
                               isn't a concatenation?? ~a1"
                            :args (list ctx x))
                     x))

                ((unless (and (posp (vl-expr->finalwidth b))
                              (eq (vl-expr->finaltype b) :vl-unsigned)))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: multiple concat's second argument didn't ~
                               get a unsigned positive result?? serious bug ~
                               in our sizing/typing code.  Expression: ~a1"
                            :args (list ctx x))
                     x))

                (inner-width (* (vl-resolved->val a) (vl-expr->finalwidth b)))
                ((unless (<= inner-width finalwidth))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: multiconcat width > finalwidth??? Serious ~
                               bug in our sizing code."
                            :args (list ctx))
                     x))

                ((when (and (= inner-width 0)
                            (< 0 finalwidth)))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: multiconcat width is zero but we want its ~
                               finalwidth to be ~x1??? serious bug in our ~
                               sizing code.  Expr: ~a2"
                            :args (list ctx finalwidth x))
                     x))

                (warnings
                 ;; Special extra (non-fatal) warning for 0-replications, because
                 ;; some tools do crazy things with them.
                 (if (posp (vl-resolved->val a))
                     warnings
                   (warn :type :vl-zero-replication
                         :msg "~a0: found 0-sized replication: ~a1.  This is ~
                               well defined by the Verilog standards and is ~
                               handled correctly by NCVerilog.  However, we ~
                               have seen bugs in VCS and Verilog-XL.  To ~
                               avoid mismatches between Verilog tools, you ~
                               should probably avoid this construct!"
                         :args (list ctx x))))

                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth inner-width
                                          :finaltype :vl-unsigned))

                ;; Inner-width can be less than finalwidth; may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-size args ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))
                ;; discard these warnings because they'll be redundant
                ((mv ?warnings1 selfsize) (vl-expr-selfsize x ss ctx warnings))
                ((unless (eql selfsize 1))
                 (mv nil
                     (fatal :type :vl-bad-bitselect
                            :msg "~a0: bitselect expressions should selfsize ~
                                  to 1, but ~a1 selfsized to ~x2"
                            :args (list ctx x selfsize))
                     x))
                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth 1
                                          :finaltype :vl-unsigned))
                ;; Inner is only one bit, so we may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-size args ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))

                (left-expr  (second args-prime))
                (right-expr (third args-prime))
                ((unless (and (vl-expr-resolved-p left-expr)
                              (vl-expr-resolved-p right-expr)))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: part-select indices should be resolved."
                            :args (list ctx))
                     x))

                (inner-width (+ 1 (abs (- (vl-resolved->val left-expr)
                                          (vl-resolved->val right-expr)))))
                ;; discard these warnings because they'll be redundant
                ((mv ?warnings1 selfsize) (vl-expr-selfsize x ss ctx warnings))
                ((unless (eql selfsize inner-width))
                 (mv nil
                     (fatal :type :vl-bad-bitselect
                            :msg "~a0: partselect expression was expected to ~
                                  selfsize to its index width ~x1, but ~a2 ~
                                  selfsized to ~x3"
                            :args (list ctx x inner-width selfsize))
                     x))
                ((unless (<= inner-width finalwidth))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: partselect width > finalwidth??? Serious ~
                               bug in our sizing code."
                            :args (list ctx))
                     x))
                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth inner-width
                                          :finaltype :vl-unsigned))
                ;; Inner-width can be less than finalwidth; may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
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
                            :args (list ctx))
                     x))
                ((mv successp warnings args-prime)
                 (vl-exprlist-size args ss ctx warnings))
                ((unless successp)
                 (mv nil warnings x))
                (width-expr (third args-prime))
                ((unless (vl-expr-resolved-p width-expr))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: indexed part-select's width should be resolved."
                            :args (list ctx))
                     x))
                (inner-width (vl-resolved->val width-expr))
                ;; discard these warnings because they'll be redundant
                ((mv ?warnings1 selfsize) (vl-expr-selfsize x ss ctx warnings))
                ((unless (eql selfsize inner-width))
                 (mv nil
                     (fatal :type :vl-bad-bitselect
                            :msg "~a0: partselect expression was expected to ~
                                  selfsize to its index width ~x1, but ~a2 ~
                                  selfsized to ~x3"
                            :args (list ctx x inner-width selfsize))
                     x))
                ((unless (<= inner-width finalwidth))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: indexed partselect width > finalwidth???  ~
                               Serious bug in our sizing code."
                            :args (list ctx))
                     x))
                (inner (change-vl-nonatom x
                                          :args args-prime
                                          :finalwidth inner-width
                                          :finaltype :vl-unsigned))
                ;; Inner-width can be less than finalwidth; may need to zero-extend.
                ((mv successp warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
                ((unless successp)
                 (mv nil warnings x)))
             (mv t warnings new-x)))

          (:vl-funcall
           ;; Skip the function, self-size the arguments.
           (b* (((unless (consp args))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: Function call without function name: ~a1"
                            :args (list ctx x))
                     x))
                ((cons fnname fn-args) args)
                ((mv ok warnings fn-args)
                 (vl-exprlist-size fn-args ss ctx warnings))
                ((unless ok) (mv nil warnings x))
                (new-x (change-vl-nonatom
                        x
                        :args (cons fnname fn-args)
                        :finalwidth finalwidth
                        :finaltype finaltype)))
             (mv ok warnings new-x)))

          ((:vl-syscall)
           (b* (((unless (and (consp args)
                              (vl-sysfunexpr-p (car args))))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: system function call without function name: ~a1."
                            :args (list ctx x))
                     x))
                ((cons fn fnargs) args)
                (fnname   (vl-sysfunexpr->name (car args)))

                ((mv ok warnings fnargs)
                 ;; Size the arguments only if we are supposed to do so.  This avoids
                 ;; trying to size things like $bits.
                 (if (vl-sysfun-should-size-args-p fnname)
                     (vl-exprlist-size fnargs ss ctx warnings)
                   (mv t warnings fnargs)))
                ((unless ok)
                 (mv nil warnings x))

                ((mv warnings selfwidth) (vl-syscall-selfsize x ss ctx warnings))
                ((mv warnings selftype)  (vl-syscall-typedecide x ss ctx warnings))
                ((unless (and selfwidth selftype))
                 ;; This is probably not what we really want to do here?
                 (mv nil
                     (fatal :type :vl-unsupported-syscall
                            :msg "~a0: system call ~s1 not implemented: ~a2."
                            :args (list ctx fnname x))
                     x))
                (inner (change-vl-nonatom x
                                          :args (cons fn fnargs)
                                          :finalwidth selfwidth
                                          :finaltype finaltype))
                ((when (eql selfwidth finalwidth))
                 (mv t warnings inner))
                ((when (< finalwidth selfwidth))
                 (mv nil
                     (fatal :type :vl-programming-error
                            :msg "~a0: finalwidth of ~s1 call can't be less ~
                                  than ~x2; bug with our sizing code: ~a3"
                            :args (list ctx fnname selfwidth x))
                     x))
                ;; Else, we need to extend.
                ((unless (eq finaltype :vl-unsigned))
                 (mv nil
                     (fatal :type :vl-sign-extend-too-lazy
                            :msg "~a0: sign extending ~s1 system call is not ~
                                  yet implemented: ~a2."
                            :args (list ctx fnname x))
                     x))
                ((mv ok warnings new-x)
                 (vl-expandsizes-zeroextend inner finalwidth ctx warnings))
                ((when ok)
                 (mv ok warnings new-x)))
             (mv nil warnings x)))

          ((:vl-mintypmax :vl-index
            :vl-scope :vl-hid-dot

            ;; BOZO these might not belong here, but it seems like the
            ;; safest place to put them until they're implemented
            :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
            :vl-tagged :vl-binary-cast
            :vl-pattern-multi
            :vl-pattern-type
            :vl-pattern-positional
            :vl-pattern-keyvalue
            :vl-keyvalue
            )
           (mv nil
               (fatal :type :vl-unsupported
                      :msg "~a0: add sizing support for ~x1."
                      :args (list ctx op))
               x))

          ((;; Sizing just shouldn't encounter these
            :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec
            :vl-binary-assign
            :vl-binary-plusassign :vl-binary-minusassign
            :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
            :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
            :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign

            :vl-inside :vl-valuerange :vl-valuerangelist)
           (mv nil
               (fatal :type :vl-bad-operator
                      :msg "~a0: sizing should not encounter ~x1 because it should ~
                            get eliminated by the increment-elim transform."
                      :args (list ctx op))
               x))

          (otherwise
           (progn$ (impossible)
                   (mv nil warnings x))))))
    :prepwork
    ((local (in-theory (disable my-disables
                                (:t vl-exprtype-fix)
                                (:t vl-warninglist-p))))
     (local (std::set-returnspec-mrec-default-hints
             ;; for whatever reason, it is faster here NOT to wait until
             ;; stable-under-simplification to expand calls, so we pass NIL as
             ;; the wait-until-stablep parameter.
             ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world)))))
    :flag-local nil))


(local (in-theory (e/d (; vl-expr-size
                        ; vl-exprlist-size
                        ; vl-expr-expandsizes
                        ; vl-exprlist-expandsizes
                        )
                       (my-disables)
                       (lnfix))))


(deffixequiv vl-expr-size
  :hints(("Goal"
          :expand ((:free (lhs-size ss ctx warnings)
                    (vl-expr-size lhs-size x ss ctx warnings))
                   (:free (lhs-size ss ctx warnings)
                    (vl-expr-size lhs-size (vl-expr-fix x) ss ctx warnings))))))

(deffixequiv vl-expr-expandsizes
  :hints(("Goal"
          :expand
          ((:free (finalwidth finaltype ss ctx warnings)
            (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings))
           (:free (finalwidth finaltype ss ctx warnings)
            (vl-expr-expandsizes (vl-expr-fix x) finalwidth finaltype ss ctx warnings))))))

(encapsulate
  ()
  (local (defun my-ind (x ss ctx warnings)
           ;; Same as vl-exprlist-size
           (b* (((when (atom x))
                 (mv t (ok) nil))
                ((mv car-successp warnings car-prime) (vl-expr-size nil (car x) ss ctx warnings))
                ((mv cdr-successp warnings cdr-prime) (my-ind (cdr x) ss ctx warnings)))
             (mv (and car-successp cdr-successp)
                 warnings
                 (cons car-prime cdr-prime)))))

  (defthm true-listp-of-vl-exprlist-size
    (true-listp (mv-nth 2 (vl-exprlist-size x ss ctx warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-ind x ss ctx warnings)
            :expand ((vl-exprlist-size x ss ctx warnings)))))

  (deffixequiv vl-exprlist-size
    :hints(("Goal"
            :induct (my-ind x ss ctx warnings)
            :do-not '(generalize fertilize)
            :expand
            ((:free (ss ctx warnings)
              (vl-exprlist-size x ss ctx warnings))
             (:free (ss ctx warnings)
              (vl-exprlist-size (vl-exprlist-fix x) ss ctx warnings)))))))

(encapsulate
  ()
  (local (defun my-ind (x finalwidth finaltype ss ctx warnings)
           ;; same as vl-exprlist-expandsizes
           (b* ((finalwidth (lnfix finalwidth))
                ((when (atom x))
                 (mv t (ok) nil))
                ((mv car-successp warnings car-prime)
                 (vl-expr-expandsizes (car x) finalwidth finaltype ss ctx warnings))
                ((mv cdr-successp warnings cdr-prime)
                 (my-ind (cdr x) finalwidth finaltype ss ctx warnings)))
             (mv (and car-successp cdr-successp)
                 warnings
                 (cons car-prime cdr-prime)))))

  (defthm true-listp-of-vl-exprlist-expandsizes
    (true-listp (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-ind x finalwidth finaltype ss ctx warnings)
            :expand ((vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings)))))

  (deffixequiv vl-exprlist-expandsizes
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :induct (my-ind x finalwidth finaltype ss ctx warnings)
            :expand
            ((:free (finalwidth finaltype ss ctx warnings)
              (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))
             (:free (finalwidth finaltype ss ctx warnings)
              (vl-exprlist-expandsizes (vl-exprlist-fix x) finalwidth finaltype ss ctx warnings)))))))

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
          (let ((new-x (mv-nth 2 (vl-exprlist-size x ss ctx warnings))))
            (and (iff new-x (consp x))
                 (iff (cdr new-x) (consp (cdr x)))
                 (iff (cddr new-x) (consp (cddr x)))
                 (equal (consp new-x) (consp x))
                 (equal (consp (cdr new-x)) (consp (cdr x)))
                 (equal (consp (cddr new-x)) (consp (cddr x)))))
          :use ((:instance crock
                 (new-x (mv-nth 2 (vl-exprlist-size x ss ctx warnings)))))))

(local (defrule vl-exprlist-expandsizes-under-iff
          (let ((new-x (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))))
            (and (iff new-x (consp x))
                 (iff (cdr new-x) (consp (cdr x)))
                 (iff (cddr new-x) (consp (cddr x)))
                 (equal (consp new-x) (consp x))
                 (equal (consp (cdr new-x)) (consp (cdr x)))
                 (equal (consp (cddr new-x)) (consp (cddr x)))))
          :use ((:instance crock
                 (new-x (mv-nth 2 (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings)))))))

(local (defthm member-of-nil
         (not (member x nil))
         :hints(("Goal" :in-theory (enable member)))))

(with-output :off (event)
  (encapsulate nil
    (local (defthm len-cdr-plus-one
             (implies (consp x)
                      (equal (+ 1 (len (cdr x)))
                             (len x)))))
    (local (defthm member-of-cdr-exprlist-finalwidths
             (implies (not (member k (vl-exprlist->finalwidths x)))
                      (not (member k (vl-exprlist->finalwidths (cdr x)))))
             :hints(("Goal" :in-theory (enable vl-exprlist->finalwidths member)))))
    (verify-guards vl-expr-size
      :hints(("Goal"
              :in-theory (e/d (maybe-natp
                               acl2::member-of-cons
                               ARG1-EXISTS-BY-ARITY
                               VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
                               vl-nonatom->op-forward
                               )
                              (vl-expr-size
                               vl-exprlist-size
                               vl-expr-expandsizes
                               vl-exprlist-expandsizes
                               (tau-system))))))))

(with-output :off (prove)
  (encapsulate
    ()
    (local (in-theory (enable no-change-loser-of-vl-expandsizes-zeroextend
                              no-change-loserp-of-vl-atom-expandsizes)))

    (defthm-vl-expr-size-flag

      (defthm no-change-loserp-of-vl-expr-size
        (let ((ret (vl-expr-size lhs-size x ss ctx warnings)))
          (implies (not (mv-nth 0 ret))
                   (equal (mv-nth 2 ret)
                          (vl-expr-fix x))))
        :hints ('(:expand ((:free (lhs-size ss ctx warnings)
                            (vl-expr-size lhs-size x ss ctx warnings)))))
        :flag vl-expr-size)

      (defthm no-change-loserp-of-vl-expr-expandsizes
        (let ((ret (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))
          (implies (not (mv-nth 0 ret))
                   (equal (mv-nth 2 ret)
                          (vl-expr-fix x))))
        :hints ('(:expand ((:free (finalwidth finaltype ss ctx warnings)
                            (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))))
        :flag vl-expr-expandsizes)
      :skip-others t
      :hints(("Goal"
              :do-not '(generalize fertilize))))))


(defthm vl-expr-size-successp-implies-vl-expr-selfsize/typedecide
  (b* (((mv ok & &) (vl-expr-size lhs-size x ss ctx warnings))
       ((mv & selfsize) (vl-expr-selfsize x ss ctx warnings2))
       ((mv & selftype) (vl-expr-typedecide x ss ctx warnings3)))
    (implies ok
             (and selfsize
                  (natp selfsize)
                  selftype
                  (vl-exprtype-p selftype))))
  :hints (("goal" :expand ((vl-expr-size lhs-size x ss ctx warnings))
           :in-theory (enable WARNING-IRRELEVANCE-OF-VL-EXPR-TYPEDECIDE
                              WARNING-IRRELEVANCE-OF-VL-EXPR-SELFSIZE))))

(defsection warning-irrelevance-of-vl-expr-size
  (local
   (flag::def-doublevar-induction vl-expr-size-flag-doublewarnings
     :orig-fn vl-expr-size-flag
     :old-var warnings
     :new-var warnings2))

  (local
   (with-output :off (prove)
     (defthm-vl-expr-size-flag
       (defthm warning-irrelevance-of-vl-expr-size-1
         (b* (((mv ok & new-x) (vl-expr-size lhs-size x ss ctx warnings))
              ((mv ok1 & new-x1) (vl-expr-size lhs-size x ss ctx warnings2)))
           (implies (bind-free (and (not (equal warnings ''nil)) '((warnings2 . 'nil))) (warnings2))
                    (and (equal ok ok1)
                         (equal new-x new-x1))))
         :hints ('(:expand ((:free (lhs-size warnings)
                             (vl-expr-size lhs-size x ss ctx warnings)))
                   :in-theory (e/d (warning-irrelevance-of-vl-expr-selfsize
                                    warning-irrelevance-of-vl-expr-typedecide)
                                   (vl-expr-size
                                    vl-expr-expandsizes))))
         :flag vl-expr-size)
       (defthm warning-irrelevance-of-vl-exprlist-size-1
         (b* (((mv ok & new-x) (vl-exprlist-size x ss ctx warnings))
              ((mv ok1 & new-x1) (vl-exprlist-size x ss ctx warnings2)))
           (implies (bind-free (and (not (equal warnings ''nil)) '((warnings2 . 'nil))) (warnings2))
                    (and (equal ok ok1)
                         (equal new-x new-x1))))
         :hints ('(:expand ((:free (warnings) (vl-exprlist-size x ss ctx warnings)))
                   :in-theory (e/d ()
                                   (vl-exprlist-size vl-expr-size))))
         :flag vl-exprlist-size)
       (defthm warning-irrelevance-of-vl-exprlist-expandsizes-1
         (b* (((mv ok & new-x) (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))
              ((mv ok1 & new-x1) (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings2)))
           (implies (bind-free (and (not (equal warnings ''nil)) '((warnings2 . 'nil))) (warnings2))
                    (and (equal ok ok1)
                         (equal new-x new-x1))))
         :hints ('(:expand ((:free (warnings) (vl-exprlist-expandsizes
                                               x finalwidth finaltype ss ctx warnings)))
                   :in-theory (disable vl-exprlist-expandsizes vl-expr-expandsizes)))
         :flag vl-exprlist-expandsizes)
       (defthm warning-irrelevance-of-vl-expr-expandsizes-lemma-1
         (b* (((mv ok & new-x) (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings))
              ((mv ok1 & new-x1) (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings2)))
           (implies (bind-free (and (not (equal warnings ''nil)) '((warnings2 . 'nil))) (warnings2))
                    (and (equal ok ok1)
                         (equal new-x new-x1))))
         :hints ('(:expand ((:free (warnings finalwidth finaltype)
                             (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))
                   :in-theory (e/d (warning-irrelevance-of-vl-expandsizes-zeroextend
                                    warning-irrelevance-of-vl-expr-selfsize
                                    warning-irrelevance-of-vl-expr-typedecide)
                                   (vl-expr-size vl-exprlist-size vl-exprlist-expandsizes
                                                 vl-expr-expandsizes))))
         :flag vl-expr-expandsizes)
       :hints (("Goal" :induct (vl-expr-size-flag-doublewarnings
                                flag lhs-size x finalwidth finaltype ss ctx warnings warnings2))))))

  (local
   (flag::def-doublevar-induction vl-expr-size-flag-doublectx
     :orig-fn vl-expr-size-flag
     :old-var ctx
     :new-var ctx2))

  (with-output :off (prove)
    (defthm-vl-expr-size-flag
      (defthm warning-irrelevance-of-vl-expr-size
        (b* (((mv ok & new-x) (vl-expr-size lhs-size x ss ctx warnings))
             ((mv ok1 & new-x1) (vl-expr-size lhs-size x ss ctx2 nil)))
          (implies (and (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                        (bind-free '((ctx2 . 'nil)) (ctx2)))
                   (and (equal ok ok1)
                        (equal new-x new-x1))))
        :hints ('(:expand ((:free (lhs-size ctx warnings)
                            (vl-expr-size lhs-size x ss ctx warnings)))
                  :in-theory (e/d (warning-irrelevance-of-vl-expr-selfsize
                                   warning-irrelevance-of-vl-expr-typedecide)
                                  (vl-expr-size
                                   vl-expr-expandsizes))))
        :flag vl-expr-size)
      (defthm warning-irrelevance-of-vl-exprlist-size
        (b* (((mv ok & new-x) (vl-exprlist-size x ss ctx warnings))
             ((mv ok1 & new-x1) (vl-exprlist-size x ss ctx2 nil)))
          (implies (and (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                        (bind-free '((ctx2 . 'nil)) (ctx2)))
                   (and (equal ok ok1)
                        (equal new-x new-x1))))
          :hints ('(:expand ((:free (ctx warnings) (vl-exprlist-size x ss ctx warnings)))
                    :in-theory (e/d ()
                                    (vl-exprlist-size vl-expr-size))))
          :flag vl-exprlist-size)
        (defthm warning-irrelevance-of-vl-exprlist-expandsizes
          (b* (((mv ok & new-x) (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))
               ((mv ok1 & new-x1) (vl-exprlist-expandsizes x finalwidth finaltype ss ctx2 nil)))
            (implies (and (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                        (bind-free '((ctx2 . 'nil)) (ctx2)))
                     (and (equal ok ok1)
                          (equal new-x new-x1))))
          :hints ('(:expand ((:free (ctx warnings) (vl-exprlist-expandsizes
                                                x finalwidth finaltype ss ctx warnings)))
                    :in-theory (disable vl-exprlist-expandsizes vl-expr-expandsizes)))
          :flag vl-exprlist-expandsizes)
        (defthm warning-irrelevance-of-vl-expr-expandsizes
          (b* (((mv ok & new-x) (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings))
               ((mv ok1 & new-x1) (vl-expr-expandsizes x finalwidth finaltype ss ctx2 nil)))
            (implies (and (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                          (bind-free '((ctx2 . 'nil)) (ctx2)))
                     (and (equal ok ok1)
                          (equal new-x new-x1))))
          :hints ('(:expand ((:free (ctx warnings finalwidth finaltype)
                              (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))
                    :in-theory (e/d (warning-irrelevance-of-vl-expandsizes-zeroextend
                                     warning-irrelevance-of-vl-expr-selfsize
                                     warning-irrelevance-of-vl-expr-typedecide)
                                    (vl-expr-size vl-exprlist-size vl-exprlist-expandsizes
                                                  vl-expr-expandsizes))))
          :flag vl-expr-expandsizes)
        :hints (("Goal" :induct (vl-expr-size-flag-doublectx
                                 flag lhs-size x finalwidth finaltype ss ctx warnings ctx2))))))


(defsection vl-expr-welltyped-p-of-vl-expr-size

  (local (defthm car-of-vl-arity-fix
           (implies (< 0 (vl-op-arity op))
                    (equal (car (vl-arity-fix op (cons a b))) a))
           :hints(("Goal" :in-theory (enable vl-arity-fix
                                             append)
                   :expand ((take (vl-op-arity op) (cons a b)))
                   :cases ((natp (vl-op-arity op)))))))

  (local (defthm vl-arity-fix-by-len
           (implies (equal (len x) (vl-op-arity op))
                    (equal (vl-arity-fix op x) x))
           :hints(("Goal" :in-theory (enable vl-arity-fix)))))

  ;; (local (defthm cdr-of-vl-arity-fix
  ;;          (implies (< 0 (vl-op-arity op))
  ;;                   (equal (car (vl-arity-fix op (cons a b))) a))))

  (local (defthm member-equal-when-member-non-intersecting
           (implies (and (syntaxp (quotep x))
                         (member k y)
                         (syntaxp (quotep y))
                         (not (intersectp-equal x y)))
                    (not (member k x)))
           :hints ((set-reasoning))))
  (local (defthm reduce-member-equal-when-not-member
           (implies (and (syntaxp (quotep x))
                         (not (member k y))
                         (syntaxp (quotep y))
                         (intersectp-equal x y))
                    (iff (member k x)
                         (member k (set-difference-equal x y))))
           :hints (("goal" :in-theory (enable acl2::member-of-set-difference-equal))
                   (set-reasoning))))
  (local (defthm equal-when-member-non-member
           (implies (and (syntaxp (quotep v))
                         (member k x)
                         (syntaxp (quotep x))
                         (not (member v x)))
                    (not (equal k v)))))
  (local (defthm member-of-singleton
           (iff (member a (cons x nil))
                (equal a x))
           :hints(("Goal" :in-theory (enable member)))))
  (local (defthm reduce-member-equal-when-not-equal
           (implies (and (syntaxp (quotep x))
                         (not (equal k v))
                         (syntaxp (quotep v))
                         (member v x))
                    (iff (member k x)
                         (member k (remove-equal v x))))
           :hints ((set-reasoning))))

  (local (defund check-op-arities (ops n)
           (if (atom ops)
               t
             (and (let ((arity (vl-op-arity (car ops))))
                    (equal arity n))
                  (check-op-arities (cdr ops) n)))))

  (local (defthm vl-arity-ok-p-when-member
           (implies (and (member op ops)
                         (syntaxp (quotep ops))
                         (check-op-arities ops (len args)))
                    (vl-arity-ok-p op args))
           :hints(("Goal" :in-theory (enable member check-op-arities
                                             vl-arity-ok-p)
                   :induct (member op ops)))))

  (local (defthm all-equalp-nil
           (all-equalp x nil)
           :hints(("Goal" :in-theory (enable acl2::all-equalp-when-atom)))))

  (local (in-theory (e/d (acl2::all-equalp-of-cons)
                         (all-equalp
                          acl2::member-of-cons
                          MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                          ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                          default-car
                          default-cdr
                          acl2::true-listp-member-equal
                          ;; VL-NONATOM->OP-WHEN-HIDINDEX-RESOLVED-P
                          set::double-containment
                          acl2::subsetp-member
                          acl2::zp-open
                          acl2::all-equalp-when-atom
                          vl-exprlist-welltyped-p-when-not-consp
                          (tau-system)
                          max abs
                          ))))

  (local (defthmd arity-by-member-when-check-op-arities
           (implies (and (member op ops)
                         (check-op-arities ops arity))
                    (equal (vl-op-arity op) arity))
           :hints(("Goal" :in-theory (enable check-op-arities member)))))

  (local (defthm consp-of-args-by-member-class
           (implies (and (member (vl-nonatom->op x) ops)
                         (syntaxp (quotep ops))
                         (consp ops)
                         (bind-free `((arity . ',(vl-op-arity (car (acl2::unquote ops)))))
                                    (arity))
                         (< 0 arity)
                         (check-op-arities ops arity))
                    (consp (vl-nonatom->args x)))
           :hints (("goal" :use ((:instance arity-by-member-when-check-op-arities
                                  (op (vl-nonatom->op x)))
                                 (:instance len-of-vl-nonatom->args))
                    :in-theory (disable len-of-vl-nonatom->args)))))

  (local (defthm consp-of-cdr-args-by-member-class
           (implies (and (member (vl-nonatom->op x) ops)
                         (syntaxp (quotep ops))
                         (consp ops)
                         (bind-free `((arity . ',(vl-op-arity (car (acl2::unquote ops)))))
                                    (arity))
                         (< 1 arity)
                         (check-op-arities ops arity))
                    (consp (cdr (vl-nonatom->args x))))
           :hints (("goal" :use ((:instance arity-by-member-when-check-op-arities
                                  (op (vl-nonatom->op x)))
                                 (:instance len-of-vl-nonatom->args))
                    :in-theory (disable len-of-vl-nonatom->args)))))



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


  (local (defthm hidindex-p-of-reassemble
           (implies (and (vl-hidindex-p x)
                         (not (equal (vl-expr-kind x) :atom)))
                    (vl-hidindex-p
                     (make-vl-nonatom :op (vl-nonatom->op x)
                                      :args (vl-nonatom->args x)
                                      :atts atts
                                      :finalwidth fw
                                      :finaltype ft)))
           :hints(("Goal" :in-theory (e/d (vl-hidindex-p)
                                          ((force)))))))

  (local (defthm hidexpr-p-of-reassemble
           (implies (and (vl-hidexpr-p x)
                         (not (equal (vl-expr-kind x) :atom))
                         (equal (vl-nonatom->op x) op))
                    (vl-hidexpr-p
                     (make-vl-nonatom :op op
                                      :args (vl-nonatom->args x)
                                      :atts atts
                                      :finalwidth fw
                                      :finaltype ft)))
           :hints(("Goal" :in-theory (e/d (vl-hidexpr-p)
                                          ((force)))))))

  (local (in-theory (disable (force))))


  (local (defthm len-plus-one
           (implies (consp x)
                    (equal (+ 1 (len (cdr x)))
                           (len x)))))

  (local (in-theory (enable arg1-exists-by-arity)))

  (local (defthm vl-syscall->returninfo-of-vl-nonatom
           (implies (and (equal (vl-nonatom->op x) :vl-syscall)
                         (not (vl-atom-p x))
                         (vl-atts-p atts)
                         (vl-maybe-exprtype-p finaltype)
                         (maybe-natp finalwidth))
                    (equal (vl-syscall->returninfo (make-vl-nonatom :op :vl-syscall
                                                                    :args (vl-nonatom->args x)
                                                                    :atts atts
                                                                    :finalwidth finalwidth
                                                                    :finaltype finaltype))
                           (vl-syscall->returninfo x)))
           :hints(("Goal" :in-theory (enable vl-syscall->returninfo
                                             vl-0ary-syscall-p
                                             vl-unary-syscall-p
                                             vl-*ary-syscall-p
                                             vl-$random-expr-p)))))

  (local (defthm vl-syscall->returninfo-of-vl-nonatom-reassemble
           (implies (and (equal (vl-nonatom->op x) :vl-syscall)
                         (same-lengthp rest (rest (vl-nonatom->args x)))
                         (vl-exprlist-p rest)
                         (not (vl-atom-p x))
                         (vl-atts-p atts)
                         (vl-maybe-exprtype-p finaltype)
                         (maybe-natp finalwidth))
                    (equal (vl-syscall->returninfo (make-vl-nonatom :op :vl-syscall
                                                                    :args (cons (first (vl-nonatom->args x))
                                                                                rest)
                                                                    :atts atts
                                                                    :finalwidth finalwidth
                                                                    :finaltype finaltype))
                           (vl-syscall->returninfo x)))
           :hints(("Goal" :in-theory (enable vl-syscall->returninfo
                                             vl-0ary-syscall-p
                                             vl-unary-syscall-p
                                             vl-*ary-syscall-p
                                             vl-$random-expr-p
                                             my-disables
                                             )
                   :expand ((len (vl-nonatom->args x))
                            (len (cdr (vl-nonatom->args x)))
                            (len rest)
                            (len (cdr rest)))))))

  (defthm-vl-expr-size-flag

    (defthm vl-expr-welltyped-p-of-vl-expr-size
      (let ((ret (vl-expr-size lhs-size x ss ctx warnings)))
        (implies (mv-nth 0 ret)
                 (vl-expr-welltyped-p (mv-nth 2 ret))))
      :hints ('(:expand ((vl-expr-size lhs-size x ss ctx warnings)
                         (vl-expr-size nil x ss ctx warnings)
                         (:free (op atts args finalwidth finaltype)
                          (vl-expr-welltyped-p
                           (vl-nonatom op atts args finalwidth finaltype))))))
      :flag vl-expr-size)

    (defthm vl-exprlist-welltyped-p-of-vl-exprlist-size
      (let ((ret (vl-exprlist-size x ss ctx warnings)))
        (implies (mv-nth 0 ret)
                 (vl-exprlist-welltyped-p (mv-nth 2 ret))))
      :hints ('(:expand ((vl-exprlist-size x ss ctx warnings))))
      :flag vl-exprlist-size)

    (defthm vl-expr-welltyped-p-of-vl-expr-expandsizes
      (let ((ret (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings)))
        (implies (mv-nth 0 ret)
                 (and (vl-expr-welltyped-p (mv-nth 2 ret))
                      (equal (vl-expr->finalwidth (mv-nth 2 ret))
                             (nfix finalwidth))
                      (equal (vl-expr->finaltype (mv-nth 2 ret))
                             (vl-exprtype-fix finaltype)))))
      :hints ('(:expand ((:free (finalwidth)
                          (vl-expr-expandsizes x finalwidth finaltype ss ctx warnings))
                         (:free (op atts args finalwidth finaltype)
                          (vl-expr-welltyped-p
                           (vl-nonatom op atts args finalwidth finaltype))))
                :in-theory (enable vl-syscall-selfsize)
                )
              (and stable-under-simplificationp
                   '(:expand ((:free (warnings)
                               (vl-expr-selfsize x ss ctx warnings))
                              (:free (op atts args finalwidth finaltype)
                               (vl-expr-welltyped-p
                                (vl-nonatom op atts args finalwidth finaltype))))))
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::member-of-cons
                                        vl-selexpr-welltyped-p))))
      :flag vl-expr-expandsizes)

    (defthm vl-exprlist-welltyped-p-of-vl-exprlist-expandsizes
      (let ((ret (vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings)))
        (implies (mv-nth 0 ret)
                 (and (vl-exprlist-welltyped-p (mv-nth 2 ret))
                      (all-equalp (nfix finalwidth)
                                  (vl-exprlist->finalwidths (mv-nth 2 ret)))
                      (all-equalp (vl-exprtype-fix finaltype)
                                  (vl-exprlist->finaltypes (mv-nth 2 ret))))))
      :hints ('(:expand ((vl-exprlist-expandsizes x finalwidth finaltype ss ctx warnings))))
      :flag vl-exprlist-expandsizes)

    :hints(("Goal"
            :in-theory (e/d (vl-nonatom->op-forward
                             ;; acl2::member-of-cons
                             ARG1-EXISTS-BY-ARITY
                             acl2::member-when-atom)
                            ((force)))
            :do-not '(generalize fertilize)))))

(defthm vl-expr->finalwidth-of-vl-expr-size-when-lhs-size
  ;; ;; This is an important corollary.  It shows us that if we actually provide
  ;; ;; an lhs-size argument, we're guaranteed to get back an expression that is
  ;; ;; at least as large as lhs-size.
  (let ((ret (vl-expr-size lhs-size x ss ctx warnings)))
    (implies (and (mv-nth 0 ret)
                  (natp lhs-size))
             (<= lhs-size (vl-expr->finalwidth (mv-nth 2 ret)))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :expand ((vl-expr-size lhs-size x ss ctx warnings)))))


(define vl-datatype->packedp ((x vl-datatype-p))
  :parents (vl-datatype)
  :short "Check to see whether a datatype is packed."
  :long "<p>Doesn't do deep consistency checking to say whether the datatype
really can be considered packed -- just that it doesn't have unpacked dims, and
it's of a bit-stream coretype or a packed struct/union type.  Ignoring enums
for the moment.</p>"

  (b* (((when (consp (vl-datatype->udims x))) nil))
    (vl-datatype-case x
      :vl-coretype (and (member x.name '(:vl-logic
                                         :vl-reg
                                         :vl-bit
                                         :vl-byte
                                         :vl-shortint
                                         :vl-int
                                         :vl-longint
                                         :vl-integer
                                         :vl-time))
                        t)
      :vl-struct x.packedp
      :vl-union x.packedp
      :vl-enum t
      :otherwise nil ;; usertypes should be resolved
      )))

(define vl-basictype->datatype ((x vl-basictypekind-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (implies (not warning) (vl-datatype-p type))))
  (b* ((x (vl-basictypekind-fix x))
       ((when (vl-coretypename-p x))
        (mv nil (make-vl-coretype :name x))))
    (mv (make-vl-warning :type :vl-basictype->datatype-fail
                         :msg "Couldn't resolve type of ~a0."
                         :args (list x))
        nil)))



(define vl-castexpr->datatype ((x vl-expr-p) (ss vl-scopestack-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (implies (not warning) (vl-datatype-p type))))
  ;; missing support for type parameters and maybe some other things
  (b* ((x (vl-expr-fix x))
       ((unless (vl-atom-p x))
        (mv (make-vl-warning :type :vl-castexpr->datatype-fail
                             :msg "Couldn't resolve type of ~a0 (not implemented)."
                             :args (list x))
            nil))
       ((vl-atom x))
       ((when (eq (tag x.guts) :vl-basictype))
        (vl-basictype->datatype (vl-basictype->kind x.guts)))
       ((unless (eq (tag x.guts) :vl-typename))
        (mv (make-vl-warning :type :vl-castexpr->datatype-fail
                             :msg "Couldn't resolve type of ~a0 (not implemented)."
                             :args (list x))
            nil)))
    (vl-datatype-usertype-elim (make-vl-usertype :kind x) ss 100)))

(defconst *simple-vector-datatype*
  (make-vl-coretype :name :vl-logic :pdims (list (make-vl-range
                                                  :msb (vl-make-index 0)
                                                  :lsb (vl-make-index 0)))))

(define vl-atom-selfdetermine-type ((x vl-expr-p)
                                    (ss vl-scopestack-p)
                                    (ctx vl-context-p)
                                    (warnings vl-warninglist-p))
  :guard (vl-atom-p x)
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (type     (implies successp (vl-datatype-p type)))
               (new-warnings vl-warninglist-p))
  (b* (((vl-atom x))
       (warnings (vl-warninglist-fix warnings)))
    (case (tag x.guts)
      ((:vl-constint :vl-weirdint :vl-extint)
       (mv t *simple-vector-datatype* warnings))
      ((:vl-hidpiece :vl-id)
       (b* (((mv warning type)
             (vl-index-find-type x ss (vl-context-fix ctx)))
            ((when warning)
             (mv nil nil (cons warning warnings))))
         (mv t type warnings)))
      (otherwise
       (mv nil nil
           (warn :type :vl-expr-selfdetermined-type-fail
                 :msg  "~a0: Couldn't determine the type of atom ~a1."
                 :args (list (vl-context-fix ctx) (vl-expr-fix x))))))))


(define vl-op-simple-vector-p ((x vl-op-p))
  ;; We think all of these operators always produce a simple vector.  The one
  ;; odd case is the concatenation op when it is really an unpacked
  ;; concatenation.  For this reason we don't include the concatenation
  ;; operator here.
  (member (vl-op-fix x)
          '(:vl-unary-plus
            :vl-unary-minus
            :vl-unary-lognot
            :vl-unary-bitnot
            :vl-unary-bitand
            :vl-unary-nand
            :vl-unary-bitor
            :vl-unary-nor
            :vl-unary-xor
            :vl-unary-xnor
            :vl-binary-plus
            :vl-binary-minus
            :vl-binary-times
            :vl-binary-div
            :vl-binary-rem
            :vl-binary-eq
            :vl-binary-neq
            :vl-binary-ceq
            :vl-binary-cne
            :vl-binary-wildeq
            :vl-binary-wildneq
            :vl-binary-logand
            :vl-binary-logor
            :vl-binary-power
            :vl-binary-lt
            :vl-binary-lte
            :vl-binary-gt
            :vl-binary-gte
            :vl-binary-bitand
            :vl-binary-bitor
            :vl-binary-xor
            :vl-binary-xnor
            :vl-binary-shr
            :vl-binary-shl
            :vl-binary-ashr
            :vl-binary-ashl
            :vl-implies
            :vl-equiv
            :vl-bitselect
            :vl-select-colon
            :vl-select-pluscolon
            :vl-select-minuscolon
            :vl-partselect-colon
            :vl-partselect-pluscolon
            :vl-partselect-minuscolon
            :vl-multiconcat)))

(local (in-theory (enable arg1-exists-by-arity
                          vl-expr-p-of-car-when-vl-exprlist-p)))

(define vl-expr-selfdetermine-type ((x vl-expr-p)
                                    (ss vl-scopestack-p)
                                    (ctx vl-context-p)
                                    (warnings vl-warninglist-p))
  :parents (expression-sizing)
  :short "Determine the (unpacked) type of an expression."
  :long "<p>Note: this function isn't used yet, because we don't try to support
unpacked array concatenations yet.</p>

<p>In the context of unpacked array concatenations, the expressions inside the
concatenation have to have self-determined type.  We think this means that it
has to be clear from looking at the expression whether it's an unpacked
array/struct/whatever.  If it is a packed structure, we think it doesn't matter
what its type is.</p>

<p>If this function is successful, it returns a datatype.  If it is an unpacked
datatype, then we think it's the exact self-determined datatype of the
expression.  However, all packed datatypes are treated the same here -- in
particular, the size and signedness of the packed datatype returned doesn't
mean anything.</p>"
  :measure (vl-expr-count x)
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (type     (implies successp (vl-datatype-p type)))
               (new-warnings vl-warninglist-p))
  :verify-guards nil
  (b* ((warnings (vl-warninglist-fix warnings))
       ((when (vl-atom-p x))
        (vl-atom-selfdetermine-type x ss ctx warnings))
       ((vl-nonatom x))
       ((when (member x.op '(:vl-hid-dot :vl-index)))
        (b* (((mv warning type) (vl-index-find-type x ss (vl-context-fix ctx)))
             ((when warning) (mv nil nil (cons warning (vl-warninglist-fix warnings)))))
          (mv t type warnings)))
       ((when (eq x.op :vl-qmark))
        (b* (((mv ok1 type1 warnings)
              (vl-expr-selfdetermine-type (second x.args) ss ctx warnings))
             ((mv ok2 type2 warnings)
              (vl-expr-selfdetermine-type (third x.args) ss ctx warnings))
             ((unless (and ok1 ok2))
              (mv nil nil warnings))
             ((when (equal type1 type2))
              (mv t type1 warnings))
             ((when (and (vl-datatype->packedp type1)
                         (vl-datatype->packedp type2)))
              ;; OK -- both types are packed, so it doesn't really matter
              (mv t type1 warnings)))
          (mv nil nil
              (warn :type :vl-expr-self-determined-type-fail
                    :msg "~a0: Couldn't self-determine the type of ~a1 ~
                          because the branches have different types: ~a2 ~
                          versus ~a3."
                    :args (list (vl-context-fix ctx)
                                (vl-expr-fix x) type1 type2)))))
       ((when (eq x.op :vl-pattern-type))
        (b* (((mv warning type) (vl-castexpr->datatype (first x.args) ss))
             ((when warning) (mv nil nil (cons warning (vl-warninglist-fix warnings)))))
          (mv t type warnings)))

       ((when (or (vl-op-simple-vector-p x.op)
                  (eq x.op :vl-concat)))
        ;; Doesn't matter what packed datatype we return, so we just make a logic vector.
        (mv t *simple-vector-datatype*
            warnings)))
    (mv nil nil
        (warn :type :vl-expr-self-determined-type-fail
              :msg "~a0: Couldn't self-determine the type of ~a1."
              :args (list (vl-context-fix ctx) (vl-expr-fix x)))))
  ///
  (verify-guards vl-expr-selfdetermine-type))

(define vl-expr-has-patterns ((x vl-expr-p))
  :measure (vl-expr-count x)
  (b* (((when (vl-atom-p x)) nil)
       ((vl-nonatom x))
       ((when (member x.op '(:vl-pattern-positional
                             :vl-pattern-keyvalue
                             :vl-pattern-multi
                             :vl-pattern-type)))
        t)
       ((when (eq x.op :vl-qmark))
        (or (vl-expr-has-patterns (second x.args))
            (vl-expr-has-patterns (third x.args)))))
    nil))

(fty::defalist vl-type-expr-pairs :key-type vl-datatype :val-type vl-expr)




(fty::deflist vl-datatypelist :elt-type vl-datatype :true-listp nil :elementp-of-nil nil)

(defprojection vl-structmemberlist->types ((x vl-structmemberlist-p))
  (vl-structmember->type x)
  :returns (types vl-datatypelist-p))

(local (defthm vl-type-expr-pairs-of-pairlis
         (implies (and (equal (len x) (len y))
                       (vl-datatypelist-p x)
                       (vl-exprlist-p y))
                  (vl-type-expr-pairs-p (pairlis$ x y)))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(define vl-exprlist-max-count ((x vl-exprlist-p))
  :verify-guards nil
  (if (atom x)
      0
    (max (vl-expr-count (car x))
         (vl-exprlist-max-count (cdr x)))))

(local (fty::deffixcong list-equiv equal (vl-exprlist-max-count x) x
         :hints(("Goal" :in-theory (enable list-fix
                                           vl-exprlist-max-count)))))

(local
 (defthm vl-exprlist-max-count-less-than-vl-exprlist-count
   (< (vl-exprlist-max-count x)
      (vl-exprlist-count x))
   :hints(("Goal" :in-theory (enable vl-exprlist-max-count
                                     pairlis$ len)
           :expand ((vl-exprlist-count vals))))
   :rule-classes :linear))

;; (local (in-theory (enable acl2::true-listp-of-list-fix
;;                           (:t repeat)
;;                           acl2::len-of-repeat)))
(local (in-theory (enable acl2::len-of-repeat)))

(define vl-type-expr-pairs-sum-datatype-sizes ((x vl-type-expr-pairs-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (size (implies (not warning) (natp size)) :rule-classes :type-prescription))
  :measure (len (vl-type-expr-pairs-fix x))
  :verify-guards nil
  (b* ((x (vl-type-expr-pairs-fix x)))
    (if (atom x)
        (mv nil 0)
      (b* (((mv warning size1) (vl-datatype-size (caar x)))
           ((when warning) (mv warning nil))
           ((mv warning size2) (vl-type-expr-pairs-sum-datatype-sizes (cdr x)))
           ((when warning) (mv warning nil)))
        (mv nil (+ size1 size2)))))
  ///
  (verify-guards vl-type-expr-pairs-sum-datatype-sizes))


(local (in-theory (enable basic-arithmetic-rules)))

(local (defthm vl-datatype-size-of-cdr-udims
         (b* (((mv warning size) (vl-datatype-size type))
              ((mv warning1 size1) (vl-datatype-size
                                    (vl-datatype-update-dims
                                     (vl-datatype->pdims type)
                                     (cdr (vl-datatype->udims type))
                                     type))))
           (implies (and (not warning)
                         (consp (vl-datatype->udims type)))
                    (and (not warning1)
                         (equal size1
                                (/ size (vl-range-size (car (vl-datatype->udims type))))))))
         :hints(("Goal" :in-theory (enable vl-datatype->pdims
                                           vl-datatype->udims
                                           vl-datatype-size
                                           vl-datatype-update-dims
                                           vl-packeddimensionlist-total-size)))))

(local (defthm vl-datatype-size-of-cdr-pdims
         (b* (((mv warning size) (vl-datatype-size type))
              ((mv warning1 size1) (vl-datatype-size
                                    (vl-datatype-update-dims
                                     (cdr (vl-datatype->pdims type))
                                     nil
                                     type))))
           (implies (and (not warning)
                         (consp (vl-datatype->pdims type))
                         (not (consp (vl-datatype->udims type))))
                    (and (not warning1)
                         (equal size1
                                (/ size (vl-range-size (car (vl-datatype->pdims type))))))))
         :hints(("Goal" :in-theory (enable vl-datatype->pdims
                                           vl-datatype->udims
                                           vl-datatype-size
                                           vl-datatype-update-dims
                                           vl-packeddimensionlist-total-size)))))


(local (defthm vl-type-expr-pairs-sum-datatype-sizes-of-pairlis-structmember-types
         (b* (((mv warning sizes) (vl-structmemberlist-sizes members))
              ((mv warning1 size) (vl-type-expr-pairs-sum-datatype-sizes
                                   (pairlis$ (vl-structmemberlist->types members) exprs))))
           (implies (not warning)
                    (and (not warning1)
                         (equal size (sum-nats sizes)))))
         :hints (("goal" :induct (pairlis$ members exprs)
                  :in-theory (enable pairlis$ vl-structmemberlist->types
                                     vl-type-expr-pairs-sum-datatype-sizes
                                     vl-structmemberlist-sizes)))))

(local (defthm vl-structmemberlist->sizes-ok-when-type-size-ok
         (b* (((mv warning size) (vl-datatype-size type))
              ((mv warning1 sizes) (vl-structmemberlist-sizes
                                    (vl-struct->members type))))
           (implies (and (not warning)
                         (equal (vl-datatype-kind type) :vl-struct))
                    (and (not warning1)
                         (implies (and (not (consp (vl-datatype->pdims type)))
                                       (not (consp (vl-datatype->udims type))))
                                  (equal (sum-nats sizes) size)))))
         :hints (("Goal" :expand ((vl-datatype-size type))
                  :in-theory (enable vl-datatype->pdims
                                     vl-datatype->udims
                                     vl-packeddimensionlist-total-size)))))

(local (defthm blah
           (implies (and (acl2-numberp a)
                         (acl2-numberp n))
                    (equal (+ a (* (+ -1 n) a))
                           (* n a)))))

(define vl-assignpattern-positional-replacement ((lhs-type vl-datatype-p)
                                                 (fields vl-exprlist-p)
                                                 (orig-x vl-expr-p)
                                                 (ctx vl-context-p)
                                                 (warnings vl-warninglist-p))
    :parents (expression-sizing)
    :short "Return the list of type/expression pairs to concatenate together to
replace a positional assignment pattern."
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (pairs vl-type-expr-pairs-p)
                 (new-warnings vl-warninglist-p))
  (b* ((pdims (vl-datatype->pdims lhs-type))
       (udims (vl-datatype->udims lhs-type))
       ((unless (or (consp udims) (consp pdims)))
        (b* (((unless (eq (vl-datatype-kind lhs-type) :vl-struct))
              (mv nil nil
                  (warn :type :vl-assignpattern-elim-fail
                        :msg "~a0: Positional assignment pattern must be in a ~
                              struct or array type context: ~a1"
                        :args (list (vl-context-fix ctx) (vl-expr-fix orig-x)))))
             ((vl-struct lhs-type))
             ((unless (eql (len fields) (len lhs-type.members)))
              (mv nil nil
                  (warn :type :vl-assignpattern-elim-fail
                        :msg "~a0: Wrong number of fields in positional ~
                              assignment pattern ~a1"
                        :args (list (vl-context-fix ctx) (vl-expr-fix orig-x))))))
          (mv t (pairlis$ (vl-structmemberlist->types lhs-type.members)
                          (list-fix (vl-exprlist-fix fields)))
              (ok))))
       (dim (if (consp udims) (car udims) (car pdims)))
       ((unless (and (not (eq dim :vl-unsized-dimension))
                     (vl-range-resolved-p dim)))
        (mv nil nil
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Unresolved packed dimensions in LHS datatype ~a1"
                  :args (list (vl-context-fix ctx) (vl-datatype-fix lhs-type)))))
       ((unless (eql (vl-range-size dim) (len fields)))
        (mv nil nil
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Wrong number of fields in positional assignment ~
                        pattern ~a1"
                  :args (list (vl-context-fix ctx) (vl-expr-fix orig-x)))))

       (new-datatype (if (consp udims)
                         (vl-datatype-update-dims pdims (cdr udims) lhs-type)
                       (vl-datatype-update-dims (cdr pdims) nil lhs-type))))
    (mv t (pairlis$ (repeat (len fields) new-datatype)
                    (list-fix (vl-exprlist-fix fields)))
        (ok)))
  ///
  (defthm vl-exprlist-max-count-of-vl-assignpattern-positional-replacement
    (< (vl-exprlist-max-count
        (alist-vals
         (mv-nth 1 (vl-assignpattern-positional-replacement
                    lhs-type fields orig-x ctx warnings))))
       (vl-exprlist-count fields))
    :rule-classes :linear)

  (defthm vl-exprlist-max-count-of-vl-assignpattern-positional-replacement-lte-max-count
    (<= (vl-exprlist-max-count
         (alist-vals
          (mv-nth 1 (vl-assignpattern-positional-replacement
                     lhs-type fields orig-x ctx warnings))))
        (vl-exprlist-max-count fields))
    :rule-classes :linear)


  (local (defthm vl-type-expr-pairs-sum-datatype-sizes-of-pairlis-repeat
           (b* (((mv warning size) (vl-datatype-size type))
                ((mv warning1 size2) (vl-type-expr-pairs-sum-datatype-sizes
                                      (pairlis$ (repeat n type) exprs))))
             (implies (not warning)
                      (and (not warning1)
                           (equal size2 (* (nfix n) size)))))
           :hints(("Goal" :in-theory (enable pairlis$ repeat nthcdr
                                             vl-type-expr-pairs-sum-datatype-sizes)
                   :induct (nthcdr n exprs)))))

  (defthm sum-sizes-of-vl-assignpattern-positional-replacement
    (b* (((mv ok pairs &) (vl-assignpattern-positional-replacement
                           lhs-type fields orig-x ctx warnings))
         ((mv warning size) (vl-datatype-size lhs-type))
         ((mv warning1 size-sum) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
      (implies (and ok (not warning))
               (and (not warning1)
                    (equal size-sum size))))))


(define append-n ((count natp) (list))
  (if (zp count)
      nil
    (append-without-guard list (append-n (1- count) list))))

(define vl-assignpattern-multi-replacement ((lhs-type vl-datatype-p)
                                            (args vl-exprlist-p)
                                            (orig-x vl-expr-p)
                                            (ctx vl-context-p)
                                            (warnings vl-warninglist-p))
  :parents (expression-sizing)
  :short "Return the list of type/expression pairs to concatenate together to
replace a positional assignment pattern."
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (pairs vl-type-expr-pairs-p)
               (new-warnings vl-warninglist-p))
  :prepwork ((local (defthm vl-exprlist-p-of-append-n-expressions
                      (implies (vl-exprlist-p list)
                               (vl-exprlist-p (append-n count list)))
                      :hints(("Goal" :in-theory (enable append-n))))))
  (b* ((ctx (vl-context-fix ctx))
       (orig-x (vl-expr-fix orig-x))
       ((unless (and (eql (len args) 2)
                     (vl-expr-resolved-p (first args))
                     (not (eq (vl-expr-kind (second args)) :atom))
                     (eq (vl-nonatom->op (second args)) :vl-concat)))
        (mv nil nil
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Ill-formed replication assignment pattern: ~a1"
                  :args (list ctx orig-x))))
       (replications (vl-resolved->val (first args)))
       (fields (append-n replications (vl-nonatom->args (second args)))))
    ;; bozo the warnings produced by this will probably be weird
    (vl-assignpattern-positional-replacement lhs-type fields orig-x ctx warnings))
  ///

  (local (defthm vl-exprlist-max-count-of-append
           (equal (vl-exprlist-max-count (append x y))
                  (max (vl-exprlist-max-count x)
                       (vl-exprlist-max-count y)))
           :hints(("Goal" :in-theory (enable vl-exprlist-max-count)))))

  (local (defthm vl-exprlist-max-count-of-append-n
           (<= (vl-exprlist-max-count (append-n n x))
               (vl-exprlist-max-count x))
           :hints(("Goal" :in-theory (enable append-n
                                             vl-exprlist-max-count)))
           :rule-classes :linear))

  (defthm vl-exprlist-max-count-of-vl-assignpattern-multi-replacement
    (< (vl-exprlist-max-count
        (alist-vals (mv-nth 1 (vl-assignpattern-multi-replacement
                               lhs-type args orig-x ctx warnings))))
       (vl-exprlist-count args))
    :rule-classes :linear)

  (defthm sum-sizes-of-vl-assignpattern-multi-replacement
    (b* (((mv ok pairs &) (vl-assignpattern-multi-replacement
                           lhs-type args orig-x ctx warnings))
         ((mv warning size) (vl-datatype-size lhs-type))
         ((mv warning1 size-sum) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
      (implies (and ok (not warning))
               (and (not warning1)
                    (equal size-sum size))))))

;; Alist for storing the correspondences from a key/value assignment pattern.
;; We don't give the keys a type because they can be an index or a string or
;; :default and we don't think it's needed.
(fty::defalist vl-expr-val-alist :val-type vl-expr)

(define vl-expr-val-alist-max-count ((x vl-expr-val-alist-p))
  :verify-guards nil
  :measure (len (vl-expr-val-alist-fix x))
  (b* ((x (vl-expr-val-alist-fix x)))
    (if (atom x)
        0
      (max (vl-expr-count (cdar x))
           (vl-expr-val-alist-max-count (cdr x))))))


(local
 (defthm vl-expr-val-alist-max-count-of-pairlis$
   (implies (equal (len keys) (len vals))
            (< (vl-expr-val-alist-max-count (pairlis$ keys vals))
               (vl-exprlist-count vals)))
   :hints(("Goal" :in-theory (enable vl-expr-val-alist-fix
                                     vl-expr-val-alist-max-count
                                     pairlis$ len)
           :expand ((vl-exprlist-count vals))
           :induct (pairlis$ keys vals)))
   :rule-classes :linear))

(define vl-parse-keyval-pattern-array ((fields vl-exprlist-p)
                                       (range (and (vl-range-p range)
                                                   (vl-range-resolved-p range)))
                                       (orig-x vl-expr-p)
                                       (ctx vl-context-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (alist vl-expr-val-alist-p)
               (new-warnings vl-warninglist-p))
  :hooks ((:fix :hints (("goal" :induct (vl-parse-keyval-pattern-array
                                         fields range orig-x ctx warnings)
                         :expand ((:free (range orig-x ctx warnings)
                                   (vl-parse-keyval-pattern-array
                                    fields range orig-x ctx warnings))
                                  (vl-parse-keyval-pattern-array
                                   (vl-exprlist-fix fields) range orig-x ctx warnings))
                         :in-theory (disable (:d vl-parse-keyval-pattern-array))))))

  (b* ((warnings (vl-warninglist-fix warnings))
       (ctx (vl-context-fix ctx))
       (orig-x (vl-expr-fix orig-x))
       ((when (atom fields)) (mv t nil warnings))
       (pair (vl-expr-fix (car fields)))
       ((unless (and (not (vl-atom-p pair))
                     (eq (vl-nonatom->op pair) :vl-keyvalue)))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Expected key-value pairs in assignment ~
                                  pattern ~a1 (bad: ~a2)"
                          :args (list ctx orig-x pair))))
       (pair.args (vl-nonatom->args pair))
       (idx (first pair.args))
       (defaultp (and (vl-atom-p idx)
                      (equal (vl-atom->guts idx) (vl-keyguts :vl-default))))
       ((unless (or defaultp (vl-expr-resolved-p idx)))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Expected keys in array keyval pattern ~
                                  to be integers (except for default): ~a1 ~
                                  (bad: ~a2)"
                          :args (list ctx orig-x pair))))
       (key (if defaultp
                :default
              (vl-resolved->val idx)))
       ((unless (or defaultp
                    (and (<= key (vl-resolved->val (vl-range->msb range)))
                         (<= (vl-resolved->val (vl-range->lsb range)) key))
                    (and (<= (vl-resolved->val (vl-range->msb range)) key)
                         (<= key (vl-resolved->val (vl-range->lsb range))))))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Assign pattern key out of range for ~
                                  array type: ~a1 (bad: ~a2)"
                          :args (list ctx orig-x pair))))

       ((mv rest-ok rest warnings)
        (vl-parse-keyval-pattern-array (cdr fields) range orig-x ctx warnings)))
    (mv rest-ok
        (cons (cons key (second pair.args))
              rest)
        warnings))
  ///
  (defthm vl-exprlist-max-count-of-vl-parse-keyval-pattern-array
    (< (vl-exprlist-max-count
        (alist-vals (mv-nth 1 (vl-parse-keyval-pattern-array
                               fields range orig-x ctx warnings))))
       (vl-exprlist-count fields))
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count)))
    :rule-classes :linear))


(define vl-parse-keyval-pattern-struct ((fields vl-exprlist-p)
                                        (members vl-structmemberlist-p)
                                        (orig-x vl-expr-p)
                                        (ctx vl-context-p)
                                        (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (alist vl-expr-val-alist-p)
               (new-warnings vl-warninglist-p))
  :hooks ((:fix :hints (("goal" :induct (vl-parse-keyval-pattern-struct
                                         fields members orig-x ctx warnings)
                         :expand ((:free (members orig-x ctx warnings)
                                   (vl-parse-keyval-pattern-struct
                                    fields members orig-x ctx warnings))
                                  (vl-parse-keyval-pattern-struct
                                   (vl-exprlist-fix fields) members orig-x ctx warnings))
                         :in-theory (disable (:d vl-parse-keyval-pattern-struct))))))

  (b* ((warnings (vl-warninglist-fix warnings))
       (ctx (vl-context-fix ctx))
       (orig-x (vl-expr-fix orig-x))
       ((when (atom fields)) (mv t nil warnings))
       (pair (vl-expr-fix (car fields)))
       ((unless (and (not (vl-atom-p pair))
                     (eq (vl-nonatom->op pair) :vl-keyvalue)))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Expected key-value pairs in assignment ~
                                  pattern ~a1 (bad: ~a2)"
                          :args (list ctx orig-x pair))))
       (pair.args (vl-nonatom->args pair))
       (idx (first pair.args))
       (defaultp (and (vl-atom-p idx)
                      (equal (vl-atom->guts idx) (vl-keyguts :vl-default))))
       ((unless (or defaultp (vl-idexpr-p idx)))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Expected keys in struct keyval pattern ~
                                  to be identifiers (except for default): ~a1 ~
                                  (bad: ~a2)"
                          :args (list ctx orig-x pair))))
       (key (if defaultp
                :default
              (vl-idexpr->name idx)))
       ((unless (or defaultp
                    (vl-find-structmember key members)))
        (mv nil nil (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Assign pattern key out of range for ~
                                  struct type: ~a1 (bad: ~a2)"
                          :args (list ctx orig-x pair))))

       ((mv rest-ok rest warnings)
        (vl-parse-keyval-pattern-struct (cdr fields) members orig-x ctx warnings)))
    (mv rest-ok
        (cons (cons key (second pair.args))
              rest)
        warnings))
  ///
  (defthm vl-exprlist-max-count-of-vl-parse-keyval-pattern-struct
    (< (vl-exprlist-max-count
        (alist-vals (mv-nth 1 (vl-parse-keyval-pattern-struct
                               fields members orig-x ctx warnings))))
       (vl-exprlist-count fields))
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count)))
    :rule-classes :linear))


;; (local (defthm vl-expr-count-of-lookup-in-expr-val-alist
;;          (implies (hons-assoc-equal k alist)
;;                   (<= (vl-expr-count (cdr (hons-assoc-equal k alist)))
;;                       (vl-expr-val-alist-max-count alist)))
;;          :hints(("Goal" :in-theory (enable vl-expr-val-alist-max-count
;;                                            hons-assoc-equal)
;;                  :induct (hons-assoc-equal k alist)
;;                  :expand ((vl-expr-val-alist-fix alist)
;;                           (vl-expr-val-alist-max-count alist))))))

(local (defthm vl-expr-count-of-lookup-in-expr-val-alist-fix
         (implies (hons-assoc-equal k (vl-expr-val-alist-fix alist))
                  (<= (vl-expr-count (cdr (hons-assoc-equal k (vl-expr-val-alist-fix alist))))
                      (vl-exprlist-max-count (alist-vals alist))))
         :hints(("Goal" :in-theory (enable vl-exprlist-max-count
                                           hons-assoc-equal)
                 :induct (hons-assoc-equal k alist)
                 :expand ((vl-expr-val-alist-fix alist)
                          (alist-vals alist))))
         :rule-classes (:rewrite :linear)))

(local (fty::deffixcong vl-expr-val-alist-equiv vl-exprlist-equiv
         (alist-vals x) x
         :hints(("Goal" :in-theory (enable vl-expr-val-alist-fix)))))

(define vl-keyvalue-pattern-collect-array-replacements
  ((count natp)
   (idx integerp)
   (incr integerp)
   (datatype vl-datatype-p)
   (field-alist vl-expr-val-alist-p)
   (orig-x vl-expr-p)
   (ctx vl-context-p)
   (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (pairs vl-type-expr-pairs-p)
               (new-warnings vl-warninglist-p))
  (b* ((warnings (vl-warninglist-fix warnings))
       (orig-x (vl-expr-fix orig-x))
       (ctx (vl-context-fix ctx))
       (idx (lifix idx))
       (field-alist (vl-expr-val-alist-fix field-alist))
       ((when (zp count)) (mv t nil warnings))
       (lookup (or (hons-assoc-equal idx field-alist)
                   (hons-assoc-equal :default field-alist)))
       ((unless lookup)
        (mv nil nil
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Missing array index ~x1 in assignment pattern ~a2"
                  :args (list ctx idx orig-x))))
       ((mv ok rest warnings)
        (vl-keyvalue-pattern-collect-array-replacements
         (1- count) (+ idx (lifix incr)) incr
         datatype field-alist orig-x ctx warnings)))
    (mv ok (cons (cons (vl-datatype-fix datatype) (cdr lookup)) rest) warnings))
  ///

  (defthm vl-exprlist-max-count-of-vl-keyvalue-pattern-collect-array-replacements
    (<= (vl-exprlist-max-count
         (alist-vals
          (mv-nth 1 (vl-keyvalue-pattern-collect-array-replacements
                     count idx incr datatype field-alist orig-x ctx warnings))))
        (vl-exprlist-max-count (alist-vals field-alist)))
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count)))
    :rule-classes :linear)

  (defthm vl-type-expr-pairs-sum-datatype-sizes-of-array-replacements
    (b* (((mv ok pairs &) (vl-keyvalue-pattern-collect-array-replacements
                           count idx incr datatype field-alist orig-x ctx warnings))
         ((mv warning size) (vl-datatype-size datatype))
         ((mv warning1 size1) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
      (implies (and ok (not warning))
               (and (not warning1)
                    (equal size1 (* (nfix count) size)))))
    :hints(("Goal" :in-theory (enable vl-type-expr-pairs-sum-datatype-sizes)))))

(define vl-keyvalue-pattern-collect-struct-replacements
  ((members vl-structmemberlist-p)
   (field-alist vl-expr-val-alist-p)
   (orig-x vl-expr-p)
   (ctx vl-context-p)
   (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (pairs vl-type-expr-pairs-p)
               (new-warnings vl-warninglist-p))
  (b* ((warnings (vl-warninglist-fix warnings))
       (orig-x (vl-expr-fix orig-x))
       (ctx (vl-context-fix ctx))
       (field-alist (vl-expr-val-alist-fix field-alist))
       ((when (atom members)) (mv t nil warnings))
       ((vl-structmember first) (car members))
       (lookup (or (hons-assoc-equal first.name field-alist)
                   (hons-assoc-equal :default field-alist)))
       ((unless lookup)
        (mv nil nil
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Missing struct member ~s1 in assignment pattern ~a2"
                  :args (list ctx first.name orig-x))))
       ((mv ok rest warnings)
        (vl-keyvalue-pattern-collect-struct-replacements
         (cdr members) field-alist orig-x ctx warnings)))
    (mv ok (cons (cons first.type (cdr lookup)) rest) warnings))
  ///
  (defthm vl-exprlist-max-count-of-vl-keyvalue-pattern-collect-struct-replacements
    (<= (vl-exprlist-max-count
         (alist-vals (mv-nth 1 (vl-keyvalue-pattern-collect-struct-replacements
                                members field-alist orig-x ctx warnings))))
        (vl-exprlist-max-count (alist-vals field-alist)))
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count)))
    :rule-classes :linear)

  (defthm vl-type-expr-pairs-sum-datatype-sizes-of-struct-replacements
    (b* (((mv ok pairs &) (vl-keyvalue-pattern-collect-struct-replacements
                           members field-alist orig-x ctx warnings))
         ((mv warning sizes) (vl-structmemberlist-sizes members))
         ((mv warning1 size1) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
      (implies (and ok (not warning))
               (and (not warning1)
                    (equal size1 (sum-nats sizes)))))
    :hints(("Goal" :in-theory (enable vl-type-expr-pairs-sum-datatype-sizes
                                      vl-structmemberlist-sizes)))))


(define vl-assignpattern-keyvalue-replacement ((lhs-type vl-datatype-p)
                                               (fields vl-exprlist-p)
                                               (orig-x vl-expr-p)
                                               (ctx vl-context-p)
                                               (warnings vl-warninglist-p))
    :parents (expression-sizing)
    :short "Return the list of type/expression pairs to concatenate together to
replace a key/value assignment pattern."
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (pairs vl-type-expr-pairs-p)
                 (new-warnings vl-warninglist-p))
    (b* ((warnings (vl-warninglist-fix warnings))
         (ctx (vl-context-fix ctx))
         (orig-x (vl-expr-fix orig-x))
         (pdims (vl-datatype->pdims lhs-type))
         (udims (vl-datatype->udims lhs-type))
         ((unless (or (consp udims) (consp pdims)))
          (b* (((unless (eq (vl-datatype-kind lhs-type) :vl-struct))
                (mv nil nil
                    (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Positional assignment pattern must be in a ~
                              struct or array type context: ~a1"
                          :args (list (vl-context-fix ctx) (vl-expr-fix orig-x)))))
               ((vl-struct lhs-type))
               ((mv ok alist warnings)
                (vl-parse-keyval-pattern-struct fields lhs-type.members orig-x ctx warnings))
               ((unless ok) (mv nil nil warnings))
               ((unless (uniquep (alist-keys alist)))
                (mv nil nil (warn :type :vl-assignpattern-elim-fail
                                  :msg "~a0: Duplicate keys in assignment pattern: ~a1"
                                  :args (list ctx orig-x)))))
            (vl-keyvalue-pattern-collect-struct-replacements
             lhs-type.members alist orig-x ctx warnings)))
         (dim (if (consp udims) (car udims) (car pdims)))
         ((unless (and (not (eq dim :vl-unsized-dimension))
                       (vl-range-resolved-p dim)))
          (mv nil nil
              (warn :type :vl-assignpattern-elim-fail
                    :msg "~a0: Unresolved packed dimensions in LHS datatype ~a1"
                    :args (list (vl-context-fix ctx) (vl-datatype-fix lhs-type)))))
         ((mv ok alist warnings)
          (vl-parse-keyval-pattern-array fields dim orig-x ctx warnings))
         ((unless ok) (mv nil nil warnings))
         ((unless (uniquep (alist-keys alist)))
          (mv nil nil (warn :type :vl-assignpattern-elim-fail
                            :msg "~a0: Duplicate keys in assignment pattern: ~a1"
                            :args (list ctx orig-x))))
         (new-datatype (if (consp udims)
                           (vl-datatype-update-dims pdims (cdr udims) lhs-type)
                         (vl-datatype-update-dims (cdr pdims) nil lhs-type)))
         (msb (vl-resolved->val (vl-range->msb dim)))
         (lsb (vl-resolved->val (vl-range->lsb dim)))
         (direction (if (< msb lsb) 1 -1)))
      (vl-keyvalue-pattern-collect-array-replacements
       (vl-range-size dim) msb direction
       new-datatype alist
       orig-x ctx warnings))
    ///
    (defthm vl-exprlist-max-count-of-vl-assignpattern-keyvalue-replacement
      (< (vl-exprlist-max-count
          (alist-vals (mv-nth 1 (vl-assignpattern-keyvalue-replacement
                                 lhs-type fields orig-x ctx warnings))))
         (vl-exprlist-count fields))
      :rule-classes :linear)

    (defthm sum-sizes-of-vl-assignpattern-keyvalue-replacement
      (b* (((mv ok pairs &) (vl-assignpattern-keyvalue-replacement
                             lhs-type fields orig-x ctx warnings))
           ((mv warning size) (vl-datatype-size lhs-type))
           ((mv warning1 size-sum) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
        (implies (and ok (not warning))
                 (and (not warning1)
                      (equal size-sum size))))))

(define vl-assignpattern-replacement ((lhs-type vl-datatype-p)
                                      (x vl-expr-p)
                                      (ctx vl-context-p)
                                      (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (member (vl-nonatom->op x)
                      '(:vl-pattern-positional
                        :vl-pattern-multi
                        :vl-pattern-keyvalue)))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (pairs vl-type-expr-pairs-p)
                 (new-warnings vl-warninglist-p))
    (b* (((vl-nonatom x)))
      (case x.op
        (:vl-pattern-positional
         (vl-assignpattern-positional-replacement lhs-type x.args x ctx warnings))
        (:vl-pattern-multi
         (vl-assignpattern-multi-replacement lhs-type x.args x ctx warnings))
        (:vl-pattern-keyvalue
         (vl-assignpattern-keyvalue-replacement lhs-type x.args x ctx warnings))
        (otherwise (mv (mbe :logic nil :exec 'impossible) nil nil))))
    ///
    (defthm vl-exprlist-max-count-of-vl-assignpattern-replacement
      (implies (not (vl-atom-p x))
               (< (vl-exprlist-max-count
                   (alist-vals (mv-nth 1 (vl-assignpattern-replacement
                                          lhs-type x ctx warnings))))
                  (vl-expr-count x)))
      :rule-classes :linear)

    (defthm sum-sizes-of-vl-assignpattern-replacement
      (b* (((mv ok pairs &) (vl-assignpattern-replacement
                             lhs-type x ctx warnings))
           ((mv warning size) (vl-datatype-size lhs-type))
           ((mv warning1 size-sum) (vl-type-expr-pairs-sum-datatype-sizes pairs)))
        (implies (and ok (not warning))
                 (and (not warning1)
                      (equal size-sum size))))))

(local (defthm vl-expr-size-of-concat
         (b* (((mv ok1 & new-x) (vl-expr-size
                                 lhs-size
                                 (make-vl-nonatom :op :vl-concat
                                                  :args args)
                                 ss ctx warnings))
              ((mv & sizes) (vl-exprlist-selfsize args ss ctx warnings1)))
           (and (implies (member nil sizes)
                         (not ok1))
                (implies ok1
                         (equal (vl-expr->finalwidth new-x)
                                (if lhs-size
                                    (max (nfix lhs-size) (sum-nats sizes))
                                  (sum-nats sizes))))))
:hints (("goal" :expand ((:free (size x) (vl-expr-size size x ss ctx warnings))
                             (:free (op args warnings)
                              (vl-expr-selfsize
                               (make-vl-nonatom :op op
                                                :args args)
                               ss ctx warnings))
                             (:free (guts warnings)
                              (vl-expr-selfsize
                               (make-vl-atom :guts guts)
                               ss ctx warnings)))
             :in-theory (enable vl-op-selfsize
                                vl-atom-selfsize
                                vl-exprlist-selfsize
                                warning-irrelevance-of-vl-expr-selfsize
                                warning-irrelevance-of-vl-exprlist-selfsize)))))

(local (defthm vl-expr-selfsize-of-concat
         (b* (((mv & selfsize) (vl-expr-selfsize
                                (make-vl-nonatom :op :vl-concat
                                                 :args args
                                                 :atts atts
                                                 :finalwidth finalwidth
                                                 :finaltype finaltype)
                                ss ctx warnings))
              ((mv & sizes) (vl-exprlist-selfsize args ss ctx warnings1)))
           (and (iff selfsize
                     (not (member nil sizes)))
                (implies selfsize
                         (equal selfsize
                                (sum-nats sizes)))))
         :hints (("goal" :expand ((:free (op args warnings)
                                   (vl-expr-selfsize
                                    (make-vl-nonatom :op op
                                                     :args args
                                                     :atts atts
                                                     :finalwidth finalwidth
                                                     :finaltype finaltype)
                                    ss ctx warnings)))
                  :in-theory (enable vl-op-selfsize
                                     vl-atom-selfsize
                                     vl-exprlist-selfsize
                                     warning-irrelevance-of-vl-expr-selfsize
                                     warning-irrelevance-of-vl-exprlist-selfsize)))))

(local (defthm vl-expr-selfsize-of-qmark
         (b* (((mv & selfsize) (vl-expr-selfsize
                                (make-vl-nonatom :op :vl-qmark
                                                 :args args
                                                 :atts atts
                                                 :finalwidth finalwidth
                                                 :finaltype finaltype)
                                ss ctx warnings))
              ((mv & condsize) (vl-expr-selfsize (first args) ss ctx nil))
              ((mv & truesize) (vl-expr-selfsize (second args) ss ctx nil))
              ((mv & falsesize) (vl-expr-selfsize (third args) ss ctx nil)))
           (implies (equal (len args) 3)
                    (and (iff selfsize (and truesize falsesize condsize))
                         (implies (and selfsize )
                                  (equal selfsize
                                         (max truesize falsesize))))))
         :hints (("goal" :expand ((:free (op args ctx warnings)
                                   (vl-expr-selfsize
                                    (make-vl-nonatom :op op
                                                     :args args
                                                     :atts atts
                                                     :finalwidth finalwidth
                                                     :finaltype finaltype)
                                    ss ctx nil))
                                  (:free (ctx) (vl-exprlist-selfsize args ss ctx nil))
                                  (:free (ctx) (vl-exprlist-selfsize (cdr args) ss ctx nil))
                                  (:free (ctx) (vl-exprlist-selfsize (cddr args) ss ctx nil))
                                  (:free (ctx) (vl-exprlist-selfsize (cdddr args) ss ctx nil)))
                  :in-theory (e/d (vl-op-selfsize
                                   ;; vl-exprlist-selfsize
                                   ;; vl-expr-selfsize
                                   warning-irrelevance-of-vl-expr-selfsize
                                   warning-irrelevance-of-vl-exprlist-selfsize
                                   )
                                  (max acl2::posp-rw natp-when-posp acl2::natp-rw))))))


(define vl-expr-assignpattern-extend/truncate ((lhs-type vl-datatype-p)
                                               (x vl-expr-p)
                                               (in-pattern)
                                               (ss vl-scopestack-p)
                                               (ctx vl-context-p)
                                               (warnings vl-warninglist-p))
  ;; bozo -- Do we ever need to worry about the sign of the resulting expression?
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (new-x vl-expr-p)
                 (new-warnings vl-warninglist-p))
  (b* ((warnings (vl-warninglist-fix warnings))
       (x (vl-expr-fix x))
       ((unless in-pattern) (mv t x warnings))
       ((mv warnings1 selfsize) (vl-expr-selfsize x ss ctx nil))
       ((mv warnings2 exprtype) (vl-expr-typedecide x ss ctx nil))
       ((unless (and selfsize exprtype))
        (mv nil x (append-without-guard warnings1 warnings2 warnings)))
       ((mv warning typesize) (vl-datatype-size lhs-type))
       ((when warning) (mv nil x (cons warning warnings)))
       ((when (< selfsize typesize))
        (b* ((width (- typesize selfsize))
             ((when (eq exprtype :vl-signed))
              (mv nil x
                  (warn :type :vl-assignpattern-elim-fail
                        :msg "~a0: sign-extension of assignment pattern ~
                              ctxents not yet implemented: ~a1"
                        :args (list (vl-context-fix ctx) x)))))
          (mv t (make-vl-nonatom
                 :op :vl-concat
                 ;; zero extend
                 :args (list (make-vl-atom :guts (make-vl-constint :origwidth width
                                                                   :origtype :vl-unsigned
                                                                   :value 0))
                             x))
              warnings)))
       ((when (< typesize selfsize))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: truncation of assignment pattern ctxents not ~
                        yet implemented: ~a1"
                  :args (list (vl-context-fix ctx) x)))))
    (mv t x warnings))
  ///
  (defthm vl-expr-size-of-vl-expr-assignpattern-extend/truncate-when-in-pattern
    (b* (((mv ok1 x1 &) (vl-expr-assignpattern-extend/truncate
                         lhs-type x t ss ctx warningsa))
         ((mv warning size) (vl-datatype-size lhs-type))
         ((mv ok2 & x2) (vl-expr-size size1 x1 ss ctxb warningsb)))
      (and (implies warning (not ok1))
           (implies (and ok1 ok2)
                    (equal (vl-expr->finalwidth x2)
                           (if size1
                               (max (nfix size1) size)
                             size)))))
    :hints (("goal" :expand ((:free (ctx warningsb size) (vl-expr-size size x ss ctx warningsb))
                             (:free (op args ctx warnings)
                              (vl-expr-selfsize
                               (make-vl-nonatom :op op
                                                :args args)
                               ss ctx warnings))
                             (:free (guts ctx warnings)
                              (vl-expr-selfsize
                               (make-vl-atom :guts guts)
                               ss ctx warnings)))
             :in-theory (enable vl-op-selfsize
                                vl-atom-selfsize
                                vl-exprlist-selfsize
                                ;; vl-expr-selfsize
                                warning-irrelevance-of-vl-expr-selfsize
                                warning-irrelevance-of-vl-exprlist-selfsize)))
    )

  (defthm vl-expr-size-of-vl-expr-assignpattern-extend/truncate-when-in-pattern-selfsize
    (b* (((mv ok1 x1 &) (vl-expr-assignpattern-extend/truncate
                         lhs-type x in-pattern ss ctx warningsa))
         ((mv warning size) (vl-datatype-size lhs-type))
         ((mv & selfsize) (vl-expr-selfsize x1 ss ctxb warningsb)))
      (implies in-pattern
               (and (implies warning (not ok1))
                    (implies ok1
                             (equal selfsize
                                    size)))))
    :hints (("goal" :expand ((:free (size ctx warnings) (vl-expr-size size x ss ctx warningsb))
                             (:free (op args ctx warnings)
                              (vl-expr-selfsize
                               (make-vl-nonatom :op op
                                                :args args)
                               ss ctx warnings))
                             (:free (guts ctx warnings)
                              (vl-expr-selfsize
                               (make-vl-atom :guts guts)
                               ss ctx warnings)))
             :in-theory (enable vl-op-selfsize
                                vl-atom-selfsize
                                vl-exprlist-selfsize
                                warning-irrelevance-of-vl-expr-selfsize
                                warning-irrelevance-of-vl-exprlist-selfsize)))
    ))




(defines vl-expr-replace-assignpatterns
  (define vl-expr-replace-assignpatterns
    ((lhs-type vl-datatype-p                  "The type that we want x to assume.")
     (x vl-expr-p                             "The expression to size/type.")
     (in-pattern                              "True if we're inside an assignment pattern")
     (ss vl-scopestack-p                      "Identifier bindings.")
     (ctx     vl-context-p                "Context for sizing error messages.")
     (warnings vl-warninglist-p               "Ordinary @(see warnings) accumulator."))
    :parents (expression-sizing)
    :short "Rewrite an expression to replace assignment patterns with concatenations."
    :long "<p>Important caveat:  This is only correct for packed datatypes.</p>"
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (new-x vl-expr-p)
                 (new-warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-expr-count x) 0)
    :verify-guards nil
    (b* ((warnings (vl-warninglist-fix warnings))
         (ctx (vl-context-fix ctx))
         (x (vl-expr-fix x))
         ((when (vl-atom-p x))
          (vl-expr-assignpattern-extend/truncate lhs-type x in-pattern ss ctx warnings))
         ((vl-nonatom x))
         ((when (eq x.op :vl-qmark))
          (b* (((mv true-ok true warnings)
                (vl-expr-replace-assignpatterns lhs-type (second x.args) in-pattern ss ctx warnings))
               ((mv false-ok false warnings)
                (vl-expr-replace-assignpatterns lhs-type (third x.args) in-pattern ss ctx warnings))
               ((unless (and true-ok false-ok)) (mv nil x warnings)))
            (mv t (change-vl-nonatom x :args (list (first x.args) true false)) warnings)))
         ((when (member x.op '(:vl-pattern-positional
                               :vl-pattern-multi
                               :vl-pattern-keyvalue)))
          (b* (((mv ok type-expr-pairs warnings)
                (vl-assignpattern-replacement lhs-type x ctx warnings))
               ((unless ok) (mv nil x warnings))
               ((mv ok args warnings)
                (vl-exprlist-replace-assignpatterns type-expr-pairs ss ctx warnings))
               ((unless ok) (mv nil x warnings)))
            (mv t
                ;; bozo -- Do we ever need to worry about the sign?
                (make-vl-nonatom :op :vl-concat
                                 :args args)
                warnings)))
         ((when (eq x.op :vl-pattern-type))
          (b* (((mv warning pattype) (vl-castexpr->datatype (first x.args) ss))
               ((when warning) (mv nil x (cons warning warnings)))
               ((unless (vl-datatype->packedp pattype))
                (mv nil x
                    (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Assignment pattern given unpacked type ~
                                in packed context: ~a1"
                          :args (list ctx x))))
               ((mv ok new-x warnings)
                (vl-expr-replace-assignpatterns pattype (second x.args) t ss ctx warnings))
               ((unless ok) (mv nil x warnings)))
            (vl-expr-assignpattern-extend/truncate lhs-type new-x in-pattern ss ctx warnings))))
      (vl-expr-assignpattern-extend/truncate lhs-type x in-pattern ss ctx warnings)))

  (define vl-exprlist-replace-assignpatterns
    ((x  vl-type-expr-pairs-p)
     (ss vl-scopestack-p)
     (ctx vl-context-p)
     (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-exprlist-max-count (alist-vals (vl-type-expr-pairs-fix x)))
                               (len (vl-type-expr-pairs-fix x)))
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count alist-vals
                                      vl-type-expr-pairs-fix)))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (new-x vl-exprlist-p)
                 (new-warnings vl-warninglist-p))
    (b* ((x (vl-type-expr-pairs-fix x))
         ((when (atom x)) (mv t nil (vl-warninglist-fix warnings)))
         ((mv ok1 first warnings) (vl-expr-replace-assignpatterns
                                   (caar x) (cdar x) t ss ctx warnings))
         ((mv ok2 rest warnings) (vl-exprlist-replace-assignpatterns
                                  (cdr x) ss ctx warnings)))
      (mv (and ok1 ok2) (cons first rest) warnings)))
  ///
  (verify-guards vl-expr-replace-assignpatterns)

  (defthm-vl-expr-replace-assignpatterns-flag
    (defthm vl-expr-size-of-vl-expr-replace-assignpatterns-in-pattern
      (b* (((mv ok1 x1 &) (vl-expr-replace-assignpatterns
                           lhs-type x in-pattern ss ctx warnings))
           ((mv warning size) (vl-datatype-size lhs-type))
           ((mv & selfsize) (vl-expr-selfsize x1 ss ctxb warningsb)))
        ;; (and (implies warning
        ;;               (not ok1))
        (implies (and ok1 selfsize (not warning) in-pattern)
                 (equal selfsize
                        size)))
      :hints ('(:expand ((vl-expr-replace-assignpatterns
                          lhs-type x in-pattern ss ctx warnings))
                :in-theory (e/d (warning-irrelevance-of-vl-expr-selfsize)
                                (vl-expr-replace-assignpatterns
                                 vl-exprlist-replace-assignpatterns))
                :do-not-induct t))
      :flag vl-expr-replace-assignpatterns)
    (defthm vl-type-expr-pairs-sum-datatype-sizes-of-vl-exprlist-replace-assignpatterns
      (b* (((mv ok1 x1 &) (vl-exprlist-replace-assignpatterns
                           x ss ctx warnings))
           ((mv warning size) (vl-type-expr-pairs-sum-datatype-sizes x))
           ((mv & sizes) (vl-exprlist-selfsize x1 ss ctxb warningsb)))
        (implies (and ok1 (not warning)
                      (not (member nil sizes)))
                 (equal (sum-nats sizes)
                        size)))
      :hints ('(:expand ((vl-type-expr-pairs-sum-datatype-sizes x)
                         (vl-exprlist-replace-assignpatterns x ss ctx warnings)
                         (:free (ctx warnings)
                          (vl-exprlist-size nil ss ctx warnings)))
                :in-theory (e/d (vl-exprlist-selfsize
                                 vl-exprlist->finalwidths
                                 warning-irrelevance-of-vl-exprlist-selfsize)
                                (vl-exprlist-replace-assignpatterns
                                 vl-expr-replace-assignpatterns))))
      :flag vl-exprlist-replace-assignpatterns))

  (deffixequiv-mutual vl-expr-replace-assignpatterns
    :hints ('(:expand ((:free (lhs-type in-pattern ss ctx warnings)
                        (vl-expr-replace-assignpatterns
                         lhs-type x in-pattern ss ctx warnings))
                       (:free (lhs-type in-pattern ss ctx warnings)
                        (vl-expr-replace-assignpatterns
                         lhs-type (vl-expr-fix x) in-pattern ss ctx warnings))
                       (:free (ss ctx warnings)
                        (vl-exprlist-replace-assignpatterns x ss ctx warnings))
                       (:free (ss ctx warnings)
                        (vl-exprlist-replace-assignpatterns
                         (vl-type-expr-pairs-fix x) ss ctx warnings)))
              :in-theory (disable vl-expr-replace-assignpatterns
                                  vl-exprlist-replace-assignpatterns)))))


(define vl-index-expr-size-assigncontext ((lhs-type vl-datatype-p)
                                          (x vl-expr-p)
                                          (ss vl-scopestack-p)
                                          (ctx vl-context-p)
                                          (warnings vl-warninglist-p))
  :parents (vl-expr-size-assigncontext)
  :short "Check and size an index expression in an unpacked type context."
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (new-x vl-expr-p)
               (new-warnings vl-warninglist-p))
  ;; We only need to deal with atoms that could represent an unpacked value.
  (b* ((x (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       ((mv warning type) (vl-index-find-type x ss ctx))
       ((when warning) (mv nil x (cons warning (ok))))
       ((unless (equal type (vl-datatype-fix lhs-type)))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: RHS expression ~a1 is not of type ~a2 (rather, ~a3)"
                  :args (list ctx x (vl-datatype-fix lhs-type) type)))))
    (mv t x (ok)))
  ///
  (local (Defthm vl-index-find-type-implies
           (implies (not (mv-nth 0 (vl-index-find-type x ss ctx)))
                    (if (equal (vl-expr-kind x) :atom)
                        (or (and (vl-id-p (vl-atom->guts x))
                                 (equal (tag (vl-atom->guts x)) :vl-id))
                            (and (vl-hidpiece-p (vl-atom->guts x))
                                 (equal (tag (vl-atom->guts x)) :vl-hidpiece)))
                      (or (equal (vl-nonatom->op x) :vl-hid-dot)
                          (equal (vl-nonatom->op x) :vl-index)
                          (equal (vl-nonatom->op x) :vl-bitselect))))
           :hints(("Goal" :in-theory (enable vl-index-find-type vl-hidexpr-p
                                             vl-hidname-p
                                             tag-when-vl-id-p
                                             tag-when-vl-hidpiece-p)))
           :rule-classes :forward-chaining))

  (defthm vl-expr-selfsize-of-vl-index-expr-size-assigncontext
    (b* (((mv ok new-x &) (vl-index-expr-size-assigncontext
                                  lhs-type x ss ctx warnings))
         ((mv warning typesize) (vl-datatype-size lhs-type))
         ((mv & selfsize) (vl-expr-selfsize new-x ss ctx2 warnings2)))
      (implies (and ok (not warning))
               (equal selfsize typesize)))
    :hints(("Goal" :expand ((:free (ctx warnings) (vl-expr-selfsize x ss ctx warnings))
                            (:free (ctx warnings) (vl-atom-selfsize x ss ctx warnings)))
            :in-theory (enable tag-when-vl-id-p
                               tag-when-vl-hidpiece-p
                               tag-when-vl-weirdint-p
                               tag-when-vl-constint-p
                               tag-when-vl-string-p
                               vl-index-selfsize)))))

(define vl-arrayslice-expr-size-assigncontext ((lhs-type vl-datatype-p)
                                               (x vl-expr-p)
                                               (ss vl-scopestack-p)
                                               (ctx vl-context-p)
                                               (warnings vl-warninglist-p))
  :parents (vl-expr-size-assigncontext)
  :short "Check and size a range-select expression in an unpacked type context."
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (new-x vl-expr-p)
               (new-warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (member (vl-nonatom->op x)
                      '(:vl-select-colon
                        :vl-select-pluscolon
                        :vl-select-minuscolon
                        :vl-partselect-colon
                        :vl-partselect-pluscolon
                        :vl-partselect-minuscolon)))
  ;; We only need to deal with atoms that could represent an unpacked value.
  (b* ((x (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       ((mv warning type) (vl-partselect-expr-type x ss ctx))
       ((when warning) (mv nil x (cons warning (ok))))
       (x-udims (vl-datatype->udims type))
       ((unless (consp x-udims))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg (if (consp (vl-datatype->pdims type))
                           "~a0: Can't assign packed array select ~a1 in an ~
                            unpacked type context"
                         "~a0: Can't apply select operator to non-array: ~a1")
                  :args (list ctx x))))
       (lhs-udims (vl-datatype->udims lhs-type))
       ((unless (consp lhs-udims))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Can't assign array select ~a1 in a ~
                        non-unpacked-array type context"
                  :args (list ctx x))))
       ((unless (equal (vl-datatype-update-udims (cdr x-udims) type)
                       (vl-datatype-update-udims (cdr lhs-udims)
                                                 lhs-type)))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Incompatible types for unpacked array slice ~
                        assignment (~a1): lhs type ~a2, rhs type ~a3"
                  :args (list ctx x (vl-datatype-fix lhs-type) type))))
       ((unless (and (not (eq (car lhs-udims) :vl-unsized-dimension))
                     (vl-range-resolved-p (car lhs-udims))
                     (not (eq (car x-udims) :vl-unsized-dimension))
                     (vl-range-resolved-p (car x-udims))))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Can't assign array slice ~a1 because datatype ~
                        dimensions are unresolved: lhs ~a2, rhs ~a3"
                  :args (list ctx x (vl-datatype-fix lhs-type) type))))
       ((unless (equal (vl-range-size (car lhs-udims))
                       (vl-range-size (car x-udims))))
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Can't assign array slice ~a1 because datatype ~
                        dimensions differ: lhs ~a2, rhs ~a3"
                  :args (list ctx x (vl-datatype-fix lhs-type) type)))))
    (mv t x (ok)))

  ///

  (local (Defthm vl-partselect-expr-type-implies
           (implies (not (mv-nth 0 (vl-partselect-expr-type x ss ctx)))
                    ;; (and (not (equal (vl-expr-kind x) :atom))
                         (or (equal (vl-nonatom->op x) :vl-partselect-colon)
                             (equal (vl-nonatom->op x) :vl-partselect-pluscolon)
                             (equal (vl-nonatom->op x) :vl-partselect-minuscolon)
                             (equal (vl-nonatom->op x) :vl-select-colon)
                             (equal (vl-nonatom->op x) :vl-select-pluscolon)
                             (equal (vl-nonatom->op x) :vl-select-minuscolon)))
           :hints(("Goal" :in-theory (enable vl-partselect-expr-type
                                             tag-when-vl-id-p
                                             tag-when-vl-hidpiece-p)))
           :rule-classes :forward-chaining))

  (local
   (defthmd vl-datatype-size-when-update-dims-equal
     (b* ((udims1 (vl-datatype->udims x1))
          (udims2 (vl-datatype->udims x2))
          ((mv warn1 size1) (vl-datatype-size x1))
          ((mv warn2 size2) (vl-datatype-size x2)))
       (implies (and (equal (vl-datatype-update-dims (vl-datatype->pdims x1)
                                                     (cdr udims1) x1)
                            (vl-datatype-update-dims (vl-datatype->pdims x2)
                                                     (cdr udims2) x2))
                     (consp udims1)
                     (consp udims2)
                     (not (equal (car udims1) :vl-unsized-dimension))
                     (vl-range-resolved-p (car udims1))
                     (not (equal (car udims2) :vl-unsized-dimension))
                     (vl-range-resolved-p (car udims2))
                     (equal (vl-range-size (car udims1))
                            (vl-range-size (car udims2))))
                (and (equal (iff warn1 warn2) t)
                     (equal (equal size1 size2) t))))
     :hints(("Goal" :in-theory (enable vl-datatype-update-dims
                                       vl-datatype-size
                                       vl-datatype->udims
                                       vl-datatype->pdims
                                       vl-packeddimensionlist-total-size)))))

  (defthm vl-expr-selfsize-of-vl-arrayslice-expr-size-assigncontext
    (b* (((mv ok new-x &) (vl-arrayslice-expr-size-assigncontext
                           lhs-type x ss ctx warnings))
         ((mv warning typesize) (vl-datatype-size lhs-type))
         ((mv & selfsize) (vl-expr-selfsize new-x ss ctx2 warnings2)))
      (implies (and ok (not warning)
                    (not (vl-atom-p x)))
               (equal selfsize typesize)))
    :hints(("Goal" :expand ((:free (ctx warnings) (vl-expr-selfsize x ss ctx warnings)))
            :use ((:instance vl-datatype-size-when-update-dims-equal
                   (x1 lhs-type)
                   (x2 (mv-nth 1 (vl-partselect-expr-type x ss nil)))))
            :in-theory (e/d (tag-when-vl-id-p
                               tag-when-vl-hidpiece-p
                               tag-when-vl-weirdint-p
                               tag-when-vl-constint-p
                               tag-when-vl-string-p
                               vl-partselect-selfsize)
                            (;vl-$bits-call-p
                             ))))))


(define vl-atom-size-assigncontext ((lhs-type vl-datatype-p)
                                    (x vl-expr-p)
                                    (ss vl-scopestack-p)
                                    (ctx vl-context-p)
                                    (warnings vl-warninglist-p))
  :parents (vl-expr-size-assigncontext)
  :short "Check and size an atom in an unpacked type context."
  :guard (vl-atom-p x)
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (new-x vl-expr-p)
               (new-warnings vl-warninglist-p))
  ;; We only need to deal with atoms that could represent an unpacked value.
  (b* ((x (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       ((vl-atom x))
       ((unless (member (tag x.guts) '(:vl-id :vl-hidpiece)))
        ;; any others?
        (mv nil x
            (warn :type :vl-assignpattern-elim-fail
                  :msg "~a0: Bad expression for unpacked type context: ~a1"
                  :args (list ctx x)))))
    (vl-index-expr-size-assigncontext lhs-type x ss ctx warnings))

  ///
  (defthm vl-expr-selfsize-of-vl-atom-expr-size-assigncontext
    (b* (((mv ok new-x &) (vl-atom-size-assigncontext
                           lhs-type x ss ctx warnings))
         ((mv warning typesize) (vl-datatype-size lhs-type))
         ((mv & selfsize) (vl-expr-selfsize new-x ss ctx2 warnings2)))
      (implies (and ok (not warning))
               (equal selfsize typesize)))))



(defines vl-expr-size-assigncontext
  (define vl-expr-size-assigncontext
    ((lhs-type vl-datatype-p                         "The type that we want x to assume.")
     (x vl-expr-p                                    "The expression to size/type.")
     (in-pattern                                     "are we inside an assignment pattern?")
     (ss vl-scopestack-p                             "Identifier bindings.")
     (ctx     vl-context-p                       "Context for sizing error messages.")
     (warnings vl-warninglist-p                      "Ordinary @(see warnings) accumulator."))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (new-x vl-expr-p)
                 (new-warnings vl-warninglist-p))
    :parents (expression-sizing)
    :short "Size and resolve assignment patterns in an expression, given the type of its LHS."
    :long "<p>If successful, returns a sized (welltyped) expression.  If the
LHS type is an unpacked datatype, then the size of the expression is the
datatype size and the type is unsigned.</p>"
    :measure (two-nats-measure (vl-expr-count x) 0)
    :hints(("Goal" :in-theory (enable vl-exprlist-max-count
                                      alist-vals vl-type-expr-pairs-fix)))
    :verify-guards nil
    (b* ((warnings (vl-warninglist-fix warnings))
         (ctx (vl-context-fix ctx))
         (x (vl-expr-fix x))
         ((when (vl-datatype->packedp lhs-type))
          (vl-expr-replace-assignpatterns lhs-type x in-pattern ss ctx warnings)
          ;; (b* (((mv ok new-x warnings)
          ;;       (vl-expr-replace-assignpatterns lhs-type x in-pattern ss ctx warnings))
          ;;      ((unless ok) (mv nil x warnings))
          ;;      ((mv warning size) (vl-packed-datatype-size lhs-type))
          ;;      ((when warning)
          ;;       (mv nil x (cons warning warnings)))
          ;;      ((mv ok warnings new-x)
          ;;       (vl-expr-size size new-x ss ctx warnings)))
          ;;   (mv ok new-x warnings))
          )
         ((when (vl-atom-p x))
          ;; We have an unpacked datatype.  This function must check that the
          ;; type of x is compatible.
          (vl-atom-size-assigncontext lhs-type x ss ctx warnings))
         ((vl-nonatom x))
         ((when (member x.op '(:vl-hid-dot :vl-index)))
          ;; Must have an unpacked datatype.  This function must check that the
          ;; type of x is compatible.
          (vl-index-expr-size-assigncontext lhs-type x ss ctx warnings))
         ((when (member x.op '(:vl-select-colon
                          :vl-select-pluscolon
                          :vl-select-minuscolon
                          :vl-partselect-colon
                          :vl-partselect-pluscolon
                          :vl-partselect-minuscolon)))
          (vl-arrayslice-expr-size-assigncontext lhs-type x ss ctx warnings))
         ((when (eq x.op :vl-qmark))
          ;; Since we have an unpacked datatype, each branch of the conditional
          ;; should end up as the same size (= the size of the datatype).
          (b* (((list cond truebr falsebr) x.args)
               ((mv cond-ok warnings cond1) (vl-expr-size nil cond ss ctx warnings))
               ((mv true-ok true1 warnings) (vl-expr-size-assigncontext
                                             lhs-type truebr in-pattern ss ctx warnings))
               ((mv false-ok false1 warnings) (vl-expr-size-assigncontext
                                               lhs-type falsebr in-pattern ss ctx warnings))
               ((unless (and cond-ok true-ok false-ok))
                (mv nil x warnings)))
            (mv t (make-vl-nonatom :op :vl-qmark
                                   :args (list cond1 true1 false1))
                warnings)))
         ((when (member x.op '(:vl-pattern-positional
                               :vl-pattern-multi
                               :vl-pattern-keyvalue)))
          (b* (((mv ok type-expr-pairs warnings)
                (vl-assignpattern-replacement lhs-type x ctx warnings))
               ((unless ok) (mv nil x warnings))
               ((mv ok args warnings)
                (vl-exprlist-size-assigncontext type-expr-pairs ss ctx warnings))
               ((unless ok) (mv nil x warnings)))
            (mv t (make-vl-nonatom :op :vl-concat
                                   :args args)
                warnings)))

         ((when (eq x.op :vl-pattern-type))
          (b* (((mv warning pattype) (vl-castexpr->datatype (first x.args) ss))
               ((when warning) (mv nil x (cons warning warnings)))
               ((unless (equal pattype (vl-datatype-fix lhs-type)))
                ;; bozo -- is there a different compatibility test we should use?
                (mv nil x
                    (warn :type :vl-assignpattern-elim-fail
                          :msg "~a0: Assignment pattern type is incompatible ~
                                with LHS type: ~a1"
                          :args (list ctx x)))))
            (vl-expr-size-assigncontext pattype (second x.args) t ss ctx warnings)))

         ((when (eq x.op :vl-concat))
          (mv nil (vl-expr-fix x)
              (warn :type :vl-assignpattern-elim-fail
                    :msg "~a0: Unpacked array concatenations are not yet ~
                          implemented (~a1)"
                    :args (list ctx x)))))

      (mv nil (vl-expr-fix x)
              (warn :type :vl-assignpattern-elim-fail
                    :msg "~a0: Bad expression for unpacked LHS type: ~a1"
                    :args (list ctx x)))))

  (define vl-exprlist-size-assigncontext ((x vl-type-expr-pairs-p)
                                          (ss vl-scopestack-p)
                                          (ctx vl-context-p)
                                          (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (new-x vl-exprlist-p)
                 (new-warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-exprlist-max-count (alist-vals (vl-type-expr-pairs-fix x)))
                               (len (vl-type-expr-pairs-fix x)))
    (b* ((x (vl-type-expr-pairs-fix x))
         ((when (atom x)) (mv t nil (vl-warninglist-fix warnings)))
         ((mv ok x1 warnings) (vl-expr-size-assigncontext
                               (caar x) (cdar x) t ss ctx warnings))
         ((unless ok) (mv nil nil warnings))
         ((mv ok x2 warnings) (vl-exprlist-size-assigncontext (cdr x) ss ctx warnings))
         ((unless ok) (mv nil nil warnings)))
      (mv t (cons x1 x2) warnings)))
  ///

  (local
   (defthm finalwidth-when-selfsize/exprsize-same
     (b* (((mv ok & new-x) (vl-expr-size lhs-size x ss ctx warnings))
          ((mv & selfsize) (vl-expr-selfsize x ss ctx warnings)))
       (implies (and ok (equal lhs-size selfsize))
                (equal (vl-expr->finalwidth new-x)
                       selfsize)))
     :hints(("Goal" :expand ((:free (lhs-size warnings)
                              (vl-expr-size lhs-size x ss ctx warnings)))))))

  (defthm-vl-expr-size-assigncontext-flag
    (defthm vl-expr-size-of-vl-expr-size-assigncontext
      (b* (((mv ok1 x1 &) (vl-expr-size-assigncontext
                           lhs-type x in-pattern ss ctx warnings))
           ((mv warning size) (vl-datatype-size lhs-type))
           ((mv & selfsize)   (vl-expr-selfsize x1 ss ctx1 warnings1)))
        ;; (and (implies warning
        ;;               (not ok1))
        (implies (and ok1 (not warning) selfsize in-pattern)
                 (equal selfsize
                        size)))
      :hints ('(:expand ((vl-expr-size-assigncontext
                          lhs-type x in-pattern ss ctx warnings))
                :in-theory (e/d (warning-irrelevance-of-vl-expr-selfsize
                                 warning-irrelevance-of-vl-exprlist-selfsize)
                                (vl-expr-size-assigncontext
                                 vl-exprlist-size-assigncontext))))
      :flag vl-expr-size-assigncontext)
    (defthm vl-type-expr-pairs-sum-datatype-sizes-of-vl-exprlist-size-assigncontext
      (b* (((mv ok1 x1 &) (vl-exprlist-size-assigncontext
                           x ss ctx warnings))
           ((mv warning size) (vl-type-expr-pairs-sum-datatype-sizes x))
           ((mv & sizes) (vl-exprlist-selfsize x1 ss ctx1 warnings1)))
        (implies (and ok1 (not (member nil sizes)) (not warning))
                 (equal (sum-nats sizes)
                        size)))
      :hints ('(:expand ((vl-type-expr-pairs-sum-datatype-sizes x)
                         (vl-exprlist-size-assigncontext x ss ctx warnings)
                         (vl-exprlist-size nil ss ctx warningsb))
                :in-theory (e/d (vl-exprlist-selfsize
                                 vl-exprlist->finalwidths
                                 warning-irrelevance-of-vl-expr-selfsize
                                 warning-irrelevance-of-vl-exprlist-selfsize)
                                (vl-exprlist-size-assigncontext
                                 vl-expr-size-assigncontext))))
      :flag vl-exprlist-size-assigncontext))

  (verify-guards vl-exprlist-size-assigncontext)

  (deffixequiv-mutual vl-expr-size-assigncontext
    :hints ('(:expand ((:free (lhs-type in-pattern ss ctx warnings)
                        (vl-expr-size-assigncontext
                         lhs-type x in-pattern ss ctx warnings))
                       (:free (lhs-type in-pattern ss ctx warnings)
                        (vl-expr-size-assigncontext
                         lhs-type (vl-expr-fix x) in-pattern ss ctx warnings))
                       (:free (ss ctx warnings)
                        (vl-exprlist-size-assigncontext x ss ctx warnings))
                       (:free (ss ctx warnings)
                        (vl-exprlist-size-assigncontext
                         (vl-type-expr-pairs-fix x) ss ctx warnings)))
              :in-theory (disable vl-expr-size-assigncontext
                                  vl-exprlist-size-assigncontext)))))



(define vl-lvalue-type ((x vl-expr-p) (ss vl-scopestack-p) (ctx acl2::any-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (implies (and (not warning) type)
                              (vl-datatype-p type))))
  (b* (((when (vl-atom-p x))
        ;; has to be an identifier
        (vl-index-find-type x ss ctx))
       ((vl-nonatom x))
       ((when (member x.op '(:vl-hid-dot :vl-index :bitselect)))
        (vl-index-find-type x ss ctx)))
       ;; We think the above are the only lvalue ops that can be targets of
       ;; assignment patterns.  The remaining lvalue ops are partselects and
       ;; concats, which don't have indices of their own so we won't support
       ;; them.
    (mv nil nil)))

(define vl-assigncontext-size ((lhs vl-expr-p)
                               (rhs vl-expr-p)
                               (ss vl-scopestack-p)
                               (ctx vl-context-p)
                               (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (new-lhs vl-expr-p)
               (new-rhs vl-expr-p)
               (new-warnings vl-warninglist-p))
  (b* ((ctx (vl-context-fix ctx))
       (lhs (vl-expr-fix lhs))
       (rhs (vl-expr-fix rhs))
       ((mv lhs-successp warnings lhs-prime)
        (vl-expr-size nil lhs ss ctx warnings))
       ((unless lhs-successp)
        (mv nil lhs rhs warnings))

       (lhs-size (vl-expr->finalwidth lhs-prime))
       ((unless (posp lhs-size))
        (mv nil
            lhs-prime rhs
            (fatal :type :vl-bad-assignment
                   :msg "~a0: The size of the left-hand side ~a1 was not ~
                          a positive number?"
                   :args (list ctx lhs))))

       ((mv warning lhs-type) (vl-lvalue-type lhs-prime ss ctx))
       ((when warning) (mv nil lhs-prime rhs (cons warning (ok))))

       ((mv ok new-rhs warnings)
        (if lhs-type
            (vl-expr-size-assigncontext lhs-type rhs nil ss ctx warnings)
          (mv t rhs warnings)))

       ((unless ok) (mv nil lhs-prime rhs warnings))

       ((mv rhs-successp warnings rhs-prime)
        (vl-expr-size lhs-size new-rhs ss ctx warnings))

       ((unless rhs-successp) (mv nil lhs-prime rhs warnings)))
    (mv t lhs-prime rhs-prime warnings))
  ///
  (defthm vl-expr->finalwidth-of-vl-assigncontext-size-lhs
    (b* (((mv ok new-lhs & &) (vl-assigncontext-size lhs rhs ss ctx warnings)))
      (implies ok
               (posp (vl-expr->finalwidth new-lhs))))
    :rule-classes :type-prescription))
