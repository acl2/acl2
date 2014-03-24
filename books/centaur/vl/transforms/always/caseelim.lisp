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
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/context")
(include-book "../../mlib/welltyped")
(include-book "../../mlib/constint-bits")
(include-book "../../mlib/expr-slice")
(local (include-book "../../util/arithmetic"))
(local (in-theory (disable all-equalp)))

(local (defthm vl-compoundstmt->casetype-forward
         (implies (force (vl-compoundstmt-p x))
                  (or (not (vl-compoundstmt->casetype x))
                      (equal (vl-compoundstmt->casetype x) :vl-casex)
                      (equal (vl-compoundstmt->casetype x) :vl-casez)))
         :rule-classes
         ((:forward-chaining :trigger-terms ((vl-compoundstmt->casetype x))))
         :hints(("Goal"
                 :in-theory (disable return-type-of-vl-compoundstmt->casetype)
                 :use ((:instance return-type-of-vl-compoundstmt->casetype))))))

(local (defthm vl-casestmt->casetype-forward
         (implies (force (vl-casestmt-p x))
                  (or (not (vl-casestmt->casetype x))
                      (equal (vl-casestmt->casetype x) :vl-casex)
                      (equal (vl-casestmt->casetype x) :vl-casez)))
         :rule-classes
         ((:forward-chaining :trigger-terms ((vl-casestmt->casetype x))))
         :hints(("Goal" :in-theory (enable vl-casestmt->casetype)))))



(defxdoc caseelim
  :parents (transforms)
  :short "Replace simple @(see case-statements) with equivalent @(see
if-statements)."

  :long "<p>This rewrite eliminates @(see case-statements) into @(see
if-statements).  It requires that sizes have been computed that the test
expressions and match expressions agree on their sizes.  If these conditions
are not met, it may issue non-fatal warnings and fail to rewrite the case
statements.</p>

<p>This transform is practically useful for supporting designs that involve
case statements, and we believe it is basically reasonable.  But Verilog's case
statements have <b>significant problems</b> with regards to the handling of X
and Z values.  There are, therefore, many cases where this translation will
change a module's simulation semantics.  More information about these problems
can be found in @(see case-statement-problems).</p>

<p>At any rate, the basic idea of the transform is to just rewrite, e.g., for
plain @('case') statements:</p>

@({
    case (<test>)
     <match-1>: <body-1>
     <match-2>: <body-2>
     ...
     <match-n>: <body-N>
     default:   <default-body>
    endcase

       -->

    if (<test> === <match-1>)      <body-1>
    else if (<test> === <match-2>) <body-2>
    ...
    else if (<test> === <body-n>)  <body-n>
    else                           <default-body>
})

<p>This rewrite is intuitively correct, and appears to produce identical
results in some test simulations on NCVerilog and Verilog-XL.</p>

<p>This transform isn't quite correct if @('test') can cause side-effects.  The
Verilog standard says that @('test') should be evaluated only once, before the
@('match') expressions.  In our transformed code, @('test') may be evaluated
multiple times.  This is not a problem for back-end tools like @(see esim)
where there is no such notion of evaluation.</p>

<p>We considered doing something more sophisticated to avoid replicating the
@('test') expression, which would avoid this problem.  It would be easy enough
to simply assign the test expression to some temporary wire, then check
@('temp') against each match expression.  But we might then need to also
include this new wire in the sensitivity list for the always block, which could
become tricky/messy.  So for now, our transform really is just as naive as the
above suggests.</p>

<p>Our support for @('casex') and @('casez') statements is somewhat more
limited.  Here, we require that the @('test') expression is a sliceable
expression, and that each @('match') expression be some simple, atomic @(see
vl-constint-p) or @(see vl-weirdint-p) expression.  These constraints allow us
to carry out an especially naive transformation, e.g.,:</p>

@({
    casez (in)
      4'b001?: <body-1>
      4'b01??: <body-2>
      4'b1???: <body-3>
      default: <default-body>
    endcase
       -->
    if (in[3] === 1'b0 & in[2] === 1'b0 & in[1] === 1'b1)  <body-1>
    else if (in[3] === 1'b0 & in[2] === 1'b1)              <body-2>
    else if (in[3] === 1'b1)                               <body-3>
    else                                                   <default-body>
})

<p>That is, our @('if') statement conditions simply omit the x/z/? bits as
appropriate, and check that the other bits are matched.  This transformation is
<b>completely wrong</b> in the case where @('data') has X or Z bits, because in
the Verilog semantics these bits are not to be tested.  On the other hand,
these are terrible, non-conservative semantics, and we think our behavior is
about as reasonable as possible.</p>")

(defxdoc case-statement-problems
  :parents (case-statements caseelim)
  :short "The official behavior of @('case'), @('casez') and @('casex') is
problematic with respect to X and Z values."

  :long "<p>Generally speaking, Verilog's behavioral modeling constructs are
rife with problems when it comes to the handling of unknown and high-impedence
values.  Even the basic @('if') statement treats X values as false, which is
deeply troubling&mdash;if we don't know what some value is, we certainly should
not simply assume it is false.</p>

<p>Verilog's @('case'), @('casex'), and @('casez') statements have especially
bad behavior with regards to X and Z values.</p>

<p>For basic @('case') statements, each match is compared against the test
expression using case-equality @('===') instead of ordinary equality @('==').
This allows you to match precisely against X and Z, which can easily lead to an
improper, non-conservative treatment of X.</p>

<p>The fancier @('casez') and @('casex') statements are especially badly
behaved.  At first glance these statements seem pretty convenient.  For
instance, in @('casez') you are told that you can use @('Z') or (equivalently)
@('?') as a pattern-matching character.  You might look at a code fragment like
this:</p>

@({
   casez (inst)
     5'b00001: out = a + b;
     5'b0001?: out = a - b;
     5'b001??: out = a & b;
     5'b01???; out = a | b;
     default:  out = 16'hXXXX;
   endcase
})

<p>And think&mdash;<i>wow, that looks nice</i>.  You might expect that the
second pattern here, @('5'b0001?'), will match:</p>

<ul>
<li>00010</li>
<li>00011</li>
<li>0001X</li>
<li>0001Z</li>
</ul>

<p>And you're right.  Unfortunately, what you probably did not expect, is that
this pattern will <b>also</b> match many other values, like:</p>

<ul>
<li>Z0010</li>
<li>ZZ010</li>
<li>ZZ0Z0</li>
<li>ZZZZZ</li>
</ul>

<p>And so on.  This is because Z values are treated as wildcards not only in
your pattern, but also <i>in the data itself</i>, which is terrible and makes
no sense at all.</p>

<p>The @('casex') statement is even worse.  Here, any X or Z values in the data
will match anything you've written in your pattern.  So, for instance,</p>

@({
    casex (inst)
      5'b00001: out = GOOD;
      default:  out = BAD;
    endcase
})

<p>Will, quite unexpectedly, produce GOOD for instructions such as @('XXXXX'),
@('ZZZZZ'), and so on.</p>")

(local (xdoc::set-default-parents caseelim))


; -----------------------------------------------------------------------------
;
;                           Basic Size Checking
;
; -----------------------------------------------------------------------------

(define vl-casestmt-size-warnings-aux
  ((test     vl-expr-p       "The test expression, which should typically have
                              its width already computed.")
   (exprs    vl-exprlist-p   "The match expressions.")
   (ctx      vl-modelement-p "Context for @(see warnings)."))
  :returns
  (warnings vl-warninglist-p)
  (b* (((when (atom exprs))
        nil)
       (rest (vl-casestmt-size-warnings-aux test (cdr exprs) ctx))
       ((unless (equal (vl-expr->finalwidth test)
                       (vl-expr->finalwidth (car exprs))))
        (cons
         (make-vl-warning
          :type :vl-case-stmt-size
          :msg "In ~a0: case statement sizes are incompatible:~%     ~
                  - ~x1-bit test:  ~a3~%     ~
                  - ~x2-bit match: ~a4"
          :args (list ctx
                      (vl-expr->finalwidth test)
                      (vl-expr->finalwidth (car exprs))
                      test
                      (car exprs)))
         rest))
       ((unless (vl-expr->finaltype (car exprs)))
        (cons
         (make-vl-warning
          :type :vl-case-stmt-type
          :msg "In ~a0: failed to determine signedness of case-statement ~
                match expression: ~a1."
          :args (list ctx (car exprs)))
         rest)))
    rest)
  ///
  (defthm vl-casestmt-size-warnings-aux-basics
    (implies (not (vl-casestmt-size-warnings-aux test exprs ctx))
             (and (all-equalp (vl-expr->finalwidth test)
                              (vl-exprlist->finalwidths exprs))
                  (not (member nil (vl-exprlist->finaltypes exprs)))))))

(define vl-casestmt-size-warnings
  :short "Check case statements for compatible sizes, and issue warnings if we
find any incompatible sizes."

  ((test     vl-expr-p       "The test expression, which should typically have
                              its width already computed.")
   (exprs    vl-exprlist-p   "The match expressions.")
   (ctx      vl-modelement-p "Context for @(see warnings)."))
  :returns
  (warnings vl-warninglist-p)

  :long "<p>Regarding the sizing of case expressions, the Verilog-2005
standard (9.5) says:</p>

<box><p>Care is needed in specifying the expressions in the case statement.
The bit length of all the expressions shall be equal so that exact bitwise
matching can be performed. The length of all the case item expressions, as well
as the case expression in the parentheses, shall be made equal to the length of
the longest case expression and case item expression. If any of these
expressions is unsigned, then all of them shall be treated as unsigned. If all
of these expressions are signed.</p></box>

<p>This is just a wrapper for @(see vl-casestmt-size-warnings-aux), which does
most of the real work.  We have this wrapper mainly to avoid giving multiple
warnings if there is some problem with sizing the test expression.  (This would
typically cause one warning per match expression if we just called the aux
function without checking for it.)</p>

<p>BOZO we should eventually properly incorporate this into our @(see
expression-sizing) code.</p>"

  (b* (((unless (and (posp (vl-expr->finalwidth test))
                     (vl-expr->finaltype test)))
        ;; Avoid giving 100 warnings if we failed to size the test expr.
        (list
         (make-vl-warning
          :type :vl-case-stmt-size
          :msg "In ~a0: case statement is testing expression whose ~
                size/type was not successfully determined: ~a1."
          :args (list ctx test)))))
    (vl-casestmt-size-warnings-aux test exprs ctx))
  ///
  (defthm widths-after-vl-casestmt-size-warnings
    (implies (not (vl-casestmt-size-warnings test exprs ctx))
             (and (posp (vl-expr->finalwidth test))
                  (vl-expr->finaltype test)
                  (all-equalp (vl-expr->finalwidth test)
                              (vl-exprlist->finalwidths exprs))
                  (not (member nil (vl-exprlist->finaltypes exprs)))))))



; -----------------------------------------------------------------------------
;
;                 Ordinary "Case" Statement -> If Statement
;
; -----------------------------------------------------------------------------

(define vl-casestmt-compare-expr
  :short "Creates, e.g., the expression @('foo === 3'b110'), for handling
@('case(foo) ... 3'b110: ... endcase')."
  ((test vl-expr-p "The test expression, e.g., @('foo').")
   (expr vl-expr-p "One match expression, e.g., @('3'b110')."))
  :returns
  (compare-expr vl-expr-p :hyp :fguard)
  :long "<p>This is mostly dealing with sizing.  Recall from 5.5.1 that
comparisons always produce unsigned results.  Our guard is strong enough to
ensure that we'll always have equal-width expressions and that we know their
types.  We haven't assumed anything about their types agreeing.  To make sure
that we produce well-typed expressions, we'll coerce anything signed into an
unsigned equivalent, by just wrapping it in a one-bit concatenation.</p>"
  :guard (and (posp (vl-expr->finalwidth test))
              (vl-expr->finaltype test)
              (equal (vl-expr->finalwidth test)
                     (vl-expr->finalwidth expr))
              (vl-expr->finaltype expr))
  (b* ((width     (vl-expr->finalwidth test))
       (test-fix  (case (vl-expr->finaltype test)
                    (:vl-unsigned test)
                    (:vl-signed   (make-vl-nonatom :op         :vl-concat
                                                   :args       (list test)
                                                   :finalwidth width
                                                   :finaltype  :vl-unsigned))
                    (otherwise (progn$ (impossible) test))))
       (expr-fix (case (vl-expr->finaltype expr)
                   (:vl-unsigned expr)
                   (:vl-signed   (make-vl-nonatom :op         :vl-concat
                                                  :args       (list expr)
                                                  :finalwidth width
                                                  :finaltype  :vl-unsigned))
                   (otherwise (progn$ (impossible) expr)))))
    (make-vl-nonatom :op :vl-binary-ceq
                     :args (list test-fix expr-fix)
                     :finaltype :vl-unsigned
                     :finalwidth 1))
  :prepwork ((local
              (defthm l0
                (implies (vl-expr-p x)
                         (or (equal (vl-expr->finaltype x) :vl-unsigned)
                             (equal (vl-expr->finaltype x) :vl-signed)
                             (equal (vl-expr->finaltype x) nil)))
                :rule-classes ((:forward-chaining
                                :trigger-terms ((vl-expr->finaltype x))))
                :hints(("Goal"
                        :in-theory (disable vl-exprtype-p)
                        :use ((:instance vl-exprtype-p
                                         (x (vl-expr->finaltype x)))))))))
  ///
  (defthm vl-expr-welltyped-p-of-vl-casestmt-compare-expr
    (implies (and (vl-expr-p test)
                  (vl-expr-p expr)
                  (posp (vl-expr->finalwidth test))
                  (vl-expr->finaltype test)
                  (equal (vl-expr->finalwidth test)
                         (vl-expr->finalwidth expr))
                  (vl-expr->finaltype expr)
                  (vl-expr-welltyped-p test)
                  (vl-expr-welltyped-p expr))
             (vl-expr-welltyped-p (vl-casestmt-compare-expr test expr)))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p)))))

(define vl-casestmt-elim-aux
  ((test     vl-expr-p        "The test expression, already sized.")
   (exprs    vl-exprlist-p    "Compatibly sized match expressions, in order.")
   (bodies   vl-stmtlist-p    "The body for each match expression, in order.")
   (default  vl-stmt-p        "The body for the @('default') case."))
  :guard (and (same-lengthp exprs bodies)
              (posp (vl-expr->finalwidth test))
              (vl-expr->finaltype test)
              (all-equalp (vl-expr->finalwidth test)
                          (vl-exprlist->finalwidths exprs))
              (not (member nil (vl-exprlist->finaltypes exprs))))
  :returns (new-stmt vl-stmt-p :hyp :fguard)
  (if (atom exprs)
      default
    (make-vl-ifstmt
     :condition (vl-casestmt-compare-expr test (car exprs))
     :truebranch (car bodies)
     :falsebranch
     (vl-casestmt-elim-aux test (cdr exprs) (cdr bodies) default))))

(define vl-casestmt-elim
  :short "Rewrite an ordinary @('case') statement into @('if') statements."

  ((test     vl-expr-p        "The test expression, should be sized.")
   (exprs    vl-exprlist-p    "The match expressions in order, should be sized.")
   (bodies   vl-stmtlist-p    "The body for each match expression, in order.")
   (default  vl-stmt-p        "The body for the @('default') case.")
   (atts     vl-atts-p        "Any attributes on the whole case statement.")
   (ctx      vl-modelement-p  "Context for @(see warnings).")
   (warnings vl-warninglist-p "Ordinary warnings accumulator."))

  :guard (equal (len exprs) (len bodies))
  :returns (mv (warnings vl-warninglist-p)
               (new-stmt vl-stmt-p
                         :hyp (and (force (vl-expr-p test))
                                   (force (vl-exprlist-p exprs))
                                   (force (vl-stmtlist-p bodies))
                                   (force (equal (len exprs) (len bodies)))
                                   (force (vl-stmt-p default))
                                   (force (vl-atts-p atts)))))
  (b* ((warnings     (vl-warninglist-fix warnings))
       (new-warnings (vl-casestmt-size-warnings test exprs ctx))
       ((when new-warnings)
        ;; Some sizing problem, so just fail to rewrite the case statement.
        (mv (append new-warnings warnings)
            (make-vl-casestmt :casetype nil
                              :test     test
                              :exprs    exprs
                              :bodies   bodies
                              :default  default
                              :atts     atts))))
    ;; Else, all sizes are good enough, we can turn it into ifs.  BOZO we're
    ;; going to lose any attributes associated with the case statement.
    ;; Maybe that's okay?
    (mv warnings
        (vl-casestmt-elim-aux test exprs bodies default))))



; -----------------------------------------------------------------------------
;
;               "Casez" and "Casex" Statements -> If Statement
;
; -----------------------------------------------------------------------------

(define vl-casezx-match-bits
  :short "Try to explode a match-expression into a @(see vl-bitlist-p)."

  ((x (and (vl-expr-p x)
           (vl-expr-welltyped-p x))
      "A match expression in a @('casex') or @('casez') statement, e.g.,
       typically this is a weirdint with some wildcard bits, such as
       @('4'b10??')."))

  :returns
  (mv (okp      booleanp     :rule-classes :type-prescription)
      (msb-bits (and (vl-bitlist-p msb-bits)
                     (implies okp
                              (equal (len msb-bits)
                                     (vl-expr->finalwidth x))))
                :hyp :fguard))

  :long "<p>For now we just support simple weirdints and constints.  We could
probably easily extend this to arbitrary concatenations of weirdints and
constints, but that's probably overkill.</p>"

  (b* (((unless (vl-fast-atom-p x))
        ;; We only support weirdints and constints for now.
        (mv nil nil))
       (guts (vl-atom->guts x))
       ((when (vl-fast-weirdint-p guts))
        (mv t (vl-weirdint->bits guts)))
       ((unless (vl-constint-p guts))
        (mv nil nil)))
    (mv t (vl-constint->msb-bits x)))

  :prepwork
  ((local (in-theory (enable vl-expr-welltyped-p
                             vl-expr->finalwidth
                             vl-atom-welltyped-p)))))


(define vl-casezx-matchexpr-aux
  ((type       vl-casetype-p)
   (test-bits  vl-exprlist-p "One-bit expressions for @('data') in MSB-first order.")
   (match-bits vl-bitlist-p  "Bits of the match expression like @('4'b10??') in
                              MSB-first order."))
  :guard (and (member type '(:vl-casez :vl-casex))
              (same-lengthp test-bits match-bits)
              (vl-exprlist-welltyped-p test-bits)
              (all-equalp 1 (vl-exprlist->finalwidths test-bits))
              (all-equalp :vl-unsigned (vl-exprlist->finaltypes test-bits)))

  :returns (expr vl-expr-p
                 :hyp (and (force (vl-exprlist-p test-bits))
                           (force (vl-bitlist-p match-bits))
                           (force (same-lengthp test-bits match-bits))))

  (b* (((when (atom test-bits))
        ;; Since our match expression is basically the AND of all the
        ;; relevant bits matching, the base case is that we've matched
        ;; everything else and so it's just true.
        |*sized-1'b1*|)

       (bit1-wild?
        (or
         ;; Z bits are always wild for both casex and casez statements
         (eq (first match-bits) :vl-zval)
         ;; X bits are also wild for casex statements.
         (and (eq type :vl-casex)
              (eq (first match-bits) :vl-xval))))

       ((when bit1-wild?)
        ;; Nothing to check for this bit.
        (vl-casezx-matchexpr-aux type (cdr test-bits) (cdr match-bits)))

       ;; First bit is not wild, so this has to match.
       (match-expr (case (first match-bits)
                     (:vl-0val |*sized-1'b0*|)
                     (:vl-1val |*sized-1'b1*|)
                     (:vl-xval |*sized-1'bx*|)
                     (otherwise (impossible))))
       (match1 (make-vl-nonatom
                ;; data[3] === 1'b0.  Always unsized,
                :op :vl-binary-ceq
                :args (list (car test-bits) match-expr)
                :finalwidth 1
                :finaltype :vl-unsigned))

       (match-rest
        (vl-casezx-matchexpr-aux type (cdr test-bits) (cdr match-bits)))

       ((when (equal match-rest |*sized-1'b1*|))
        ;; Purely aesthetic: eliminate the final "& 1'b1" if possible.
        match1))
    (make-vl-nonatom :op :vl-binary-bitand
                     :args (list match1 match-rest)
                     :finalwidth 1
                     :finaltype :vl-unsigned))
  ///
  (defthm vl-expr->finalwidth-of-vl-casezx-matchexpr-aux
    (equal (vl-expr->finalwidth (vl-casezx-matchexpr-aux type test-bits match-bits))
           1))

  (defthm vl-expr->finaltype-of-vl-casezx-matchexpr-aux
    (equal (vl-expr->finaltype (vl-casezx-matchexpr-aux type test-bits match-bits))
           :vl-unsigned))

  (defthm vl-expr-welltyped-p-of-vl-casezx-matchexpr-aux
    (implies
     (and (force (vl-exprlist-p test-bits))
          (force (vl-bitlist-p match-bits))
          (force (same-lengthp test-bits match-bits))
          (force (vl-exprlist-welltyped-p test-bits))
          (force (all-equalp 1 (vl-exprlist->finalwidths test-bits)))
          (force (all-equalp :vl-unsigned (vl-exprlist->finaltypes test-bits))))
     (vl-expr-welltyped-p
      (vl-casezx-matchexpr-aux type test-bits match-bits)))
    :hints(("Goal"
            :expand ((:free (op args atts finalwidth finaltype)
                            (vl-expr-welltyped-p
                             (make-vl-nonatom :op op
                                              :args args
                                              :atts atts
                                              :finalwidth finalwidth
                                              :finaltype finaltype))))))))


(define vl-casezx-matchexpr
  :short "Creates, e.g., the expression @('data[3] === 1'b1 & data[2] ===
1'b0') for handling @('casez(data) ... 4'b10??: ... endcase')."

  ((type       vl-casetype-p "Kind of case statement.")
   (test-bits  vl-exprlist-p "E.g., for @('casex(data) ...'), the msb-first
                              bits of @('data').")
   (match-expr vl-expr-p     "E.g., @('4'b10??'), the expression to match;
                              usually a weird integer with some wildcard bits.")
   (ctx        vl-modelement-p  "Context for @(see warnings).")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard
  (and (member type '(:vl-casez :vl-casex))
       (vl-exprlist-welltyped-p test-bits)
       (all-equalp 1 (vl-exprlist->finalwidths test-bits))
       (all-equalp :vl-unsigned (vl-exprlist->finaltypes test-bits)))
  :returns
  (mv (warnings vl-warninglist-p)
      (expr? "On failure @('nil'), otherwise an expression that checks whether
              we have a match, i.e., @('data[3] === 1'b1 & data[2] === 1'b0')."
             (equal (vl-expr-p expr?) (if expr? t nil))
             :hyp (and (vl-exprlist-p test-bits)
                       (vl-expr-p match-expr))))

  (b* (((unless (and (vl-expr-welltyped-p match-expr)
                     (equal (vl-expr->finalwidth match-expr) (len test-bits))))
        (mv (warn :type :vl-casezx-fail
                  :msg "~a0: can't handle ~s1 statement; match expression ~a2 ~
                        is too complex or incorrectly sized."
                  :args (list ctx
                              (if (eq type :vl-casex) "casex" "casez")
                              match-expr))
            nil))

       ((mv ok match-bits) (vl-casezx-match-bits match-expr))
       ((unless ok)
        (mv (warn :type :vl-casezx-fail
                  :msg "~a0: can't handle ~s1 statement; match expression ~a2 ~
                        is too complex.  (We only support integer literals ~
                        here.)"
                  :args (list ctx
                              (if (eq type :vl-casex) "casex" "casez")
                              match-expr))
            nil)))

    (mv (ok) (vl-casezx-matchexpr-aux type test-bits match-bits)))
  ///

  (defthm vl-expr-welltyped-p-of-vl-casezx-matchexpr
    (implies
     (and (vl-exprlist-p test-bits)
          (vl-exprlist-welltyped-p test-bits)
          (all-equalp 1 (vl-exprlist->finalwidths test-bits))
          (all-equalp :vl-unsigned (vl-exprlist->finaltypes test-bits))
          (vl-expr-p match-expr))
     (b* (((mv & result)
           (vl-casezx-matchexpr type test-bits match-expr ctx warnings)))
       (implies result
                (and (vl-expr-welltyped-p result)
                     (equal (vl-expr->finalwidth result) 1)
                     (equal (vl-expr->finaltype result) :vl-unsigned)))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p)))))


(define vl-casezx-elim-aux
  ((type       vl-casetype-p    "Kind of case statement.")
   (test-bits  vl-exprlist-p    "E.g., for @('casex(data) ...'), the msb-first
                                 bits of @('data').")
   (exprs      vl-exprlist-p    "Compatibly sized match expressions, in order.")
   (bodies     vl-stmtlist-p    "The body for each match expression, in order.")
   (default    vl-stmt-p        "The body for the @('default') case.")
   (ctx        vl-modelement-p  "Context for @(see warnings).")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard
  (and (member type '(:vl-casez :vl-casex))
       (vl-exprlist-welltyped-p test-bits)
       (all-equalp 1 (vl-exprlist->finalwidths test-bits))
       (all-equalp :vl-unsigned (vl-exprlist->finaltypes test-bits))
       (same-lengthp exprs bodies))
  :verify-guards nil
  :returns
  (mv (warnings vl-warninglist-p)
      (new-stmt? (equal (vl-stmt-p new-stmt?) (if new-stmt? t nil))
                 :hyp (and (force (vl-exprlist-p test-bits))
                           (force (vl-exprlist-p exprs))
                           (force (vl-stmtlist-p bodies))
                           (force (same-lengthp exprs bodies))
                           (force (vl-stmt-p default)))))
  (b* (((when (atom exprs))
        (mv (ok) default))

       ((mv warnings match-expr)
        (vl-casezx-matchexpr type test-bits (car exprs) ctx warnings))
       ((unless match-expr)
        (mv warnings nil))

       ((mv warnings rest-stmt)
        (vl-casezx-elim-aux type test-bits (cdr exprs) (cdr bodies)
                            default ctx warnings))
       ((unless rest-stmt)
        (mv warnings nil))

       (new-stmt (make-vl-ifstmt :condition match-expr
                                 :truebranch (car bodies)
                                 :falsebranch rest-stmt)))
    (mv warnings new-stmt))
  ///
  (verify-guards vl-casezx-elim-aux))


(define vl-casezx-stmt-elim
  :short "Rewrite an @('casez') or @('casex') statement into @('if') statements."

  ((type     vl-casetype-p    "Kind of case statement.")
   (test     vl-expr-p        "The test expression, should be sized.")
   (exprs    vl-exprlist-p    "The match expressions in order, should be sized.")
   (bodies   vl-stmtlist-p    "The body for each match expression, in order.")
   (default  vl-stmt-p        "The body for the @('default') case.")
   (atts     vl-atts-p        "Any attributes on the whole case statement.")
   (ctx      vl-modelement-p  "Context for @(see warnings).")
   (warnings vl-warninglist-p "Ordinary warnings accumulator.")
   (mod      vl-module-p      "Module for wire lookups, etc.")
   (ialist   (equal ialist (vl-moditem-alist mod))))
  :guard
  (and (member type '(:vl-casez :vl-casex))
       (same-lengthp exprs bodies))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-stmt vl-stmt-p
                :hyp (and (force (vl-casetype-p type))
                          (force (vl-expr-p test))
                          (force (vl-exprlist-p exprs))
                          (force (vl-stmtlist-p bodies))
                          (force (same-lengthp exprs bodies))
                          (force (vl-module-p mod))
                          (force (equal ialist (vl-moditem-alist mod)))
                          (force (vl-stmt-p default))
                          (force (vl-atts-p atts)))))

  (b* ((warnings     (vl-warninglist-fix warnings))
       (new-warnings (vl-casestmt-size-warnings test exprs ctx))

       ((mv okp new-warnings test-bits)
        (if (and (vl-expr-sliceable-p test)
                 (vl-expr-welltyped-p test))
            (vl-msb-bitslice-expr test mod ialist new-warnings)
          (mv nil new-warnings nil)))

       (new-warnings
        (if okp
            new-warnings
          (warn :type :vl-casexz-fail
                :msg "~a0: can't handle ~s1 statement because we failed to ~
                       determine the bits of the test expression ~a2."
                :args (list ctx
                            (if (eq type :vl-casex) "casex" "casez")
                            test)
                :acc new-warnings)))

       ((when new-warnings)
        ;; Some sizing problem, so just fail to rewrite the casez statement.
        (mv (append-without-guard new-warnings warnings)
            (make-vl-casestmt :casetype type
                              :test     test
                              :exprs    exprs
                              :bodies   bodies
                              :default  default
                              :atts     atts)))

       ((mv warnings new-stmt)
        (vl-casezx-elim-aux type test-bits exprs bodies default ctx warnings))

       ((unless new-stmt)
        ;; Already warned, so just leave this case statement alone.
        (mv warnings (make-vl-casestmt :casetype type
                                       :test     test
                                       :exprs    exprs
                                       :bodies   bodies
                                       :default  default
                                       :atts     atts))))

    ;; Else, it all worked.
    (mv warnings new-stmt)))



(defines vl-stmt-caseelim
  :short "Recursively eliminate @('case'), @('casez'), and @('casex')
statements within a statement."

  (define vl-stmt-caseelim ((x        vl-stmt-p)
                            (ctx      vl-modelement-p)
                            (warnings vl-warninglist-p)
                            (mod      vl-module-p)
                            (ialist   (equal ialist (vl-moditem-alist mod))))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p
                           :hyp (and (vl-stmt-p x)
                                     (vl-module-p mod)
                                     (equal ialist (vl-moditem-alist mod)))))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    (b* (((when (vl-fast-atomicstmt-p x))
          (mv (ok) x))

         ((unless (mbt (consp x)))
          (impossible)
          (mv (ok) x))

         ((unless (vl-casestmt-p x))
          (b* ((substmts
                (vl-compoundstmt->stmts x))
               ((mv warnings substmts)
                (vl-stmtlist-caseelim substmts ctx warnings mod ialist)))
            (mv warnings (change-vl-compoundstmt x :stmts substmts))))

; BOZO we aren't recursively rewriting the default statement!?

         ;; Found a case statement.
         ((vl-casestmt x) x)
         ((mv warnings bodies)
          (vl-stmtlist-caseelim x.bodies ctx warnings mod ialist))
         ((unless x.casetype)
          ;; Regular case statement, not casex/casez.
          (vl-casestmt-elim x.test x.exprs bodies x.default
                            x.atts ctx warnings)))
      (vl-casezx-stmt-elim x.casetype x.test x.exprs bodies x.default
                           x.atts ctx warnings mod ialist)))


  (define vl-stmtlist-caseelim ((x        vl-stmtlist-p)
                                (ctx      vl-modelement-p)
                                (warnings vl-warninglist-p)
                                (mod      vl-module-p)
                                (ialist   (equal ialist (vl-moditem-alist mod))))
    :returns
    (mv (warnings vl-warninglist-p)
        (new-x (and (equal (len new-x) (len x))
                    (implies (and (force (vl-stmtlist-p x))
                                  (force (vl-module-p mod))
                                  (force (equal ialist (vl-moditem-alist mod))))
                             (vl-stmtlist-p new-x)))))
    :measure (two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car)
          (vl-stmt-caseelim (car x) ctx warnings mod ialist))
         ((mv warnings cdr)
          (vl-stmtlist-caseelim (cdr x) ctx warnings mod ialist)))
      (mv warnings (cons car cdr))))

  :prepwork
  ((local
    (defthm l0
      ;; Gross, adapt vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
      ;; because the type is known in this case, so it won't match.
      (implies
       (and (force (equal (vl-compoundstmt->type x) :vl-casestmt))
            (force (vl-compoundstmt-p x))
            (force (iff (double-rewrite new-name)  (vl-compoundstmt->name x)))
            (force (iff (double-rewrite new-ctrl)  (vl-compoundstmt->ctrl x)))
            (force (equal new-sequentialp          (vl-compoundstmt->sequentialp x)))
            (force (equal new-casetype             (vl-compoundstmt->casetype x)))
            (force (equal (consp new-decls) (consp (vl-compoundstmt->decls x))))
            (force (equal (len (double-rewrite new-stmts))
                          (len (vl-compoundstmt->stmts x))))
            (force (equal (len (double-rewrite new-exprs))
                          (len (vl-compoundstmt->exprs x)))))
       (vl-compoundstmt-basic-checksp :vl-casestmt
                                      new-exprs new-stmts new-name new-decls
                                      new-ctrl new-sequentialp new-casetype))
      :hints(("Goal"
              :use ((:instance
                     vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt)))))))
  ///
  (verify-guards vl-stmt-caseelim))

(define vl-always-caseelim
  ((x        vl-always-p)
   (warnings vl-warninglist-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod))))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-always-p      :hyp :fguard))
  (b* (((mv warnings stmt)
        (vl-stmt-caseelim (vl-always->stmt x) x warnings mod ialist))
       (x-prime (change-vl-always x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-alwayslist-caseelim
  ((x        vl-alwayslist-p)
   (warnings vl-warninglist-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod))))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-alwayslist-p  :hyp :fguard))
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car) (vl-always-caseelim (car x) warnings mod ialist))
       ((mv warnings cdr) (vl-alwayslist-caseelim (cdr x) warnings mod ialist)))
    (mv warnings (cons car cdr))))

(define vl-initial-caseelim
  ((x        vl-initial-p)
   (warnings vl-warninglist-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod))))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initial-p      :hyp :fguard))
  (b* (((mv warnings stmt)
        (vl-stmt-caseelim (vl-initial->stmt x) x warnings mod ialist))
       (x-prime (change-vl-initial x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-initiallist-caseelim
  ((x        vl-initiallist-p)
   (warnings vl-warninglist-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod))))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initiallist-p  :hyp :fguard))
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car) (vl-initial-caseelim (car x) warnings mod ialist))
       ((mv warnings cdr) (vl-initiallist-caseelim (cdr x) warnings mod ialist)))
    (mv warnings (cons car cdr))))

(define vl-module-caseelim ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((unless (or x.alwayses x.initials))
        ;; Optimization: bail early on modules with no procedural stuff.
        x)

       (warnings x.warnings)
       (ialist (vl-moditem-alist x))
       ((mv warnings alwayses)
        (vl-alwayslist-caseelim x.alwayses warnings x ialist))
       ((mv warnings initials)
        (vl-initiallist-caseelim x.initials warnings x ialist)))
    (fast-alist-free ialist)
    (change-vl-module x
                      :warnings warnings
                      :alwayses alwayses
                      :initials initials)))

(defprojection vl-modulelist-caseelim (x)
  (vl-module-caseelim x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-caseelim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-caseelim x.mods))))
