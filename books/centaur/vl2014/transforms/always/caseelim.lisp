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
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/caremask")
(include-book "../../mlib/blocks")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable all-equalp)))
(local (in-theory (enable tag-reasoning)))

(local (defthm vl-casestmt->casetype-forward
         (or (not (vl-casestmt->casetype x))
             (equal (vl-casestmt->casetype x) :vl-casex)
             (equal (vl-casestmt->casetype x) :vl-casez))
         :rule-classes
         ((:forward-chaining :trigger-terms ((vl-casestmt->casetype x))))
         :hints(("Goal" :cases ((vl-casetype-p (vl-casestmt->casetype x)))))))

(defxdoc caseelim
  :parents (transforms)
  :short "Replace @(see vl-casestmt)s with equivalent @(see vl-ifstmt)s."

  :long "<p>This rewrite rewrites case statements into if statements.  It
requires that sizes have been computed that the test expressions and match
expressions agree on their sizes.  If these conditions are not met, it may
issue non-fatal warnings and fail to rewrite the case statements.</p>

<p>This transform is practically useful for supporting designs that involve
case statements and we believe it is basically reasonable.  But Verilog's case
statements have <b>significant problems</b> with regards to the handling of X
and Z values.  There are, therefore, many cases where this translation will
change a module's simulation semantics.  More information about these problems
can be found in @(see case-statement-problems).</p>

<p>The basic idea of the transform is just to rewrite, e.g., for plain
@('case') statements:</p>

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
limited.  Here, we require that each @('match') expression be some simple,
atomic @(see vl-constint-p) or @(see vl-weirdint-p) expression.  These
constraints allow us to carry out the following transform
e.g.,:</p>

@({
    casez (in)
      4'b001?: <body-1>
      4'b01??: <body-2>
      4'b1???: <body-3>
      default: <default-body>
    endcase
       -->
    if      ( (in & 4'b1110) === (4'b001z & 4'b1110) )    <body-1>
    else if ( (in & 4'b1100) === (4'b01zz & 4'b1100) )    <body-2>
    else if ( (in & 4'b1000) === (4'b1zzz & 4'b1000) )    <body-2>
    else if (in[3] === 1'b0 & in[2] === 1'b1)              <body-2>
    else if (in[3] === 1'b1)                               <body-3>
    else                                                   <default-body>
})

<p>That is, our @('if') statement conditions simply mask out the x/z/? bits as
appropriate, and check that the other bits are matched.</p>

<p>Unfortunately, this transformation is <b>completely wrong</b> in the case
where @('data') has X or Z bits, because in the Verilog semantics these bits
are not to be tested.  On the other hand, these are terrible, non-conservative
semantics, and we think our behavior is about as reasonable as possible.</p>")

(defxdoc case-statement-problems
  :parents (vl-casestmt caseelim)
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

(define vl-casestmt-matchexpr-sizes-agreep ((test        vl-expr-p)
                                            (match-exprs vl-exprlist-p))
  :parents (vl-casestmt-sizes-agreep)
  (b* (((when (atom match-exprs))
        t)
       (expr1 (car match-exprs)))
    (and (vl-expr->finaltype expr1)
         (eql (vl-expr->finalwidth test)
              (vl-expr->finalwidth expr1))
         (vl-casestmt-matchexpr-sizes-agreep test (cdr match-exprs))))
  ///
  (defthm vl-casestmt-matchexpr-sizes-agreep-when-atom
    (implies (atom match-exprs)
             (vl-casestmt-matchexpr-sizes-agreep test match-exprs)))

  (defthm vl-casestmt-matchexpr-sizes-agreep-of-cons
    (equal (vl-casestmt-matchexpr-sizes-agreep test (cons expr1 match-exprs))
           (and (vl-expr->finaltype expr1)
                (equal (vl-expr->finalwidth test)
                       (vl-expr->finalwidth expr1))
                (vl-casestmt-matchexpr-sizes-agreep test match-exprs)))))


(define vl-casestmt-sizes-agreep
  :short "Make sure all match expressions have been sized and that their sizes
          are compatible with the test expression."
  ((test vl-expr-p)
   (cases vl-caselist-p))
  :measure (vl-caselist-count cases)
  (b* ((cases (vl-caselist-fix cases))
       ((when (atom cases))
        t)
       ((cons match-exprs ?body1) (car cases)))
    (and (vl-casestmt-matchexpr-sizes-agreep test match-exprs)
         (vl-casestmt-sizes-agreep test (cdr cases))))
  ///
  (defthm vl-casestmt-sizes-agreep-when-atom
    (implies (atom cases)
             (equal (vl-casestmt-sizes-agreep test cases)
                    t)))

  (defthm vl-casestmt-sizes-agreep-of-cons
    (equal (vl-casestmt-sizes-agreep test (cons a cases))
           (if (atom a)
               (vl-casestmt-sizes-agreep test cases)
             (and (vl-casestmt-matchexpr-sizes-agreep test (car a))
                  (vl-casestmt-sizes-agreep test cases))))
    :hints(("Goal" :expand (vl-casestmt-sizes-agreep test (cons a cases))))))


(define vl-casestmt-matchexpr-size-warnings ((test        vl-expr-p)
                                             (match-exprs vl-exprlist-p)
                                             (ctx         vl-modelement-p))
  :parents (vl-casestmt-size-warnings)
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom match-exprs))
       nil)
       (test  (vl-expr-fix test))
       (expr1 (vl-expr-fix (car match-exprs)))
       (ctx   (vl-modelement-fix ctx))
       (rest  (vl-casestmt-matchexpr-size-warnings test (cdr match-exprs) ctx))
       ((unless (vl-expr->finaltype expr1))
        (warn :type :vl-case-stmt-type
              :msg "In ~a0: failed to determine signedness of case-statement ~
                    match expression: ~a1."
              :args (list ctx expr1)
              :acc rest))
       ((unless (eql (vl-expr->finalwidth test)
                     (vl-expr->finalwidth expr1)))
        (warn :type :vl-case-stmt-size
              :msg "In ~a0: case statement sizes are incompatible:~%     ~
                      - ~x1-bit test:  ~a3~%     ~
                      - ~x2-bit match: ~a4"
              :args (list ctx
                          (vl-expr->finalwidth test)
                          (vl-expr->finalwidth expr1)
                          test
                          expr1)
              :acc rest)))
    rest)
  ///
  (more-returns
   (warnings true-listp :rule-classes :type-prescription))
  (defthm vl-casestmt-matchexpr-size-warnings-correct
    (implies (not (vl-casestmt-matchexpr-size-warnings test match-exprs ctx))
             (vl-casestmt-matchexpr-sizes-agreep test match-exprs))
    :hints(("Goal" :expand (vl-casestmt-matchexpr-sizes-agreep test match-exprs)))))


(define vl-casestmt-size-warnings-aux
  :parents (vl-casestmt-size-warnings)
  ((test     vl-expr-p       "The test expression, which should typically have
                              its width already computed.")
   (cases    vl-caselist-p   "The match expressions.")
   (ctx      vl-modelement-p "Context for @(see warnings)."))
  :returns (warnings vl-warninglist-p)
  :measure (vl-caselist-count cases)
  (b* ((test  (vl-expr-fix test))
       (cases (vl-caselist-fix cases))
       (ctx   (vl-modelement-fix ctx))
       ((when (atom cases))
        nil)
       ((cons match-exprs1 ?body1) (car cases))
       (first (vl-casestmt-matchexpr-size-warnings test match-exprs1 ctx))
       (rest  (vl-casestmt-size-warnings-aux test (cdr cases) ctx)))
    (append first rest))
  ///
  (more-returns
   (warnings true-listp :rule-classes :type-prescription))
  (defthm vl-casestmt-size-warnings-aux-correct
    (implies (not (vl-casestmt-size-warnings-aux test cases ctx))
             (vl-casestmt-sizes-agreep test cases))
    :hints(("Goal" :expand (vl-casestmt-sizes-agreep test cases)))))


(define vl-casestmt-size-warnings
  :short "Check case statements for compatible sizes, and issue warnings if we
find any incompatible sizes."

  ((test     vl-expr-p       "The test expression, which should typically have
                              its width already computed.")
   (cases    vl-caselist-p   "The cases for the case statement.")
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

  (b* ((test (vl-expr-fix test))
       (ctx  (vl-modelement-fix ctx))
       ((unless (and (posp (vl-expr->finalwidth test))
                     (vl-expr->finaltype test)))
        ;; Avoid giving tons of warnings if we failed to size the test expr.
        (list
         (make-vl-warning
          :type :vl-case-stmt-size
          :msg "In ~a0: case statement is testing expression whose ~
                size/type was not successfully determined: ~a1."
          :args (list ctx test)
          :fn __function__))))
    (vl-casestmt-size-warnings-aux test cases ctx))
  ///
  (more-returns
   (warnings true-listp :rule-classes :type-prescription))
  (defthm widths-after-vl-casestmt-size-warnings
    (implies (not (vl-casestmt-size-warnings test cases ctx))
             (and (posp (vl-expr->finalwidth test))
                  (vl-expr->finaltype test)
                  (vl-casestmt-sizes-agreep test cases)))))



; -----------------------------------------------------------------------------
;
;                 Ordinary "Case" Statement -> If Statement
;
; -----------------------------------------------------------------------------

(define vl-casestmt-compare-expr1
  :parents (vl-casestmt-compare-expr)
  :short "Creates, e.g., the expression @('foo === 3'b110'), for handling
@('case(foo) ... 3'b110: ... endcase')."
  ((test vl-expr-p "The test expression, e.g., @('foo').")
   (expr vl-expr-p "One match expression, e.g., @('3'b110')."))
  :returns
  (compare-expr vl-expr-p)
  :long "<p>This is mostly dealing with sizing.  Recall from 5.5.1 that
comparisons always produce unsigned results.  Our guard is strong enough to
ensure that we'll always have equal-width expressions and that we know their
types.  We haven't assumed anything about their types agreeing.  To make sure
that we produce well-typed expressions, we'll coerce anything signed into an
unsigned equivalent, by just wrapping it in a one-bit concatenation.</p>"
  :guard (and (vl-expr->finaltype test)
              (vl-expr->finaltype expr)
              (posp (vl-expr->finalwidth test))
              (equal (vl-expr->finalwidth test) (vl-expr->finalwidth expr)))
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
                (or (equal (vl-expr->finaltype x) :vl-unsigned)
                    (equal (vl-expr->finaltype x) :vl-signed)
                    (equal (vl-expr->finaltype x) nil))
                :rule-classes ((:forward-chaining
                                :trigger-terms ((vl-expr->finaltype x))))
                :hints(("Goal"
                        :in-theory (disable vl-exprtype-p)
                        :use ((:instance vl-exprtype-p
                                         (x (vl-expr->finaltype x)))))))))
  ///
  (more-returns
   (compare-expr (equal (vl-expr->finalwidth compare-expr) 1)
                 :name vl-expr->finalwidth-of-vl-casestmt-compare-expr1)
   (compare-expr (equal (vl-expr->finaltype compare-expr) :vl-unsigned)
                 :name vl-expr->finaltype-of-vl-casestmt-compare-expr1))

  (defthm vl-expr-welltyped-p-of-vl-casestmt-compare-expr1
    (implies (and (force (posp (vl-expr->finalwidth test)))
                  (force (vl-expr->finaltype test))
                  (force (vl-expr->finaltype expr))
                  (force (equal (vl-expr->finalwidth test) (vl-expr->finalwidth expr)))
                  (force (vl-expr-welltyped-p test))
                  (force (vl-expr-welltyped-p expr)))
             (vl-expr-welltyped-p (vl-casestmt-compare-expr1 test expr)))
    :hints(("Goal"
            :in-theory (enable vl-expr-welltyped-p)
            :expand ((:free (op args atts finalwidth finaltype)
                      (vl-expr-welltyped-p (make-vl-nonatom :op op
                                                            :args args
                                                            :atts atts
                                                            :finalwidth finalwidth
                                                            :finaltype finaltype))))))))

(define vl-casestmt-compare-expr
  :short "Creates, e.g., the expression @('foo === 3'b110 | foo === 3'b111'),
for handling @('case(foo) ... 3'b110, 3'b111: ... endcase')."
  ((test        vl-expr-p "The test expression, e.g., @('foo').")
   (match-exprs vl-exprlist-p "The match expressions, e.g., @('3'b110, 3'b111')."))
  :returns
  (compare-expr vl-expr-p)
  :guard (and (vl-expr->finaltype test)
              (posp (vl-expr->finalwidth test))
              (vl-casestmt-matchexpr-sizes-agreep test match-exprs))
  (b* (((when (atom match-exprs))
        (raise "Case statement with zero match expressions?")
        |*sized-1'bx*|)
       (compare1 (vl-casestmt-compare-expr1 test (car match-exprs)))
       ((when (atom (cdr match-exprs)))
        compare1)
       (compare-rest (vl-casestmt-compare-expr test (cdr match-exprs))))
    (make-vl-nonatom :op :vl-binary-bitor
                     :args (list compare1 compare-rest)
                     :finaltype :vl-unsigned
                     :finalwidth 1))
  ///
  (more-returns
   (compare-expr (equal (vl-expr->finalwidth compare-expr) 1)
                 :name vl-expr->finalwidth-of-vl-casestmt-compare-expr)
   (compare-expr (equal (vl-expr->finaltype compare-expr) :vl-unsigned)
                 :name vl-expr->finaltype-of-vl-casestmt-compare-expr))

  (defthm vl-expr-welltyped-p-of-vl-casestmt-compare-expr
    (implies (and (force (posp (vl-expr->finalwidth test)))
                  (force (vl-expr->finaltype test))
                  (force (vl-casestmt-matchexpr-sizes-agreep test match-exprs))
                  (force (vl-expr-welltyped-p test))
                  (force (vl-exprlist-welltyped-p match-exprs)))
             (vl-expr-welltyped-p (vl-casestmt-compare-expr test match-exprs)))
    :hints(("Goal"
            :in-theory (enable vl-expr-welltyped-p)
            :expand ((:free (op args atts finalwidth finaltype)
                      (vl-expr-welltyped-p (make-vl-nonatom :op op
                                                            :args args
                                                            :atts atts
                                                            :finalwidth finalwidth
                                                            :finaltype finaltype))))))))

(define vl-casestmt-elim-aux
  ((test     vl-expr-p        "The test expression, already sized.")
   (cases    vl-caselist-p    "The match expressions and bodies.")
   (default  vl-stmt-p        "The body for the @('default') case."))
  :guard (and (vl-expr->finaltype test)
              (posp (vl-expr->finalwidth test))
              (vl-casestmt-sizes-agreep test cases))
  :returns (new-stmt vl-stmt-p)
  :measure (vl-caselist-count cases)
  (b* ((cases (vl-caselist-fix cases))
       ((when (atom cases))
        (vl-stmt-fix default))
       ((cons match-exprs1 body1) (car cases)))
    (make-vl-ifstmt
     :condition (vl-casestmt-compare-expr test match-exprs1)
     :truebranch body1
     :falsebranch (vl-casestmt-elim-aux test (cdr cases) default))))

(define vl-casestmt-elim
  :short "Rewrite an ordinary @('case') statement into @('if') statements."

  ((check    vl-casecheck-p   "The kind of checking to do, if any.")
   (test     vl-expr-p        "The test expression, should be sized.")
   (caselist vl-caselist-p    "The cases, should be sized.")
   (default  vl-stmt-p        "The body for the @('default') case.")
   (atts     vl-atts-p        "Any attributes on the whole case statement.")
   (ctx      vl-modelement-p  "Context for @(see warnings).")
   (warnings vl-warninglist-p "Ordinary warnings accumulator."))
  :returns (mv (warnings vl-warninglist-p)
               (new-stmt vl-stmt-p))
  :verbosep t

  (b* ((warnings     (vl-warninglist-fix warnings))
       (new-warnings (vl-casestmt-size-warnings test caselist ctx))
       (check        (vl-casecheck-fix check))
       ((when new-warnings)
        ;; Some sizing problem, so just fail to rewrite the case statement.
        (mv (append new-warnings warnings)
            (make-vl-casestmt :casetype nil
                              :check    check
                              :test     test
                              :caselist caselist
                              :default  default
                              :atts     atts)))
       (warnings
        ;; See SystemVerilog-2012 Section 12.5.3 for information about priority,
        ;; unique, and unique0 case statements.
        ;;
        ;; It appears that 'priority' basically just means: it is an error for
        ;; no case item to match and the case statement does not need a default
        ;; value.  We won't handle a missing default branch correctly yet, but
        ;; if there is a default, we'll still do the right thing.
        ;;
        ;; For 'unique' or 'unique0', it's supposed to be safe to evaluate the
        ;; items in any order, and it's a runtime error for multiple cases to
        ;; simultaneously match.
        ;;
        ;;   - As with 'priority', a 'unique' case doesn't need a default, and
        ;;     we currently won't be able to handle it correctly.
        ;;
        ;;   - In case of a violation, the spec says: "the implementation shall
        ;;     issue a violation report and ___execute the statement associated
        ;;     with the matching case_item that appears ***FIRST*** in the case
        ;;     statement, but ***NOT*** the statements associated with other
        ;;     matching case_items.___" So, creating an ordinary, if-then-else
        ;;     style structure still gives the correct semantics, even in case
        ;;     of a violation.
        ;;
        ;; It would probably be nicer to do something smarter to handle these,
        ;; forcing the output to X in case of a violation, etc.  We'll at least
        ;; issue a warning.
        (if check
            (warn :type :vl-case-check
                  :msg "~a0: we don't yet implement priority, unique, or ~
                         unique0 checking for case statements.  We will ~
                         treat this as an ordinary case statement."
                  :args (list (vl-modelement-fix ctx)))
          (ok))))
    ;; Else, all sizes are good enough, we can turn it into ifs.  BOZO we're
    ;; going to lose any attributes associated with the case statement.
    ;; Maybe that's okay?
    (mv warnings (vl-casestmt-elim-aux test caselist default))))



; -----------------------------------------------------------------------------
;
;               "Casez" and "Casex" Statements -> If Statement
;
; -----------------------------------------------------------------------------





(define vl-casezx-matchexpr
  :short "Creates, e.g., the expression @('(data & 4'b1100) === 4'b1000')
 for handling @('casez(data) ... 4'b10??: ... endcase')."

  ((type       vl-casetype-p "Kind of case statement.")
   (test       vl-expr-p     "E.g., for @('casex(data) ...'), data.")
   (match-expr vl-expr-p     "E.g., @('4'b10??'), the expression to match;
                              usually a weird integer with some wildcard bits.")
   (ctx        vl-modelement-p  "Context for @(see warnings).")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard
  (and (member type '(:vl-casez :vl-casex))
       (vl-expr-welltyped-p test)
       (posp (vl-expr->finalwidth test))
       (eq (vl-expr->finaltype test) :vl-unsigned))
  :returns
  (mv (warnings vl-warninglist-p)
      (expr? "On failure @('nil'), otherwise an expression that checks whether
              we have a match, i.e., @('(data & 4'b1100) === 4'b1000')"
             (iff (vl-expr-p expr?) expr?)))
  :prepwork ((local (defthm max->=-a
                      (>= (max a b) a)
                      :rule-classes :linear))
             (local (defthm max->=-b
                      (>= (max a b) b)
                      :rule-classes :linear))
             (local (in-theory (disable (tau-system)
                                        member-equal-when-member-equal-of-cdr-under-iff
                                        not double-containment max))))

  (b* ((type       (vl-casetype-fix type))
       (ctx        (vl-modelement-fix ctx))
       (match-expr (vl-expr-fix match-expr))

       ((unless (and (vl-expr-welltyped-p match-expr)
                     (posp (vl-expr->finalwidth match-expr))))
        (mv (warn :type :vl-casezx-fail
                  :msg "~a0: can't handle ~s1 statement; match expression ~a2 ~
                        is too complex or incorrectly sized."
                  :args (list ctx
                              (if (eq type :vl-casex) "casex" "casez")
                              match-expr))
            nil))
       ;; ((when (eq (vl-expr->finaltype test) :vl-signed))
       ;;  (mv (warn :type :vl-casezx-fail
       ;;            :msg "~a0: Can't currently handle ~s1 statement because the ~
       ;;                  test expression ~a2 is signed.  Come back when ~
       ;;                  Verilog has a sign-extend operator."
       ;;            :args (list ctx (if (eq type :vl-casex) "casex" "casez")
       ;;                        test match-expr))
       ;;      nil))

       ((mv ok match-bits) (vl-intliteral-msb-bits match-expr))
       ((unless ok)
        (mv (warn :type :vl-casezx-fail
                  :msg "~a0: can't handle ~s1 statement; match expression ~a2 ~
                        is too complex.  (We only support integer literals ~
                        here.)"
                  :args (list ctx
                              (if (eq type :vl-casex) "casex" "casez")
                              match-expr))
            nil))

       (finalwidth (max (vl-expr->finalwidth match-expr)
                        (vl-expr->finalwidth test)))
       (finaltype (if (and (eq (vl-expr->finaltype match-expr) :vl-signed)
                           (eq (vl-expr->finaltype test) :vl-signed))
                      ;; this doesn't happen atm bc of the test above
                      :vl-signed
                    :vl-unsigned))
       (ext-match-bits (append
                        (repeat (- finalwidth (vl-expr->finalwidth match-expr))
                                (if (eq finaltype :vl-signed)
                                    (car match-bits)
                                  :vl-0val))
                        match-bits))

       ;; Care mask computation.
       (cm-value (if (eq type :vl-casez)
                     (vl-msb-bits-to-z-care-mask ext-match-bits 0)
                   (vl-msb-bits-to-zx-care-mask ext-match-bits 0)))
       (cm-guts  (make-vl-constint :value cm-value
                                   :origwidth finalwidth
                                   :origtype finaltype))
       (cm-expr  (make-vl-atom :guts cm-guts
                               :finalwidth finalwidth
                               :finaltype finaltype))
       (zap-bits (if (eq type :vl-casez)
                     (vl-msb-bits-zap-dontcares-z ext-match-bits)
                   (vl-msb-bits-zap-dontcares-zx ext-match-bits)))

       (zap-expr (vl-msb-bits-to-intliteral zap-bits finaltype))

       (test-width (vl-expr->finalwidth test))
       (test-ext (if (< test-width finalwidth)
                     ;; zero extend
                     (make-vl-nonatom :op :vl-concat
                                      :args (list (make-vl-atom :guts (make-vl-constint
                                                                       :origwidth (- finalwidth test-width)
                                                                       :origtype :vl-unsigned
                                                                       :value 0)
                                                                :finalwidth (- finalwidth test-width)
                                                                :finaltype :vl-unsigned)
                                               test)
                                   :finalwidth finalwidth
                                   :finaltype finaltype)
                   test))

       (if-test (make-vl-nonatom
                 :op :vl-binary-ceq
                 :args (list (make-vl-nonatom
                              :op :vl-binary-bitand
                              :args (list test-ext cm-expr)
                              :finalwidth finalwidth
                              :finaltype finaltype)
                             zap-expr)
                 :finalwidth 1
                 :finaltype :vl-unsigned)))
    (mv (ok) if-test))
  ///
  (more-returns
   (expr? (implies expr? (equal (vl-expr->finalwidth expr?) 1))
          :name vl-expr->finalwidth-of-vl-casezx-matchexpr)
   (expr? (implies expr? (equal (vl-expr->finaltype expr?) :vl-unsigned))
          :name vl-expr->finaltype-of-vl-casezx-matchexpr))

  (defthm vl-expr-welltyped-p-of-vl-casezx-matchexpr
    (implies
     (and (vl-expr-welltyped-p test)
          (posp (vl-expr->finalwidth test))
          (equal (vl-expr->finaltype test) :vl-unsigned))
     (b* (((mv & result)
           (vl-casezx-matchexpr type test match-expr ctx warnings)))
       (implies result
                (vl-expr-welltyped-p result))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-atom-welltyped-p)))))

(define vl-casezx-match-any-expr
  :short "Handles situations like @('casez(foo) ... 3'bxx1, 3'bx10:
... endcase'), i.e., where we have multiple match expressions associated with
the same body."

  ((type        vl-casetype-p    "Kind of case statement.")
   (test        vl-expr-p        "E.g., for @('casex(data) ...'), data.")
   (match-exprs vl-exprlist-p    "The match expressions, usually weird integers with wildcard bits.")
   (ctx         vl-modelement-p  "Context for @(see warnings).")
   (warnings    vl-warninglist-p "Ordinary @(see warnings) accumulator."))

  :returns
  (mv (warnings vl-warninglist-p)
      (expr?    "On failure @('nil'), otherwise an expression that checks whether
                 we have any match."
                (equal (vl-expr-p expr?) (if expr? t nil))))

  :guard (and (member type '(:vl-casez :vl-casex))
              (vl-expr-welltyped-p test)
              (posp (vl-expr->finalwidth test))
              (equal (vl-expr->finaltype test) :vl-unsigned))
  (b* (((when (atom match-exprs))
        (mv (fatal :type :vl-casezx-fail
                   :msg "~a0: case list has no match expressions?"
                   :args (list (vl-modelement-fix ctx)))
            nil))
       ((mv warnings compare1) (vl-casezx-matchexpr type test (car match-exprs) ctx warnings))
       ((unless compare1)
        ;; Already warned, just fail.
        (mv warnings nil))
       ((when (atom (cdr match-exprs)))
        ;; Fine -- nothing else to worry about
        (mv warnings compare1))
       ((mv warnings compare-rest) (vl-casezx-match-any-expr type test (cdr match-exprs) ctx warnings))
       ((unless compare-rest)
        ;; Already warned, just fail.
        (mv warnings nil)))
    (mv warnings (make-vl-nonatom :op :vl-binary-bitor
                                  :args (list compare1 compare-rest)
                                  :finaltype :vl-unsigned
                                  :finalwidth 1)))
  ///
  (more-returns
   (expr? (implies expr?
                   (equal (vl-expr->finalwidth expr?) 1))
          :name vl-expr->finalwidth-of-vl-casezx-match-any-expr)
   (expr? (implies expr?
                   (equal (vl-expr->finaltype expr?) :vl-unsigned))
          :name vl-expr->finaltype-of-vl-casezx-match-any-expr))

  (defthm vl-expr-welltyped-p-of-vl-casezx-match-any-expr
    (implies (and (vl-expr-welltyped-p test)
                  (posp (vl-expr->finalwidth test))
                  (equal (vl-expr->finaltype test) :vl-unsigned))
             (b* (((mv & result)
                   (vl-casezx-match-any-expr type test match-exprs ctx warnings)))
               (implies result
                        (vl-expr-welltyped-p result))))
    :hints(("Goal"
            :in-theory (enable vl-expr-welltyped-p)
            :expand ((:free (op args atts finalwidth finaltype)
                      (vl-expr-welltyped-p (make-vl-nonatom :op op
                                                            :args args
                                                            :atts atts
                                                            :finalwidth finalwidth
                                                            :finaltype finaltype))))))))

(define vl-casezx-elim-aux
  ((type       vl-casetype-p    "Kind of case statement.")
   (test       vl-expr-p        "E.g., for @('casex(data) ...'), the msb-first
                                 bits of @('data').")
   (cases      vl-caselist-p    "Compatibly sized cases.")
   (default    vl-stmt-p        "The body for the @('default') case.")
   (ctx        vl-modelement-p  "Context for @(see warnings).")
   (warnings   vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :guard
  (and (member type '(:vl-casez :vl-casex))
       (vl-expr-welltyped-p test)
       (posp (vl-expr->finalwidth test))
       (equal (vl-expr->finaltype test) :vl-unsigned))
  :verify-guards nil
  :returns
  (mv (warnings vl-warninglist-p)
      (new-stmt? (equal (vl-stmt-p new-stmt?) (if new-stmt? t nil))))
  :measure (vl-caselist-count cases)
  (b* ((cases   (vl-caselist-fix cases))
       (default (vl-stmt-fix default))
       ((when (atom cases))
        (mv (ok) default))
       ((cons match-exprs1 body1) (car cases))

       ((mv warnings match-expr)
        (vl-casezx-match-any-expr type test match-exprs1 ctx warnings))
       ((unless match-expr)
        (mv warnings nil))

       ((mv warnings rest-stmt)
        (vl-casezx-elim-aux type test (cdr cases) default ctx warnings))
       ((unless rest-stmt)
        (mv warnings nil))

       (new-stmt (make-vl-ifstmt :condition match-expr
                                 :truebranch body1
                                 :falsebranch rest-stmt)))
    (mv warnings new-stmt))
  ///
  (verify-guards vl-casezx-elim-aux))

(define vl-casezx-stmt-elim
  :short "Rewrite an @('casez') or @('casex') statement into @('if') statements."

  ((type     vl-casetype-p    "Kind of case statement.")
   (check    vl-casecheck-p   "The kind of checking to do, if any.")
   (test     vl-expr-p        "The test expression, should be sized.")
   (cases    vl-caselist-p    "The cases for the case statement, should be sized.")
   (default  vl-stmt-p        "The body for the @('default') case.")
   (atts     vl-atts-p        "Any attributes on the whole case statement.")
   (ctx      vl-modelement-p  "Context for @(see warnings).")
   (warnings vl-warninglist-p "Ordinary warnings accumulator.")
   (ss       vl-scopestack-p  "NOTE: Not currently used."))
  :guard
  (member type '(:vl-casez :vl-casex))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-stmt vl-stmt-p))
  :verbosep t
  (b* ((type         (vl-casetype-fix type))
       (check        (vl-casecheck-fix check))
       (test         (vl-expr-fix test))
       (ctx          (vl-modelement-fix ctx))
       (?ss           (vl-scopestack-fix ss))
       (warnings     (vl-warninglist-fix warnings))

       (new-warnings (vl-casestmt-size-warnings test cases ctx))
       (new-warnings (if (and (vl-expr-welltyped-p test)
                              (posp (vl-expr->finalwidth test))
                              (eq (vl-expr->finaltype test) :vl-unsigned))
                         new-warnings
                       (warn :type :vl-casezx-fail
                             :msg "~a0: can't handle ~s1 statement because ~
                                   the test expression ~a2 is either signed, ~
                                   unsized, or of size 0."
                             :args (list ctx
                                         (if (eq type :vl-casex) "casex" "casez")
                                         test)
                             :acc new-warnings)))
       ((when new-warnings)
        ;; Some sizing problem, so just fail to rewrite the casez statement.
        (mv (append-without-guard new-warnings warnings)
            (make-vl-casestmt :casetype type
                              :check    check
                              :test     test
                              :caselist cases
                              :default  default
                              :atts     atts)))

       (warnings
        (if check
            (warn :type :vl-casezx-check
                  :msg "~a0: we don't yet implement priority, unique, or ~
                         unique0 checking for casez/x statements.  We will ~
                         treat this as an ordinary casez/x statement."
                  :args (list (vl-modelement-fix ctx)))
          warnings))

       ((mv warnings new-stmt)
        (vl-casezx-elim-aux type test cases default ctx warnings))

       ((unless new-stmt)
        ;; Already warned.  Try regular casestmt elim, plus an extra scary warning.
        (b* ((warnings (warn :type :vl-casezx-unsafe-conversion
                             :msg "~a0: ~s1 statement is not supported, so we ~
                                   are processing it as a regular case ~
                                   statement, which may be unsound."
                             :args (list ctx (if (eq type :vl-casex) "casex" "casez")))))
          (vl-casestmt-elim check test cases default atts ctx warnings))))

    ;; Else, it all worked.
    (mv warnings new-stmt)))

(defines vl-stmt-caseelim
  :short "Recursively eliminate @('case'), @('casez'), and @('casex')
statements within a statement."

  (define vl-stmt-caseelim ((x        vl-stmt-p)
                            (ctx      vl-modelement-p)
                            (warnings vl-warninglist-p)
                            (ss       vl-scopestack-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (mv (ok) x))

         (substmts               (vl-compoundstmt->stmts x))
         ((mv warnings substmts) (vl-stmtlist-caseelim substmts ctx warnings ss))
         (x                      (change-vl-compoundstmt x :stmts substmts))
         ((unless (eq (vl-stmt-kind x) :vl-casestmt))
          (mv warnings x))

         ((vl-casestmt x) x)
         ((unless x.casetype)
          ;; Regular case statement, not casex/casez.
          (vl-casestmt-elim           x.check x.test x.caselist x.default x.atts ctx warnings)))
      (vl-casezx-stmt-elim x.casetype x.check x.test x.caselist x.default x.atts ctx warnings ss)))

  (define vl-stmtlist-caseelim ((x        vl-stmtlist-p)
                                (ctx      vl-modelement-p)
                                (warnings vl-warninglist-p)
                                (ss       vl-scopestack-p))
    :returns
    (mv (warnings vl-warninglist-p)
        (new-x (and (vl-stmtlist-p new-x)
                    (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car)
          (vl-stmt-caseelim (car x) ctx warnings ss))
         ((mv warnings cdr)
          (vl-stmtlist-caseelim (cdr x) ctx warnings ss)))
      (mv warnings (cons car cdr))))
  ///
  (verify-guards vl-stmt-caseelim)
  (deffixequiv-mutual vl-stmt-caseelim))

(define vl-always-caseelim
  ((x        vl-always-p)
   (warnings vl-warninglist-p)
   (ss       vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-always-p))
  (b* ((x (vl-always-fix x))
       ((mv warnings stmt)
        (vl-stmt-caseelim (vl-always->stmt x) x warnings ss))
       (x-prime (change-vl-always x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-alwayslist-caseelim
  ((x        vl-alwayslist-p)
   (warnings vl-warninglist-p)
   (ss       vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-alwayslist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car) (vl-always-caseelim (car x) warnings ss))
       ((mv warnings cdr) (vl-alwayslist-caseelim (cdr x) warnings ss)))
    (mv warnings (cons car cdr))))

(define vl-initial-caseelim
  ((x        vl-initial-p)
   (warnings vl-warninglist-p)
   (ss       vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-initial-p))
  (b* ((x (vl-initial-fix x))
       ((mv warnings stmt)
        (vl-stmt-caseelim (vl-initial->stmt x) x warnings ss))
       (x-prime (change-vl-initial x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-initiallist-caseelim
  ((x        vl-initiallist-p)
   (warnings vl-warninglist-p)
   (ss       vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-initiallist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car) (vl-initial-caseelim (car x) warnings ss))
       ((mv warnings cdr) (vl-initiallist-caseelim (cdr x) warnings ss)))
    (mv warnings (cons car cdr))))

(def-genblob-transform vl-genblob-caseelim ((ss vl-scopestack-p)
                                                (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  ;; :verify-guards nil
  (b* (((vl-genblob x) x)
       (ss (vl-scopestack-push (vl-genblob-fix x) ss))

       ((mv warnings alwayses)
        (vl-alwayslist-caseelim x.alwayses warnings ss))
       ((mv warnings initials)
        (vl-initiallist-caseelim x.initials warnings ss))

       ((mv warnings generates)  (vl-generates-caseelim  x.generates ss  warnings)))
      (mv warnings
          (change-vl-genblob
           x
           :alwayses alwayses
           :initials initials
           :generates generates)))
  :apply-to-generates vl-generates-caseelim)



(define vl-module-caseelim ((x vl-module-p) (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       (genblob (vl-module->genblob x))
       ((mv warnings new-genblob) (vl-genblob-caseelim genblob ss (vl-module->warnings x)))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module new-genblob x-warn)))

(defprojection vl-modulelist-caseelim ((x vl-modulelist-p) (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-caseelim x ss))

(define vl-design-caseelim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-caseelim x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
