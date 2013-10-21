; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
(local (include-book "../../util/arithmetic"))
(local (in-theory (disable all-equalp)))

(defxdoc caseelim
  :parents (transforms)
  :short "Replace simple @(see case-statements) with equivalent @(see
if-statements)."

  :long "<p>This rewrite eliminates @(see case-statements) into equivalent
@(see if-statements).</p>

<p>High-level notes:</p>

<ul>

<li>We expect that sizes have been computed.  We will simply fail to rewrite
case statements where any test or match expression is unsized.  We issue
non-fatal warnings if the match and test expressions have different sizes.</li>

<li>We only handle plain @('case') statements.  The fancier @('casez') and
@('casex') statements are badly behaved and we strongly advise against using
them; see @(see problems-with-casez-and-casex) for details.</li>

</ul>

<p><b>Conservativity Warning</b>.  Even simple @('case') statements have bad
semantics when it comes to X and Z values.  Each match is compared against the
test expression using case-equality @('===') instead of ordinary equality
@('==').  This allows you to match precisely against X and Z, which can easily
lead to an improper, non-conservative treatment of X.  (Generally speaking,
Verilog's behavioral modeling constructs are rife with these problems, e.g.,
even the lowly @('if') statement unsoundly treats X values as false, so you
might be well-advised not to use them.)</p>

<p>At any rate, the basic idea of the transform is to just rewrite:</p>

@({
    case (<test>)
     <match-1>: <body-1>
     <match-2>: <body-2>
     ...
     <match-n>: <body-N>
     default:   <default-body>
    endcase

       -->

    if (<test> === <match-1>)
      <body-1>
    else if (<test> === <match-2>)
      <body-2>
    ...
    else if (<test> === <body-n>)
      <body-n>
    else
      <default-body>
})

<p>This rewrite is intuitively correct, and appears to produce identical
results in some test simulations on NCVerilog and Verilog-XL.  So, we think it
is probably safe enough to use.</p>

<p>We considered using a more sophisticated rewrite that would avoid
replicating the @('test') expression above.  This seems easy: just assign the
test expression to some temporary wire, then check @('temp') against each match
expression.  The problem with this is that we might need to then include this
new wire in the sensitivity list for the always block, and this could get messy
in general.  So, our transform really is just as naive as the above
suggests.</p>")


(defxdoc problems-with-casez-and-casex
  :parents (vl-casetype-p caseelim)
  :short "Why we don't support @('casez') and @('casex') statements."

  :long "<p>Besides the ordinary @('case') statement, Verilog provides
@('casez') and @('casex') constructs that allow you to treat @('x') or @('z')
values as don't-cares.</p>

<p>At first glance these things seem pretty convenient.  For instance, in
@('casez') you are told that you can use @('Z') or (equivalently) @('?') as a
pattern-matching character.  You might look at a piece of code like this:</p>

@({
   casez (inst)
     5'b00001: out = a + b;
     5'b0001?: out = a - b;
     5'b001??: out = a & b;
     5'b01???; out = a | b;
     default:  out = 16'hXXXX;
   endcase
})

<p>And think&mdash;<i>wow, that looks nice</i>.  You are probably thinking that
the second pattern here, @('5'b0001?'), is going to match:</p>

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

<p>And so on.  <i>What?</i> you say.  Basically, Z values are treated as
wildcards not only in your pattern, but also <i>in the data itself</i>, which
is terrible and makes no sense at all.</p>

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


(define vl-casestmt-size-warnings-aux
  :parents (vl-casestmt-size-warnings)
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
  :parents (caseelim)
  :short "Check case statements for compatible sizes, and issue warnings if we
find any incompatible sizes."

  ((test     vl-expr-p       "The test expression, which should typically have
                              its width already computed.")
   (exprs    vl-exprlist-p   "The match expressions.")
   (ctx      vl-modelement-p "Context for @(see warnings)."))
  :returns
  (warnings vl-warninglist-p)

  :long "<p>Regarding the sizing of case expressions, the Verilog
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


(define vl-casestmt-compare-expr
  :parents (vl-casestmt-rewrite-aux)
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
  :parents (caseelim)
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
  :parents (caseelim)
  :short "Rewrite an ordinary @('case') statement into @('if') statements."

  ((test     vl-expr-p        "The test expression, should be sized.")
   (exprs    vl-exprlist-p    "The match expressions in order, should be sized.")
   (bodies   vl-stmtlist-p    "The body for each match expression, in order.")
   (default  vl-stmt-p        "The body for the @('default') case.")
   (atts     vl-atts-p        "Any attributes on the whole case statement.")
   (ctx      vl-modelement-p  "Context for @(see warnings).")
   (warnings vl-warninglist-p "Ordinary warnings accumulator."))

  :guard (equal (len exprs) (len bodies))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-stmt vl-stmt-p        :hyp :fguard))

  (b* ((new-warnings (vl-casestmt-size-warnings test exprs ctx))
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

(defsection vl-stmt-caseelim
  :parents (caseelim)
  :short "Recursively eliminate @('case') statements within a statement."

  (mutual-recursion
   (defund vl-stmt-caseelim (x ctx warnings)
     "Returns (mv warnings new-x)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-modelement-p ctx)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (mv warnings x))

          ((unless (mbt (consp x)))
           (impossible)
           (mv warnings x))


          ((unless (and (vl-casestmt-p x)
                        (not (vl-casestmt->casetype x))))
           (b* ((substmts
                 (vl-compoundstmt->stmts x))
                ((mv warnings substmts)
                 (vl-stmtlist-caseelim substmts ctx warnings)))
             (mv warnings (change-vl-compoundstmt x :stmts substmts))))

          ;; Found an ordinary, plain case statement.  Try to rewrite it.
          ((vl-casestmt x) x)
          ((mv warnings bodies)
           (vl-stmtlist-caseelim x.bodies ctx warnings)))
       (vl-casestmt-elim x.test x.exprs bodies x.default
                         x.atts ctx warnings)))

   (defund vl-stmtlist-caseelim (x ctx warnings)
     "Returns (mv warnings new-x)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-modelement-p ctx)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car) (vl-stmt-caseelim (car x) ctx warnings))
          ((mv warnings cdr) (vl-stmtlist-caseelim (cdr x) ctx warnings)))
       (mv warnings (cons car cdr)))))

  (flag::make-flag vl-flag-stmt-caseelim
                   vl-stmt-caseelim
                   :flag-mapping ((vl-stmt-caseelim . stmt)
                                  (vl-stmtlist-caseelim . list)))

  (local (defun my-induction (x ctx warnings)
           (b* (((when (atom x))
                 (mv warnings nil))
                ((mv warnings car) (vl-stmt-caseelim (car x) ctx warnings))
                ((mv warnings cdr) (my-induction (cdr x) ctx warnings)))
             (mv warnings (cons car cdr)))))

  (defthm len-of-vl-stmtlist-caseelim
    (equal (len (mv-nth 1 (vl-stmtlist-caseelim x ctx warnings)))
           (len x))
    :hints(("Goal"
            :induct (my-induction x ctx warnings)
            :expand (vl-stmtlist-caseelim x ctx warnings))))

  (local
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
                    vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt))))))

  (defthm-vl-flag-stmt-caseelim
    (defthm return-type-of-vl-stmt-caseelim
      (implies (and (force (vl-stmt-p x))
                    (force (vl-modelement-p ctx))
                    (force (vl-warninglist-p warnings)))
               (b* (((mv warnings new-x)
                     (vl-stmt-caseelim x ctx warnings)))
                 (and (vl-warninglist-p warnings)
                      (vl-stmt-p new-x))))
      :flag stmt)
    (defthm return-type-of-vl-stmtlist-caseelim
      (implies (and (force (vl-stmtlist-p x))
                    (force (vl-modelement-p ctx))
                    (force (vl-warninglist-p warnings)))
               (b* (((mv warnings new-x)
                     (vl-stmtlist-caseelim x ctx warnings)))
                 (and (vl-warninglist-p warnings)
                      (vl-stmtlist-p new-x))))
      :flag list)
    :hints(("Goal"
            :induct (vl-flag-stmt-caseelim flag x ctx warnings)
            :expand ((vl-stmt-caseelim x ctx warnings)
                     (vl-stmtlist-caseelim x ctx warnings)))))

  (verify-guards vl-stmt-caseelim))

(define vl-always-caseelim
  :parents (caseelim)
  ((x        vl-always-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-always-p      :hyp :fguard))
  (b* (((mv warnings stmt)
        (vl-stmt-caseelim (vl-always->stmt x) x warnings))
       (x-prime (change-vl-always x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-alwayslist-caseelim
  :parents (caseelim)
  ((x        vl-alwayslist-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-alwayslist-p  :hyp :fguard))
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car) (vl-always-caseelim (car x) warnings))
       ((mv warnings cdr) (vl-alwayslist-caseelim (cdr x) warnings)))
    (mv warnings (cons car cdr))))

(define vl-initial-caseelim
  :parents (caseelim)
  ((x        vl-initial-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initial-p      :hyp :fguard))
  (b* (((mv warnings stmt)
        (vl-stmt-caseelim (vl-initial->stmt x) x warnings))
       (x-prime (change-vl-initial x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-initiallist-caseelim
  :parents (caseelim)
  ((x        vl-initiallist-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initiallist-p  :hyp :fguard))
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car) (vl-initial-caseelim (car x) warnings))
       ((mv warnings cdr) (vl-initiallist-caseelim (cdr x) warnings)))
    (mv warnings (cons car cdr))))


(define vl-module-caseelim ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (caseelim)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((unless (or x.alwayses x.initials))
        ;; Optimization: bail early on modules with no procedural stuff.
        x)

       (warnings x.warnings)
       ((mv warnings alwayses) (vl-alwayslist-caseelim x.alwayses warnings))
       ((mv warnings initials) (vl-initiallist-caseelim x.initials warnings)))
    (change-vl-module x
                      :warnings warnings
                      :alwayses alwayses
                      :initials initials))
  ///
  (defthm vl-module->name-of-vl-module-caseelim
    (equal (vl-module->name (vl-module-caseelim x))
           (vl-module->name x))))


(defprojection vl-modulelist-caseelim (x)
  (vl-module-caseelim x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-caseelim
     (equal (vl-modulelist->names (vl-modulelist-caseelim x))
            (vl-modulelist->names x)))))
