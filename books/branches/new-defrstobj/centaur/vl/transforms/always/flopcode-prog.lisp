; VL Verilog Toolkit
; Copyright (C) 2008-2012 Centaur Technology
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
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/welltyped")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))

; Recognizers for valid flopcode programs

(defxdoc flopcode
  :parents (synthalways)
  :short "Core subset of Verilog statements used in flop synthesis."

  :long "<p>Our lowest-level flop synthesis transformation targets a very
limited subset of Verilog statements that we call <b>flopcode</b>.</p>

<p>Generally speaking, VL can handle a much larger subset of statements than
what we are about to describe.  You can think of flopcode as a sort of back-end
mini-language.  Other transforms deal with richer statements by reducing them
into flopcode, so our final synthesis step only has to deal with flopcode.</p>

<p>Here is an example flopcode program:</p>

@({
 a <= x0;
 a <= (x1 & x2) | x3;
 if (c2) a <= x2;
 if (c2) a <= x3;
 if (c3) a <= x4;
 a <= x5 & 1;
})

<p>A flopcode program is a @(see vl-stmtlist-p) that meets several
restrictions.  These restrictions are meant to make it easy to synthesize
flopcode programs correctly.  Here are some \"local\" requirements:</p>

<ul>

<li>All expressions have their widths and types computed.</li>

<li>Every assignment must be a non-blocking, i.e., it uses @('<=') instead of
@('=').</li>

<li>Every assignment must be to a simple identifier, i.e., the left-hand side
is not something like @('a[3]').</li>

<li>Every assignment must be either control-free or have a simple delay
control, i.e., @('#5').</li>

<li>Top-level @(see if-statements) are allowed, but the @('true') branch must
be an assignment and the @('else') branch must be a @(see vl-nullstmt-p).  In
other words, there really aren't any @('else') statements.</li>

<li>No other statements are allowed.</li>

</ul>

<p>There are some \"global\" requirements:</p>

<ul>

<li>There must be at least one statement, and</li>

<li>Every assignment is to the same identifier.  For instance, notice above
that every assignment writes to @('a').  We'll call this the <b>target
register</b> of the program.</li>

<li>Every assignment must have the same delay.</li>

<li>All lhses/rhses must have the same width.</li>

</ul>

<p>Moreover, our core algorithm for synthesizing flopcode deals with
@('always') blocks of the form:</p>

@({
 always @(posedge clk)
 begin
   prog
 end
})

<p>where @('clk') is some one-bit expression and @('prog') is a valid flopcode
program.  For flopcode synthesis to succeed, we also require that:</p>

<ul>

<li>The target register of @('prog') must be defined as a <tt>reg</tt> in the
module; it must be a simple register, i.e., not an array, etc.</li>

<li>No other always blocks may write to the target register.</li>

</ul>

<p>If an @('always') block doesn't satisfy these criteria, our flopcode
synthesis will leave it unchanged.</p>")

(define vl-flopcodeassign-p ((x vl-assignstmt-p))
  :parents (vl-flopcodestmt-p)
  (b* (((vl-assignstmt x) x))
    (and (eq x.type :vl-nonblocking)
         (vl-idexpr-p x.lvalue)
         (or (not x.ctrl)
             (and (mbe :logic (vl-delaycontrol-p x.ctrl)
                       :exec (eq (tag x.ctrl) :vl-delaycontrol))
                  (vl-simpledelaycontrol-p x.ctrl)))
         (vl-expr-welltyped-p x.lvalue)
         (vl-expr-welltyped-p x.expr)
         (posp (vl-expr->finalwidth x.lvalue))
         (posp (vl-expr->finalwidth x.expr))
         (int= (vl-expr->finalwidth x.lvalue)
               (vl-expr->finalwidth x.expr)))))

(define vl-flopcodestmt-p ((x vl-stmt-p))
  :parents (flopcode)
  :short "Recognizer for flopcode statements."

  :long "<p>Every @(see flopcode) statement matches one of the following
forms:</p>

<ul>
<li>@('lhs <= [#(delay)] rhs')</li>
<li>@('if (test) lhs <= [#(delay)] rhs')</li>
</ul>

<p>It is convenient to define accessors to deal with flopcode statements in a
uniform way:</p>

<ul>

<li>@(call vl-flopcodestmt->test) returns the @('test') for conditional
flopcode assignments, or @('nil') for unconditional statements.</li>

<li>@(call vl-flopcodestmt->lhs) returns the @('lhs') in either case.</li>

<li>@(call vl-flopcodestmt->rhs) returns the @('rhs') in either case.</li>

<li>@(call vl-flopcodestmt->delay) returns the delay amount, a natural number
or @('nil') for no delay.</li>

</ul>"

  (b* (((when (vl-fast-atomicstmt-p x))
        (and (vl-fast-assignstmt-p x)
             (vl-flopcodeassign-p x)))
       ((unless (vl-ifstmt-p x))
        nil)
       ((vl-ifstmt x) x))
    (and (vl-assignstmt-p x.truebranch)
         (vl-flopcodeassign-p x.truebranch)
         (vl-nullstmt-p x.falsebranch)
         (vl-expr->finaltype x.condition)
         (vl-expr-welltyped-p x.condition)
         (eql (vl-expr->finalwidth x.condition) 1))))

(define vl-flopcodestmt->test ((x (and (vl-stmt-p x)
                                       (vl-flopcodestmt-p x))))
  :returns (test :hyp :fguard
                 (and (equal (vl-expr-p test) (if test t nil))
                      (implies test
                               (and (equal (vl-expr->finalwidth test) 1)
                                    (vl-expr->finaltype test)
                                    (vl-expr-welltyped-p test)))))
  :parents (vl-flopcodestmt-p)
  :inline t
  (and (vl-fast-compoundstmt-p x)
       (vl-ifstmt->condition x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p)))))

(define vl-flopcodestmt->lhs ((x (and (vl-stmt-p x)
                                      (vl-flopcodestmt-p x))))
  :returns (lhs :hyp :fguard (and (vl-expr-p lhs)
                                  (vl-idexpr-p lhs)
                                  (vl-expr-welltyped-p lhs)))
  :parents (vl-flopcodestmt-p)
  :inline t
  (if (vl-fast-compoundstmt-p x)
      (vl-assignstmt->lvalue (vl-ifstmt->truebranch x))
    (vl-assignstmt->lvalue x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p))))
  ///
  (defthm vl-flopcodestmt->lhs-width
    (implies (and (force (vl-stmt-p x))
                  (force (vl-flopcodestmt-p x)))
             (posp (vl-expr->finalwidth (vl-flopcodestmt->lhs x))))
    :rule-classes :type-prescription))

(define vl-flopcodestmt->rhs ((x (and (vl-stmt-p x)
                                      (vl-flopcodestmt-p x))))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (vl-expr-welltyped-p rhs)
                     (equal (vl-expr->finalwidth rhs)
                            (vl-expr->finalwidth (vl-flopcodestmt->lhs x)))))
  :parents (vl-flopcodestmt-p)
  :inline t
  (if (vl-fast-compoundstmt-p x)
      (vl-assignstmt->expr (vl-ifstmt->truebranch x))
    (vl-assignstmt->expr x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p
                                       vl-flopcodestmt->lhs)))))

(define vl-flopcodestmt->delay ((x (and (vl-stmt-p x)
                                        (vl-flopcodestmt-p x))))
  :returns ticks
  :parents (vl-flopcodestmt-p)
  :inline t
  (b* (((vl-assignstmt ass) (if (vl-fast-compoundstmt-p x)
                                (vl-ifstmt->truebranch x)
                              x)))
    (and ass.ctrl
         (vl-simpledelaycontrol->ticks ass.ctrl)))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p))))
  ///
  (defthm vl-maybe-natp-of-vl-flopcodestmt->delay
    (vl-maybe-natp (vl-flopcodestmt->delay x))
    :rule-classes :type-prescription))


(deflist vl-flopcodestmtlist-p (x)
  (vl-flopcodestmt-p x)
  :guard (vl-stmtlist-p x)
  :elementp-of-nil nil
  :parents (flopcode))

(defprojection vl-flopcodestmtlist->tests (x)
  (vl-flopcodestmt->test x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :parents (vl-flopcodestmtlist-p))

(defprojection vl-flopcodestmtlist->lhses (x)
  (vl-flopcodestmt->lhs x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-exprlist-p
  :parents (vl-flopcodestmtlist-p)
  :rest
  ((defthm vl-idexprlist-p-of-vl-flopcodestmtlist->lhses
     (implies (and (force (vl-stmtlist-p x))
                   (force (vl-flopcodestmtlist-p x)))
              (vl-idexprlist-p (vl-flopcodestmtlist->lhses x))))))

(defprojection vl-flopcodestmtlist->rhses (x)
  (vl-flopcodestmt->rhs x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-exprlist-p
  :parents (vl-flopcodestmtlist-p)
  :rest
  ((defthm vl-exprlist->finalwidths-of-vl-flopcodestmtlist->rhses
     ;; This holds because we require the widths to agree on the lhs/rhs in
     ;; vl-flopcodestmt-p.  This is important in vl-flopcode-next-expr.
     (implies (and (force (vl-stmtlist-p x))
                   (force (vl-flopcodestmtlist-p x)))
              (equal (vl-exprlist->finalwidths (vl-flopcodestmtlist->rhses x))
                     (vl-exprlist->finalwidths (vl-flopcodestmtlist->lhses x)))))))

(defprojection vl-flopcodestmtlist->delays (x)
  (vl-flopcodestmt->delay x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-maybe-nat-listp
  :parents (vl-flopcodestmtlist-p))



(define vl-flopcodeprog-p ((x vl-stmtlist-p))
  :parents (flopcode)
  :short "Extends the local @(see vl-flopcodestmtlist-p)s checks with the
global requirements for flopcode programs."
  (b* (((unless (vl-flopcodestmtlist-p x))
        nil)
       (lhses (vl-flopcodestmtlist->lhses x))
       ((unless lhses)
        ;; Not a valid flop program since there isn't even one statement.
        nil)
       (lhs1   (car lhses))
       (name1  (vl-idexpr->name lhs1))
       (width1 (vl-expr->finalwidth lhs1))
       (delays (vl-flopcodestmtlist->delays x))
       (delay1 (car delays)))
    (and (all-equalp name1  (vl-idexprlist->names lhses))
         (all-equalp width1 (vl-exprlist->finalwidths lhses))
         (all-equalp delay1 delays)))
  ///
  (defthm consp-when-vl-flopcodeprog-p
    (implies (vl-flopcodeprog-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-flopcodestmtlist-p-when-vl-flopcodeprog-p
    (implies (vl-flopcodeprog-p x)
             (vl-flopcodestmtlist-p x))))

(define vl-flopcodeprog->target ((x (and (vl-stmtlist-p x)
                                         (vl-flopcodeprog-p x))))
  :returns (target :hyp :fguard (and (vl-expr-p target)
                                     (vl-idexpr-p target)
                                     (vl-expr-welltyped-p target)))
  :parents (vl-flopcodeprog-p)
  :short "Get the target register from a valid flopcode program."
  :inline t
  (vl-flopcodestmt->lhs (car x))
  ///
  (defthm vl-expr->finalwidth-of-vl-flopcodeprog->target
    (implies (and (force (vl-stmtlist-p x))
                  (force (vl-flopcodeprog-p x)))
             (posp (vl-expr->finalwidth (vl-flopcodeprog->target x))))
    :rule-classes :type-prescription))

(define vl-flopcodeprog->delay ((x (and (vl-stmtlist-p x)
                                        (vl-flopcodeprog-p x))))
  :returns ticks
  :parents (vl-flopcodeprog-p)
  :short "Get the delay for each assignment in a valid flopcode program."
  :inline t
  (vl-flopcodestmt->delay (car x))
  ///
  (defthm vl-maybe-natp-of-vl-flopcodeprog->delay
    (vl-maybe-natp (vl-flopcodeprog->delay x))
    :rule-classes :type-prescription))

