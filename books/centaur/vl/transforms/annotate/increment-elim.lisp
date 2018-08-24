; VL Verilog Toolkit
; Copyright (C) 2008-2016 Centaur Technology
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
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/ctxexprs")
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/hid-tools")
(include-book "../../mlib/strip")
(include-book "../../util/cwtime")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc increment-elim
  :parents (annotate)
  :short "Split increment, decrement, and assignment operators out of
expressions and into separate statements."

  :long "<h3>Introduction</h3>

<p>SystemVerilog-2012 adds C-style increment, decrement, and intra-expression
assignment operators.  Per Section 11.4.1 and 11.4.2, these expressions are to
behave like blocking assignments.</p>

<p>In this transform, our basic goal is to eliminate these operators by
splitting them out into separate, explicit assignment statements.  For
instance, we want to do rewrites like this:</p>

@({
     begin                           begin
       a = (i++) + 2;         --->      a = i + 2;
     end                                i = i + 1; //  post increment
                                     end
})

<p>Something tricky is that these operators are permitted in <b>all</b>
expressions, but they only make sense in certain contexts like procedural
statements.  For instance, it doesn't make any sense to use an increment
operator in a continuous assignment statement like</p>

@({
     assign w1 = w2++;
})

<p>because there's no notion of \"before\" or \"after\" this assignment and no
way to control when or how often a continuous assignment gets executed.  If
this sort of thing were legal, at best it would do something like increment
@('w2') by some unknown amount.  We find that tools such as NCVerilog and VCS
prohibit many such uses of @('++') and @('--'), and we do not want to permit
them either.</p>

<p>So our goal in this transform is actually to do two things.  First, we want
to translate any valid uses of these operators into ordinary blocking
assignments.  Second, we want to identify any invalid uses of these operators
and, if we find any, cause corresponding fatal warnings.</p>

<p>Even when these operators are used in valid contexts, SystemVerilog may not
guarantee what behavior is supposed to occur.  For instance, if we're in some
procedural block and we run across a statement like</p>

@({
     i = 5;
     j = i++ + (i = i - 1);
})

<p>then we don't know what value will get assigned to @('j') because
SystemVerilog leaves undefined the relative ordering of the @('i++') and @('i =
i - 1') expressions.  To reduce the possibility of different interpretations by
different tools, we try to recognize these sorts of situations and cause fatal
errors when there can be confusion.</p>")

(local (xdoc::set-default-parents increment-elim))

(define vl-incexpr-p ((x vl-expr-p))
  :returns (bool booleanp :rule-classes :type-prescription)
  :short "Recognizer for pre/post increment/decrement and assignment expressions."
  (vl-expr-case x
    :vl-unary
    (or (vl-unaryop-equiv x.op :vl-unary-preinc)
        (vl-unaryop-equiv x.op :vl-unary-predec)
        (vl-unaryop-equiv x.op :vl-unary-postinc)
        (vl-unaryop-equiv x.op :vl-unary-postdec))
    :vl-binary
    (or (vl-binaryop-equiv x.op :vl-binary-assign)
        (vl-binaryop-equiv x.op :vl-binary-plusassign)
        (vl-binaryop-equiv x.op :vl-binary-minusassign)
        (vl-binaryop-equiv x.op :vl-binary-timesassign)
        (vl-binaryop-equiv x.op :vl-binary-divassign)
        (vl-binaryop-equiv x.op :vl-binary-remassign)
        (vl-binaryop-equiv x.op :vl-binary-andassign)
        (vl-binaryop-equiv x.op :vl-binary-orassign)
        (vl-binaryop-equiv x.op :vl-binary-xorassign)
        (vl-binaryop-equiv x.op :vl-binary-shlassign)
        (vl-binaryop-equiv x.op :vl-binary-shrassign)
        (vl-binaryop-equiv x.op :vl-binary-ashlassign)
        (vl-binaryop-equiv x.op :vl-binary-ashrassign))
    :otherwise
    nil))

(deflist vl-incexprlist-p (x)
  :guard (vl-exprlist-p x)
  (vl-incexpr-p x))

(define vl-incexpr-post-p ((x vl-expr-p))
  :guard (vl-incexpr-p x)
  :returns (post-p booleanp :rule-classes :type-prescription)
  :short "Recognizer for post increment/decrement operators."
  :long "<p>Note that we treat all assignment operators as if they were
pre-increment operations, because they should \"return\" the updated value,
i.e., @('(a+=1)') behaves like @('++a') instead of @('a++').</p>"
  :prepwork ((local (in-theory (enable vl-incexpr-p))))
  :inline t
  (vl-expr-case x
    :vl-unary
    (or (vl-unaryop-equiv x.op :vl-unary-postinc)
        (vl-unaryop-equiv x.op :vl-unary-postdec))
    :otherwise
    nil))

(define vl-incexpr->lhsexpr ((x vl-expr-p))
  :short "Get the lvalue part from an increment, decrement, or assignment expression."
  :guard (vl-incexpr-p x)
  :returns (lhs vl-expr-p)
  :prepwork ((local (in-theory (enable vl-incexpr-p))))
  :inline t
  (vl-expr-case x
    :vl-unary x.arg
    :otherwise (vl-binary->left x)))


(defval *vl-incexpr-1*
  :parents (vl-incexpr->rhsexpr)
  :short "The literal @('1') we use when eliminating increment/decrement expressions."

  :long "<p>Context: we are converting real increment/decrement expressions,
i.e., @('a++'), @('++a'), @('a--'), or @('--a'), into assignments such as @('a
= a + 1'b1') or @('a = a - 1'b1').</p>

<p>Using @('1'b1') works correctly but sign/sizing deserves some justification.
If @('a') is unsigned, then the expression @('a + 1'b1') or @('a - 1'b1') are
clearly fine.  If @('a') is signed, then @('a + 1'b1') or @('a - 1'b1') are
going to be treated as unsigned additions.  But this is fine since addition and
subtraction are the same in 2's complement signed or unsigned arithmetic, and
these are the only operators we're dealing with.</p>"

  (hons-copy (make-vl-literal :val (make-vl-constint :value 1
                                                     :origwidth 1
                                                     :origsign :vl-unsigned))))

(define vl-incexpr->rhsexpr ((x vl-expr-p))
  :short "Get a normalized right-hand side expression for an increment,
          decrement, or assignment expression."
  :guard (vl-incexpr-p x)
  :returns (rhs vl-expr-p)
  :long "<p>Examples:</p>
@({
      (a=1)              -->  1
      a++, ++a, (a+=1)   -->  a + 1
      a--, --a, (a-=1)   -->  a - 1
      (a += b)           -->  a + b
      (a *= 7)           -->  a * 7
})"
  :prepwork ((local (in-theory (enable vl-incexpr-p))))
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-unary
      (case x.op
        ((:vl-unary-preinc :vl-unary-postinc)
         (make-vl-binary :op :vl-binary-plus
                         :left x.arg
                         :right *vl-incexpr-1*
                         :atts (list (cons "VL_INCREMENT" x))))
        ((:vl-unary-predec :vl-unary-postdec)
         (make-vl-binary :op :vl-binary-minus
                         :left x.arg
                         :right *vl-incexpr-1*
                         :atts (list (cons "VL_DECREMENT" x))))
        (otherwise
         (progn$ (impossible) x)))

      :vl-binary
      (case x.op
        (:vl-binary-assign x.right)
        (otherwise
         ;; Example: x *= y --> x * y
         (make-vl-binary :op (case x.op
                               (:vl-binary-plusassign  :vl-binary-plus)
                               (:vl-binary-minusassign :vl-binary-minus)
                               (:vl-binary-timesassign :vl-binary-times)
                               (:vl-binary-divassign   :vl-binary-div)
                               (:vl-binary-remassign   :vl-binary-rem)
                               (:vl-binary-andassign   :vl-binary-bitand)
                               (:vl-binary-orassign    :vl-binary-bitor)
                               (:vl-binary-xorassign   :vl-binary-xor)
                               (:vl-binary-shlassign   :vl-binary-shl)
                               (:vl-binary-shrassign   :vl-binary-shr)
                               (:vl-binary-ashlassign  :vl-binary-ashl)
                               (:vl-binary-ashrassign  :vl-binary-ashr))
                         :left  x.left
                         :right x.right
                         :atts (list (cons "VL_ASSIGNEXPR" x)))))

      :otherwise
      (progn$ (impossible) x))))

(defines vl-expr-has-incexprs-p
  :short "Check whether there are any increment, decrement, or assignment
          expressions within an expression."

  (define vl-expr-has-incexprs-p ((x vl-expr-p))
    :measure (vl-expr-count x)
    (or (vl-incexpr-p x)
        (vl-exprlist-has-incexprs-p (vl-expr->subexprs x))))

  (define vl-exprlist-has-incexprs-p ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-incexprs-p (car x))
          (vl-exprlist-has-incexprs-p (cdr x))))))

(define vl-maybe-expr-has-incexprs-p ((x vl-maybe-expr-p))
  (let ((x (vl-maybe-expr-fix x)))
    (if x
        (vl-expr-has-incexprs-p x)
      nil)))

(define vl-maybe-exprlist-has-incexprs-p ((x vl-maybe-exprlist-p))
  :measure (len x)
  (if (atom x)
      nil
    (or (vl-maybe-expr-has-incexprs-p (car x))
        (vl-maybe-exprlist-has-incexprs-p (cdr x)))))


(defines vl-expr-increwrite-aux
  :verify-guards nil

  (define vl-expr-increwrite-aux
    :short "Core routine for eliminating increment, decrement, and assignment
            expressions.  Doesn't try to defend against ambiguities."
    ((x    vl-expr-p
           "Expression to rewrite.  May contain increments, decrements, or
            assignment expressions.")
     (pre  vl-stmtlist-p
           "Accumulator.  List of assignment statements that should be done
            \"before\" the rewritten expression.  Backwards from the order
            in which they should occur.  This is subtle, see below.")
     (post vl-stmtlist-p
           "Accumulator.  List of assignment statements that should be done
            \"after\" the rewritten expression.  Order is probably not
            important assuming no ambiguities.")
     (loc  vl-location-p
           "Location to use for new assignments."))
    :returns
    (mv (new-x vl-expr-p
               "Rewritten version of @('x'), free of increment, decrement, and
                assignment operators.  Equivalent to @('x') assuming that:
                (1) the pre-increment stuff is done first, (2) the
                post-increment stuff is done afterwards, and (3) there are no
                ambiguities.")
        (pre   vl-stmtlist-p)
        (post  vl-stmtlist-p))
    :measure (vl-expr-count x)
    :long "<p>Note that the ordering of pre/post is subtle.  These are true
           accumulators.  They need to be reversed and then processed in the
           resulting order.  This is important to correctly handle things
           like:</p>

           @({ lhs1 = (a=(b=(c=0))); })

           <p>In particular, we first recur down all the way to the @('(c=0)')
           term and cons that assignment onto PRE.  Then as we unwind we cons
           @('(b=c)') onto PRE, and then finally @('(a=b)'). So, the resulting
           PRE assignments we produce are in backwards order, and they need to
           be reversed before we use them.</p>

           <p>Note that all fancy assignment-expression operators like @('+='),
           @('*='), etc., as well as the ordinary @('=') operator and act like
           pre-increment operators, i.e., they act like @('++a') instead of
           @('a++'), and hence contribute to the list of PRE assignments.  So
           the situation for</p>

           @({ lhs2 = (a += (b *= (c = 0))) ; })

           <p>is much like the above: we push onto PRE first @('c=0'), then
           @('b=b*c'), then finally @('a=a+b'), and it is critical that these
           be processed in the correct order.</p>

           <p>The only post operators are @('a++') and @('a--').  These can't
           be chained together in the same way as the pre-operators, so it
           seems unlikely that the order really matters.  For instance, if we
           have an expression like:</p>

           @({ lhs3 = a++ * b++ * c++; })

           <p>then it's fine to do the post-increments in any order.</p>"

    (b* ((x    (vl-expr-fix x))
         (pre  (vl-stmtlist-fix pre))
         (post (vl-stmtlist-fix post))
         ;; Rewrite the arguments first, because if we run into something like
         ;; (a=(b++)), we want to dive all the way down into b++, extract the b
         ;; = b+1 assignment into POST, and then just deal with (a=b).
         ((mv args pre post) (vl-exprlist-increwrite-aux (vl-expr->subexprs x) pre post loc))
         (new-x              (vl-expr-update-subexprs x args))
         ((unless (vl-incexpr-p new-x))
          ;; Not an increment/decrement/assignment expr, so now that we've
          ;; rewritten the args, there's nothing left to do.
          (mv new-x pre post))
         (lhs (vl-incexpr->lhsexpr new-x))
         (rhs (make-vl-rhsexpr :guts (vl-incexpr->rhsexpr new-x)))
         ((when (vl-incexpr-post-p new-x))
          ;; Post-increment/decrement operator like a++ or a--.
          ;;   - We'll rewrite X to just be A, because the current expression
          ;;     needs to read its current value.
          ;;   - We add a POST assignment:
          ;;     - LHS is a.
          ;;     - RHS is a + 1 or a - 1 as appropriate.
          (mv lhs pre (cons (make-vl-assignstmt :type :vl-blocking
                                                :lvalue lhs
                                                :rhs rhs
                                                :loc loc)
                            post))))
      ;; Otherwise, pre-operator like ++a, --a, a=5, a+=5, etc.
      ;;   - We'll rewrite X to just be A, because we'll assume the update
      ;;     is going to be done separately, before hand.
      ;;   - We'll add a PRE assignment:
      ;;      - LHS is a
      ;;      - RHS is a + 1, a - 1, 5, a + 5, etc., as appropriate.
      (mv lhs
          (cons (make-vl-assignstmt :type :vl-blocking
                                    :lvalue lhs
                                    :rhs rhs
                                    :loc loc)
                pre)
          post)))

  (define vl-exprlist-increwrite-aux
    ((x    vl-exprlist-p "Expressions to rewrite.")
     (pre  vl-stmtlist-p)
     (post vl-stmtlist-p)
     (loc  vl-location-p))
    :returns (mv (new-x (and (vl-exprlist-p new-x)
                             (equal (len new-x) (len x))))
                 (pre   vl-stmtlist-p)
                 (post  vl-stmtlist-p))
    :measure (vl-exprlist-count x)
    (b* (((when (atom x))
          (mv nil (vl-stmtlist-fix pre) (vl-stmtlist-fix post)))
         ((mv car pre post) (vl-expr-increwrite-aux (car x) pre post loc))
         ((mv cdr pre post) (vl-exprlist-increwrite-aux (cdr x) pre post loc)))
      (mv (cons car cdr) pre post)))
  ///
  (verify-guards vl-expr-increwrite-aux)
  (deffixequiv-mutual vl-expr-increwrite-aux))

(define vl-maybe-expr-increwrite-aux
  ((x    vl-maybe-expr-p)
   (pre  vl-stmtlist-p)
   (post vl-stmtlist-p)
   (loc  vl-location-p))
  :returns
  (mv (new-x vl-maybe-expr-p)
      (pre   vl-stmtlist-p)
      (post  vl-stmtlist-p))
  (if x
      (vl-expr-increwrite-aux x pre post loc)
    (mv nil
        (vl-stmtlist-fix pre)
        (vl-stmtlist-fix post))))

(define vl-maybe-exprlist-increwrite-aux
  ((x    vl-maybe-exprlist-p)
   (pre  vl-stmtlist-p)
   (post vl-stmtlist-p)
   (loc  vl-location-p))
  :returns (mv (new-x (and (vl-maybe-exprlist-p new-x)
                           (equal (len new-x) (len x))))
               (pre   vl-stmtlist-p)
               (post  vl-stmtlist-p))
  :measure (len x)
  (b* (((when (atom x))
        (mv nil (vl-stmtlist-fix pre) (vl-stmtlist-fix post)))
       ((mv car pre post) (vl-maybe-expr-increwrite-aux (car x) pre post loc))
       ((mv cdr pre post) (vl-maybe-exprlist-increwrite-aux (cdr x) pre post loc)))
    (mv (cons car cdr) pre post)))

(define vl-expr-increwrite
  :short "Main function for rewriting expressions."
  ((x    vl-expr-p
         "Expression to rewrite.  May contain increments, decrements, or
          assignment expressions.")
   (loc  vl-location-p
         "Location to use for new assignment statements."))
  :returns
  (mv (new-x vl-expr-p
             "Rewritten version of @('x'), free of increment, decrement, and
              assignment operators.  Equivalent to @('x') assuming that: (1)
              the pre-increment stuff is done first, (2) the post-increment
              stuff is done afterwards, and (3) there are no ambiguities.")
      (pre   vl-stmtlist-p
             "New assignments that must happen before @('new-x'), in the
              proper order that they should be performed in.")
      (post  vl-stmtlist-p
             "New assignments that must happen after @('new-x'), in the
              proper order that they should be performed in."))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  (b* ((x (vl-expr-fix x))
       ((unless (vl-expr-has-incexprs-p x))
        ;; Optimization.  There aren't any increment/decrement operators
        ;; anywhere in here, so we don't need to recons anything.
        (mv x nil nil))
       ((mv new-x pre-rev post-rev)
        (vl-expr-increwrite-aux x nil nil loc)))
    (mv new-x (rev pre-rev) (rev post-rev))))

(define vl-exprlist-increwrite
  :short "Main function for rewriting expression lists."
  ((x    vl-exprlist-p
         "Expressions to rewrite.  May contain increments, decrements, or
          assignment expressions.")
   (loc  vl-location-p
         "Location to use for new assignment statements."))
  :returns
  (mv (new-x vl-exprlist-p
             "Rewritten version of @('x'), free of increment, decrement, and
              assignment operators.  Equivalent to @('x') assuming that: (1)
              the pre-increment stuff is done first, (2) the post-increment
              stuff is done afterwards, and (3) there are no ambiguities.")
      (pre   vl-stmtlist-p
             "New assignments that must happen before @('new-x'), in the
              proper order that they should be performed in.")
      (post  vl-stmtlist-p
             "New assignments that must happen after @('new-x'), in the
              proper order that they should be performed in."))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  (b* ((x (vl-exprlist-fix x))
       ((unless (vl-exprlist-has-incexprs-p x))
        ;; Optimization.  There aren't any increment/decrement operators
        ;; anywhere in here, so we don't need to recons anything.
        (mv x nil nil))
       ((mv new-x pre-rev post-rev)
        (vl-exprlist-increwrite-aux x nil nil loc)))
    (mv new-x (rev pre-rev) (rev post-rev))))

(define vl-maybe-expr-increwrite
  ((x    vl-maybe-expr-p)
   (loc  vl-location-p))
  :returns
  (mv (new-x vl-maybe-expr-p)
      (pre   vl-stmtlist-p)
      (post  vl-stmtlist-p))
  (b* ((x (vl-maybe-expr-fix x))
       ((unless (vl-maybe-expr-has-incexprs-p x))
        ;; Optimization.  There aren't any increment/decrement operators
        ;; anywhere in here, so we don't need to recons anything.
        (mv x nil nil))
       ((mv new-x pre-rev post-rev)
        (vl-maybe-expr-increwrite-aux x nil nil loc)))
    (mv new-x (rev pre-rev) (rev post-rev))))

(define vl-maybe-exprlist-increwrite
  ((x    vl-maybe-exprlist-p)
   (loc  vl-location-p))
  :returns
  (mv (new-x vl-maybe-exprlist-p)
      (pre   vl-stmtlist-p)
      (post  vl-stmtlist-p))
  (b* ((x (vl-maybe-exprlist-fix x))
       ((unless (vl-maybe-exprlist-has-incexprs-p x))
        ;; Optimization.  There aren't any increment/decrement operators
        ;; anywhere in here, so we don't need to recons anything.
        (mv x nil nil))
       ((mv new-x pre-rev post-rev)
        (vl-maybe-exprlist-increwrite-aux x nil nil loc)))
    (mv new-x (rev pre-rev) (rev post-rev))))

(define vl-rhs-increwrite
  ((x   vl-rhs-p)
   (loc vl-location-p))
  :returns
  (mv (new-x vl-rhs-p)
      (pre   vl-stmtlist-p)
      (post  vl-stmtlist-p))
  (b* ((x (vl-rhs-fix x)))
    (vl-rhs-case x
      (:vl-rhsexpr
       (b* (((unless (vl-expr-has-incexprs-p x.guts))
             ;; Optimization.  There aren't any increment/decrement operators
             ;; anywhere in here, so we don't need to recons anything.
             (mv x nil nil))
            ((mv new-guts pre-rev post-rev)
             (vl-expr-increwrite-aux x.guts nil nil loc)))
         (mv (change-vl-rhsexpr x :guts new-guts)
             (rev pre-rev)
             (rev post-rev))))
      (:vl-rhsnew
       (b* (((mv new-arrsize pre1 post1) (vl-maybe-expr-increwrite x.arrsize loc))
            ((mv new-args pre2 post2)    (vl-exprlist-increwrite x.args loc)))
         (mv (change-vl-rhsnew x
                               :arrsize new-arrsize
                               :args new-args)
             (append-without-guard pre1 pre2)
             (append-without-guard post1 post2)))))))


(defines vl-stmt-increwrite

  (define vl-stmtlist-increwrite ((x vl-stmtlist-p))
    :returns (new-x vl-stmtlist-p)
    :measure (two-nats-measure (vl-stmtlist-count x) 0)
    :verify-guards nil
    (b* (((when (atom x))
          nil)
         ((mv new-car pre post) (vl-stmt-increwrite (car x))))
      (append pre
              (list new-car)
              post
              (vl-stmtlist-increwrite (cdr x)))))

  (define vl-stmt-increwrite-flat ((x vl-stmt-p))
    :returns (new-x vl-stmt-p "Possibly a new begin/end block if necessary.")
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* (((mv new-x pre post) (vl-stmt-increwrite x))
         ((when (and (not pre)
                     (not post)))
          ;; Nothing much to do.
          new-x)
         (stmts (append pre (list new-x) post)))
      (make-vl-blockstmt :blocktype :vl-beginend
                         :stmts stmts)))

  (define vl-caselist-increwrite ((x vl-caselist-p))
    :returns (new-x vl-caselist-p)
    :measure (two-nats-measure (vl-caselist-count x) 0)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          nil)
         ;; Note that we don't allow increments in the match-exprs.  See the
         ;; commentary in :vl-casestmt below for more on this.
         ((cons match-exprs body) (car x))
         (new-body (vl-stmt-increwrite-flat body)))
      (cons (cons match-exprs new-body)
            (vl-caselist-increwrite (cdr x)))))

  (define vl-stmt-increwrite ((x vl-stmt-p))
    :returns (mv (new-x vl-stmt-p
                        "Updated version of @('x') with no internal
                         increment/decrement/assignment expressions.")
                 (pre   vl-stmtlist-p
                        "New statements that should be spliced into the current
                         statement list before @('new-x'), for pre-increments.
                         In proper order.")
                 (post  vl-stmtlist-p
                        "New statements that should be spliced into the current
                         statement list after @('new-x'), for post-increments.
                         In proper order."))
    :measure (two-nats-measure (vl-stmt-count x) 0)
    (b* ((x (vl-stmt-fix x)))
      (vl-stmt-case x
        :vl-nullstmt
        ;; The only case I really trust is correct. ;)
        (mv x nil nil)

        :vl-assignstmt
        ;; We probably don't want to allow increments in the lvalue, that seems
        ;; like it's a parse error?  See failtest/inc11.v.  It probably is also
        ;; not OK to have any increments in the control expression itself.  See
        ;; failtest/inc11b.v.  So, I think we only want to eliminate increments
        ;; that happen to be in x.expr, and not in x.lvalue or x.ctrl.
        (b* (((when (or (vl-assign-type-equiv x.type :vl-assign)
                        (vl-assign-type-equiv x.type :vl-force)))
              ;; SystemVerilog-2012 11.3.6 explicitly prohibits assignment
              ;; expressions in procedural continuous assignments.  I think
              ;; this prohibition should also apply to increment, etc.  So
              ;; since this is a procedural assignment, don't process the
              ;; expression.  See also failtest/inc11e.v and inc11f.v.
              (mv x nil nil))
             ((when x.ctrl)
              ;; NCV seems to prohibit increments in blocking assignments that
              ;; have an event control, i.e., see failtest/inc11c.v and
              ;; inc11d.v.  So we will too.
              (mv x nil nil))
             ;; Otherwise let's call it good.  Note that both NCV and VCS seem
             ;; to tolerate increments in non-blocking assignments, which may
             ;; not make a whole lot of sense.  I think, though, that we should
             ;; regard checking for blocking/nonblocking sanity as something
             ;; that is definitely beyond the scope of increwrite, so we'll
             ;; allow it too.
             ((mv new-rhs pre post) (vl-rhs-increwrite x.rhs x.loc))
             (new-x (change-vl-assignstmt x :rhs new-rhs)))
          (mv new-x pre post))

        :vl-callstmt
        ;; I don't think we want to allow increments in the ID or typearg?  But
        ;; it might be OK to have them there.  See failtest/inc12.v.  It seems
        ;; OK to have them in the arguments.
        (b* (((mv new-args pre post) (vl-maybe-exprlist-increwrite x.args x.loc))
             (new-x (change-vl-callstmt x :args new-args)))
          (mv new-x pre post))

        :vl-ifstmt
        ;; In principle we could allow increments in the condition, but this
        ;; seems error prone.  We'd probably have to put the post-increment
        ;; statements into the body expressions for both branches.  But even
        ;; then: are they supposed to take effect before ELSE branch conditions
        ;; are computed?  What a mess.  Let's just not allow them in the
        ;; condition for now.  See also failtest/inc13.v
        (b* ((new-true  (vl-stmt-increwrite-flat x.truebranch))
             (new-false (vl-stmt-increwrite-flat x.falsebranch))
             (new-x     (change-vl-ifstmt x
                                          :truebranch new-true
                                          :falsebranch new-false)))
          (mv new-x nil nil))

        :vl-casestmt
        ;; NCVerilog and VCS seem to allow increments to occur in the case
        ;; expression, i.e., case(foo++) is allowed.  They also seem allow
        ;; increments to occur in the case matching expressions, e.g., case
        ;; (foo) bar++: ans = 0; endcase.  However, it doesn't seem like this
        ;; really makes any sense and it's unclear how that's supposed to
        ;; affect the semantics of subsequent cases.  So let's not allow them
        ;; in these places, just as we don't allow them in if statement tests.
        (b* ((new-caselist (vl-caselist-increwrite x.caselist))
             (new-default  (vl-stmt-increwrite-flat x.default))
             (new-x        (change-vl-casestmt x
                                               :caselist new-caselist
                                               :default new-default)))
          (mv new-x nil nil))

        :vl-foreverstmt
        ;; Plausibly this is OK, for instance, VCS seems to accept constructs
        ;; like the following and seems to simulate them sensibly enough:
        ;;
        ;;   logic clk;
        ;;   integer i;
        ;;   initial begin
        ;;     clk = 0;
        ;;     i = 0;
        ;;     forever clk = #10 i++;
        ;;   end
        ;;
        ;; NCVerilog however complains about this---well, it complains about
        ;; all blocking assignments with delays).  If I take the delay out, NCV
        ;; seems to accept it but also seems to go into an infinite loop during
        ;; simulation.  Well whatever, let's go ahead and allow this; it's not
        ;; like we're going to do anything sensible with a foreverstmt anyway.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-foreverstmt x :body new-body)))
          (mv new-x nil nil))

        :vl-waitstmt
        ;; I think we should NOT allow increments in the condition for the same
        ;; reasons as we don't allow them in IF statements, etc.  Actually
        ;; maybe even for better reasons, e.g., the wait condition is similar
        ;; to an event expression, and SystemVerilog-2012 11.3.6 talks about
        ;; not allowing assignments in these...
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-waitstmt x :body new-body)))
          (mv new-x nil nil))

        :vl-repeatstmt
        ;; Disallow increments in the condition for similar reasons to wait.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-repeatstmt x :body new-body)))
          (mv new-x nil nil))

        :vl-returnstmt
        ;; It probably makes no sense to do a post-increment in a return
        ;; statement, but pre-increment stuff seems basically reasonable and,
        ;; anyway, it's seems no more wrong to write "return a++;" than to
        ;; write "return a; a = a+1".  So, tolerate increments here, and if we
        ;; want to check for dead code after returns, that'd be a fine linter
        ;; check to write some day.
        (b* (((unless x.val)
              ;; Just a plain "return" with no value, nothing to do.
              (mv x nil nil))
             ((mv new-val pre post) (vl-expr-increwrite x.val x.loc))
             (new-x                 (change-vl-returnstmt x :val new-val)))
          (mv new-x pre post))

        :vl-whilestmt
        ;; Hard to properly support increments in the condition.  Where to put
        ;; pre-assigns?  Where to put post-assigns?  (Into the loop body
        ;; probably, but also afterward?)  Just prohibit them for now.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-whilestmt x :body new-body)))
          (mv new-x nil nil))

        :vl-dostmt
        ;; Hard to properly support increments in the condition.  Where to put
        ;; pre-assigns?  Where to put post-assigns?  (Into the loop body
        ;; probably, but also afterward?)  Just prohibit them for now.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-dostmt x :body new-body)))
          (mv new-x nil nil))

        :vl-forstmt
        ;; The next steps expression is special and the parser handles it.  The
        ;; other initialization and loop test stuff seems tricky: where to put
        ;; pre/post assigns.  So only allow increments in the body, at least
        ;; for now.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-forstmt x :body new-body)))
          (mv new-x nil nil))

        :vl-foreachstmt
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-foreachstmt x :body new-body)))
          (mv new-x nil nil))

        :vl-blockstmt
        ;; BOZO do we need to be careful about fork/join blocks or anything
        ;; like that?
        ;;
        ;; BOZO?  We currently are paying no attention to the block's vardecls,
        ;; which will mean that we don't support reasonable looking things like
        ;;
        ;;     begin
        ;;       integer b = a++;
        ;;       ...
        ;;     end
        ;;
        ;; Probably we should be dealing with these in some systematic way.  It
        ;; might be that we can just globally walk through the block statements
        ;; and convert all the declaration-time assignments to be statements
        ;; that come before the rest of the block?  This is tricky due to parse
        ;; order stuff, but that might be the most sensible thing to do.
        (b* ((new-stmts (vl-stmtlist-increwrite x.stmts))
             (new-x     (change-vl-blockstmt x :stmts new-stmts)))
          (mv new-x nil nil))

        :vl-timingstmt
        ;; Things like @(posedge clk) <body>.  SystemVerilog-2012 11.3.6 pretty
        ;; clearly says we can't have increments in an event expression.  So
        ;; just process the body.
        (b* ((new-body (vl-stmt-increwrite-flat x.body))
             (new-x    (change-vl-timingstmt x :body new-body)))
          (mv new-x nil nil))

        ;; I don't think we want to allow increments in these
        :vl-disablestmt (mv x nil nil)
        :vl-deassignstmt (mv x nil nil)
        :vl-eventtriggerstmt (mv x nil nil)
        :vl-breakstmt (mv x nil nil)
        :vl-continuestmt (mv x nil nil)

        ;; I think these may have special other uses of the increment operator
        ;; for sequences, so it seems best to completely ignore these for now.
        :vl-assertstmt (mv x nil nil)
        :vl-cassertstmt (mv x nil nil))))
  ///
  (verify-guards vl-stmt-increwrite)
  (deffixequiv-mutual vl-stmt-increwrite))


(fty::defvisitor-template increwrite ((x :object))
  :returns (new-x :update)
  :type-fns ((vl-stmt vl-stmt-increwrite-flat)
             (vl-assertion-p :skip)
             (vl-cassertion-p :skip))
  :field-fns ((parse-temps :skip))
  :fnname-template <type>-increwrite)

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitors vl-increwrite
  :template increwrite
  :types (vl-design))

;; Any increments that survived that are bad, so warn about them.

(defines vl-expr-incexprs
  :short "Gather all increment/decrement/assignment expressions from an expression."
  (define vl-expr-incexprs ((x vl-expr-p))
    :returns (incexprs (and (vl-exprlist-p incexprs)
                            (vl-incexprlist-p incexprs)))
    :measure (vl-expr-count x)
    :verify-guards nil
    (b* ((x (vl-expr-fix x))
         ((when (vl-incexpr-p x))
          (cons x (vl-exprlist-incexprs (vl-expr->subexprs x)))))
      (vl-exprlist-incexprs (vl-expr->subexprs x))))

  (define vl-exprlist-incexprs ((x vl-exprlist-p))
    :returns (incexprs (and (vl-exprlist-p incexprs)
                            (vl-incexprlist-p incexprs)))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-incexprs (car x))
              (vl-exprlist-incexprs (cdr x)))))
  ///
  (verify-guards vl-expr-incexprs)
  (deffixequiv-mutual vl-expr-incexprs))

(define vl-expr-prohibit-incexprs ((x vl-expr-p)
                                   (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* ((incexprs (vl-expr-incexprs x))
       ((when (atom incexprs))
        (ok)))
    (fatal :type :vl-illegal-incexpr
           :msg "found an increment, decrement, or internal assignment expressions ~
                 where it is not allowed: ~a0."
           :args (list (car incexprs)))))

(local (in-theory (disable (tau-system)
                              vl-warninglist-p-when-not-consp
                              double-containment
                              vl-warninglist-p-when-subsetp-equal
                              member-equal-when-member-equal-of-cdr-under-iff
                              acl2::consp-when-member-equal-of-cons-listp
                              acl2::consp-when-member-equal-of-atom-listp
                              acl2::subsetp-when-atom-right
                              acl2::subsetp-when-atom-left)))

(def-visitor-exprcheck prohibit-incexprs :scopestack nil)

(define vl-design-increment-elim ((x vl-design-p))
  :returns (new-x vl-design-p)
  :short "Top-level @(see increment-elim) transform."
  (b* ((x (xf-cwtime (vl-design-increwrite x)))
       (x (xf-cwtime (vl-design-prohibit-incexprs x))))
    x))


