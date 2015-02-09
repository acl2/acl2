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
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/allexprs")
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/hid-tools")
(include-book "../../mlib/strip")
(local (include-book "../../util/arithmetic"))

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
  (b* (((when (vl-atom-p x))
        nil)
       ((vl-nonatom x)))
    (case x.op
      ((:vl-unary-preinc :vl-unary-postinc :vl-unary-predec :vl-unary-postdec
        :vl-binary-assign
        :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign)
       t)
      (otherwise
       nil)))
  ///
  (defthm vl-incexpr-p-when-vl-atom-p
    (implies (vl-atom-p x)
             (equal (vl-incexpr-p x)
                    nil))))

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
  (case (vl-nonatom->op x)
    ((:vl-unary-postinc :vl-unary-postdec) t)
    (otherwise nil)))

(define vl-incexpr->lhsexpr
  :short "Get the lvalue part from an increment, decrement, or assignment expression."
  ((x vl-expr-p))
  :guard (vl-incexpr-p x)
  :returns (lhs vl-expr-p)
  :inline t
  :prepwork ((local (in-theory (enable vl-incexpr-p))))
  (vl-expr-fix (first (vl-nonatom->args x))))


(defval *vl-incexpr-1*
  :parents (vl-incexpr->rhsexpr)
  :short "The literal @('1') we use when translating increment/decrement
expressions."

  :long "<p>Sizing and signedness is very subtle here.  If we're going to
translate an expression like @('a++') into @('a + 1'), what do we mean by
@('1')?  Is it a signed or unsigned 1, and does its width matter?  These kinds
of things would normally be very scary.</p>

<p>We are spared from serious complications here because of how we are going to
use the rhs expression.  Basically we're going to pull things like @('a++') out
of whatever expression they are used in, and convert them into \"pre\"
assignments of the form:</p>

@({  a = a + 1; })

<p>It wouldn't work to use a signed @('1'sb1') here, because when @('a') is
wide this would get sign-extended and that would not be right.</p>

<p>However, using an unsigned @('1'b1') fortunately happens to work out.  If
@('a') is unsigned then it's clearly okay to add or subtract an unsigned
@('1').  If instead @('a') is signed, then we're (oddly) going to end up
interpreting it as unsigned, but that's okay because in 2's complement
arithmetic, plus and minus are the same no matter whether they're signed or
unsigned, so it all works out correctly.</p>"

  (make-vl-atom :guts (make-vl-constint :origwidth 1
                                        :origtype :vl-unsigned
                                        :value 1
                                        :wasunsized nil)))

(define vl-incexpr->rhsexpr
  :short "Get a normalized right-hand side expression for an increment,
          decrement, or assignment expression."
  ((x vl-expr-p))
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
  (b* (((vl-nonatom x)))
    (case x.op
      (:vl-binary-assign
       (vl-expr-fix (second x.args)))
      ((:vl-unary-preinc :vl-unary-postinc)
       (make-vl-nonatom :op :vl-binary-plus
                        :args (list (first x.args) *vl-incexpr-1*)))
      ((:vl-unary-predec :vl-unary-postdec)
       (make-vl-nonatom :op :vl-binary-minus
                        :args (list (first x.args) *vl-incexpr-1*)))
      (otherwise
       (make-vl-nonatom :op
                        (case x.op
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
                        :args
                        ;; Example: x *= y --> (* x y)
                        x.args)))))

(defines vl-expr-has-incexprs-p
  :short "Check whether there are any increment, decrement, or assignment
  expressions within an expression."

  (define vl-expr-has-incexprs-p ((x vl-expr-p))
    :measure (vl-expr-count x)
    (cond ((vl-incexpr-p x)
           t)
          ((vl-atom-p x)
           nil)
          (t
           (vl-exprlist-has-incexprs-p (vl-nonatom->args x)))))

  (define vl-exprlist-has-incexprs-p ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-incexprs-p (car x))
          (vl-exprlist-has-incexprs-p (cdr x))))))


(defines vl-expr-increment-elim-aux
  :short "Core routine for eliminating increment, decrement, and assignment
expressions.  Doesn't try to defend against ambiguities."
  :verify-guards nil

  (define vl-expr-increment-elim-aux
    ((x    vl-expr-p
           "Expression to rewrite.  May contain increments, decrements, or
            assignment expressions.")
     (pre  vl-stmtlist-p
           "Accumulator.  List of assignment statements that should be done
            \"before\" the rewritten expression.  Backwards from the order
            in which they should occur.")
     (post vl-stmtlist-p
           "Accumulator.  List of assignment statements that should be done
            \"after\" the rewritten expression.  Backwards from the order
            in which they should occur.")
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
accumulators.  They need to be reversed and then processed in the resulting
order.  This is important to correctly handle things like:</p>

@({
     lhs = (a=(b=(c=0)));
})

<p>In particular, we recur down all the way to the @('(c=0)') term and cons
that assignment onto PRE.  Then as we unwind we cons @('(b=c)') onto PRE, and
then finally @('(a=b)'). So, the resulting PRE assignments we produce are in
backwards order, and they need to be reversed before we use them.</p>"

    (b* ((x    (vl-expr-fix x))
         (pre  (vl-stmtlist-fix pre))
         (post (vl-stmtlist-fix post))

         ((when (vl-atom-p x))
          ;; Can't have any incexprs, nothing to do here.
          (mv x pre post))

         ;; Nonatom case.  Rewrite the arguments first because if we run into
         ;; something like (a=(b++)), we want to dive all the way down into
         ;; b++, extract the b = b+1 assignment into POST, and then just deal
         ;; with (a=b).  That is, doing the interior arguments first ensures
         ;; that the rewritten args are increment/decrement/assignment free,
         ;; which is really handy.
         ((vl-nonatom x))
         ((mv args pre post) (vl-exprlist-increment-elim-aux x.args pre post loc))
         (new-x (change-vl-nonatom x :args args))
         ((unless (vl-incexpr-p new-x))
          ;; Not an increment/decrement/assignment expr, so now that we've
          ;; rewritten the args, there's nothing left to do.
          (mv new-x pre post))

         (lhs (vl-incexpr->lhsexpr new-x))
         (rhs (vl-incexpr->rhsexpr new-x))

         ((when (vl-incexpr-post-p new-x))
          ;; Post-increment/decrement operator like a++ or a--.
          ;;   - We'll rewrite X to just be A, because the current expression
          ;;     needs to read its current value.
          ;;   - We add a POST assignment:
          ;;     - LHS is a.
          ;;     - RHS is a + 1 or a - 1 as appropriate.
          (mv lhs pre (cons (make-vl-assignstmt :type :vl-blocking
                                                :lvalue lhs
                                                :expr rhs
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
                                    :expr rhs
                                    :loc loc)
                pre)
          post)))

  (define vl-exprlist-increment-elim-aux
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
          (mv nil
              (vl-stmtlist-fix pre)
              (vl-stmtlist-fix post)))
         ((mv car pre post) (vl-expr-increment-elim-aux (car x) pre post loc))
         ((mv cdr pre post) (vl-exprlist-increment-elim-aux (cdr x) pre post loc)))
      (mv (cons car cdr) pre post)))

  ///
  (verify-guards vl-expr-increment-elim-aux)
  (deffixequiv-mutual vl-expr-increment-elim-aux))

(define vl-expr-increment-elim
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
  :measure (vl-expr-count x)
  (b* (((unless (vl-expr-has-incexprs-p x))
        ;; Optimization.  There aren't any increment/decrement operators
        ;; anywhere in here, so we don't need to recons anything.
        (mv (vl-expr-fix x) nil nil))
       ((mv new-x pre-rev post-rev)
        (vl-expr-increment-elim-aux x nil nil loc)))
    (mv new-x (rev pre-rev) (rev post-rev))))


(defines vl-expr-incexprs
  :short "Gather all increment/decrement/assignment expressions from
an expression."
  (define vl-expr-incexprs ((x vl-expr-p))
    :returns (incexprs (and (vl-exprlist-p incexprs)
                            (vl-incexprlist-p incexprs)))
    :measure (vl-expr-count x)
    :verify-guards nil
    (b* ((x (vl-expr-fix x))
         ((when (vl-atom-p x))
          nil)
         ((vl-nonatom x))
         (sub (vl-exprlist-incexprs x.args))
         ((when (vl-incexpr-p x))
          (cons x sub)))
      sub))

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

(define vl-prohibit-incexprs ((ctx      vl-context-p)
                              (x        vl-exprlist-p)
                              (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((incexprs (vl-exprlist-incexprs x))
       ((when (atom incexprs))
        (ok)))
    (fatal :type :vl-illegal-incexpr
           :msg  "~a0: increment, decrement, and internal assignment expressions ~
                  like (a=b) or (a+=b) are not allowed here, but found ~a1."
           :args (list ctx (car incexprs)))))

(defmacro def-vl-prohibit-incexprs (name)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type     (mksym name '-p))
       (fix      (mksym name '-fix))
       (allexprs (mksym name '-allexprs))
       (fn       (mksym name '-prohibit-incexprs)))
    `(define ,fn ((x ,type) &key ((warnings vl-warninglist-p) 'warnings))
       :returns (new-warnings vl-warninglist-p)
       (b* ((x (,fix x)))
         (vl-prohibit-incexprs (vl-context x) (,allexprs x) warnings)))))

(defmacro def-vl-prohibit-incexprs-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type    (mksym name '-p))
       (fn      (mksym name '-prohibit-incexprs))
       (elem-fn (mksym element '-prohibit-incexprs)))
    `(define ,fn
       ((x ,type) &key ((warnings vl-warninglist-p) 'warnings))
       :returns (new-warnings vl-warninglist-p)
       (b* (((when (atom x))
             (ok))
            (warnings (,elem-fn (car x))))
         (,fn (cdr x))))))

(def-vl-prohibit-incexprs vl-port)
(def-vl-prohibit-incexprs-list vl-portlist :element vl-port)

(def-vl-prohibit-incexprs vl-portdecl)
(def-vl-prohibit-incexprs-list vl-portdecllist :element vl-portdecl)

(def-vl-prohibit-incexprs vl-vardecl)
(def-vl-prohibit-incexprs-list vl-vardecllist :element vl-vardecl)

(def-vl-prohibit-incexprs vl-paramdecl)
(def-vl-prohibit-incexprs-list vl-paramdecllist :element vl-paramdecl)

(def-vl-prohibit-incexprs vl-assign)
(def-vl-prohibit-incexprs-list vl-assignlist :element vl-assign)

(def-vl-prohibit-incexprs vl-alias)
(def-vl-prohibit-incexprs-list vl-aliaslist :element vl-alias)



(define vl-module-increment-elim ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (warnings x.warnings)
       ;; Imports have no expressions, nothing to do there
       (warnings (vl-portlist-prohibit-incexprs      x.ports))
       (warnings (vl-portdecllist-prohibit-incexprs  x.portdecls))
       (warnings (vl-vardecllist-prohibit-incexprs   x.vardecls))
       (warnings (vl-paramdecllist-prohibit-incexprs x.paramdecls))
       ;; bozo support functions
       ;; bozo support tasks
       (warnings (vl-assignlist-prohibit-incexprs    x.assigns))
       (warnings (vl-aliaslist-prohibit-incexprs     x.aliases))

       )
    

    ;; (VL-FUNDECLLIST-P FUNDECLS)
    ;; (VL-TASKDECLLIST-P TASKDECLS)
    ;; (VL-ASSIGNLIST-P ASSIGNS)
    ;; (VL-ALIASLIST-P ALIASES)
    ;; (VL-MODINSTLIST-P MODINSTS)
    ;; (VL-GATEINSTLIST-P GATEINSTS)
    ;; (VL-ALWAYSLIST-P ALWAYSES)
    ;; (VL-INITIALLIST-P INITIALS)
    ;; (VL-GENELEMENTLIST-P GENERATES)
    (cw "BOZO implement vl-module-increment-elim.")
    (change-vl-module x
                      :warnings warnings)))

(defprojection vl-modulelist-increment-elim ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-increment-elim x))

(define vl-design-increment-elim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (warnings x.warnings)
       (mods                    (vl-modulelist-increment-elim x.mods))
       ((mv warnings fundecls)  (vl-fundecllist-increment-elim x.fundecls))
       ((mv warnings taskdecls) (vl-taskdecllist-increment-elim x.taskdecls))

        
       )
    (change-vl-design x
                      :mods mods
                      :fun
                      

       
  (progn$
   (cw "BOZO implement increment elim.")
   (vl-design-fix x)))


