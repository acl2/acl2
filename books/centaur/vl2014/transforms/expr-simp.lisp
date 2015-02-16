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
(include-book "../mlib/expr-tools")
(include-book "../mlib/fmt")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (enable tag-reasoning)))

(defsection expr-simp
  :parents (transforms)
  :short "Carry out basic expression simplification. (UNSOUND)"

  :long "<p>This transform does a lot of basic rewriting of expressions, e.g.,
it will eliminate double negations, propagate constants through ANDs, use
Demorgan's rule to simplify negated ANDs, pushing nots down into the branches
of ?: expressions, and so forth.</p>

<p><b>WARNING</b>: These transforms are almost certainly unsound in general.
For instance, even something as simple as removing double negatives isn't
stricly correct, @('~~A') will produce @('X') when @('A') is @('Z').  On the
other hand, these rewrites are <i>probably</i> okay if we only care about the
Boolean values of expressions.</p>

<p><b>BUT FOR SERIOUSLY -- WARNING</b>: I am really not too concerned with
soundness here.  There are probably many things that could go wrong
w.r.t. expression sizes, etc.  You should check that this produces reasonable
output using an equivalence checker.</p>")

(local (xdoc::set-default-parents expr-simp))

(local (defthm crock
         (implies (vl-expr-resolved-p x)
                  (eq (vl-expr-kind x) :atom))
         :hints(("Goal" :in-theory (enable vl-expr-resolved-p)))))

(define vl-expr-simp-unary-bitnot
  ((x    vl-expr-p     "Expression to rewrite, of the form ~FOO.")
   (args vl-exprlist-p "Its already-rewritten args."))
  :guard (and (not (vl-atom-p x))
              (equal (vl-nonatom->op x) :vl-unary-bitnot)
              (equal (len args) 1))
  :returns (new-x vl-expr-p)

  (b* ((arg (first args))

       ;; Reduce ~~A to A
       ((when (and (not (vl-atom-p arg))
                   (eq (vl-nonatom->op arg) :vl-unary-bitnot)))
        (first (vl-nonatom->args arg)))

       ;; Reduce ~1'b1 to 1'b0 and ~1'b0 to 1'b1
       ((when (and (vl-atom-p arg)
                   (vl-expr-resolved-p arg)
                   (or (eql (vl-resolved->val arg) 1)
                       (eql (vl-resolved->val arg) 0))
                   (equal (vl-expr->finalwidth x) 1)
                   (equal (vl-expr->finaltype x) :vl-unsigned)))
        (b* ((curr (vl-resolved->val arg))
             (ans  (if (eql curr 0)
                       |*sized-1'b1*|
                     |*sized-1'b0*|)))
          (vl-cw-ps-seq (vl-cw "NC Rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce ~(A ? B : C) to (A ? ~B : ~C)
       ((when (and (not (vl-atom-p arg))
                   (eq (vl-nonatom->op arg) :vl-qmark)))
        (b* (((list a b c) (vl-nonatom->args arg))
             (~b (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list b)
                                  :finalwidth (vl-expr->finalwidth b)
                                  :finaltype (vl-expr->finaltype b)))
             (~c (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list c)
                                  :finalwidth (vl-expr->finalwidth c)
                                  :finaltype (vl-expr->finaltype c)))
             (ans (change-vl-nonatom arg
                                     :args (list a ~b ~c))))
          (vl-cw-ps-seq (vl-cw "QM Rewrite ~a0 to ~a1!~%" x ans))
          ans))

       ;; Reduce ~(A & B) using demorgan's law, but only if one of A or B is a
       ;; negated expression (so that we think the negation will cancel on at
       ;; least one branch.)
       #||
       (thm (iff (not (and a b)) (or (not a) (not b))))
       ||#
       ((when (and (not (vl-atom-p arg))
                   (eq (vl-nonatom->op arg) :vl-binary-bitand)
                   ;; (let ((and-args (vl-nonatom->args arg)))
                   ;;   (or (and (vl-nonatom-p (first and-args))
                   ;;            (eq (vl-nonatom->op (first and-args)) :vl-unary-bitnot))
                   ;;       (and (vl-nonatom-p (second and-args))
                   ;;            (eq (vl-nonatom->op (second and-args)) :vl-unary-bitnot))))
                   ))
        (b* (((list a b) (vl-nonatom->args arg))
             (~a (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list a)
                                  :finalwidth (vl-expr->finalwidth a)
                                  :finaltype (vl-expr->finaltype a)))
             (~b (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list b)
                                  :finalwidth (vl-expr->finalwidth b)
                                  :finaltype (vl-expr->finaltype b)))
             (ans (change-vl-nonatom arg
                                     :op :vl-binary-bitor
                                     :args (list ~a ~b))))
          (vl-cw-ps-seq (vl-cw "DMA Rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce ~(A | B) using demorgan's law, but only if one of A or B is
       ;; a negated expression
       #||
       (thm (iff (not (or a b)) (and (not a) (not b))))
       ||#
       ((when (and (not (vl-atom-p arg))
                   (eq (vl-nonatom->op arg) :vl-binary-bitor)
                   ;; (let ((and-args (vl-nonatom->args arg)))
                   ;;   (or (and (vl-nonatom-p (first and-args))
                   ;;            (eq (vl-nonatom->op (first and-args)) :vl-unary-bitnot))
                   ;;       (and (vl-nonatom-p (second and-args))
                   ;;            (eq (vl-nonatom->op (second and-args)) :vl-unary-bitnot))))
                   ))
        (b* (((list a b) (vl-nonatom->args arg))
             (~a (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list a)
                                  :finalwidth (vl-expr->finalwidth a)
                                  :finaltype (vl-expr->finaltype a)))
             (~b (make-vl-nonatom :op :vl-unary-bitnot
                                  :args (list b)
                                  :finalwidth (vl-expr->finalwidth b)
                                  :finaltype (vl-expr->finaltype b)))
             (ans (change-vl-nonatom arg
                                     :op :vl-binary-bitand
                                     :args (list ~a ~b))))
          (vl-cw-ps-seq (vl-cw "DMO Rewrite ~a0 to ~a1~%" x ans))
          ans)))

    ;; Else, no rewrites to do.  Just install the new args.
    (change-vl-nonatom x :args args)))


(define vl-expr-simp-binary-bitand
  ((x    vl-expr-p     "Expression to rewrite, of the form @('a & b').")
   (args vl-exprlist-p "Its already-rewritten args."))
  :guard (and (not (vl-atom-p x))
              (equal (vl-nonatom->op x) :vl-binary-bitand)
              (equal (len args) 2))
  :returns (new-x vl-expr-p)
  (b* (((list arg1 arg2) args)

       ;; Reduce (A & 0) to 0
       ((when (and (vl-expr-resolved-p arg2)
                   (eql (vl-resolved->val arg2) 0)))
        (b* ((ans (change-vl-atom arg2
                                  :finaltype (vl-expr->finaltype x)
                                  :finalwidth (vl-expr->finalwidth x))))
          (vl-cw-ps-seq (vl-cw "AND0a rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (0 & A) to 0.
       ((when (and (vl-expr-resolved-p arg1)
                   (eql (vl-resolved->val arg1) 0)))
        (b* ((ans (change-vl-atom arg1
                                  :finaltype (vl-expr->finaltype x)
                                  :finalwidth (vl-expr->finalwidth x))))
          (vl-cw-ps-seq (vl-cw "AND0b rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (A & 1'b1) to A (for 1-bit A only)
       ((when (and (vl-expr-resolved-p arg2)
                   (eql (vl-resolved->val arg2) 1)
                   (equal (vl-expr->finalwidth x) 1)
                   (equal (vl-expr->finaltype x) :vl-unsigned)
                   (equal (vl-expr->finalwidth arg1) 1)
                   (equal (vl-expr->finaltype arg1) :vl-unsigned)))
        (b* ((ans (vl-expr-fix arg1)))
          (vl-cw-ps-seq (vl-cw "AND1a rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (1'b1 & A) to A (for 1-bit A only)
       ((when (and (vl-expr-resolved-p arg1)
                   (eql (vl-resolved->val arg1) 1)
                   (equal (vl-expr->finalwidth x) 1)
                   (equal (vl-expr->finaltype x) :vl-unsigned)
                   (equal (vl-expr->finalwidth arg2) 1)
                   (equal (vl-expr->finaltype arg2) :vl-unsigned)))
        (b* ((ans (vl-expr-fix arg2)))
          (vl-cw-ps-seq (vl-cw "AND1b rewrite ~a0 to ~a1~%" x ans))
          ans)))

    ;; Else, no rewrites to do.  Just install the new args.
    (change-vl-nonatom x :args args)))



(define vl-expr-simp-binary-bitor
  ((x    vl-expr-p     "Expression to rewrite, of the form FOO | BAR.")
   (args vl-exprlist-p "Its already-rewritten args."))
  :guard (and (not (vl-atom-p x))
              (equal (vl-nonatom->op x) :vl-binary-bitor)
              (equal (len args) 2))
  :returns (new-x vl-expr-p)
  (b* (((list arg1 arg2) args)

       ;; Reduce (A | 0) to A, for A of any width.
       ((when (and (vl-expr-resolved-p arg2)
                   (eql (vl-resolved->val arg2) 0)
                   (equal (vl-expr->finalwidth x) (vl-expr->finalwidth arg1))
                   (equal (vl-expr->finaltype x) (vl-expr->finaltype arg1))))
        (b* ((ans (vl-expr-fix arg1)))
          (vl-cw-ps-seq (vl-cw "ORa0 rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (0 | A) to A, for A of any width.
       ((when (and (vl-expr-resolved-p arg1)
                   (eql (vl-resolved->val arg1) 0)
                   (equal (vl-expr->finalwidth x) (vl-expr->finalwidth arg2))
                   (equal (vl-expr->finaltype x) (vl-expr->finaltype arg2))))
        (b* ((ans (vl-expr-fix arg2)))
          (vl-cw-ps-seq (vl-cw "OR0a rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (A | 1'b1) to 1'b1, for one-bit A.
       ((when (and (vl-expr-resolved-p arg2)
                   (eql (vl-resolved->val arg2) 1)
                   (equal (vl-expr->finalwidth x) 1)
                   (equal (vl-expr->finalwidth arg1) 1)
                   (equal (vl-expr->finalwidth arg2) 1)
                   (eq (vl-expr->finaltype x) :vl-unsigned)
                   (eq (vl-expr->finaltype arg1) :vl-unsigned)
                   (eq (vl-expr->finaltype arg2) :vl-unsigned)))
        (b* ((ans (vl-expr-fix arg2)))
          (vl-cw-ps-seq (vl-cw "ORa1 rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce (1'b1 | A) to 1'b1, for one-bit A
       ((when (and (vl-expr-resolved-p arg1)
                   (eql (vl-resolved->val arg1) 1)
                   (equal (vl-expr->finalwidth x) 1)
                   (equal (vl-expr->finalwidth arg1) 1)
                   (equal (vl-expr->finalwidth arg2) 1)
                   (eq (vl-expr->finaltype x) :vl-unsigned)
                   (eq (vl-expr->finaltype arg1) :vl-unsigned)
                   (eq (vl-expr->finaltype arg2) :vl-unsigned)))
        (b* ((ans (vl-expr-fix arg1)))
          (vl-cw-ps-seq (vl-cw "OR1a rewrite ~a0 to ~a1~%" x ans))
          ans)))

    ;; Else, no rewrites to do.  Just install the new args.
    (change-vl-nonatom x :args args)))



(define vl-expr-simp-qmark
  ((x    vl-expr-p     "Expression to rewrite, of the form FOO ? BAR : BAZ.")
   (args vl-exprlist-p "Its already-rewritten args."))
  :guard (and (not (vl-atom-p x))
              (equal (vl-nonatom->op x) :vl-qmark)
              (equal (len args) 3))
  :returns (new-x vl-expr-p)
  (b* (((list a b c) args)

       ;; Reduce ~A ? B : C to A ? C : B
       ((when (and (not (vl-atom-p a))
                   (eq (vl-nonatom->op a) :vl-unary-bitnot)))
        (b* (((list ~a b c) args)
             (a   (first (vl-nonatom->args ~a)))
             (ans (change-vl-nonatom x :args (list a c b))))
          (vl-cw-ps-seq (vl-cw "QM~ Rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce 1 ? B : C to B
       ((when (and (vl-expr-resolved-p a)
                   (eql (vl-resolved->val a) 1)
                   (equal (vl-expr->finalwidth x) (vl-expr->finalwidth b))
                   (equal (vl-expr->finaltype x) (vl-expr->finaltype b))))
        (b* ((ans (vl-expr-fix b)))
          (vl-cw-ps-seq (vl-cw "QM1 rewrite ~a0 to ~a1~%" x ans))
          ans))

       ;; Reduce 0 ? B : C to C
       ((when (and (vl-expr-resolved-p a)
                   (eql (vl-resolved->val a) 0)
                   (equal (vl-expr->finalwidth x) (vl-expr->finalwidth c))
                   (equal (vl-expr->finaltype x) (vl-expr->finaltype c))))
        (b* ((ans (vl-expr-fix c)))
          (vl-cw-ps-seq (vl-cw "QM0 rewrite ~a0 to ~a1~%" x ans))
          ans)))

    ;; Else, no rewrites to do.  Just install the new args.
    (change-vl-nonatom x :args args)))

(defines vl-expr-simp
  :short "Core routine to simplify expressions."
  (define vl-expr-simp
    ((x vl-expr-p))
    :returns (new-x vl-expr-p)
    :measure (vl-expr-count x)
    :verify-guards nil
    :flag :expr
    (b* ((x (vl-expr-fix x))
         ((when (vl-idexpr-p x))
          (b* ((name (vl-idexpr->name x))
               ((when (and (or (equal name "vdd0")
                               (equal name "vdd3"))
                           (equal (vl-expr->finalwidth x) 1)
                           (equal (vl-expr->finaltype x) :vl-unsigned)))
                |*sized-1'b1*|)
               ((when (and (equal name "vss0")
                           (equal (vl-expr->finalwidth x) 1)
                           (equal (vl-expr->finaltype x) :vl-unsigned)))
                |*sized-1'b0*|))
            ;; Otherwise leave it alone
            x))
         ((when (vl-fast-atom-p x))
          x)
         ((vl-nonatom x) x)
         (args (vl-exprlist-simp x.args))
         ((when (eq x.op :vl-unary-bitnot))  (vl-expr-simp-unary-bitnot x args))
         ((when (eq x.op :vl-binary-bitand)) (vl-expr-simp-binary-bitand x args))
         ((when (eq x.op :vl-binary-bitor))  (vl-expr-simp-binary-bitor x args))
         ((when (eq x.op :vl-qmark))         (vl-expr-simp-qmark x args))
         )
      ;; Else, nothing to do, just install the reweritten args
      (change-vl-nonatom x :args args)))

  (define vl-exprlist-simp
    ((x vl-exprlist-p))
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        nil
      (cons (vl-expr-simp (car x))
            (vl-exprlist-simp (cdr x)))))
  ///
  (verify-guards vl-expr-simp))


; We could do these reductions in more places, but mainly we care about
; assignments and instance arguments.

(define vl-assign-simp ((x vl-assign-p))
  :returns (new-x vl-assign-p)
  (change-vl-assign x :expr (vl-expr-simp (vl-assign->expr x))))

(defprojection vl-assignlist-simp ((x vl-assignlist-p))
  :returns (new-x vl-assignlist-p)
  (vl-assign-simp x))

(define vl-plainarg-simp ((x vl-plainarg-p))
  :returns (new-x vl-plainarg-p)
  (b* ((x (vl-plainarg-fix x))
       ((vl-plainarg x) x)
       ((unless (eq x.dir :vl-input))
        ;; Don't want to tamper with outputs/inouts, not that they should
        ;; have negations anyway...
        x)
       ((unless x.expr)
        x))
    (change-vl-plainarg x :expr (vl-expr-simp x.expr))))

(defprojection vl-plainarglist-simp ((x vl-plainarglist-p))
  :returns (new-x vl-plainarglist-p)
  (vl-plainarg-simp x))

(define vl-modinst-simp ((x vl-modinst-p))
  :returns (new-x vl-modinst-p)
  (b* ((x (vl-modinst-fix x))
       ((vl-modinst x) x))
    (vl-arguments-case x.portargs
      :vl-arguments-named
      ;; Not resolved, don't modify
      x
      :vl-arguments-plain
      (b* ((plainargs (vl-plainarglist-simp x.portargs.args))
           (args      (make-vl-arguments-plain :args plainargs)))
        (change-vl-modinst x :portargs args)))))

(defprojection vl-modinstlist-simp ((x vl-modinstlist-p))
  :returns (new-x vl-modinstlist-p)
  (vl-modinst-simp x))

(define vl-module-simp ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x))
    (change-vl-module x
                      :assigns (vl-assignlist-simp x.assigns)
                      :modinsts (vl-modinstlist-simp x.modinsts))))

(defprojection vl-modulelist-simp ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-simp x))

(define vl-design-simp
  :short "Top-level @(see expr-simp) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-simp x.mods))))


