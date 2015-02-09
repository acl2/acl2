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
(include-book "../mlib/range-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection expression-optimization
  :parents (transforms)
  :short "Simplify expressions in a few trivial ways, mainly to clean up ugly
generated expressions."

  :long "<p>During the course of expression rewriting, splitting, and so on, we
often introduce intermediate expressions which are ugly, large, confusing,
etc.; We now introduce a routine to perform some really trivial optimizations,
which actually produce a pretty significant impact when applied throughout the
rewritten, split up, simplified tree.</p>

<p>WARNING: These are only valid on sized expressions!</p>")

(local (xdoc::set-default-parents expression-optimization))


(define vl-op-optimize
  :short "Core function in @(see expression-optimization)."
  ((op     "Some operator being applied to @('args')."
           vl-op-p)
   (args   vl-exprlist-p)
   (ss     vl-scopestack-p "Stack of scopes in which this occurs."))
  :guard (or (not (vl-op-arity op))
             (eql (len args) (vl-op-arity op)))
  :returns (new-expr?
            "NIL if we have no optimizations to make, or a new expression which
             is to replace @('OP(ARGS)').  For correctness, this new expression
             must be semantically equal to OP(ARGS) in this context."
            (equal (vl-expr-p new-expr?)
                   (if new-expr? t nil)))
  :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity vl-ops-table)))

  (b* ((op   (vl-op-fix op))
       (args (vl-exprlist-fix args)))
    (case op

; Hrmn, no, this optimization does not seem valid.  I think the testing code I
; used to convince myself it was okay had a bug in it.  This bug showed up when
; we started using plain assignments instead of inserting bufs everywhere; our
; buf insertion was probably masking the problem.
;
;    ((:vl-unary-bitor :vl-unary-bitand)
;     ;; A one-bit OR and AND are the identity.  Note that surprisingly a
;     ;; one-bit XOR is NOT the identity (at least according to Cadence), and
;     ;; produces an X instead of a Z when the input is Z.
;     (if (equal (vl-expr->finalwidth (first args)) 1)
;         (first args)
;       nil))

      (:vl-bitselect
       ;; Depending on the declaration of foo, foo[i] may be reducible to foo.
       (b* ((from  (first args))
            (what  (second args))
            ((unless (and (vl-idexpr-p from)
                          (vl-expr-resolved-p what)))
             nil)
            (name  (vl-idexpr->name from))
            (index (vl-resolved->val what))
            ((mv successp range)
             (vl-ss-find-range name ss)))
         (cond ((not successp)
                nil)

               ((and (not range)
                     (zp index))
                ;; foo[0] of a foo with no range --> foo
                from)

               ((and range
                     (vl-range-resolved-p range)
                     (eql index (vl-resolved->val (vl-range->msb range)))
                     (eql index (vl-resolved->val (vl-range->lsb range))))
                ;; foo[i] of a foo with range [i:i] --> foo
                from)

               (t nil))))

      (:vl-partselect-colon
       (b* ((from  (first args))
            (left  (second args))
            (right (third args))
            ((unless (and (vl-idexpr-p from)
                          (vl-expr-resolved-p left)
                          (vl-expr-resolved-p right)))
             nil)
            (name    (vl-idexpr->name from))
            (l-index (vl-resolved->val left))
            (r-index (vl-resolved->val right))
            ((mv successp range) (vl-ss-find-range name ss)))

         (cond ((not successp)
                nil)

               ((and (not range)
                     (zp l-index)
                     (zp r-index))
                ;; foo[0:0] of foo which has no range --> foo
                from)

               ((and range
                     (vl-range-resolved-p range)
                     (eql l-index (vl-resolved->val (vl-range->msb range)))
                     (eql r-index (vl-resolved->val (vl-range->lsb range))))
                ;; foo[left:right] from foo whose range is [left:right] --> foo
                from)

               ((equal l-index r-index)
                ;; foo[i:i] of any other foo -> foo[i]
                (make-vl-nonatom :op :vl-bitselect
                                 :finalwidth 1
                                 :finaltype :vl-unsigned
                                 :args (list from left)))

               (t nil))))

      (otherwise
       nil))))

(defines vl-expr-optimize
  :short "Optimize sub-expressions throughout an expression."
  :long "<p>The use of @('changedp') is only to avoid re-consing expressions
  that aren't being optimized.</p>"

  (define vl-expr-optimize
    ((x      vl-expr-p) (ss vl-scopestack-p))
    :returns (mv (changedp booleanp :rule-classes :type-prescription)
                 (new-x    vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    (b* ((x   (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (mv nil x))
         (op                            (vl-nonatom->op x))
         (args                          (vl-nonatom->args x))
         ((mv args-changedp args-prime) (vl-exprlist-optimize args ss))
         (candidate                     (vl-op-optimize op args-prime ss))
         ((when candidate)
          (mv t candidate))
         ((when args-changedp)
          (mv t (change-vl-nonatom x :args args-prime))))
      (mv nil x)))

  (define vl-exprlist-optimize
    ((x      vl-exprlist-p) (ss vl-scopestack-p))
    :returns
    (mv (changedp booleanp :rule-classes :type-prescription)
        (new-x    (and (vl-exprlist-p new-x)
                       (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    (b* (((when (atom x))
          (mv nil nil))
         ((mv car-changedp car-prime) (vl-expr-optimize (car x) ss))
         ((mv cdr-changedp cdr-prime) (vl-exprlist-optimize (cdr x) ss)))
      (mv (or car-changedp cdr-changedp)
          (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-expr-optimize)
  (deffixequiv-mutual vl-expr-optimize))

(defmacro def-vl-optimize (name body)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn   (mksym name '-optimize))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn
       :short ,(cat "Optimize expressions throughout a @(see " (symbol-name type) ").")
       ((x      ,type)
        (ss     vl-scopestack-p))
       :returns
       (mv (changedp booleanp :rule-classes :type-prescription)
           (new-x    ,type))
       (b* ((x (,fix x)))
         ,body))))

(defmacro def-vl-optimize-list (name element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn      (mksym name '-optimize))
       (elem-fn (mksym element '-optimize))
       (type    (mksym name '-p)))
    `(define ,fn
       :short ,(cat "Optimize expressions throughout a @(see " (symbol-name type) ").")
       ((x      ,type)
        (ss     vl-scopestack-p))
       :returns
       (mv (changedp booleanp :rule-classes :type-prescription)
           (new-x    ,type))
       (b* (((when (atom x))
             (mv nil nil))
            ((mv car-changedp car-prime) (,elem-fn (car x) ss))
            ((mv cdr-changedp cdr-prime) (,fn (cdr x) ss)))
         (mv (or car-changedp cdr-changedp)
             (cons car-prime cdr-prime)))
     ///
     (defmvtypes ,fn (nil true-listp)))))

(def-vl-optimize vl-assign
  (b* (((mv lvalue-changedp lvalue-prime)
        (vl-expr-optimize (vl-assign->lvalue x) ss))
       ((mv expr-changedp expr-prime)
        (vl-expr-optimize (vl-assign->expr x) ss))
       ((when (or lvalue-changedp expr-changedp))
        (mv t (change-vl-assign x :lvalue lvalue-prime :expr expr-prime))))
    (mv nil x)))

(def-vl-optimize-list vl-assignlist vl-assign)

(def-vl-optimize vl-plainarg
  (b* ((expr (vl-plainarg->expr x))
       ((unless expr)
        (mv nil x))
       ((mv changedp expr-prime)
        (vl-expr-optimize expr ss))
       ((unless changedp)
        (mv nil x)))
    (mv t (change-vl-plainarg x :expr expr-prime))))

(def-vl-optimize-list vl-plainarglist vl-plainarg)

(def-vl-optimize vl-namedarg
  (b* ((expr (vl-namedarg->expr x))
       ((unless expr)
        (mv nil x))
       ((mv changedp expr-prime)
        (vl-expr-optimize expr ss))
       ((unless changedp)
        (mv nil x)))
    (mv t (change-vl-namedarg x :expr expr-prime))))

(def-vl-optimize-list vl-namedarglist vl-namedarg)

(def-vl-optimize vl-arguments
  (vl-arguments-case x
    :vl-arguments-named
    (b* (((mv changedp args-prime) (vl-namedarglist-optimize x.args ss)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-arguments-named x :args args-prime))))
    :vl-arguments-plain
    (b* (((mv changedp args-prime) (vl-plainarglist-optimize x.args ss)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-arguments-plain x :args args-prime))))))

(def-vl-optimize vl-modinst
  (b* (((mv changedp args-prime)
        (vl-arguments-optimize (vl-modinst->portargs x) ss)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-modinst x :portargs args-prime)))))

(def-vl-optimize-list vl-modinstlist vl-modinst)

(def-vl-optimize vl-gateinst
  (b* (((mv changedp args-prime)
        (vl-plainarglist-optimize (vl-gateinst->args x) ss))
       ((unless changedp)
        (mv nil x)))
    (mv t (change-vl-gateinst x :args args-prime))))

(def-vl-optimize-list vl-gateinstlist vl-gateinst)

(define vl-module-optimize ((x vl-module-p) (ss vl-scopestack-p))
  :short "Optimize expressions throughout a module."
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       (ss (vl-scopestack-push x ss))
       ((when (vl-module->hands-offp x))
        x)
       ((mv modinsts-changedp modinsts)   (vl-modinstlist-optimize (vl-module->modinsts x) ss))
       ((mv gateinsts-changedp gateinsts) (vl-gateinstlist-optimize (vl-module->gateinsts x) ss))
       ((mv assigns-changedp assigns)     (vl-assignlist-optimize (vl-module->assigns x) ss)))
    (if (or modinsts-changedp gateinsts-changedp assigns-changedp)
        (change-vl-module x
                          :modinsts modinsts
                          :gateinsts gateinsts
                          :assigns assigns)
      x)))

(defprojection vl-modulelist-optimize ((x vl-modulelist-p) (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-optimize x ss))

(define vl-design-optimize
  :short "Top-level @(see optimize) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-optimize x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
