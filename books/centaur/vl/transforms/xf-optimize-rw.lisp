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
(local (include-book "../util/arithmetic"))

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
   (mod    "Module where this expression takes place."
           vl-module-p)
   (ialist "For fast lookups within @('mod')."
           (equal ialist (vl-moditem-alist mod)) ))
  :guard (or (not (vl-op-arity op))
             (eql (len args) (vl-op-arity op)))
  :returns (new-expr?
            "NIL if we have no optimizations to make, or a new expression which
             is to replace @('OP(ARGS)').  For correctness, this new expression
             must be semantically equal to OP(ARGS) in this context."
            (equal (vl-expr-p new-expr?)
                   (if new-expr? t nil))
            :hyp :fguard)
  :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity)))

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
           (vl-find-net/reg-range name mod ialist)))
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
          ((mv successp range) (vl-find-net/reg-range name mod ialist)))

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
     nil)))

(defines vl-expr-optimize
  :short "Optimize sub-expressions throughout an expression."
  :long "<p>The use of @('changedp') is only to avoid re-consing expressions
  that aren't being optimized.</p>"

  (define vl-expr-optimize
    ((x      vl-expr-p)
     (mod    vl-module-p)
     (ialist (equal ialist (vl-moditem-alist mod))))
    :returns (mv (changedp booleanp :rule-classes :type-prescription)
                 (new-x    vl-expr-p :hyp :fguard))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    (b* (((when (vl-fast-atom-p x))
          (mv nil x))
         (op                            (vl-nonatom->op x))
         (args                          (vl-nonatom->args x))
         ((mv args-changedp args-prime) (vl-exprlist-optimize args mod ialist))
         (candidate                     (vl-op-optimize op args-prime mod ialist))
         ((when candidate)
          (mv t candidate))
         ((when args-changedp)
          (mv t (change-vl-nonatom x :args args-prime))))
      (mv nil x)))

  (define vl-exprlist-optimize
    ((x      vl-exprlist-p)
     (mod    vl-module-p)
     (ialist (equal ialist (vl-moditem-alist mod))))
    :returns
    (mv (changedp booleanp :rule-classes :type-prescription)
        (new-x    (and (implies (and (force (vl-exprlist-p x))
                                     (force (vl-module-p mod))
                                     (force (equal ialist (vl-moditem-alist mod))))
                                (vl-exprlist-p new-x))
                       (equal (len new-x) (len x)))))
    :measure (two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (mv nil nil))
         ((mv car-changedp car-prime) (vl-expr-optimize (car x) mod ialist))
         ((mv cdr-changedp cdr-prime) (vl-exprlist-optimize (cdr x) mod ialist)))
      (mv (or car-changedp cdr-changedp)
          (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-expr-optimize))

(defmacro def-vl-optimize (name type body)
  `(define ,name
     :short ,(cat "Optimize expressions throughout a @(see " (symbol-name type) ").")
     ((x      ,type)
      (mod    vl-module-p)
      (ialist (equal ialist (vl-moditem-alist mod))))
     :returns
     (mv (changedp booleanp :rule-classes :type-prescription)
         (new-x    ,type    :hyp :fguard))
     (declare (ignorable x mod ialist))
     ,body))

(defmacro def-vl-optimize-list (name list-type element-name)
  `(define ,name
     :short ,(cat "Optimize expressions throughout a @(see "
                  (symbol-name list-type) ").")
     ((x      ,list-type)
      (mod    vl-module-p)
      (ialist (equal ialist (vl-moditem-alist mod))))
     :returns
     (mv (changedp booleanp :rule-classes :type-prescription)
         (new-x    ,list-type :hyp :fguard))
     (b* (((when (atom x))
           (mv nil nil))
          ((mv car-changedp car-prime) (,element-name (car x) mod ialist))
          ((mv cdr-changedp cdr-prime) (,name (cdr x) mod ialist)))
       (mv (or car-changedp cdr-changedp)
           (cons car-prime cdr-prime)))
     ///
     (defmvtypes ,name (nil true-listp))))

(def-vl-optimize vl-assign-optimize vl-assign-p
  (b* (((mv lvalue-changedp lvalue-prime)
        (vl-expr-optimize (vl-assign->lvalue x) mod ialist))
       ((mv expr-changedp expr-prime)
        (vl-expr-optimize (vl-assign->expr x) mod ialist))
       ((when (or lvalue-changedp expr-changedp))
        (mv t (change-vl-assign x :lvalue lvalue-prime :expr expr-prime))))
    (mv nil x)))

(def-vl-optimize-list vl-assignlist-optimize vl-assignlist-p
  vl-assign-optimize)

(def-vl-optimize vl-plainarg-optimize vl-plainarg-p
  (b* ((expr (vl-plainarg->expr x))
       ((unless expr)
        (mv nil x))
       ((mv changedp expr-prime)
        (vl-expr-optimize expr mod ialist)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-plainarg x :expr expr-prime)))))

(def-vl-optimize-list vl-plainarglist-optimize vl-plainarglist-p
  vl-plainarg-optimize)

(def-vl-optimize vl-namedarg-optimize vl-namedarg-p
  (b* ((expr (vl-namedarg->expr x))
       ((unless expr)
        (mv nil x))
       ((mv changedp expr-prime)
        (vl-expr-optimize expr mod ialist)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-namedarg x :expr expr-prime)))))

(def-vl-optimize-list vl-namedarglist-optimize vl-namedarglist-p
  vl-namedarg-optimize)

(def-vl-optimize vl-arguments-optimize vl-arguments-p
  (b* ((namedp (vl-arguments->namedp x))
       (args   (vl-arguments->args x))
       ((mv changedp args-prime) (if namedp
                                     (vl-namedarglist-optimize args mod ialist)
                                   (vl-plainarglist-optimize args mod ialist))))
      (if (not changedp)
          (mv nil x)
        (mv t (vl-arguments namedp args-prime)))))

(def-vl-optimize vl-modinst-optimize vl-modinst-p
  (b* (((mv changedp args-prime)
        (vl-arguments-optimize (vl-modinst->portargs x) mod ialist)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-modinst x :portargs args-prime)))))

(def-vl-optimize-list vl-modinstlist-optimize vl-modinstlist-p
  vl-modinst-optimize)

(def-vl-optimize vl-gateinst-optimize vl-gateinst-p
  (b* (((mv changedp args-prime)
        (vl-plainarglist-optimize (vl-gateinst->args x) mod ialist)))
      (if (not changedp)
          (mv nil x)
        (mv t (change-vl-gateinst x :args args-prime)))))

(def-vl-optimize-list vl-gateinstlist-optimize vl-gateinstlist-p
  vl-gateinst-optimize)

(define vl-module-optimize ((x vl-module-p))
  :short "Optimize expressions throughout a module."
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((when (vl-module->hands-offp x))
        x)
       (ialist                            (vl-moditem-alist x))
       ((mv modinsts-changedp modinsts)   (vl-modinstlist-optimize (vl-module->modinsts x) x ialist))
       ((mv gateinsts-changedp gateinsts) (vl-gateinstlist-optimize (vl-module->gateinsts x) x ialist))
       ((mv assigns-changedp assigns)     (vl-assignlist-optimize (vl-module->assigns x) x ialist))
       (-                                 (flush-hons-get-hash-table-link ialist)))
    (if (or modinsts-changedp gateinsts-changedp assigns-changedp)
        (change-vl-module x
                          :modinsts modinsts
                          :gateinsts gateinsts
                          :assigns assigns)
      x)))

(defprojection vl-modulelist-optimize (x)
  (vl-module-optimize x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-optimize
  :short "Top-level @(see optimize) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-optimize x.mods))))
