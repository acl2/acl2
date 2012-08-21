; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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


;                         EXPRESSION OPTIMIZATION
;
; During the course of expression rewriting, splitting, and so on, we often
; introduce intermediate expressions which are ugly, large, confusing, etc.; We
; now introduce a routine to perform some really trivial optimizations, which
; actually produce a pretty significant impact when applied throughout the
; rewritten, split up, simplified tree.

; WARNING: These are only valid on sized expressions!


(defund vl-op-optimize (op args mod ialist)
  (declare (xargs :guard (and (vl-op-p op)
                              (vl-exprlist-p args)
                              (or (not (vl-op-arity op))
                                  (equal (len args) (vl-op-arity op)))
                              (vl-module-p mod)
                              (equal ialist (vl-moditem-alist mod)))
                  :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity)))))

; This function is the core of our optimizations.  OP is some operator which is
; being applied to ARGS.  The operation takes place in within the module MOD
; (so we can look up ranges, etc.) and IALIST is the pre-computed ialist for
; MOD (so we can do these lookups quickly).

; We return either NIL (to indicate that we have no suggestions) or a new
; expression which is to replace OP(ARGS).  For correctness, this new
; expression must be semantically equal to OP(ARGS) in this context.

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
                     (equal index 0))
                ;; foo[0] of a foo with no range --> foo
                from)

               ((and range
                     (vl-range-resolved-p range)
                     (= index (vl-resolved->val (vl-range->msb range)))
                     (= index (vl-resolved->val (vl-range->lsb range))))
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
                     (equal l-index 0)
                     (equal r-index 0))
                ;; foo[0:0] of foo which has no range --> foo
                from)

               ((and range
                     (vl-range-resolved-p range)
                     (= l-index (vl-resolved->val (vl-range->msb range)))
                     (= r-index (vl-resolved->val (vl-range->lsb range))))
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

(defthm vl-expr-p-of-vl-op-optimize
  (implies (and (force (vl-op-p op))
                (force (vl-exprlist-p args))
                (force (or (not (vl-op-arity op))
                           (equal (len args) (vl-op-arity op))))
                (force (vl-module-p mod))
                (force (equal ialist (vl-moditem-alist mod))))
           (equal (vl-expr-p (vl-op-optimize op args mod ialist))
                  (if (vl-op-optimize op args mod ialist)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-op-optimize))))




(mutual-recursion

; The introduction of changedp is only to avoid re-consing expressions that aren't
; being optimized.

 (defund vl-expr-optimize (x mod ialist)
   "Returns (MV CHANGEDP X-PRIME)"
   (declare (xargs :guard (and (vl-expr-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod)))
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 1)))
   (if (vl-fast-atom-p x)
       (mv nil x)
     (b* ((op                            (vl-nonatom->op x))
          (args                          (vl-nonatom->args x))
          ((mv args-changedp args-prime) (vl-exprlist-optimize args mod ialist))
          (candidate                     (vl-op-optimize op args-prime mod ialist)))
         (cond (candidate
                (mv t candidate))
               (args-changedp
                (mv t (change-vl-nonatom x :args args-prime)))
               (t
                (mv nil x))))))

 (defund vl-exprlist-optimize (x mod ialist)
   "Returns (MV CHANGEDP X-PRIME)"
   (declare (xargs :guard (and (vl-exprlist-p x)
                               (vl-module-p mod)
                               (equal ialist (vl-moditem-alist mod)))
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 0)))
   (if (atom x)
       (mv nil nil)
     (b* (((mv car-changedp car-prime) (vl-expr-optimize (car x) mod ialist))
          ((mv cdr-changedp cdr-prime) (vl-exprlist-optimize (cdr x) mod ialist)))
         (mv (or car-changedp cdr-changedp)
             (cons car-prime cdr-prime))))))

(defthm vl-exprlist-optimize-when-not-consp
  (implies (not (consp x))
           (equal (vl-exprlist-optimize x mod ialist)
                  (mv nil nil)))
  :hints(("Goal" :in-theory (enable vl-exprlist-optimize))))

(defthm vl-exprlist-optimize-of-cons
  (equal (vl-exprlist-optimize (cons a x) mod ialist)
         (b* (((mv car-changedp car-prime) (vl-expr-optimize a mod ialist))
              ((mv cdr-changedp cdr-prime) (vl-exprlist-optimize x mod ialist)))
             (mv (or car-changedp cdr-changedp)
                 (cons car-prime cdr-prime))))
  :hints(("Goal" :in-theory (enable vl-exprlist-optimize))))

(defthm true-listp-of-vl-exprlist-optimize
  (true-listp (mv-nth 1 (vl-exprlist-optimize x mod ialist)))
  :rule-classes :type-prescription
  :hints(("Goal" :induct (len x))))

(defthm len-of-vl-exprlist-optimize
  (equal (len (mv-nth 1 (vl-exprlist-optimize x mod ialist)))
         (len x))
  :hints(("Goal" :induct (len x))))

(encapsulate
 ()
 (local (defthm lemma
          (case flag
            (expr (implies (and (vl-expr-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))
                           (vl-expr-p (mv-nth 1 (vl-expr-optimize x mod ialist)))))
            (atts t)
            (t (implies (and (vl-exprlist-p x)
                             (vl-module-p mod)
                             (equal ialist (vl-moditem-alist mod)))
                        (vl-exprlist-p (mv-nth 1 (vl-exprlist-optimize x mod ialist))))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (vl-expr-induct flag x)
                  :expand ((vl-expr-optimize x mod ialist))))))

 (defthm vl-expr-p-of-vl-expr-optimize
   (implies (and (force (vl-expr-p x))
                 (force (vl-module-p mod))
                 (force (equal ialist (vl-moditem-alist mod))))
            (vl-expr-p (mv-nth 1 (vl-expr-optimize x mod ialist))))
   :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

 (defthm vl-exprlist-p-of-vl-exprlist-optimize
   (implies (and (force (vl-exprlist-p x))
                 (force (vl-module-p mod))
                 (force (equal ialist (vl-moditem-alist mod))))
            (vl-exprlist-p (mv-nth 1 (vl-exprlist-optimize x mod ialist))))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(verify-guards vl-expr-optimize
               :hints(("Goal" :in-theory (enable vl-expr-optimize))))




(defmacro def-vl-optimize (name type body)
  `(encapsulate
    ()
    (defund ,name (x mod ialist)
      "Returns (MV CHANGEDP X-PRIME)"
      (declare (xargs :guard (and (,type x)
                                  (vl-module-p mod)
                                  (equal ialist (vl-moditem-alist mod))))
               (ignorable x mod ialist))
      ,body)

    (local (in-theory (enable ,name)))

    (defthm ,(intern-in-package-of-symbol
              (cat (symbol-name type) "-OF-" (symbol-name name))
              name)
      (implies (and (force (,type x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (,type (mv-nth 1 (,name x mod ialist)))))

    ))

(defmacro def-vl-optimize-list (name list-type element-name)
  `(encapsulate
    ()
    (defund ,name (x mod ialist)
      "Returns (MV CHANGEDP X-PRIME)"
      (declare (xargs :guard (and (,list-type x)
                                  (vl-module-p mod)
                                  (equal ialist (vl-moditem-alist mod)))))
      (if (atom x)
          (mv nil nil)
        (b* (((mv car-changedp car-prime) (,element-name (car x) mod ialist))
             ((mv cdr-changedp cdr-prime) (,name (cdr x) mod ialist)))
            (mv (or car-changedp cdr-changedp)
                (cons car-prime cdr-prime)))))

    (local (in-theory (enable ,name)))

    (defthm ,(intern-in-package-of-symbol
              (cat "TRUE-LISTP-OF-" (symbol-name name) "-2")
              name)
      (true-listp (mv-nth 1 (,name x mod ialist)))
      :rule-classes :type-prescription)

    (defthm ,(intern-in-package-of-symbol
              (cat (symbol-name list-type) "-OF-" (symbol-name name))
              name)
      (implies (and (force (,list-type x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (,list-type (mv-nth 1 (,name x mod ialist))))
      :hints(("Goal" :induct (len x))))

    ))


(def-vl-optimize vl-assign-optimize vl-assign-p
  (b* (((mv lvalue-changedp lvalue-prime)
        (vl-expr-optimize (vl-assign->lvalue x) mod ialist))
       ((mv expr-changedp expr-prime)
        (vl-expr-optimize (vl-assign->expr x) mod ialist)))
      (if (or lvalue-changedp expr-changedp)
          (mv t (change-vl-assign x :lvalue lvalue-prime :expr expr-prime))
        (mv nil x))))

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



(defund vl-module-optimize (x)
  (declare (xargs :guard (vl-module-p x)))
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

(defthm vl-module-p-of-vl-module-optimize
  (implies (force (vl-module-p x))
           (vl-module-p (vl-module-optimize x)))
  :hints(("Goal" :in-theory (enable vl-module-optimize))))

(defthm vl-module->name-of-vl-module-optimize
  (equal (vl-module->name (vl-module-optimize x))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-optimize))))



(defprojection vl-modulelist-optimize (x)
  (vl-module-optimize x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(defthm vl-modulelist->names-of-vl-modulelist-optimize
  (equal (vl-modulelist->names (vl-modulelist-optimize x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))
