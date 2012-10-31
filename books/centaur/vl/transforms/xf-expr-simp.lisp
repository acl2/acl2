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
(include-book "../mlib/expr-tools")
(include-book "../mlib/fmt")
(local (include-book "../util/arithmetic"))

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

(local (defthm crock
         (implies (vl-expr-resolved-p x)
                  (vl-atom-p x))
         :hints(("Goal" :in-theory (enable vl-expr-resolved-p)))))


(defsection vl-expr-simp
  :parents (expr-simp)
  :short "Core routine to simplify expressions."

  (mutual-recursion

   (defund vl-expr-simp (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (vl-expr-count x)
                     :verify-guards nil))
     (b* (((when (vl-idexpr-p x))
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

          ;; Reduce ~~A to A
          ((when (and (eq x.op :vl-unary-bitnot)
                      (vl-nonatom-p (first args))
                      (eq (vl-nonatom->op (first args)) :vl-unary-bitnot)))
           (first (vl-nonatom->args (first args))))

          ;; Reduce ~1'b1 to 1'b0 and ~1'b0 to 1'b1
          ((when (and (eq x.op :vl-unary-bitnot)
                      (vl-atom-p (first args))
                      (vl-expr-resolved-p (first args))
                      (or (= (vl-resolved->val (first args)) 1)
                          (= (vl-resolved->val (first args)) 0))
                      (equal (vl-expr->finalwidth x) 1)
                      (equal (vl-expr->finaltype x) :vl-unsigned)))
           (b* ((curr (vl-resolved->val (first args)))
                (ans  (if (= curr 0)
                          |*sized-1'b1*|
                        |*sized-1'b0*|)))
             (vl-cw-ps-seq
              (vl-cw "NC Rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce ~(A ? B : C) to (A ? ~B : ~C)
          ((when (and (eq x.op :vl-unary-bitnot)
                      (vl-nonatom-p (first args))
                      (eq (vl-nonatom->op (first args)) :vl-qmark)))
           (b* (((list a b c) (vl-nonatom->args (first args)))
                (~b (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list b)
                                     :finalwidth (vl-expr->finalwidth b)
                                     :finaltype (vl-expr->finaltype b)))
                (~c (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list c)
                                     :finalwidth (vl-expr->finalwidth c)
                                     :finaltype (vl-expr->finaltype c)))
                (ans (change-vl-nonatom (first args)
                                        :args (list a ~b ~c))))
             (vl-cw-ps-seq
              (vl-cw "QM Rewrite ~a0 to ~a1!~%" x ans))
             ans))

          ;; Reduce ~(A & B) using demorgan's law, but only if one of A or B is a
          ;; negated expression (so that we think the negation will cancel on at
          ;; least one branch.)
          #||
          (thm (iff (not (and a b))
          (or (not a) (not b))))
          ||#
          ((when (and (eq x.op :vl-unary-bitnot)
                      (vl-nonatom-p (first args))
                      (eq (vl-nonatom->op (first args)) :vl-binary-bitand)
;(let ((and-args (vl-nonatom->args (first args))))
;  (or (and (vl-nonatom-p (first and-args))
;           (eq (vl-nonatom->op (first and-args)) :vl-unary-bitnot))
;      (and (vl-nonatom-p (second and-args))
;           (eq (vl-nonatom->op (second and-args)) :vl-unary-bitnot))))
                      ))
           (b* (((list a b) (vl-nonatom->args (first args)))
                (~a (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list a)
                                     :finalwidth (vl-expr->finalwidth a)
                                     :finaltype (vl-expr->finaltype a)))
                (~b (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list b)
                                     :finalwidth (vl-expr->finalwidth b)
                                     :finaltype (vl-expr->finaltype b)))
                (ans (change-vl-nonatom (first args)
                                        :op :vl-binary-bitor
                                        :args (list ~a ~b))))
             (vl-cw-ps-seq
              (vl-cw "DMA Rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce ~(A | B) using demorgan's law, but only if one of A or B is
          ;; a negated expression
          #|| 
          (thm (iff (not (or a b))
          (and (not a) (not b))))
          ||#
          ((when (and (eq x.op :vl-unary-bitnot)
                      (vl-nonatom-p (first args))
                      (eq (vl-nonatom->op (first args)) :vl-binary-bitor)
;(let ((and-args (vl-nonatom->args (first args))))
;  (or (and (vl-nonatom-p (first and-args))
;           (eq (vl-nonatom->op (first and-args)) :vl-unary-bitnot))
;      (and (vl-nonatom-p (second and-args))
;           (eq (vl-nonatom->op (second and-args)) :vl-unary-bitnot))))
                      ))
           (b* (((list a b) (vl-nonatom->args (first args)))
                (~a (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list a)
                                     :finalwidth (vl-expr->finalwidth a)
                                     :finaltype (vl-expr->finaltype a)))
                (~b (make-vl-nonatom :op :vl-unary-bitnot
                                     :args (list b)
                                     :finalwidth (vl-expr->finalwidth b)
                                     :finaltype (vl-expr->finaltype b)))
                (ans (change-vl-nonatom (first args)
                                        :op :vl-binary-bitand
                                        :args (list ~a ~b))))
             (vl-cw-ps-seq
              (vl-cw "DMO Rewrite ~a0 to ~a1~%" x ans))
             ans))


          ;; Reduce (A & 0) to 0
          ((when (and (eq x.op :vl-binary-bitand)
                      (and (vl-expr-resolved-p (second args))
                           (= (vl-resolved->val (second args)) 0))))
           (b* ((ans (change-vl-atom (second args)
                                     :finaltype (vl-expr->finaltype x)
                                     :finalwidth (vl-expr->finalwidth x))))
             (vl-cw-ps-seq
              (vl-cw "AND0a rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce (0 & A) to 0.
          ((when (and (eq x.op :vl-binary-bitand)
                      (and (vl-expr-resolved-p (first args))
                           (= (vl-resolved->val (first args)) 0))))
           (b* ((ans (change-vl-atom (first args)
                                     :finaltype (vl-expr->finaltype x)
                                     :finalwidth (vl-expr->finalwidth x))))
             (vl-cw-ps-seq
              (vl-cw "AND0b rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce (A & 1) to A
          ((when (and (eq x.op :vl-binary-bitand)
                      (and (vl-expr-resolved-p (second args))
                           (= (vl-resolved->val (second args)) 1))
                      (equal (vl-expr->finalwidth x) 1)
                      (equal (vl-expr->finaltype x) :vl-unsigned)
                      (equal (vl-expr->finalwidth (first args)) 1)
                      (equal (vl-expr->finaltype (first args)) :vl-unsigned)))
           (b* ((ans (first args)))
             (vl-cw-ps-seq
              (vl-cw "AND1a rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce (1 & A) to A
          ((when (and (eq x.op :vl-binary-bitand)
                      (and (vl-expr-resolved-p (first args))
                           (= (vl-resolved->val (first args)) 1))
                      (equal (vl-expr->finalwidth x) 1)
                      (equal (vl-expr->finaltype x) :vl-unsigned)
                      (equal (vl-expr->finalwidth (second args)) 1)
                      (equal (vl-expr->finaltype (second args)) :vl-unsigned)))
           (b* ((ans (second args)))
             (vl-cw-ps-seq
              (vl-cw "AND1b rewrite ~a0 to ~a1~%" x ans))
             ans))

          ;; Reduce ~A ? B : C to A ? C : B
          ((when (and (eq x.op :vl-qmark)
                      (vl-nonatom-p (first args))
                      (eq (vl-nonatom->op (first args)) :vl-unary-bitnot)))
           (b* (((list ~a b c) args)
                (a   (first (vl-nonatom->args ~a)))
                (ans (change-vl-nonatom x :args (list a c b))))
             (vl-cw-ps-seq
              (vl-cw "QM Rewrite ~a0 to ~a1~%" x ans))
             ans)))

       (change-vl-nonatom x :args args)))

   (defund vl-exprlist-simp (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (vl-exprlist-count x)))
     (if (atom x)
         nil
       (cons (vl-expr-simp (car x))
             (vl-exprlist-simp (cdr x))))))

  (local (flag::make-flag flag-vl-expr-simp
                          vl-expr-simp
                          :flag-mapping ((vl-expr-simp . expr)
                                         (vl-exprlist-simp . list))))

  (defthm len-of-vl-exprlist-simp
    (equal (len (vl-exprlist-simp x))
           (len x))
    :hints(("Goal"
            :induct (len x)
            :expand (vl-exprlist-simp x)))
    :rule-classes ((:rewrite)
                   (:forward-chaining :trigger-terms ((vl-exprlist-simp x)))))

  (defthm consp-of-vl-exprlist-simp
    (equal (consp (vl-exprlist-simp x))
           (consp x))
    :hints(("Goal"
            :induct (len x)
            :expand (vl-exprlist-simp x)))
    :rule-classes ((:rewrite)
                   (:forward-chaining :trigger-terms ((vl-exprlist-simp x)))))

  (defthm vl-nonatom-p-when-vl-expr-resolved-p
    (implies (vl-expr-resolved-p x)
             (equal (vl-nonatom-p x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (defthm vl-exprlist-simp-under-iff
    (iff (vl-exprlist-simp x)
         (consp x))
    :hints(("Goal" :induct (len x)
            :expand (vl-exprlist-simp x))))

  (local
   (defsection gah
     (local (defthm cdr-of-vl-exprlist-simp
              (equal (cdr (vl-exprlist-simp x))
                     (vl-exprlist-simp (cdr x)))
              :hints(("Goal" :expand (vl-exprlist-simp x)))))

     (defthm gaaaaaah
       (iff (CDR (VL-EXPRLIST-SIMP X))
            (consp (cdr x))))

     (defthm gaaaaaaaaah!@@$!%
       (iff (CDDR (VL-EXPRLIST-SIMP X))
            (consp (cddr x))))))

  (local (defthm-flag-vl-expr-simp
           (defthm vl-expr-p-of-vl-expr-simp
             (implies (force (vl-expr-p x))
                      (vl-expr-p (vl-expr-simp x)))
             :flag expr)
           (defthm vl-exprlist-p-of-vl-exprlist-simp
             (implies (force (vl-exprlist-p x))
                      (vl-exprlist-p (vl-exprlist-simp x)))
             :flag list)
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :expand ((vl-expr-simp x)
                            (vl-exprlist-simp x))))))

  (defthm vl-expr-p-of-vl-expr-simp
    (implies (force (vl-expr-p x))
             (vl-expr-p (vl-expr-simp x))))

  (defthm vl-exprlist-p-of-vl-exprlist-simp
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-exprlist-simp x))))

  (verify-guards vl-expr-simp))


; We could do these reductions in more places, but mainly we care about
; assignments and instance arguments...

(defsection vl-assign-simp
  :parents (expr-simp)

  (defund vl-assign-simp (x)
    (declare (xargs :guard (vl-assign-p x)))
    (change-vl-assign x :expr (vl-expr-simp (vl-assign->expr x))))

  (local (in-theory (enable vl-assign-simp)))

  (defthm vl-assign-p-of-vl-assign-simp
    (implies (vl-assign-p x)
             (vl-assign-p (vl-assign-simp x)))))

(defprojection vl-assignlist-simp (x)
  (vl-assign-simp x)
  :guard (vl-assignlist-p x)
  :result-type vl-assignlist-p
  :parents (expr-simp))



(defsection vl-plainarg-simp
  :parents (expr-simp)

  (defund vl-plainarg-simp (x)
    (declare (xargs :guard (vl-plainarg-p x)))
    (b* (((vl-plainarg x) x)
         ((unless (eq x.dir :vl-input))
          ;; Don't want to tamper with outputs/inouts, not that they should
          ;; have negations anyway...
          x)
         ((unless x.expr)
          x))
      (change-vl-plainarg x :expr (vl-expr-simp x.expr))))

  (local (in-theory (enable vl-plainarg-simp)))

  (defthm vl-plainarg-p-of-vl-plainarg-simp
    (implies (vl-plainarg-p x)
             (vl-plainarg-p (vl-plainarg-simp x)))))

(defprojection vl-plainarglist-simp (x)
  (vl-plainarg-simp x)
  :guard (vl-plainarglist-p x)
  :result-type vl-plainarglist-p
  :parents (expr-simp))



(defsection vl-modinst-simp
  :parents (expr-simp)

  (defund vl-modinst-simp (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* (((vl-modinst x) x)
         ((when (vl-arguments->namedp x.portargs))
          ;; Not resolved, don't modify
          x)
         (args (vl-arguments->args x.portargs))
         (args (vl-plainarglist-simp args)))
      (change-vl-modinst x
                         :portargs (vl-arguments nil args))))

  (local (in-theory (enable vl-modinst-simp)))

  (defthm vl-modinst-p-of-vl-modinst-simp
    (implies (vl-modinst-p x)
             (vl-modinst-p (vl-modinst-simp x)))))

(defprojection vl-modinstlist-simp (x)
  (vl-modinst-simp x)
  :guard (vl-modinstlist-p x)
  :result-type vl-modinstlist-p
  :parents (expr-simp))



(defsection vl-module-simp
  :parents (expr-simp)

  (defund vl-module-simp (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x))
      (change-vl-module x
                        :assigns (vl-assignlist-simp x.assigns)
                        :modinsts (vl-modinstlist-simp x.modinsts))))

  (local (in-theory (enable vl-module-simp)))

  (defthm vl-module-p-of-vl-module-simp
    (implies (vl-module-p x)
             (vl-module-p (vl-module-simp x))))

  (defthm vl-module->name-of-vl-module-simp
    (equal (vl-module->name (vl-module-simp x))
           (vl-module->name x))))

(defprojection vl-modulelist-simp (x)
  (vl-module-simp x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (expr-simp))