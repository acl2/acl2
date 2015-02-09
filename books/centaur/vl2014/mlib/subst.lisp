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
(include-book "../parsetree")
(include-book "expr-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system)
                           acl2::consp-under-iff-when-true-listp
                           acl2::consp-when-member-equal-of-atom-listp
                           double-containment)))

(defxdoc substitution
  :parents (mlib)
  :short "Substitution into Verilog constructs"

  :long "<p>We implement routines to substitute values for identifiers
throughout Verilog constructs such as expressions, assignments, and
modules.</p>

<p>Our original use of substitution was in unparameterization, where we used
substitution to replace parameters with their values throughout a module.
Because of this, and since there are usually only a couple of parameters per
module, we historically created ordinary alists and look up with @(see
hons-assoc-equal) rather than @(see hons-get).  Since then we have found
substitution to be more generally useful, and prefer to use fast alists.</p>")

(local (xdoc::set-default-parents substitution))

(fty::defalist vl-sigma
  :key-type stringp
  :val-type vl-expr-p
  :count vl-sigma-count
  :short "An alist mapping strings to expressions, used in @(see substitution)."
  :keyp-of-nil nil
  :valp-of-nil nil)

;; (defthm vl-sigma-count-of-cdr-strong
;;   (implies (and (vl-sigma-p x)
;;                 (consp x))
;;            (< (vl-sigma-count (cdr x))
;;               (vl-sigma-count x)))
;;   :rule-classes ((:rewrite) (:linear))
;;   :hints(("Goal" :in-theory (enable vl-sigma-count))))

(defthm vl-exprlist-p-of-alist-vals-when-vl-sigma-p
  (implies (vl-sigma-p x)
           (vl-exprlist-p (alist-vals x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-sigma-p-of-pairlis$
  (implies (and (force (same-lengthp strs exprs))
                (force (string-listp strs))
                (force (vl-exprlist-p exprs)))
           (vl-sigma-p (pairlis$ strs exprs)))
  :hints(("Goal" :in-theory (enable (:induction pairlis$)))))

(local (defthm vl-expr-fix-nonnil
         (consp (vl-expr-fix x))
         :hints(("Goal" :in-theory (enable (tau-system))))
         :rule-classes :type-prescription))

(defines vl-expr-subst
  :short "Substitute into a @(see vl-expr-p)."

  :long "<p>We substitute into an expression, replacing any simple
identifiers (i.e., atoms which are @(see vl-id-p)'s) that are bound in
@('sigma') with their values.</p>

<p>Note that this function does not descend into attributes.  It is not clear
whether that is the right behavior, but it seems that the handling of
attributes is left up to the implementation.</p>"

  (define vl-expr-subst ((x     vl-expr-p)
                         (sigma vl-sigma-p))
    :returns (new-x vl-expr-p)
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x     (vl-expr-fix x))
         (sigma (vl-sigma-fix sigma))
         ((when (vl-fast-atom-p x))
          (let ((guts (vl-atom->guts x)))
            (if (vl-fast-id-p guts)
                (or (cdr (hons-get (vl-id->name guts) sigma))
                    x)
              x)))
         (args-prime (vl-exprlist-subst (vl-nonatom->args x) sigma)))
      (change-vl-nonatom x :args args-prime)))

  (define vl-exprlist-subst ((x     vl-exprlist-p)
                             (sigma vl-sigma-p))
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-exprlist-count x)
    :flag :list
    (if (consp x)
        (cons (vl-expr-subst (car x) sigma)
              (vl-exprlist-subst (cdr x) sigma))
      nil)
    ///
    (defprojection vl-exprlist-subst (x sigma)
      (vl-expr-subst x sigma)
      :already-definedp t
      :nil-preservingp nil))
  ///
  (verify-guards vl-expr-subst)
  (deffixequiv-mutual vl-expr-subst)

  (defthm consp-of-vl-expr-subst
    (consp (vl-expr-subst x sigma))
    :hints(("Goal" :in-theory (enable (tau-system))))
    :rule-classes :type-prescription))


; Now we can extend our notion of expression substitution across an entire
; module.  There's really nothing to this, we just walk through it and look for
; expressions.  But it's painful and long because of the complication of our
; parse tree.

(defmacro def-vl-subst (name &key type body verbosep prepwork)
  `(define ,name
     :short ,(cat "Substitute into a @(see " (symbol-name type) ").")
     ((x     ,type)
      (sigma vl-sigma-p))
     :returns (new-x ,type)
     :verbosep ,verbosep
     :prepwork ,prepwork
     (declare (ignorable x sigma))
     ,body))

(defmacro def-vl-subst-list (name &key type element)
  `(defprojection ,name ((x ,type)
                         (sigma vl-sigma-p))
     :returns (new-x ,type)
     (,element x sigma)))

(def-vl-subst vl-maybe-expr-subst
  :type vl-maybe-expr-p
  :body (and x
             (vl-expr-subst x sigma)))

(def-vl-subst vl-range-subst
  :type vl-range-p
  :body (change-vl-range x
                         :msb (vl-expr-subst (vl-range->msb x) sigma)
                         :lsb (vl-expr-subst (vl-range->lsb x) sigma)))

(def-vl-subst vl-maybe-range-subst
  :type vl-maybe-range-p
  :body (and x
             (vl-range-subst x sigma)))

(def-vl-subst-list vl-rangelist-subst
  :type vl-rangelist-p
  :element vl-range-subst)

(def-vl-subst vl-gatedelay-subst
  :type vl-gatedelay-p
  :body (change-vl-gatedelay x
                             :rise (vl-expr-subst (vl-gatedelay->rise x) sigma)
                             :fall (vl-expr-subst (vl-gatedelay->fall x) sigma)
                             :high (vl-maybe-expr-subst (vl-gatedelay->high x) sigma)))

(def-vl-subst vl-maybe-gatedelay-subst
  :type vl-maybe-gatedelay-p
  :body (and x (vl-gatedelay-subst x sigma)))

(def-vl-subst vl-packeddimension-subst
  :type vl-packeddimension-p
  :body
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        x
      (vl-range-subst x sigma))))

(def-vl-subst vl-maybe-packeddimension-subst
  :type vl-maybe-packeddimension-p
  :body
  (and x
       (vl-packeddimension-subst x sigma)))

(def-vl-subst-list vl-packeddimensionlist-subst
  :type vl-packeddimensionlist-p
  :element vl-packeddimension-subst)

(def-vl-subst vl-enumbasetype-subst
  :type vl-enumbasetype-p
  :body (b* (((vl-enumbasetype x) x))
          (change-vl-enumbasetype x
                                  :dim (vl-maybe-packeddimension-subst x.dim sigma))))

(def-vl-subst vl-enumitem-subst
  :type vl-enumitem-p
  :body
  (b* (((vl-enumitem x) x))
    (change-vl-enumitem x
                        :range (vl-maybe-range-subst x.range sigma)
                        :value (vl-maybe-expr-subst x.value sigma))))

(def-vl-subst-list vl-enumitemlist-subst
  :type vl-enumitemlist-p
  :element vl-enumitem-subst)


(defines vl-datatype-subst
  :verify-guards nil

  (define vl-datatype-subst ((x vl-datatype-p)
                             (sigma vl-sigma-p))
    :measure (vl-datatype-count x)
    :returns (new-x vl-datatype-p)
    (vl-datatype-case x
      (:vl-coretype
       (change-vl-coretype x
                           :pdims (vl-packeddimensionlist-subst x.pdims sigma)
                           :udims (vl-packeddimensionlist-subst x.udims sigma)))
      (:vl-struct
       (change-vl-struct x
                         :pdims (vl-packeddimensionlist-subst x.pdims sigma)
                         :udims (vl-packeddimensionlist-subst x.udims sigma)
                         :members (vl-structmemberlist-subst x.members sigma)))
      (:vl-union
       (change-vl-union x
                        :pdims (vl-packeddimensionlist-subst x.pdims sigma)
                        :udims (vl-packeddimensionlist-subst x.udims sigma)
                        :members (vl-structmemberlist-subst x.members sigma)))
      (:vl-enum
       (change-vl-enum x
                       :basetype (vl-enumbasetype-subst x.basetype sigma)
                       :items (vl-enumitemlist-subst x.items sigma)
                       :pdims (vl-packeddimensionlist-subst x.pdims sigma)
                       :udims (vl-packeddimensionlist-subst x.udims sigma)))
      (:vl-usertype
       (change-vl-usertype x
                           :kind (vl-expr-subst x.kind sigma)
                           :pdims (vl-packeddimensionlist-subst x.pdims sigma)
                           :udims (vl-packeddimensionlist-subst x.udims sigma)))))

  (define vl-structmemberlist-subst ((x vl-structmemberlist-p)
                                     (sigma vl-sigma-p))
    :measure (vl-structmemberlist-count x)
    :returns (new-x vl-structmemberlist-p)
    (if (atom x)
        nil
      (cons (vl-structmember-subst (car x) sigma)
            (vl-structmemberlist-subst (cdr x) sigma))))

  (define vl-structmember-subst ((x vl-structmember-p)
                                 (sigma vl-sigma-p))
    :measure (vl-structmember-count x)
    :returns (new-x vl-structmember-p)
    (b* (((vl-structmember x) x))
      (change-vl-structmember x
                              :rhs (vl-maybe-expr-subst x.rhs sigma)
                              :type (vl-datatype-subst x.type sigma))))
  ///
  (verify-guards vl-datatype-subst)
  (deffixequiv-mutual vl-datatype-subst))

(def-vl-subst vl-maybe-datatype-subst
  :type vl-maybe-datatype-p
  :body (if x
            (vl-datatype-subst x sigma)
          nil))

(def-vl-subst vl-interfaceport-subst
  :type vl-interfaceport-p
  :body (change-vl-interfaceport x
                                 :udims (vl-packeddimensionlist-subst
                                         (vl-interfaceport->udims x) sigma)))

(def-vl-subst vl-regularport-subst
  :type vl-regularport-p
  :body (change-vl-regularport x
                               :expr (b* ((expr (vl-regularport->expr x)))
                                       (and expr
                                            (vl-expr-subst expr sigma)))))

(def-vl-subst vl-port-subst
  :type vl-port-p
  :body (b* ((x (vl-port-fix x)))
          (case (tag x)
            (:vl-interfaceport (vl-interfaceport-subst x sigma))
            (otherwise         (vl-regularport-subst x sigma)))))

(def-vl-subst-list vl-portlist-subst
  :type vl-portlist-p
  :element vl-port-subst)


(def-vl-subst vl-portdecl-subst
  :type vl-portdecl-p
  :body (b* (((vl-portdecl x) x))
          (change-vl-portdecl x
                              :type (vl-datatype-subst x.type sigma))))

(def-vl-subst-list vl-portdecllist-subst
  :type vl-portdecllist-p
  :element vl-portdecl-subst)


(def-vl-subst vl-assign-subst
  :type vl-assign-p
  :body (change-vl-assign x
                          :lvalue (vl-expr-subst (vl-assign->lvalue x) sigma)
                          :expr   (vl-expr-subst (vl-assign->expr x) sigma)
                          :delay  (vl-maybe-gatedelay-subst (vl-assign->delay x) sigma)))

(def-vl-subst-list vl-assignlist-subst
  :type vl-assignlist-p
  :element vl-assign-subst)

(def-vl-subst vl-vardecl-subst
  :type vl-vardecl-p
  :body (b* (((vl-vardecl x) x))
          (change-vl-vardecl x
                             :type    (vl-datatype-subst x.type sigma)
                             :initval (vl-maybe-expr-subst x.initval sigma)
                             :delay   (vl-maybe-gatedelay-subst x.delay sigma))))

(def-vl-subst-list vl-vardecllist-subst
  :type vl-vardecllist-p
  :element vl-vardecl-subst)

(def-vl-subst vl-paramtype-subst
  :type vl-paramtype-p
  :body
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (change-vl-implicitvalueparam x
                                   :range (vl-maybe-range-subst x.range sigma)
                                   :default (vl-maybe-expr-subst x.default sigma)))
    (:vl-explicitvalueparam
     (change-vl-explicitvalueparam x
                                   :type (vl-datatype-subst x.type sigma)
                                   :default (vl-maybe-expr-subst x.default sigma)))
    (:vl-typeparam
     (change-vl-typeparam x
                          :default (vl-maybe-datatype-subst x.default sigma)))))

(def-vl-subst vl-paramdecl-subst
  :type vl-paramdecl-p
  :body (b* (((vl-paramdecl x) x))
          (change-vl-paramdecl x
                               :type (vl-paramtype-subst x.type sigma))))

(def-vl-subst-list vl-paramdecllist-subst
  :type vl-paramdecllist-p
  :element vl-paramdecl-subst)


(def-vl-subst vl-plainarg-subst
  :type vl-plainarg-p
  :body (change-vl-plainarg x
                            :expr (vl-maybe-expr-subst (vl-plainarg->expr x) sigma)))

(def-vl-subst-list vl-plainarglist-subst
  :type vl-plainarglist-p
  :element vl-plainarg-subst)

(def-vl-subst vl-namedarg-subst
  :type vl-namedarg-p
  :body (change-vl-namedarg x
                            :expr (vl-maybe-expr-subst (vl-namedarg->expr x) sigma)))

(def-vl-subst-list vl-namedarglist-subst
  :type vl-namedarglist-p
  :element vl-namedarg-subst)

(def-vl-subst vl-arguments-subst
  :type vl-arguments-p
  :body
  (vl-arguments-case x
    :vl-arguments-named (change-vl-arguments-named x :args (vl-namedarglist-subst x.args sigma))
    :vl-arguments-plain (change-vl-arguments-plain x :args (vl-plainarglist-subst x.args sigma))))

(def-vl-subst vl-paramvalue-subst
  :type vl-paramvalue-p
  :body
  (b* ((x (vl-paramvalue-fix x)))
    (vl-paramvalue-case x
      :expr     (vl-expr-subst x sigma)
      :datatype (vl-datatype-subst x sigma))))

(def-vl-subst-list vl-paramvaluelist-subst
  :type vl-paramvaluelist-p
  :element vl-paramvalue-subst)

(def-vl-subst vl-maybe-paramvalue-subst
  :type vl-maybe-paramvalue-p
  :body (and x (vl-paramvalue-subst x sigma)))

(def-vl-subst vl-namedparamvalue-subst
  :type vl-namedparamvalue-p
  :body
  (b* (((vl-namedparamvalue x) x))
    (change-vl-namedparamvalue x :value (vl-maybe-paramvalue-subst x.value sigma))))

(def-vl-subst-list vl-namedparamvaluelist-subst
  :type vl-namedparamvaluelist-p
  :element vl-namedparamvalue-subst)

(def-vl-subst vl-paramargs-subst
  :type vl-paramargs-p
  :body
  (vl-paramargs-case x
    :vl-paramargs-named
    (change-vl-paramargs-named x :args (vl-namedparamvaluelist-subst x.args sigma))
    :vl-paramargs-plain
    (change-vl-paramargs-plain x :args (vl-paramvaluelist-subst x.args sigma))))


(def-vl-subst vl-modinst-subst
  :type vl-modinst-p
  :body (change-vl-modinst x
                           :range (vl-maybe-range-subst (vl-modinst->range x) sigma)
                           :paramargs (vl-paramargs-subst (vl-modinst->paramargs x) sigma)
                           :portargs (vl-arguments-subst (vl-modinst->portargs x) sigma)))

(def-vl-subst-list vl-modinstlist-subst
  :type vl-modinstlist-p
  :element vl-modinst-subst)

(def-vl-subst vl-gateinst-subst
  :type vl-gateinst-p
  :body (change-vl-gateinst x
                            :range (vl-maybe-range-subst (vl-gateinst->range x) sigma)
                            :delay (vl-maybe-gatedelay-subst (vl-gateinst->delay x) sigma)
                            :args (vl-plainarglist-subst (vl-gateinst->args x) sigma)))

(def-vl-subst-list vl-gateinstlist-subst
  :type vl-gateinstlist-p
  :element vl-gateinst-subst)



(def-vl-subst vl-evatom-subst
  :type vl-evatom-p
  :body (change-vl-evatom x
                          :expr (vl-expr-subst (vl-evatom->expr x) sigma)))

(def-vl-subst-list vl-evatomlist-subst
  :type vl-evatomlist-p
  :element vl-evatom-subst)

(def-vl-subst vl-eventcontrol-subst
  :type vl-eventcontrol-p
  :body (change-vl-eventcontrol x
                                :atoms (vl-evatomlist-subst (vl-eventcontrol->atoms x) sigma)))
(def-vl-subst vl-delaycontrol-subst
  :type vl-delaycontrol-p
  :body (change-vl-delaycontrol x
                                :value (vl-expr-subst (vl-delaycontrol->value x) sigma)))

(def-vl-subst vl-repeateventcontrol-subst
  :type vl-repeateventcontrol-p
  :body (change-vl-repeateventcontrol x
                                      :expr (vl-expr-subst (vl-repeateventcontrol->expr x) sigma)
                                      :ctrl (vl-eventcontrol-subst (vl-repeateventcontrol->ctrl x) sigma)))

(def-vl-subst vl-delayoreventcontrol-subst
  :type vl-delayoreventcontrol-p
  :body (b* ((x (vl-delayoreventcontrol-fix x)))
          (case (tag x)
            (:vl-delaycontrol (vl-delaycontrol-subst x sigma))
            (:vl-eventcontrol (vl-eventcontrol-subst x sigma))
            (otherwise        (vl-repeateventcontrol-subst x sigma)))))

(def-vl-subst vl-maybe-delayoreventcontrol-subst
  :type vl-maybe-delayoreventcontrol-p
  :body (and x
             (vl-delayoreventcontrol-subst x sigma)))

(defthm vl-maybe-delayoreventcontrol-p-of-nil
  (iff (vl-maybe-delayoreventcontrol-subst x sigma)
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-subst))))


(defines vl-stmt-subst
  :short "Substitute into a @(see vl-stmt-p)"

  (define vl-stmt-subst ((x     vl-stmt-p)
                         (sigma vl-sigma-p))
    :returns (new-x vl-stmt-p)
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* ((x (vl-stmt-fix x)))
      (if (vl-atomicstmt-p x)
          (case (vl-stmt-kind x)
            (:vl-nullstmt x)
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x))
               (change-vl-assignstmt x
                                     :lvalue (vl-expr-subst x.lvalue sigma)
                                     :expr (vl-expr-subst x.expr sigma)
                                     :ctrl (vl-maybe-delayoreventcontrol-subst x.ctrl sigma))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x))
               (change-vl-deassignstmt x
                                       :lvalue (vl-expr-subst x.lvalue sigma))))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x))
               (change-vl-enablestmt x
                                     :id (vl-expr-subst x.id sigma)
                                     :args (vl-exprlist-subst x.args sigma))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x))
               (change-vl-disablestmt x
                                      :id (vl-expr-subst x.id sigma))))
            (:vl-returnstmt
             (b* (((vl-returnstmt x)))
               (if x.val
                   (change-vl-returnstmt x :val (vl-expr-subst x.val sigma))
                 x)))

            (otherwise
             (b* (((vl-eventtriggerstmt x) x))
               (change-vl-eventtriggerstmt x
                                           :id (vl-expr-subst x.id sigma)))))
        (change-vl-compoundstmt
         x
         :exprs (vl-exprlist-subst (vl-compoundstmt->exprs x) sigma)
         :stmts (vl-stmtlist-subst (vl-compoundstmt->stmts x) sigma)
         :vardecls (vl-vardecllist-subst (vl-compoundstmt->vardecls x) sigma)
         :paramdecls (vl-paramdecllist-subst (vl-compoundstmt->paramdecls x) sigma)
         :ctrl (vl-maybe-delayoreventcontrol-subst (vl-compoundstmt->ctrl x) sigma)))))

  (define vl-stmtlist-subst ((x     vl-stmtlist-p)
                             (sigma vl-sigma-p))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :verify-guards nil
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (consp x)
        (cons (vl-stmt-subst (car x) sigma)
              (vl-stmtlist-subst (cdr x) sigma))
      nil))
  ///
  (defprojection vl-stmtlist-subst (x sigma)
    (vl-stmt-subst x sigma)
    :already-definedp t)

  (verify-guards vl-stmt-subst)

  (deffixequiv-mutual vl-stmt-subst))


(def-vl-subst vl-always-subst
  :type vl-always-p
  :body (change-vl-always x
                          :stmt (vl-stmt-subst (vl-always->stmt x) sigma)))

(def-vl-subst-list vl-alwayslist-subst
  :type vl-alwayslist-p
  :element vl-always-subst)

(def-vl-subst vl-initial-subst
  :type vl-initial-p
  :body (change-vl-initial x
                           :stmt (vl-stmt-subst (vl-initial->stmt x) sigma)))

(def-vl-subst-list vl-initiallist-subst
  :type vl-initiallist-p
  :element vl-initial-subst)



(def-vl-subst vl-fundecl-subst
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x))
    (change-vl-fundecl x
                       :rettype (vl-datatype-subst x.rettype sigma)
                       :vardecls (vl-vardecllist-subst x.vardecls sigma)
                       :paramdecls (vl-paramdecllist-subst x.paramdecls sigma)
                       :portdecls (vl-portdecllist-subst x.portdecls sigma)
                       :body (vl-stmt-subst x.body sigma))))

(def-vl-subst-list vl-fundecllist-subst
  :type vl-fundecllist-p
  :element vl-fundecl-subst)

(def-vl-subst vl-module-subst
  :type vl-module-p
  :body (b* (((vl-module x) x))
          (change-vl-module x
                            ;; name is unchanged
                            ;; BOZO wtf are params?
                            :ports      (vl-portlist-subst      x.ports      sigma)
                            :portdecls  (vl-portdecllist-subst  x.portdecls  sigma)
                            :assigns    (vl-assignlist-subst    x.assigns    sigma)
                            :vardecls   (vl-vardecllist-subst   x.vardecls   sigma)
                            :fundecls   (vl-fundecllist-subst   x.fundecls   sigma)
                            :paramdecls (vl-paramdecllist-subst x.paramdecls sigma)
                            :modinsts   (vl-modinstlist-subst   x.modinsts   sigma)
                            :gateinsts  (vl-gateinstlist-subst  x.gateinsts  sigma)
                            :alwayses   (vl-alwayslist-subst    x.alwayses   sigma)
                            :initials   (vl-initiallist-subst   x.initials   sigma)
                            ;; atts are unchanged
                            )))

(def-vl-subst-list vl-modulelist-subst
  :type vl-modulelist-p
  :element vl-module-subst)
