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
(include-book "../parsetree")
(include-book "expr-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

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
  :val-type vl-expr-p)

(defalist vl-sigma-p (x)
  :short "An alist mapping strings to expressions, used in @(see substitution)."
  :key (stringp x)
  :val (vl-expr-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :already-definedp t)

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
  (deffixequiv-mutual vl-expr-subst))


; Now we can extend our notion of expression substitution across an entire
; module.  There's really nothing to this, we just walk through it and look for
; expressions.  But it's painful and long because of the complication of our
; parse tree.

(defmacro def-vl-subst (name &key type body verbosep)
  `(define ,name
     :short ,(cat "Substitute into a @(see " (symbol-name type) ").")
     ((x     ,type)
      (sigma vl-sigma-p))
     :returns (new-x ,type)
     :verbosep ,verbosep
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
       (change-vl-coretype x :dims (vl-packeddimensionlist-subst x.dims sigma)))
      (:vl-struct
       (change-vl-struct x
                         :dims (vl-packeddimensionlist-subst x.dims sigma)
                         :members (vl-structmemberlist-subst x.members sigma)))
      (:vl-union
       (change-vl-union x
                        :dims (vl-packeddimensionlist-subst x.dims sigma)
                        :members (vl-structmemberlist-subst x.members sigma)))
      (:vl-enum
       (change-vl-enum x
                       :basetype (vl-enumbasetype-subst x.basetype sigma)
                       :items (vl-enumitemlist-subst x.items sigma)
                       :dims (vl-packeddimensionlist-subst x.dims sigma)))
      (:vl-usertype
       (change-vl-usertype x
                           :kind (vl-expr-subst x.kind sigma)
                           :dims (vl-packeddimensionlist-subst x.dims sigma)))))

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
                              :dims (vl-packeddimensionlist-subst x.dims sigma)
                              :type (vl-datatype-subst x.type sigma))))
  ///
  (verify-guards vl-datatype-subst)
  (deffixequiv-mutual vl-datatype-subst))

(def-vl-subst vl-port-subst
  :type vl-port-p
  :body (change-vl-port x
                        :expr (vl-maybe-expr-subst (vl-port->expr x) sigma)))

(def-vl-subst-list vl-portlist-subst
  :type vl-portlist-p
  :element vl-port-subst)


(def-vl-subst vl-portdecl-subst
  :type vl-portdecl-p
  :body (change-vl-portdecl x
                            :range (vl-maybe-range-subst (vl-portdecl->range x) sigma)))

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



(def-vl-subst vl-netdecl-subst
  :type vl-netdecl-p
  :body (change-vl-netdecl x
                           :range (vl-maybe-range-subst (vl-netdecl->range x) sigma)
                           :arrdims (vl-rangelist-subst (vl-netdecl->arrdims x) sigma)
                           :delay (vl-maybe-gatedelay-subst (vl-netdecl->delay x) sigma)))

(def-vl-subst-list vl-netdecllist-subst
  :type vl-netdecllist-p
  :element vl-netdecl-subst)

(def-vl-subst vl-vardecl-subst
  :type vl-vardecl-p
  :body (b* (((vl-vardecl x) x))
          (change-vl-vardecl x
                             :vartype (vl-datatype-subst x.vartype sigma)
                             :dims    (vl-packeddimensionlist-subst x.dims sigma)
                             :initval (vl-maybe-expr-subst x.initval sigma))))

(def-vl-subst-list vl-vardecllist-subst
  :type vl-vardecllist-p
  :element vl-vardecl-subst)






(def-vl-subst vl-paramdecl-subst
  :type vl-paramdecl-p
  :body (change-vl-paramdecl x
                             :expr (vl-expr-subst (vl-paramdecl->expr x) sigma)
                             :range (vl-maybe-range-subst (vl-paramdecl->range x) sigma)))

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
    :named (make-vl-arguments-named :args (vl-namedarglist-subst x.args sigma))
    :plain (make-vl-arguments-plain :args (vl-plainarglist-subst x.args sigma))))

(def-vl-subst vl-modinst-subst
  :type vl-modinst-p
  :body (change-vl-modinst x
                           :range (vl-maybe-range-subst (vl-modinst->range x) sigma)
                           :paramargs (vl-arguments-subst (vl-modinst->paramargs x) sigma)
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

(def-vl-subst vl-blockitem-subst
  :type vl-blockitem-p
  :body (b* ((x (vl-blockitem-fix x)))
          (case (tag x)
            (:vl-vardecl   (vl-vardecl-subst x sigma))
            (otherwise     (vl-paramdecl-subst x sigma)))))

(def-vl-subst-list vl-blockitemlist-subst
  :type vl-blockitemlist-p
  :element vl-blockitem-subst)



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
            (otherwise
             (b* (((vl-eventtriggerstmt x) x))
               (change-vl-eventtriggerstmt x
                                           :id (vl-expr-subst x.id sigma)))))
        (change-vl-compoundstmt
         x
         :exprs (vl-exprlist-subst (vl-compoundstmt->exprs x) sigma)
         :stmts (vl-stmtlist-subst (vl-compoundstmt->stmts x) sigma)
         :decls (vl-blockitemlist-subst (vl-compoundstmt->decls x) sigma)
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

(def-vl-subst vl-taskport-subst
  :type vl-taskport-p
  :body
  (b* (((vl-taskport x) x))
    (change-vl-taskport x
                        :range (vl-maybe-range-subst x.range sigma))))

(def-vl-subst-list vl-taskportlist-subst
  :type vl-taskportlist-p
  :element vl-taskport-subst)

(def-vl-subst vl-fundecl-subst
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x))
    (change-vl-fundecl x
                       :rrange (vl-maybe-range-subst x.rrange sigma)
                       :decls (vl-blockitemlist-subst x.decls sigma)
                       :inputs (vl-taskportlist-subst x.inputs sigma)
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
                            :netdecls   (vl-netdecllist-subst   x.netdecls   sigma)
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
