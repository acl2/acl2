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
(include-book "override")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc scopesubst
  :parents (unparameterization)
  :short "Scope aware substitution that replaces occurrences of resolved
parameters with their values.")

(local (xdoc::set-default-parents scopesubst))




(defines vl-expr-scopesubst
  :short "Substitute resolved parameters into an expression."
  :long "<p>We assume that the parameters have already been processed
so that their overrides are compatible with thier types.</p>"

  (define vl-expr-scopesubst ((x  vl-expr-p)
                              (ss vl-scopestack-p))
    :returns (new-x vl-expr-p)
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x     (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (b* ((guts (vl-atom->guts x))
               ((unless (vl-fast-id-p guts)) ;; for now
                x)
               (name (vl-id->name guts))
               (item (vl-scopestack-find-item name ss))
               ((unless (and item
                             (eq (tag item) :vl-paramdecl)))
                x)
               (value (vl-paramdecl-final-value item ss))
               ((unless (and value
                             (vl-paramvalue-expr-p value)))
                x)
               (atts
                ;; See for instance vl-pp-atom.  We record the name of the
                ;; parameter that gave rise to this expression so that we can
                ;; pretty-print it if desired.  We hons part of this since it
                ;; will be repeated for all uses of the parameter.
                (list (hons "VL_PARAMNAME"
                            (make-vl-atom :guts (make-vl-string :value name))))))
            (vl-expr-add-atts atts value)))
         (args-prime (vl-exprlist-scopesubst (vl-nonatom->args x) ss)))
      (change-vl-nonatom x :args args-prime)))

  (define vl-exprlist-scopesubst ((x     vl-exprlist-p)
                                 (ss vl-scopestack-p))
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-exprlist-count x)
    :flag :list
    (if (consp x)
        (cons (vl-expr-scopesubst (car x) ss)
              (vl-exprlist-scopesubst (cdr x) ss))
      nil)
    ///
    (defprojection vl-exprlist-scopesubst (x ss)
      (vl-expr-scopesubst x ss)
      :already-definedp t
      :nil-preservingp nil))
  ///
  (verify-guards vl-expr-scopesubst)
  (deffixequiv-mutual vl-expr-scopesubst))


; Now we can extend our notion of expression substitution across an entire
; module.  There's really nothing to this, we just walk through it and look for
; expressions.  But it's painful and long because of the complication of our
; parse tree.

(defmacro def-vl-scopesubst (name &key type body verbosep)
  `(define ,name
     :short ,(cat "Scopesubstitute into a @(see " (symbol-name type) ").")
     ((x     ,type)
      (ss vl-scopestack-p))
     :returns (new-x ,type)
     :verbosep ,verbosep
     (declare (ignorable x ss))
     ,body))

(defmacro def-vl-scopesubst-list (name &key type element)
  `(defprojection ,name ((x ,type)
                         (ss vl-scopestack-p))
     :returns (new-x ,type)
     (,element x ss)))

(def-vl-scopesubst vl-maybe-expr-scopesubst
  :type vl-maybe-expr-p
  :body (and x
             (vl-expr-scopesubst x ss)))

(def-vl-scopesubst vl-range-scopesubst
  :type vl-range-p
  :body (change-vl-range x
                         :msb (vl-expr-scopesubst (vl-range->msb x) ss)
                         :lsb (vl-expr-scopesubst (vl-range->lsb x) ss)))

(def-vl-scopesubst vl-maybe-range-scopesubst
  :type vl-maybe-range-p
  :body (and x
             (vl-range-scopesubst x ss)))

(def-vl-scopesubst-list vl-rangelist-scopesubst
  :type vl-rangelist-p
  :element vl-range-scopesubst)

(def-vl-scopesubst vl-gatedelay-scopesubst
  :type vl-gatedelay-p
  :body (change-vl-gatedelay x
                             :rise (vl-expr-scopesubst (vl-gatedelay->rise x) ss)
                             :fall (vl-expr-scopesubst (vl-gatedelay->fall x) ss)
                             :high (vl-maybe-expr-scopesubst (vl-gatedelay->high x) ss)))

(def-vl-scopesubst vl-maybe-gatedelay-scopesubst
  :type vl-maybe-gatedelay-p
  :body (and x (vl-gatedelay-scopesubst x ss)))

(def-vl-scopesubst vl-packeddimension-scopesubst
  :type vl-packeddimension-p
  :body
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        x
      (vl-range-scopesubst x ss))))

(def-vl-scopesubst vl-maybe-packeddimension-scopesubst
  :type vl-maybe-packeddimension-p
  :body
  (and x
       (vl-packeddimension-scopesubst x ss)))

(def-vl-scopesubst-list vl-packeddimensionlist-scopesubst
  :type vl-packeddimensionlist-p
  :element vl-packeddimension-scopesubst)

(def-vl-scopesubst vl-enumbasetype-scopesubst
  :type vl-enumbasetype-p
  :body (b* (((vl-enumbasetype x) x))
          (change-vl-enumbasetype x
                                  :dim (vl-maybe-packeddimension-scopesubst x.dim ss))))

(def-vl-scopesubst vl-enumitem-scopesubst
  :type vl-enumitem-p
  :body
  (b* (((vl-enumitem x) x))
    (change-vl-enumitem x
                        :range (vl-maybe-range-scopesubst x.range ss)
                        :value (vl-maybe-expr-scopesubst x.value ss))))

(def-vl-scopesubst-list vl-enumitemlist-scopesubst
  :type vl-enumitemlist-p
  :element vl-enumitem-scopesubst)


(defines vl-datatype-scopesubst
  :verify-guards nil

  (define vl-datatype-scopesubst ((x vl-datatype-p)
                             (ss vl-scopestack-p))
    :measure (vl-datatype-count x)
    :returns (new-x vl-datatype-p)
    (vl-datatype-case x
      (:vl-coretype
       (change-vl-coretype x
                           :pdims (vl-packeddimensionlist-scopesubst x.pdims ss)
                           :udims (vl-packeddimensionlist-scopesubst x.udims ss)))
      (:vl-struct
       (change-vl-struct x
                         :pdims (vl-packeddimensionlist-scopesubst x.pdims ss)
                         :udims (vl-packeddimensionlist-scopesubst x.udims ss)
                         :members (vl-structmemberlist-scopesubst x.members ss)))
      (:vl-union
       (change-vl-union x
                        :pdims (vl-packeddimensionlist-scopesubst x.pdims ss)
                        :udims (vl-packeddimensionlist-scopesubst x.udims ss)
                        :members (vl-structmemberlist-scopesubst x.members ss)))
      (:vl-enum
       (change-vl-enum x
                       :basetype (vl-enumbasetype-scopesubst x.basetype ss)
                       :items (vl-enumitemlist-scopesubst x.items ss)
                       :pdims (vl-packeddimensionlist-scopesubst x.pdims ss)
                       :udims (vl-packeddimensionlist-scopesubst x.udims ss)))
      (:vl-usertype
       (change-vl-usertype x
                           :kind (vl-expr-scopesubst x.kind ss)
                           :pdims (vl-packeddimensionlist-scopesubst x.pdims ss)
                           :udims (vl-packeddimensionlist-scopesubst x.udims ss)))))

  (define vl-structmemberlist-scopesubst ((x vl-structmemberlist-p)
                                     (ss vl-scopestack-p))
    :measure (vl-structmemberlist-count x)
    :returns (new-x vl-structmemberlist-p)
    (if (atom x)
        nil
      (cons (vl-structmember-scopesubst (car x) ss)
            (vl-structmemberlist-scopesubst (cdr x) ss))))

  (define vl-structmember-scopesubst ((x vl-structmember-p)
                                      (ss vl-scopestack-p))
    :measure (vl-structmember-count x)
    :returns (new-x vl-structmember-p)
    (b* (((vl-structmember x) x))
      (change-vl-structmember x
                              :rhs (vl-maybe-expr-scopesubst x.rhs ss)
                              :type (vl-datatype-scopesubst x.type ss))))
  ///
  (verify-guards vl-datatype-scopesubst)
  (deffixequiv-mutual vl-datatype-scopesubst))

(def-vl-scopesubst vl-maybe-datatype-scopesubst
  :type vl-maybe-datatype-p
  :body (if x
            (vl-datatype-scopesubst x ss)
          nil))

(def-vl-scopesubst vl-interfaceport-scopesubst
  :type vl-interfaceport-p
  :body (change-vl-interfaceport
         x :udims (vl-packeddimensionlist-scopesubst (vl-interfaceport->udims x) ss)))

(def-vl-scopesubst vl-regularport-scopesubst
  :type vl-regularport-p
  :body (change-vl-regularport
         x :expr (vl-maybe-expr-scopesubst (vl-regularport->expr x) ss)))

(def-vl-scopesubst vl-port-scopesubst
  :type vl-port-p
  :body (b* ((x (vl-port-fix X)))
          (if (eq (tag x) :vl-interfaceport)
              (vl-interfaceport-scopesubst x ss)
            (vl-regularport-scopesubst x ss))))

(def-vl-scopesubst-list vl-portlist-scopesubst
  :type vl-portlist-p
  :element vl-port-scopesubst)


(def-vl-scopesubst vl-portdecl-scopesubst
  :type vl-portdecl-p
  :body (b* (((vl-portdecl x) x))
          (change-vl-portdecl x
                              :type (vl-datatype-scopesubst x.type ss))))

(def-vl-scopesubst-list vl-portdecllist-scopesubst
  :type vl-portdecllist-p
  :element vl-portdecl-scopesubst)


(def-vl-scopesubst vl-assign-scopesubst
  :type vl-assign-p
  :body (change-vl-assign x
                          :lvalue (vl-expr-scopesubst (vl-assign->lvalue x) ss)
                          :expr   (vl-expr-scopesubst (vl-assign->expr x) ss)
                          :delay  (vl-maybe-gatedelay-scopesubst (vl-assign->delay x) ss)))

(def-vl-scopesubst-list vl-assignlist-scopesubst
  :type vl-assignlist-p
  :element vl-assign-scopesubst)

(def-vl-scopesubst vl-alias-scopesubst
  :type vl-alias-p
  :body (change-vl-alias x
                         :lhs (vl-expr-scopesubst (vl-alias->lhs x) ss)
                         :rhs   (vl-expr-scopesubst (vl-alias->rhs x) ss)))

(def-vl-scopesubst-list vl-aliaslist-scopesubst
  :type vl-aliaslist-p
  :element vl-alias-scopesubst)


(def-vl-scopesubst vl-vardecl-scopesubst
  :type vl-vardecl-p
  :body (b* (((vl-vardecl x) x))
          (change-vl-vardecl x
                             :type    (vl-datatype-scopesubst x.type ss)
                             :initval (vl-maybe-expr-scopesubst x.initval ss)
                             :delay   (vl-maybe-gatedelay-scopesubst x.delay ss))))

(def-vl-scopesubst-list vl-vardecllist-scopesubst
  :type vl-vardecllist-p
  :element vl-vardecl-scopesubst)

(def-vl-scopesubst vl-paramtype-scopesubst
  :type vl-paramtype-p
  :body
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (change-vl-implicitvalueparam x
                                   :range (vl-maybe-range-scopesubst x.range ss)
                                   :default (vl-maybe-expr-scopesubst x.default ss)))
    (:vl-explicitvalueparam
     (change-vl-explicitvalueparam x
                                   :type (vl-datatype-scopesubst x.type ss)
                                   :default (vl-maybe-expr-scopesubst x.default ss)))
    (:vl-typeparam
     (change-vl-typeparam x
                          :default (vl-maybe-datatype-scopesubst x.default ss)))))

(def-vl-scopesubst vl-paramdecl-scopesubst
  :type vl-paramdecl-p
  :body (b* (((vl-paramdecl x) x))
          (change-vl-paramdecl x
                               :type (vl-paramtype-scopesubst x.type ss))))

(def-vl-scopesubst-list vl-paramdecllist-scopesubst
  :type vl-paramdecllist-p
  :element vl-paramdecl-scopesubst)


(def-vl-scopesubst vl-plainarg-scopesubst
  :type vl-plainarg-p
  :body (change-vl-plainarg x
                            :expr (vl-maybe-expr-scopesubst (vl-plainarg->expr x) ss)))

(def-vl-scopesubst-list vl-plainarglist-scopesubst
  :type vl-plainarglist-p
  :element vl-plainarg-scopesubst)

(def-vl-scopesubst vl-namedarg-scopesubst
  :type vl-namedarg-p
  :body (change-vl-namedarg x
                            :expr (vl-maybe-expr-scopesubst (vl-namedarg->expr x) ss)))

(def-vl-scopesubst-list vl-namedarglist-scopesubst
  :type vl-namedarglist-p
  :element vl-namedarg-scopesubst)

(def-vl-scopesubst vl-arguments-scopesubst
  :type vl-arguments-p
  :body
  (vl-arguments-case x
    :vl-arguments-named (change-vl-arguments-named x :args (vl-namedarglist-scopesubst x.args ss))
    :vl-arguments-plain (change-vl-arguments-plain x :args (vl-plainarglist-scopesubst x.args ss))))

(def-vl-scopesubst vl-paramvalue-scopesubst
  :type vl-paramvalue-p
  :body
  (b* ((x (vl-paramvalue-fix x)))
    (vl-paramvalue-case x
      :expr     (vl-expr-scopesubst x ss)
      :datatype (vl-datatype-scopesubst x ss))))

(def-vl-scopesubst-list vl-paramvaluelist-scopesubst
  :type vl-paramvaluelist-p
  :element vl-paramvalue-scopesubst)

(def-vl-scopesubst vl-maybe-paramvalue-scopesubst
  :type vl-maybe-paramvalue-p
  :body (and x (vl-paramvalue-scopesubst x ss)))

(def-vl-scopesubst vl-namedparamvalue-scopesubst
  :type vl-namedparamvalue-p
  :body
  (b* (((vl-namedparamvalue x) x))
    (change-vl-namedparamvalue x :value (vl-maybe-paramvalue-scopesubst x.value ss))))

(def-vl-scopesubst-list vl-namedparamvaluelist-scopesubst
  :type vl-namedparamvaluelist-p
  :element vl-namedparamvalue-scopesubst)

(def-vl-scopesubst vl-paramargs-scopesubst
  :type vl-paramargs-p
  :body
  (vl-paramargs-case x
    :vl-paramargs-named
    (change-vl-paramargs-named x :args (vl-namedparamvaluelist-scopesubst x.args ss))
    :vl-paramargs-plain
    (change-vl-paramargs-plain x :args (vl-paramvaluelist-scopesubst x.args ss))))


(def-vl-scopesubst vl-modinst-scopesubst
  :type vl-modinst-p
  :body (change-vl-modinst x
                           :range (vl-maybe-range-scopesubst (vl-modinst->range x) ss)
                           :paramargs (vl-paramargs-scopesubst (vl-modinst->paramargs x) ss)
                           :portargs (vl-arguments-scopesubst (vl-modinst->portargs x) ss)))

(def-vl-scopesubst-list vl-modinstlist-scopesubst
  :type vl-modinstlist-p
  :element vl-modinst-scopesubst)

(def-vl-scopesubst vl-gateinst-scopesubst
  :type vl-gateinst-p
  :body (change-vl-gateinst x
                            :range (vl-maybe-range-scopesubst (vl-gateinst->range x) ss)
                            :delay (vl-maybe-gatedelay-scopesubst (vl-gateinst->delay x) ss)
                            :args (vl-plainarglist-scopesubst (vl-gateinst->args x) ss)))

(def-vl-scopesubst-list vl-gateinstlist-scopesubst
  :type vl-gateinstlist-p
  :element vl-gateinst-scopesubst)



(def-vl-scopesubst vl-evatom-scopesubst
  :type vl-evatom-p
  :body (change-vl-evatom x
                          :expr (vl-expr-scopesubst (vl-evatom->expr x) ss)))

(def-vl-scopesubst-list vl-evatomlist-scopesubst
  :type vl-evatomlist-p
  :element vl-evatom-scopesubst)

(def-vl-scopesubst vl-eventcontrol-scopesubst
  :type vl-eventcontrol-p
  :body (change-vl-eventcontrol x
                                :atoms (vl-evatomlist-scopesubst (vl-eventcontrol->atoms x) ss)))
(def-vl-scopesubst vl-delaycontrol-scopesubst
  :type vl-delaycontrol-p
  :body (change-vl-delaycontrol x
                                :value (vl-expr-scopesubst (vl-delaycontrol->value x) ss)))

(def-vl-scopesubst vl-repeateventcontrol-scopesubst
  :type vl-repeateventcontrol-p
  :body (change-vl-repeateventcontrol x
                                      :expr (vl-expr-scopesubst (vl-repeateventcontrol->expr x) ss)
                                      :ctrl (vl-eventcontrol-scopesubst (vl-repeateventcontrol->ctrl x) ss)))

(def-vl-scopesubst vl-delayoreventcontrol-scopesubst
  :type vl-delayoreventcontrol-p
  :body (b* ((x (vl-delayoreventcontrol-fix x)))
          (case (tag x)
            (:vl-delaycontrol (vl-delaycontrol-scopesubst x ss))
            (:vl-eventcontrol (vl-eventcontrol-scopesubst x ss))
            (otherwise        (vl-repeateventcontrol-scopesubst x ss)))))

(def-vl-scopesubst vl-maybe-delayoreventcontrol-scopesubst
  :type vl-maybe-delayoreventcontrol-p
  :body (and x
             (vl-delayoreventcontrol-scopesubst x ss)))

(defthm vl-maybe-delayoreventcontrol-scopesubst-of-nil
  (iff (vl-maybe-delayoreventcontrol-scopesubst x ss)
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-scopesubst))))




(defines vl-stmt-scopesubst
  :short "Scopesubstitute into a @(see vl-stmt-p)"

  (define vl-stmt-scopesubst ((x     vl-stmt-p)
                         (ss vl-scopestack-p))
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
                                     :lvalue (vl-expr-scopesubst x.lvalue ss)
                                     :expr (vl-expr-scopesubst x.expr ss)
                                     :ctrl (vl-maybe-delayoreventcontrol-scopesubst x.ctrl ss))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x))
               (change-vl-deassignstmt x
                                       :lvalue (vl-expr-scopesubst x.lvalue ss))))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x))
               (change-vl-enablestmt x
                                     :id (vl-expr-scopesubst x.id ss)
                                     :args (vl-exprlist-scopesubst x.args ss))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x))
               (change-vl-disablestmt x
                                      :id (vl-expr-scopesubst x.id ss))))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x))
               (change-vl-returnstmt
                x :val (if x.val
                           (vl-expr-scopesubst x.val ss)
                         x.val))))
            (otherwise
             (b* (((vl-eventtriggerstmt x) x))
               (change-vl-eventtriggerstmt x
                                           :id (vl-expr-scopesubst x.id ss)))))
        (change-vl-compoundstmt
         x
         :exprs (vl-exprlist-scopesubst (vl-compoundstmt->exprs x) ss)
         :stmts (vl-stmtlist-scopesubst (vl-compoundstmt->stmts x) ss)
         :vardecls (vl-vardecllist-scopesubst (vl-compoundstmt->vardecls x) ss)
         :paramdecls (vl-paramdecllist-scopesubst (vl-compoundstmt->paramdecls x) ss)
         :ctrl (vl-maybe-delayoreventcontrol-scopesubst (vl-compoundstmt->ctrl x) ss)))))

  (define vl-stmtlist-scopesubst ((x     vl-stmtlist-p)
                             (ss vl-scopestack-p))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :verify-guards nil
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (consp x)
        (cons (vl-stmt-scopesubst (car x) ss)
              (vl-stmtlist-scopesubst (cdr x) ss))
      nil))
  ///
  (defprojection vl-stmtlist-scopesubst (x ss)
    (vl-stmt-scopesubst x ss)
    :already-definedp t)

  (verify-guards vl-stmt-scopesubst)

  (deffixequiv-mutual vl-stmt-scopesubst))


(def-vl-scopesubst vl-always-scopesubst
  :type vl-always-p
  :body (change-vl-always x
                          :stmt (vl-stmt-scopesubst (vl-always->stmt x) ss)))

(def-vl-scopesubst-list vl-alwayslist-scopesubst
  :type vl-alwayslist-p
  :element vl-always-scopesubst)

(def-vl-scopesubst vl-initial-scopesubst
  :type vl-initial-p
  :body (change-vl-initial x
                           :stmt (vl-stmt-scopesubst (vl-initial->stmt x) ss)))

(def-vl-scopesubst-list vl-initiallist-scopesubst
  :type vl-initiallist-p
  :element vl-initial-scopesubst)


;; BOZO how should subscopes work

(def-vl-scopesubst vl-fundecl-scopesubst
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       ;; BOZO is the return type of the function in its scope?  I think
       ;; probably not?
       (ss (vl-scopestack-push (vl-fundecl->blockscope x) ss)))
    (change-vl-fundecl x
                       :rettype (vl-datatype-scopesubst x.rettype ss)
                       :vardecls  (vl-vardecllist-scopesubst x.vardecls ss)
                       :paramdecls  (vl-paramdecllist-scopesubst x.paramdecls ss)
                       :portdecls (vl-portdecllist-scopesubst x.portdecls ss)
                       :body   (vl-stmt-scopesubst x.body ss))))

(def-vl-scopesubst-list vl-fundecllist-scopesubst
  :type vl-fundecllist-p
  :element vl-fundecl-scopesubst)


(def-vl-scopesubst vl-modelement-scopesubst
  :type vl-modelement-p
  :body
  (b* ((x (vl-modelement-fix x)))
    (case (tag x)
      (:vl-portdecl      (vl-portdecl-scopesubst x ss))
      (:vl-assign        (vl-assign-scopesubst x ss))
      (:vl-alias         (vl-alias-scopesubst x ss)) ;; BOZO
      (:vl-vardecl       (vl-vardecl-scopesubst x ss))
      (:vl-paramdecl     (vl-paramdecl-scopesubst x ss))
      (:vl-fundecl       (vl-fundecl-scopesubst x ss)) ;; BOZO scoping
      ;; (:vl-taskdecl   (vl-taskdecl-scopesubst x ss)) ;; BOZO
      (:vl-modinst       (vl-modinst-scopesubst x ss))
      (:vl-gateinst      (vl-gateinst-scopesubst x ss))
      (:vl-always        (vl-always-scopesubst x ss))
      (:vl-initial       (vl-initial-scopesubst x ss))
      ;; (:vl-typedef    (vl-typedef-scopesubst x ss)) ;; BOZO
      ;; (:vl-fwdtypedef (vl-fwdtypedef-scopesubst x ss)) ;; BOZO?
      ;; (:vl-import     (vl-import-scopesubst x ss)) ;; BOZO?
      (otherwise x))))




(def-vl-scopesubst vl-module-scopesubst
  :type vl-module-p
  :body (b* (((vl-module x) (vl-module-fix x))

             ;; The module may have its own parameters.  These parameters may
             ;; be overridden by other modules.  It isn't safe for us to use
             ;; their default values, because these defaults may need to be
             ;; overridden.  That means we can't just push X onto the SS.
             ;;
             ;; But, we do want to make sure that names in X appropriately
             ;; shadow any other names in other scopes, e.g., lexically
             ;; superior scopes or imported scopes.
             ;;
             ;; A stupid way to do this is to just erase the default values
             ;; from all the parameters in X.  (Our scopesubst routines only
             ;; carry out substitutions when the parameters have good, resolved
             ;; values.)  We can then push the modified X onto the scopestack
             ;; while we rewrite its interior.
             ;;
             ;; However, if we do this, then what about global parameters that
             ;; are used in X's parameters?  We'd need to

             ;; The module may have its own parameters.  These parameters may
             ;; refer to one another.  Consider for instance parameter a = 5.
             ;;

             (ss (vl-scopestack-push x ss)))
          (change-vl-module x
                            ;; name is unchanged
                            ;; BOZO wtf are params?
                            :ports      (vl-portlist-scopesubst      x.ports      ss)
                            :portdecls  (vl-portdecllist-scopesubst  x.portdecls  ss)
                            :assigns    (vl-assignlist-scopesubst    x.assigns    ss)
                            :vardecls   (vl-vardecllist-scopesubst   x.vardecls   ss)
                            :fundecls   (vl-fundecllist-scopesubst   x.fundecls   ss)
                            :paramdecls (vl-paramdecllist-scopesubst x.paramdecls ss)
                            :modinsts   (vl-modinstlist-scopesubst   x.modinsts   ss)
                            :gateinsts  (vl-gateinstlist-scopesubst  x.gateinsts  ss)
                            :alwayses   (vl-alwayslist-scopesubst    x.alwayses   ss)
                            :initials   (vl-initiallist-scopesubst   x.initials   ss)
                            ;; atts are unchanged
                            )))

(def-vl-scopesubst-list vl-modulelist-scopesubst
  :type vl-modulelist-p
  :element vl-module-scopesubst)
