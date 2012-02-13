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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

; BOZO move this whole file to mlib?


(defxdoc substitution
  :parents (mlib)
  :short "Substitution into Verilog constructs"
  :long "<p>We implement routines to substitute values for identifiers
throughout Verilog constructs such as expressions, assignments, and
modules.</p>

<p>Our main use of substitution is in unparameterization, where we use
substitution to replace parameters with their values throughout a module.
Because of this, and since there are usually only a couple of parameters per
module, we create ordinary alists and look up with @(see hons-assoc-equal)
rather than @(see hons-get).</p>")



(defalist vl-sigma-p (x)
  :parents (substitution)
  :short "An alist mapping strings to expressions, used in @(see substitution)."
  :key (stringp x)
  :val (vl-expr-p x)
  :keyp-of-nil nil
  :valp-of-nil nil)

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



(defsection vl-expr-subst
  :parents (substitution)
  :short "Substitute into a @(see vl-expr-p)."

  :long "<p>@(call vl-expr-subst) is given <tt>sigma</tt>, @(see vl-sigma-p),
and <tt>x</tt>, a @(see vl-expr-p), and produces a new expression by replacing
any simple identifiers (i.e., atoms which are @(see vl-id-p)'s) that are bound
in <tt>sigma</tt> with their values.</p>

<p>Note that this function does not descend into attributes.  It is not clear
whether that is the right behavior, but it seems that the handling of
attributes is left up to the implementation.</p>"

  (mutual-recursion
   (defund vl-expr-subst (x sigma)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-sigma-p sigma))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (let ((guts (vl-atom->guts x)))
           (if (vl-fast-id-p guts)
               (or (cdr (hons-assoc-equal (vl-id->name guts) sigma))
                   x)
             x))
       (let ((args-prime (vl-exprlist-subst (vl-nonatom->args x) sigma)))
         (change-vl-nonatom x :args args-prime))))

   (defund vl-exprlist-subst (x sigma)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-sigma-p sigma))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (cons (vl-expr-subst (car x) sigma)
               (vl-exprlist-subst (cdr x) sigma))
       nil))))

(defprojection vl-exprlist-subst (x sigma)
  (vl-expr-subst x sigma)
  :already-definedp t
  :parents (substitution)
  :nil-preservingp nil)

(defsection vl-expr-subst-lemmas
  :extension vl-expr-subst

  (local (defthm lemma
           (cond ((eq flag 'expr)
                  (implies (and (vl-expr-p x)
                                (vl-sigma-p sigma))
                           (vl-expr-p (vl-expr-subst x sigma))))
                 ((eq flag 'atts)
                  t)
                 (t
                  (implies (and (vl-exprlist-p x)
                                (vl-sigma-p sigma))
                           (vl-exprlist-p (vl-exprlist-subst x sigma)))))
           :rule-classes nil
           :hints(("Goal"
                   :induct (vl-expr-induct flag x)
                   :in-theory (enable vl-expr-subst
                                      vl-exprlist-subst)))))

  (defthm vl-expr-p-of-vl-expr-subst
    (implies (and (force (vl-expr-p x))
                  (force (vl-sigma-p sigma)))
             (vl-expr-p (vl-expr-subst x sigma)))
    :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

  (defthm vl-exprlist-p-of-vl-exprlist-subst
    (implies (and (force (vl-exprlist-p x))
                  (force (vl-sigma-p sigma)))
             (vl-exprlist-p (vl-exprlist-subst x sigma)))
    :hints(("Goal" :use ((:instance lemma (flag 'list))))))

  (verify-guards vl-expr-subst
    :hints(("Goal" :in-theory (enable vl-expr-subst)))))





; Now we can extend our notion of expression substitution across an entire
; module.  There's really nothing to this, we just walk through it and look for
; expressions.  But it's painful and long because of the complication of our
; parse tree.

(defmacro def-vl-subst (name &key type body)
  `(encapsulate
    ()
    (defxdoc ,name
      :parents (substitution)
      :short ,(str::cat "Substitute into a @(see " (symbol-name type) ").")
      :long ,(str::cat "@(def " (symbol-name name) ")"))

    (defund ,name (x sigma)
      (declare (xargs :guard (and (,type x)
                                  (vl-sigma-p sigma)))
               (ignorable x sigma))
      ,body)

    (defthm ,(intern-in-package-of-symbol
              (str::cat (symbol-name type) "-OF-" (symbol-name name))
              name)
      (implies (and (force (,type x))
                    (force (vl-sigma-p sigma)))
               (,type (,name x sigma)))
      :hints(("Goal" :in-theory (enable ,name))))))

(defmacro def-vl-subst-list (name &key type element)
  `(encapsulate
    ()
    (defxdoc ,name
      :parents (substitution)
      :short ,(str::cat "Substitute into a @(see " (symbol-name type) ").")
      :long ,(str::cat "@(def " (symbol-name name) ")"))

    (defprojection ,name (x sigma)
      (,element x sigma)
      :guard (and (,type x)
                  (vl-sigma-p sigma))
      :nil-preservingp nil)

    (defthm ,(intern-in-package-of-symbol
              (str::cat (symbol-name type) "-OF-" (symbol-name name))
              name)
      (implies (and (force (,type x))
                    (force (vl-sigma-p sigma)))
               (,type (,name x sigma)))
      :hints(("Goal" :induct (len x))))))

(def-vl-subst vl-maybe-expr-subst
  :type vl-maybe-expr-p
  :body (and x (vl-expr-subst x sigma)))

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
  :body (change-vl-vardecl x
                           :arrdims (vl-rangelist-subst (vl-vardecl->arrdims x) sigma)
                           :initval (vl-maybe-expr-subst (vl-vardecl->initval x) sigma)))

(def-vl-subst-list vl-vardecllist-subst
  :type vl-vardecllist-p
  :element vl-vardecl-subst)


(def-vl-subst vl-regdecl-subst
  :type vl-regdecl-p
  :body (change-vl-regdecl x
                           :range (vl-maybe-range-subst (vl-regdecl->range x) sigma)
                           :arrdims (vl-rangelist-subst (vl-regdecl->arrdims x) sigma)
                           :initval (vl-maybe-expr-subst (vl-regdecl->initval x) sigma)))

(def-vl-subst-list vl-regdecllist-subst
  :type vl-regdecllist-p
  :element vl-regdecl-subst)



(def-vl-subst vl-eventdecl-subst
  :type vl-eventdecl-p
  :body (change-vl-eventdecl x
                             :arrdims (vl-rangelist-subst (vl-eventdecl->arrdims x) sigma)))

(def-vl-subst-list vl-eventdecllist-subst
  :type vl-eventdecllist-p
  :element vl-eventdecl-subst)



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
  :body (vl-arguments
         (vl-arguments->namedp x)
         (if (vl-arguments->namedp x)
             (vl-namedarglist-subst (vl-arguments->args x) sigma)
           (vl-plainarglist-subst (vl-arguments->args x) sigma))))

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
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-subst x sigma))
          (:vl-eventcontrol (vl-eventcontrol-subst x sigma))
          (:vl-repeat-eventcontrol (vl-repeateventcontrol-subst x sigma))))

(def-vl-subst vl-maybe-delayoreventcontrol-subst
  :type vl-maybe-delayoreventcontrol-p
  :body (and x
             (vl-delayoreventcontrol-subst x sigma)))


(def-vl-subst vl-nullstmt-subst
  :type vl-nullstmt-p
  :body x)

(def-vl-subst vl-assignstmt-subst
  :type vl-assignstmt-p
  :body (change-vl-assignstmt x
                              :lvalue (vl-expr-subst (vl-assignstmt->lvalue x) sigma)
                              :expr (vl-expr-subst (vl-assignstmt->expr x) sigma)
                              :ctrl (vl-maybe-delayoreventcontrol-subst (vl-assignstmt->ctrl x) sigma)))

(def-vl-subst vl-deassignstmt-subst
  :type vl-deassignstmt-p
  :body (change-vl-deassignstmt x
                                :lvalue (vl-expr-subst (vl-deassignstmt->lvalue x) sigma)))

(def-vl-subst vl-enablestmt-subst
  :type vl-enablestmt-p
  :body (change-vl-enablestmt x
                              :id (vl-expr-subst (vl-enablestmt->id x) sigma)
                              :args (vl-exprlist-subst (vl-enablestmt->args x) sigma)))

(def-vl-subst vl-disablestmt-subst
  :type vl-disablestmt-p
  :body (change-vl-disablestmt x
                               :id (vl-expr-subst (vl-disablestmt->id x) sigma)))

(def-vl-subst vl-eventtriggerstmt-subst
  :type vl-eventtriggerstmt-p
  :body (change-vl-eventtriggerstmt x
                                    :id (vl-expr-subst (vl-eventtriggerstmt->id x) sigma)))

(def-vl-subst vl-atomicstmt-subst
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-subst x sigma))
          (:vl-assignstmt       (vl-assignstmt-subst x sigma))
          (:vl-deassignstmt     (vl-deassignstmt-subst x sigma))
          (:vl-enablestmt       (vl-enablestmt-subst x sigma))
          (:vl-disablestmt      (vl-disablestmt-subst x sigma))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-subst x sigma))))

(def-vl-subst vl-blockitem-subst
  :type vl-blockitem-p
  :body (case (tag x)
          (:vl-regdecl   (vl-regdecl-subst x sigma))
          (:vl-vardecl   (vl-vardecl-subst x sigma))
          (:vl-eventdecl (vl-eventdecl-subst x sigma))
          (:vl-paramdecl (vl-paramdecl-subst x sigma))))

(def-vl-subst-list vl-blockitemlist-subst
  :type vl-blockitemlist-p
  :element vl-blockitem-subst)


(defxdoc vl-stmt-subst
  :parents (substitution)
  :short "Substitute into a @(see vl-stmt-p)"
  :long "@(def vl-stmt-subst)")

(defxdoc vl-stmtlist-subst
  :parents (substitution)
  :short "Substitute into a @(see vl-stmtlist-p)"
  :long "@(def vl-stmtlist-subst)")

(mutual-recursion

 (defund vl-stmt-subst (x sigma)
   (declare (xargs :guard (and (vl-stmt-p x)
                               (vl-sigma-p sigma))
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 1)))
   (if (vl-fast-atomicstmt-p x)
       (vl-atomicstmt-subst x sigma)
     (change-vl-compoundstmt
      x
      :exprs (vl-exprlist-subst (vl-compoundstmt->exprs x) sigma)
      :stmts (vl-stmtlist-subst (vl-compoundstmt->stmts x) sigma)
      :decls (vl-blockitemlist-subst (vl-compoundstmt->decls x) sigma)
      :ctrl (vl-maybe-delayoreventcontrol-subst (vl-compoundstmt->ctrl x) sigma))))

 (defund vl-stmtlist-subst (x sigma)
   (declare (xargs :guard (and (vl-stmtlist-p x)
                               (vl-sigma-p sigma))
                   :measure (two-nats-measure (acl2-count x) 0)))
   (if (consp x)
       (cons (vl-stmt-subst (car x) sigma)
             (vl-stmtlist-subst (cdr x) sigma))
     nil)))

(defthm vl-stmtlist-subst-when-not-consp
  (implies (not (consp x))
           (equal (vl-stmtlist-subst x sigma)
                  nil))
  :hints(("Goal" :in-theory (enable vl-stmtlist-subst))))

(defthm vl-stmtlist-subst-of-cons
  (equal (vl-stmtlist-subst (cons a x) sigma)
         (cons (vl-stmt-subst a sigma)
               (vl-stmtlist-subst x sigma)))
  :hints(("Goal" :in-theory (enable vl-stmtlist-subst))))

(defprojection vl-stmtlist-subst (x sigma)
  (vl-stmt-subst x sigma)
  :already-definedp t)

(encapsulate
 ()
 (local (defthm lemma-1
          (implies (and (force (vl-maybe-delayoreventcontrol-p x))
                        (force (vl-sigma-p sigma)))
                   (iff (vl-maybe-delayoreventcontrol-subst x sigma)
                        x))
          :hints(("Goal"
                  :in-theory (e/d (vl-maybe-delayoreventcontrol-subst
                                   vl-maybe-delayoreventcontrol-p)
                                  (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-subst))
                  :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-subst))))))

 (local (defthm lemma-2
          (implies (and (not (vl-atomicstmt-p x))
                        (vl-stmtlist-p (vl-stmtlist-subst (vl-compoundstmt->stmts x) sigma))
                        (vl-stmt-p x)
                        (vl-sigma-p sigma))
                   (vl-compoundstmt-basic-checksp
                    (vl-compoundstmt->type x)
                    (vl-exprlist-subst (vl-compoundstmt->exprs x) sigma)
                    (vl-stmtlist-subst (vl-compoundstmt->stmts x) sigma)
                    (vl-compoundstmt->name x)
                    (vl-blockitemlist-subst (vl-compoundstmt->decls x) sigma)
                    (vl-maybe-delayoreventcontrol-subst (vl-compoundstmt->ctrl x) sigma)
                    (vl-compoundstmt->sequentialp x)
                    (vl-compoundstmt->casetype x)))
          :hints(("goal"
                  :in-theory (e/d (vl-compoundstmt-basic-checksp)
                                  (vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
                  :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))))))

 (defthm-vl-flag-stmt-p vl-stmt-p-of-vl-stmt-subst
   (stmt (implies (and (force (vl-stmt-p x))
                       (force (vl-sigma-p sigma)))
                  (vl-stmt-p (vl-stmt-subst x sigma))))
   (list (implies (and (force (vl-stmtlist-p x))
                       (force (vl-sigma-p sigma)))
                  (vl-stmtlist-p (vl-stmtlist-subst x sigma))))
   :hints(("Goal"
           :induct (vl-flag-stmt-p flag x)
           :expand ((vl-stmt-subst x sigma)))))

 (verify-guards vl-stmt-subst))

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
                            :regdecls   (vl-regdecllist-subst   x.regdecls   sigma)
                            :eventdecls (vl-eventdecllist-subst x.eventdecls sigma)
                            :paramdecls (vl-paramdecllist-subst x.paramdecls sigma)
                            :modinsts   (vl-modinstlist-subst   x.modinsts   sigma)
                            :gateinsts  (vl-gateinstlist-subst  x.gateinsts  sigma)
                            :alwayses   (vl-alwayslist-subst    x.alwayses   sigma)
                            :initials   (vl-initiallist-subst   x.initials   sigma)
                            ;; atts are unchanged
                            )))

(defthm vl-module->name-of-vl-module-subst
  (equal (vl-module->name (vl-module-subst x sigma))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-subst))))


(def-vl-subst-list vl-modulelist-subst
  :type vl-modulelist-p
  :element vl-module-subst)

